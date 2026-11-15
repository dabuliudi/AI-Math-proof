"""调度器：让外部编程 agent（默认是本机 Codex 命令行）无人值守地清队列或跑评测。

两种模式
* 队列：每个工人循环“领题 → 调 agent 证明 → 看结果 → 没证出就代为归还”，直到队列空、任务数或时长用完、或熔断。
* 评测：每道评测题让 agent 把证明写进指定文件；调度器自己用内核再校验一遍才记成绩，不采信 agent 的自述。

控制与记账
* 并行数、任务上限、总时长、单题时限、连续失败熔断（连续 N 次没有任何进展就整体停下）。
* 每次调用记一行到 forge/data/runs/<轮次>.jsonl：任务、工人、结果、耗时、agent 报告的 token 用量、最后一条消息摘要。

信任边界
agent 在仓库里有写权限，理论上可以改日志或队列文件，所以：库的真实性由 `forge audit --replay` 兜底
（内核重放 + 逐条核对命题与公理）；评测成绩只来自调度器自己的校验。提示词也要求 agent 只通过 ./forge.sh 改状态。
"""
import json
import os
import re
import shlex
import signal
import subprocess
import threading
import time
from pathlib import Path

from . import bench, tasks
from .leanrun import DATA, ROOT

RUNS = DATA / 'runs'
CODEX = '/Applications/ChatGPT.app/Contents/Resources/codex-cli/bin/codex'

QUEUE_PROMPT = '''You are a proving agent working in a Lean 4 "theorem forge" at {root}.
First read forge/AGENT_GUIDE.md (it is short) and follow it exactly. Your agent name is `{agent}`.

The scheduler has already claimed this task for you:
- name: {name}
- statement (Lean signature, `<binders> : <conclusion>`): {statement}
- informal / plan: {informal}
- earlier failed attempts: {attempts}

Goal: get this task into the library, either by proving it (`./forge.sh submit {name} <file> --agent {agent}`)
or, if the statement is false, by proving its negation (`<name>_disproof`, with `--disproof`). Check small cases before
trusting or doubting the statement. Use `./forge.sh check {name} <file>` while iterating; `submit` only when `check` passes.
Useful: `./forge.sh search "<words>"`, `./forge.sh lookup "<name fragments>"`, `./forge.sh show <name>`, `./forge.sh source <name>`.
Long proofs may be split with `./forge.sh sketch` (see the guide).

Rules:
- Keep drafts only in {scratch}. Change forge state only through ./forge.sh; never edit files under forge/data or lean/ directly.
- Never alter the statement. Never use sorry/axiom/native_decide or other escape hatches (the checker rejects them anyway).
- Lean checks take 5-60 s; submit takes up to ~2 min. Give shell commands a long enough timeout.
- You have about {minutes} minutes. If you cannot finish, run
  `./forge.sh release {name} --agent {agent} --note "<what you tried and where it got stuck>"` before stopping.
End with one line: RESULT: proved | disproved | sketched | released, plus a one-sentence summary.
'''

BENCH_PROMPT = '''You are a proving agent working in a Lean 4 project at {root}. Read forge/AGENT_GUIDE.md first
(the sections on writing submissions apply). Your agent name is `{agent}`.

Prove this benchmark problem. Problem name: {name}
Statement (Lean signature `<binders> : <conclusion>`; the notation assumes `open {opens}`):
{statement}

Write the complete proof to {proof} as a single Lean declaration
`theorem {name} <same binders> : <same conclusion> := by ...` (helper lemmas named `{name}_aux1`, ... may come first).
Test it with `./forge.sh bench-check {set} {name} {proof} --run {practice} --agent {agent}` (only checks; it never adds
anything to the library). Iterate until it reports "solved": true.
Rules: keep files only in {scratch}; never edit files under forge/data or lean/; never use sorry/axiom/native_decide.
You have about {minutes} minutes. End with one line: RESULT: solved | unsolved.
'''


def _tokens(text):
    found = re.findall(r'tokens used\s*\n?\s*([\d,]+)', text)
    return int(found[-1].replace(',', '')) if found else None


class Scheduler:
    def __init__(self, run, workers=2, max_tasks=10, budget_minutes=60, task_minutes=20, max_failures=4,
                 agent_cmd=None, model=None, effort=None, dry_run=False):
        if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_-]{0,60}', run):
            raise ValueError('轮次名只能含字母、数字、- 和 _')
        self.run, self.workers, self.max_tasks = run, workers, max_tasks
        self.deadline = time.time() + budget_minutes * 60
        self.task_seconds = task_minutes * 60
        self.max_failures = max_failures
        self.agent_cmd = shlex.split(agent_cmd) if agent_cmd else None
        self.model, self.effort, self.dry_run = model, effort, dry_run
        self.lock = threading.Lock()
        self.started = self.failures_in_a_row = self.tokens = 0
        self.stop_reason = None
        self.records = []
        self.scratch = DATA / 'staging' / 'agents' / run
        RUNS.mkdir(parents=True, exist_ok=True)
        self.log = RUNS / f'{run}.jsonl'

    # ---- 调 agent ----
    def _command(self, last_message):
        if self.agent_cmd:
            return self.agent_cmd
        cmd = [CODEX, 'exec', '-s', 'workspace-write', '--ephemeral', '--skip-git-repo-check', '-C', str(ROOT),
               '-o', str(last_message)]
        if self.model:
            cmd += ['-m', self.model]
        if self.effort:
            cmd += ['-c', f'model_reasoning_effort="{self.effort}"']
        return cmd + ['-']

    def _invoke(self, prompt, worker):
        """运行一次 agent，返回 (退出码, 最后一条消息, token 数, 是否超时)。提示词经 stdin 传入。"""
        last = self.scratch / f'{worker}.last.txt'
        last.unlink(missing_ok=True)
        if self.dry_run:
            return 0, 'RESULT: dry-run', 0, False
        timeout = max(60, min(self.task_seconds, self.deadline - time.time()))
        # 新进程组：超时时连同 agent 启动的 Lean 子进程一起结束，不留孤儿进程占内存。
        proc = subprocess.Popen(self._command(last), stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                cwd=ROOT, text=True, encoding='utf-8', errors='replace', start_new_session=True)
        try:
            output, _ = proc.communicate(prompt, timeout=timeout)
            code, slow = proc.returncode, False
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGTERM)
            try:
                output, _ = proc.communicate(timeout=30)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                output, _ = proc.communicate()
            code, slow = -1, True
        output = output or ''
        message = last.read_text(encoding='utf-8', errors='replace') if last.exists() else output[-2000:]
        return code, message.strip(), _tokens(output), slow

    # ---- 记账与熔断 ----
    def _record(self, row):
        row.update(run=self.run, at=time.strftime('%Y-%m-%dT%H:%M:%S%z'))
        with self.lock:
            self.records.append(row)
            self.tokens += row.get('tokens') or 0
            self.failures_in_a_row = 0 if row['progress'] else self.failures_in_a_row + 1
            if self.failures_in_a_row >= self.max_failures and not self.stop_reason:
                self.stop_reason = f'熔断：连续 {self.failures_in_a_row} 次没有进展'
            with open(self.log, 'a', encoding='utf-8') as handle:
                handle.write(json.dumps(row, ensure_ascii=False) + '\n')

    def _may_start(self):
        with self.lock:
            if self.stop_reason:
                return False
            if time.time() > self.deadline - 120:
                self.stop_reason = '总时长用完'
                return False
            if self.started >= self.max_tasks:
                self.stop_reason = '任务数用完'
                return False
            self.started += 1
            return True

    # ---- 队列模式 ----
    def _queue_worker(self, index, prefix):
        agent = f'{self.run}-w{index}'
        scratch = self.scratch / agent
        scratch.mkdir(parents=True, exist_ok=True)
        while self._may_start():
            task = tasks.claim(agent, prefix=prefix)
            if task is None:
                with self.lock:
                    self.started -= 1
                    self.stop_reason = self.stop_reason or '队列里没有可领的任务'
                return
            attempts = '; '.join(a.get('note', '')[:300] for a in task.get('attempts', [])[-3:]) or 'none'
            prompt = QUEUE_PROMPT.format(root=ROOT, agent=agent, name=task['name'], statement=task['statement'],
                                         informal=(task.get('informal') or '')[:1500] or 'none', attempts=attempts,
                                         scratch=scratch, minutes=self.task_seconds // 60)
            began = time.time()
            code, message, used, slow = self._invoke(prompt, agent)
            state, after = tasks.load(task['name'])
            if state == 'done' and after.get('closed_by') == agent:
                outcome = after.get('status', 'done')
            elif after and after.get('sketches') and state in ('open', 'claimed'):
                outcome = 'sketched'
            elif state == 'claimed' and after.get('claimed_by') == agent:
                tasks.release(task['name'], agent, f'调度器代为归还（agent 未完成{"，超时" if slow else ""}）：{message[-600:]}')
                outcome = 'released_by_scheduler'
            else:
                outcome = 'released' if state == 'open' else f'unexpected:{state}'
            self._record(dict(mode='queue', task=task['name'], worker=agent, outcome=outcome,
                              progress=outcome in ('proved', 'disproved', 'sketched'), seconds=round(time.time() - began),
                              tokens=used, exit=code, timed_out=slow, message=message[-800:]))

    # ---- 评测模式 ----
    def _bench_worker(self, index, set_name, problems):
        agent = f'{self.run}-w{index}'
        scratch = self.scratch / agent
        scratch.mkdir(parents=True, exist_ok=True)
        while True:
            with self.lock:
                if not problems:
                    self.stop_reason = self.stop_reason or '评测题都已发出'
                    return
                item = problems.pop(0)
            if not self._may_start():
                return
            proof = scratch / f'{item["name"]}.lean'
            prompt = BENCH_PROMPT.format(root=ROOT, agent=agent, name=item['name'], statement=item['statement'],
                                         opens=item.get('opens', '') or '(nothing)', proof=proof, set=set_name,
                                         practice=f'{self.run}-practice', scratch=scratch, minutes=self.task_seconds // 60)
            began = time.time()
            code, message, used, slow = self._invoke(prompt, agent)
            solved, reason = False, '没有交出证明文件'
            if proof.exists():  # 正式成绩只来自这里：调度器自己用内核校验 agent 留下的证明
                verdict = bench.check(set_name, item['name'], proof.read_text(encoding='utf-8'), self.run, 'scheduler')
                solved, reason = verdict['solved'], verdict.get('reason', '')
            self._record(dict(mode='bench', task=item['name'], worker=agent, outcome='solved' if solved else 'unsolved',
                              progress=solved, seconds=round(time.time() - began), tokens=used, exit=code,
                              timed_out=slow, reason=reason[:300], message=message[-500:]))

    def _run_threads(self, target, args):
        threads = [threading.Thread(target=target, args=(i,) + args, daemon=True) for i in range(self.workers)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()
        return self.summary()

    def run_queue(self, prefix=None):
        return self._run_threads(self._queue_worker, (prefix,))

    def run_bench(self, set_name, limit=None, only_unsolved=True):
        items = bench.load(set_name)
        if not items:
            raise ValueError(f'没有评测集 {set_name}')
        if only_unsolved:
            solved = set()
            for path in (bench.RUNS.glob(f'{set_name}.*.jsonl') if bench.RUNS.exists() else []):
                if path.name.endswith('-practice.jsonl'):
                    continue
                for line in path.read_text(encoding='utf-8').splitlines():
                    row = json.loads(line)
                    if row['solved'] and row.get('agent') == 'scheduler':
                        solved.add(row['problem'])
            items = [i for i in items if i['name'] not in solved]
        problems = items[:limit] if limit else items
        return self._run_threads(self._bench_worker, (set_name, problems))

    def summary(self):
        outcomes = {}
        for row in self.records:
            outcomes[row['outcome']] = outcomes.get(row['outcome'], 0) + 1
        return dict(run=self.run, calls=len(self.records), outcomes=outcomes, tokens=self.tokens,
                    stopped=self.stop_reason, log=os.path.relpath(self.log, ROOT))


def report(run):
    """读回某一轮的记账。"""
    path = RUNS / f'{run}.jsonl'
    if not path.exists():
        return dict(ok=False, reason=f'没有轮次 {run}')
    rows = [json.loads(line) for line in path.read_text(encoding='utf-8').splitlines() if line.strip()]
    outcomes = {}
    for row in rows:
        outcomes[row['outcome']] = outcomes.get(row['outcome'], 0) + 1
    return dict(run=run, calls=len(rows), outcomes=outcomes, tokens=sum(r.get('tokens') or 0 for r in rows),
                seconds=sum(r['seconds'] for r in rows), rows=[{k: r[k] for k in ('task', 'worker', 'outcome', 'seconds', 'tokens')}
                                                              for r in rows])
