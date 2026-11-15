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
import shutil
import signal
import subprocess
import threading
import time
from pathlib import Path

from . import bench, tasks
from .leanrun import DATA, ROOT

RUNS = DATA / 'runs'
MAC_CODEX = '/Applications/ChatGPT.app/Contents/Resources/codex-cli/bin/codex'
# agent 在提示词里看到的 forge 命令：macOS/Linux 用 ./forge.sh，Windows 用 forge.cmd
FORGE = 'forge.cmd' if os.name == 'nt' else './forge.sh'


def find_codex():
    """Codex 命令行的位置：环境变量 FORGE_CODEX 优先，其次 PATH 里的 codex，最后是 macOS 桌面版自带的那份。"""
    explicit = os.environ.get('FORGE_CODEX')
    if explicit:
        return explicit
    found = shutil.which('codex')
    if found:
        return found
    if Path(MAC_CODEX).exists():
        return MAC_CODEX
    raise RuntimeError('找不到 Codex 命令行：请安装 codex，或用环境变量 FORGE_CODEX 指定它的完整路径')


def _kill_tree(proc, hard=False):
    """结束 agent 及其启动的所有子进程（包括 Lean）。"""
    if os.name == 'nt':
        subprocess.run(['taskkill', '/PID', str(proc.pid), '/T', '/F'], capture_output=True)
        return
    try:
        os.killpg(proc.pid, signal.SIGKILL if hard else signal.SIGTERM)
    except (ProcessLookupError, PermissionError):
        pass

QUEUE_PROMPT = '''You are a proving agent working in a Lean 4 "theorem forge" at {root}.
First read forge/AGENT_GUIDE.md (it is short) and follow it exactly. Your agent name is `{agent}`.

The scheduler has already claimed this task for you:
- name: {name}
- statement (Lean signature, `<binders> : <conclusion>`): {statement}
- informal / plan: {informal}
- earlier failed attempts: {attempts}

Goal: get this task into the library, either by proving it (`{forge} submit {name} <file> --agent {agent}`)
or, if the statement is false, by proving its negation (`<name>_disproof`, with `--disproof`). Check small cases before
trusting or doubting the statement. Use `{forge} check {name} <file>` while iterating; `submit` only when `check` passes.
Useful: `{forge} search "<words>"`, `{forge} lookup "<name fragments>"`, `{forge} show <name>`, `{forge} source <name>`.
Long proofs may be split with `{forge} sketch` (see the guide).

Rules:
- Keep drafts only in {scratch}. Change forge state only through {forge}; never edit files under forge/data or lean/ directly.
- Never alter the statement. Never use sorry/axiom/native_decide or other escape hatches (the checker rejects them anyway).
- Lean checks take 5-60 s; submit takes up to ~2 min. Give shell commands a long enough timeout.
- You have about {minutes} minutes. If you cannot finish, run
  `{forge} release {name} --agent {agent} --note "<what you tried and where it got stuck>"` before stopping.
End with one line: RESULT: proved | disproved | sketched | released, plus a one-sentence summary.
'''

# 评测提示词。v1：让 agent 先读完整的 AGENT_GUIDE.md；v2：把评测需要的规则直接写进提示词（上下文小得多）。
BENCH_PROMPT_V1 = '''You are a proving agent working in a Lean 4 project at {root}. Read forge/AGENT_GUIDE.md first
(the sections on writing submissions apply). Your agent name is `{agent}`.

Prove this benchmark problem. Problem name: {name}
Statement (Lean signature `<binders> : <conclusion>`; the notation assumes `open {opens}`):
{statement}

Write the complete proof to {proof} as a single Lean declaration
`theorem {name} <same binders> : <same conclusion> := by ...` (helper lemmas named `{name}_aux1`, ... may come first).
Test it with `{forge} bench-check {set} {name} {proof} --run {practice} --agent {agent}` (only checks; it never adds
anything to the library). Iterate until it reports "solved": true.
Rules: keep files only in {scratch}; never edit files under forge/data or lean/; never use sorry/axiom/native_decide.
You have about {minutes} minutes. End with one line: RESULT: solved | unsolved.
'''

BENCH_PROMPT_V2 = '''You are a proving agent working in a Lean 4 project at {root} (Lean 4 + Mathlib). Your agent name is `{agent}`.
You do NOT need to read forge/AGENT_GUIDE.md; everything you need is here.

Prove this benchmark problem. Problem name: {name}
Statement (Lean signature `<binders> : <conclusion>`; the notation assumes `open {opens}`):
{statement}

Write the complete proof to {proof}. Format rules (the checker enforces them):
- The file is checked inside `namespace Mathlib2` with all of Mathlib imported; `open ...` lines are allowed at top level.
- Only top-level `theorem`/`lemma` declarations. Helper lemmas are named `{name}_aux1`, `{name}_aux2`, ... and come first;
  the last declaration is `theorem {name} <same binders> : <same conclusion> := by ...`.
- Not allowed: sorry, axiom, def, instance, notation, macro, set_option, native_decide, run_tac. Undefined names are errors.
- If the statement is false, prove its negation instead: `theorem {name}_disproof : ¬ (∀ <binders>, <conclusion>) := by ...`.
Check it with `{forge} bench-check {set} {name} {proof} --run {practice} --agent {agent}` (it only checks; nothing is added
to the library) and iterate until it reports "solved": true (or, for a disproof, that the check passed).
Useful: `{forge} lookup "<name fragments>"` finds exact Mathlib lemma names.
Keep files only in {scratch}; never edit files under forge/data or lean/.
You have about {minutes} minutes. End with one line: RESULT: solved | disproved | unsolved.
'''


BENCH_PROMPTS = {'v1': BENCH_PROMPT_V1, 'v2': BENCH_PROMPT_V2}

RETRY_NOTE = '''
A previous attempt on this problem (reasoning effort {effort}) did not finish. Its last proof draft is at {draft};
the checker said: {reason}
Its final message was: {message}
Build on it if it is useful, or take a different approach if it was a dead end.
'''

REVIEW_PROMPT = '''You are an independent reviewer in a Lean 4 project at {root}. You did not write the formalisation or the proof.
Your agent name is `{agent}`. Your only job is to judge whether one Lean statement faithfully says what the paper says.

Paper: {title} ({paper_id}). Its full text (LaTeX formulas inline) is in {paper_text} - read the relevant parts yourself;
do not rely on the auditor's summary below.

Item to review:
- paper label: {label}
- auditor's short paraphrase of the original: {original}
- auditor's notes on interpretation: {notes}
- Lean task name: {name}
- Lean statement (signature `<binders> : <conclusion>`): {statement}
- kernel verdict in the library: {verdict}
Library definitions used by the statement can be inspected with `{forge} source <name>` or `{forge} lookup "<fragment>"`.

Decide one of:
- faithful: the Lean statement says exactly what the paper's claim says (harmless strengthening such as dropping an unused
  hypothesis is fine, say so in the note);
- unfaithful: it changes the meaning (missing/extra hypotheses that matter, wrong quantifier, off-by-one, wrong definition, ...);
- unsure: the paper is ambiguous or you cannot tell.
If the kernel verdict is "disproved", be especially careful: say whether the PAPER's claim is false as printed, or only the
formalisation is wrong. Quote the paper sentence you relied on.

Record your verdict with exactly one command:
{forge} review {name} --agent {agent} --verdict <faithful|unfaithful|unsure> --note "<2-5 sentences, with the quoted sentence>"
Do not edit any files. End with one line: RESULT: faithful | unfaithful | unsure.
'''


def _tokens(text):
    found = re.findall(r'tokens used\s*\n?\s*([\d,]+)', text)
    return int(found[-1].replace(',', '')) if found else None


class Scheduler:
    def __init__(self, run, workers=2, max_tasks=10, budget_minutes=60, task_minutes=20, max_failures=4,
                 agent_cmd=None, model='gpt-6.1-sol', effort='xhigh', dry_run=False, sandbox='workspace-write', ladder=None, prompt='v1'):
        if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_@-]{0,60}', run):
            raise ValueError('轮次名只能含字母、数字、-、_ 和 @（例如 mf2f-r2@win）')
        self.run, self.workers, self.max_tasks = run, workers, max_tasks
        self.deadline = time.time() + budget_minutes * 60
        self.task_seconds = task_minutes * 60
        self.max_failures = max_failures
        self.agent_cmd = shlex.split(agent_cmd) if agent_cmd else None
        self.model, self.effort, self.dry_run, self.sandbox = model, effort, dry_run, sandbox
        # 分级尝试：[(推理强度, 分钟), ...]；先用便宜的档位，做不出再升档并把上一次的草稿和报错交给下一次
        self.ladder = ladder
        if prompt not in ('v1', 'v2'):
            raise ValueError('提示词版本只有 v1、v2')
        self.prompt = prompt
        self.lock = threading.Lock()
        self.started = self.failures_in_a_row = self.tokens = 0
        self.stop_reason = None
        self.records = []
        self.last_raw = {}
        self.scratch = DATA / 'staging' / 'agents' / run
        RUNS.mkdir(parents=True, exist_ok=True)
        self.log = RUNS / f'{run}.jsonl'

    # ---- 调 agent ----
    def _command(self, last_message, effort=None):
        if self.agent_cmd:
            return self.agent_cmd
        effort = effort or self.effort
        cmd = [find_codex(), 'exec', '-s', self.sandbox, '--ephemeral', '--skip-git-repo-check', '-C', str(ROOT),
               '-o', str(last_message)]
        if self.model:
            cmd += ['-m', self.model]
        if effort:
            cmd += ['-c', f'model_reasoning_effort="{effort}"']
        return cmd + ['-']

    def _invoke(self, prompt, worker, effort=None, seconds=None):
        """运行一次 agent，返回 (退出码, 最后一条消息, token 数, 是否超时)。提示词经 stdin 传入。
        effort / seconds 可以覆盖本轮的默认推理强度和单题时限（分级尝试时用）。"""
        last = self.scratch / f'{worker}.last.txt'
        last.unlink(missing_ok=True)
        if self.dry_run:
            return 0, 'RESULT: dry-run', 0, False
        timeout = max(60, min(seconds or self.task_seconds, self.deadline - time.time()))
        # 新进程组：超时时连同 agent 启动的 Lean 子进程一起结束，不留孤儿进程占内存。
        extra = dict(creationflags=subprocess.CREATE_NEW_PROCESS_GROUP) if os.name == 'nt' else dict(start_new_session=True)
        proc = subprocess.Popen(self._command(last, effort), stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                cwd=ROOT, text=True, encoding='utf-8', errors='replace', **extra)
        try:
            output, _ = proc.communicate(prompt, timeout=timeout)
            code, slow = proc.returncode, False
        except subprocess.TimeoutExpired:
            _kill_tree(proc)
            try:
                output, _ = proc.communicate(timeout=30)
            except subprocess.TimeoutExpired:
                _kill_tree(proc, hard=True)
                output, _ = proc.communicate()
            code, slow = -1, True
        output = output or ''
        message = last.read_text(encoding='utf-8', errors='replace') if last.exists() else output[-2000:]
        self.last_raw[worker] = output[-1500:]
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
            prompt = QUEUE_PROMPT.format(forge=FORGE, root=ROOT, agent=agent, name=task['name'], statement=task['statement'],
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
                              tokens=used, exit=code, timed_out=slow, message=message[-800:],
                              raw=self.last_raw.get(agent, '')[-1200:] if code not in (0, -1) else ''))

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
            steps = self.ladder or [(None, None)]
            previous = None
            for attempt, (effort, minutes) in enumerate(steps):
                prompt = BENCH_PROMPTS[self.prompt].format(forge=FORGE, root=ROOT, agent=agent, name=item['name'], statement=item['statement'],
                                             opens=item.get('opens', '') or '(nothing)', proof=proof, set=set_name,
                                             practice=f'{self.run}-practice', scratch=scratch,
                                             minutes=minutes or self.task_seconds // 60)
                if previous:
                    prompt += RETRY_NOTE.format(**previous)
                overrides = dict(effort=effort, seconds=minutes * 60) if effort else {}
                began = time.time()
                code, message, used, slow = self._invoke(prompt, agent, **overrides)
                solved, reason = False, '没有交出证明文件'
                if proof.exists():  # 正式成绩只来自这里：调度器自己用内核校验 agent 留下的证明
                    verdict = bench.check(set_name, item['name'], proof.read_text(encoding='utf-8'), self.run, 'scheduler')
                    solved, reason = verdict['solved'], verdict.get('reason', '')
                # 评测里做不出难题是正常的，不算“没有进展”；只有 agent 本身出错、或连证明文件都没交，才计入熔断。
                attempted = code == 0 and proof.exists()
                self._record(dict(mode='bench', task=item['name'], worker=agent, outcome='solved' if solved else 'unsolved',
                                  progress=solved or attempted, seconds=round(time.time() - began), tokens=used, exit=code,
                                  timed_out=slow, reason=reason[:300], message=message[-500:], attempt=attempt + 1,
                                  effort=effort or self.effort, prompt=self.prompt,
                                  raw=self.last_raw.get(agent, '')[-1200:] if code not in (0, -1) else ''))
                if solved or self.stop_reason:
                    break
                draft = scratch / f'{item["name"]}.attempt{attempt + 1}.lean'
                if proof.exists():
                    draft.write_text(proof.read_text(encoding='utf-8'), encoding='utf-8')
                previous = dict(effort=effort or self.effort, draft=draft if draft.exists() else '(no proof file was left)',
                                reason=reason[:600], message=message[-600:] or '(none)')

    # ---- 论文复核模式 ----
    def _review_worker(self, index, paper, items, paper_text):
        agent = f'{self.run}-w{index}'
        (self.scratch / agent).mkdir(parents=True, exist_ok=True)
        from .paper import reviews
        while True:
            with self.lock:
                if not items:
                    self.stop_reason = self.stop_reason or '待复核的命题都已发出'
                    return
                item, verdict = items.pop(0)
            if not self._may_start():
                return
            prompt = REVIEW_PROMPT.format(root=ROOT, agent=agent, forge=FORGE, title=paper.get('title', ''),
                                          paper_id=paper.get('arxiv', ''), paper_text=paper_text, label=item.get('label', ''),
                                          original=item.get('original', ''), notes=item.get('notes', ''), name=item['name'],
                                          statement=item['lean'], verdict=verdict)
            began = time.time()
            code, message, used, slow = self._invoke(prompt, agent)
            mine = [r for r in reviews().get(item['name'], []) if r['agent'] == agent]
            outcome = mine[-1]['verdict'] if mine else 'no_review'
            self._record(dict(mode='review', task=item['name'], worker=agent, outcome=outcome, progress=bool(mine),
                              seconds=round(time.time() - began), tokens=used, exit=code, timed_out=slow,
                              message=message[-500:], raw=self.last_raw.get(agent, '')[-1200:] if code not in (0, -1) else ''))

    def run_review(self, paper_file, paper_text):
        """复核一篇论文里已有内核结论（证明或证伪）的全部命题；已经有独立复核记录的跳过。"""
        from .paper import reviews
        paper = json.loads(Path(paper_file).read_text(encoding='utf-8'))
        if not Path(paper_text).exists():
            raise ValueError(f'找不到论文原文 {paper_text}')
        done_reviews = reviews()
        items = []
        for item in paper.get('statements', []):
            if not item.get('name') or not item.get('lean'):
                continue
            state, task = tasks.load(item['name'])
            if state != 'done' or task.get('status') not in ('proved', 'disproved', 'known'):
                continue  # 还没有内核结论的不复核
            prover = task.get('closed_by', '')
            if any(r['agent'] != prover for r in done_reviews.get(item['name'], [])):
                continue  # 已经有人独立复核过
            items.append((item, task['status']))
        return self._run_threads(self._review_worker, (paper, items, str(Path(paper_text).resolve())))

    def _run_threads(self, target, args):
        threads = [threading.Thread(target=target, args=(i,) + args, daemon=True) for i in range(self.workers)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()
        return self.summary()

    def run_queue(self, prefix=None):
        return self._run_threads(self._queue_worker, (prefix,))

    def run_bench(self, set_name, limit=None, only_unsolved=True, resume=False, shard=None, sample=None, seed=0,
                  skip_refuted=False, problems=None):
        items = bench.load(set_name)
        if not items:
            raise ValueError(f'没有评测集 {set_name}')
        if problems:
            unknown = set(problems) - {i['name'] for i in items}
            if unknown:
                raise ValueError(f'评测集里没有这些题：{sorted(unknown)}')
            items = [i for i in items if i['name'] in set(problems)]
        if skip_refuted:
            # 以前的轮次里已被内核反证的题（评测集写错了），对比不同设置时没有意义，去掉
            refuted = set()
            for row in bench.score(set_name)['runs']:
                refuted.update(row.get('refuted', []))
            items = [i for i in items if i['name'] not in refuted]
        if sample:
            # 固定种子抽样：不同档位、不同轮次拿到的是同一组题，结果才能直接比较
            import random
            chosen = set(random.Random(seed).sample([i['name'] for i in items], min(sample, len(items))))
            items = [i for i in items if i['name'] in chosen]
        if shard:
            # 多台机器分工：按题目在评测集文件里的位置切分，各台机器拿到的子集互不重叠、合起来正好是全集。
            k, n = shard
            items = [item for index, item in enumerate(items) if index % n == k - 1]
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
        if resume and self.log.exists():
            done = set()
            for line in self.log.read_text(encoding='utf-8').splitlines():
                row = json.loads(line)
                if row['outcome'] == 'solved' or row['exit'] == 0 or row['timed_out']:
                    done.add(row['task'])
            items = [i for i in items if i['name'] not in done]
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


def compare(runs, problems_from=None):
    """在同一组题上比较几个轮次：解出数、token、用时。默认取各轮都做过的题的交集，
    也可以指定以某个轮次做过的题为准（problems_from）。同一题在一个轮次里有多次尝试时，token 和用时累加。"""
    import statistics
    tables = {}
    for run in runs:
        path = RUNS / f'{run}.jsonl'
        if not path.exists():
            raise ValueError(f'没有轮次 {run}')
        per = {}
        for line in path.read_text(encoding='utf-8').splitlines():
            row = json.loads(line)
            item = per.setdefault(row['task'], dict(solved=False, tokens=0, seconds=0, attempts=0))
            item['solved'] = item['solved'] or row['outcome'] in ('solved', 'proved', 'disproved')
            item['tokens'] += row.get('tokens') or 0
            item['seconds'] += row['seconds']
            item['attempts'] += 1
        tables[run] = per
    if problems_from:
        common = set(tables[problems_from])
    else:
        common = set.intersection(*(set(t) for t in tables.values()))
    rows = []
    for run in runs:
        items = [tables[run][p] for p in common if p in tables[run]]
        solved = [i for i in items if i['solved']]
        tokens = sum(i['tokens'] for i in items)
        rows.append(dict(run=run, problems=len(items), solved=len(solved), tokens=tokens,
                         tokens_per_solved=round(tokens / len(solved)) if solved else None,
                         median_seconds=statistics.median(i['seconds'] for i in items) if items else None,
                         unsolved=sorted(p for p in common if p in tables[run] and not tables[run][p]['solved'])))
    return dict(problems=len(common), runs=rows)
