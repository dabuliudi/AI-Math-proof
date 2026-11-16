"""组合拆解：一道难题同时拆成 K 张不同的引理 DAG，各组并行证明子引理，哪一张先拼完整就算解出。

单张 DAG 的拆法多半是错的（某个子引理其实不成立，或者比原题还难），所以不把赌注押在一张图上：
1. sketch：K 个规划者各自独立写一份证明骨架，卡住的步骤留成 `sorry`。内核先确认“空洞都成立，原题就成立”，
   再把每个空洞提取成精确的子命题。每个规划者拿到不同的策略提示，让 K 张图尽量不同。
2. lemma：每个子命题交给一个证明者。它可以证明，也可以证伪（交 `<名>_disproof`）；证伪说明这张图的拆法不成立，
   整张图作废，图里其余子命题不再派人。不同图里结构相同的子命题（结构哈希一样）只证一次，各图共用。
3. assemble：一张图的子命题全部证出，就把各引理的证明和骨架拼成完整证明，交评测检查器（与直接证明同一个裁判）。
   机械拼装失败时再派一个 agent 手工拼。
所有检查都由 Lean 内核做；证明里有 sorry、额外公理或 native_decide 一律不收，所以不需要 agent 互相复核“有没有 sorry”。

子引理来自评测题，不进 Mathlib2（否则评测题的解法会漏进库里，以后的成绩就不干净了）。全部记录在
forge/data/staging/portfolio/<轮次>.json。
"""
import json
import re
import threading
import time
from pathlib import Path

from . import bench
from .leanrun import DATA, PROJECT, ROOT
from .scheduler import FORGE, PREAMBLE_NOTE, SOURCE_NOTE, Scheduler

STATE_DIR = DATA / 'staging' / 'portfolio'

STRATEGIES = [
    'Prove it the most direct way you can see; make each hole a substantial, self-contained step.',
    'Argue by contradiction or contrapositive; put the key impossibility claims into holes.',
    'Reduce the statement to a chain of known Mathlib facts; holes should be the links Mathlib lacks.',
    'Introduce a well-chosen auxiliary object (function, sequence, set, bound) and put its key properties into holes.',
    'Split into cases (small/large, parity, structure); each hard case becomes a hole.',
    'Use induction or a strengthened statement; the strengthened claim and the induction step are holes.',
    'Prove a more general or more symmetric statement first; the general claim is a hole.',
    'Work from the conclusion backwards: what intermediate inequality or identity would finish it? Make those holes.',
]

SKETCH_PROMPT = '''You are planner {k} of {K} for a hard Lean 4 + Mathlib problem in the project at {root} (agent `{agent}`).
Problem `{name}`, signature `<binders> : <conclusion>`{opens_note}:
{statement}
{notes}
Do NOT try to finish the proof. Write a proof SKELETON: a complete Lean proof of the theorem in which the hard steps are
left as `sorry`. Each `sorry` becomes a lemma that another agent proves on its own, in parallel; the kernel extracts each
hole's exact goal (with all local hypotheses) as a standalone statement.
Strategy for you (other planners use other strategies): {strategy}
Good skeletons have 2-10 holes, each clearly easier than the whole problem and TRUE (a false hole kills your plan).
Use `have hk : <claim> := by sorry` for the hard steps and finish the rest of the proof yourself.

Write the skeleton to {file} as
  theorem {name} <binders> : <conclusion> := by
    ...
Check it with `{forge} portfolio-sketch-check {run} {name} {file}` until it says ok (it lists the holes).
No axioms, no native_decide. Do not edit other files. End with one line: RESULT: sketched (<n> holes) | failed.
'''

LEMMA_PROMPT = '''In a Lean 4 + Mathlib project at {root} (agent `{agent}`), prove one lemma of a larger proof plan.
Lemma `{lemma}` (a closed statement; it is one step in a decomposition of the problem `{problem}`){opens_note}:
{statement}
{notes}
Write to {file} either
- `theorem {lemma} : <the statement above> := by ...`   (a proof), or
- `theorem {lemma}_disproof : ¬ (<the statement above>) := by ...`   (if it is false - that tells us the plan is wrong).
Helper lemmas are fine but their names must start with `{lemma}_aux`. No sorry, no axiom, no native_decide.
Check with `{forge} portfolio-lemma-check {run} {lemma} {file}` until it says ok. You have up to {minutes} minutes:
keep going; try several approaches before you stop. Do not edit other files.
End with one line: RESULT: proved | disproved | unsolved.
'''

ASSEMBLE_PROMPT = '''In a Lean 4 + Mathlib project at {root} (agent `{agent}`): all lemmas of a proof plan for `{name}` are proved.
Skeleton (with sorry holes): {skeleton}
Proved lemma files (each defines `theorem <lemma> : <closed statement>` and helpers): {lemmas}
Write ONE file {file} containing all lemma proofs (copy them, renaming every lemma and helper to start with `{name}_aux`, as
the checker requires for extra theorems) followed by the final `theorem {name} ...` whose proof is the skeleton with every
sorry replaced by a use of the matching lemma. Check it with `{forge} bench-check {set} {name} {file}`
until it says solved. Do not edit other files. End with one line: RESULT: solved | failed.
'''

HOLE = re.compile(r'(?<![\w.\'])sorry(?![\w\'])')


def _notes(item):
    notes = ''
    if item.get('preamble'):
        notes += PREAMBLE_NOTE.format(preamble=item['preamble'])
    if item.get('imports'):
        source = PROJECT / '.lake' / 'packages' / 'formal_conjectures' / item['source'] if item.get('source') else '(not recorded)'
        notes += SOURCE_NOTE.format(imports=', '.join(item['imports']), source=source)
    return notes


def _opens_note(item):
    return f' (notation assumes `open {item["opens"]}`)' if item.get('opens') else ''


def _state_path(run):
    return STATE_DIR / f'{run}.json'


def load_state(run):
    path = _state_path(run)
    return json.loads(path.read_text(encoding='utf-8')) if path.exists() else dict(run=run, problems={}, lemmas={})


def _task(item, name=None, statement=None, closed=None):
    """检查用的任务：评测题本身，或者它的一个子引理（闭命题）——都带上题目的导入、前置定义和记号设置。"""
    return dict(name=name or item['name'], statement=statement if statement is not None else item['statement'],
                opens=item.get('opens', ''), preamble=item.get('preamble', ''), imports=item.get('imports', []),
                library=False,  # 子引理不进库、也不引用库：不导入 Mathlib2，就不必等别的进程重建库
                **(dict(closed=closed) if closed else {}))


def _locked_retry(check, *args):
    """内核检查；没过就持入库锁再查一次（别的进程重建库时 .olean 会短暂缺失）。"""
    from .library import locked
    result = check(*args)
    if not result.get('ok') and result.get('errors'):
        with locked():
            result = check(*args)
    return result


def sketch_check(run, problem, path):
    from .verify import check_sketch
    state = load_state(run)
    info = state['problems'].get(problem)
    if not info:
        return dict(ok=False, reason=f'轮次 {run} 里没有题目 {problem}')
    item = next(i for i in bench.load(info['set']) if i['name'] == problem)
    try:
        return _locked_retry(check_sketch, _task(item), Path(path).read_text(encoding='utf-8'))
    except Exception as exc:  # noqa: BLE001 - 静态检查的报错（名称不符、禁用词）原样告诉 agent
        return dict(ok=False, reason=str(exc))


def lemma_check(run, lemma, path):
    from .verify import check_submission
    state = load_state(run)
    info = state['lemmas'].get(lemma)
    if not info:
        return dict(ok=False, reason=f'轮次 {run} 里没有引理 {lemma}')
    item = next(i for i in bench.load(info['set']) if i['name'] == info['problem'])
    try:
        return _locked_retry(check_submission, _task(item, lemma, ': ' + info['statement'], closed=info['statement']), Path(path).read_text(encoding='utf-8'))
    except Exception as exc:  # noqa: BLE001
        return dict(ok=False, reason=str(exc))


def aux_names(name, text):
    """评测检查器要求附加定理都叫 `<题名>_aux…`：把子引理 `<题名>_d<k>_h<i>`（及其辅助引理）改名成 `<题名>_aux_d<k>_h<i>`。"""
    return re.sub(re.escape(name) + r'_(d\d+_h\d+)', name + r'_aux_\1', text)


def assemble_body(name, skeleton, lemma_bodies, lemma_args):
    """机械拼装：引理证明放在前面，骨架里每个 sorry 处把所有引理挨个试（sorry 与目标不必一一对应）。"""
    lemma_bodies = [aux_names(name, b) for b in lemma_bodies]
    lemma_args = [(aux_names(name, lemma), args) for lemma, args in lemma_args]
    options = []
    for lemma, args in lemma_args:
        if args:
            options.append(f'exact @{lemma} {" ".join(args)}')
        options += [f'exact {lemma}', f'apply {lemma} <;> assumption', f'simpa using {lemma}']
    combined = '(first | ' + ' | '.join(options) + ')'
    return '\n\n'.join(b.strip() for b in lemma_bodies) + '\n\n' + HOLE.sub(lambda _: combined, skeleton)


class Portfolio(Scheduler):
    """在调度器上加三种工作项：sketch、lemma、assemble，放在一个共享队列里，前一步完成后把下一步放进去。"""

    def run_portfolio(self, set_name, problems, k=6, lemma_minutes=None, lemma_attempts=2, revive=False):
        self.set_name, self.k, self.lemma_attempts = set_name, k, lemma_attempts
        self.lemma_seconds = (lemma_minutes or self.task_seconds // 60) * 60
        self.items = {i['name']: i for i in bench.load(set_name) if i['name'] in set(problems)}
        missing = set(problems) - set(self.items)
        if missing:
            raise ValueError(f'评测集里没有这些题：{sorted(missing)}')
        self.state = load_state(self.run)
        for p in problems:
            self.state['problems'].setdefault(p, dict(set=set_name, dags={}, solved_by=None))
        self._save()
        if revive:
            # 检查器修好后：被判“没法检查”的引理重新开放，只因它们作废（没有被证伪的引理）的图恢复
            for lemma in self.state['lemmas'].values():
                if lemma['status'] == 'uncheckable':
                    lemma.update(status='open', attempts=0)
            for p in problems:
                for dag, d in self.state['problems'][p]['dags'].items():
                    if d['status'] in ('dead', 'assembly_failed') and not any(
                            self.state['lemmas'][h['lemma']]['status'] == 'disproved' for h in d['holes']):
                        d['status'] = 'open'
        # 接着上次的状态跑：已有骨架的图不再重写；没证完的子引理、该拼装的图重新排队
        self.queue = [('sketch', p, i) for i in range(1, k + 1) for p in problems
                      if f'd{i}' not in self.state['problems'][p]['dags']]
        for name, lemma in self.state['lemmas'].items():
            live = [d for d in lemma['dags'] if self.state['problems'][lemma['problem']]['dags'][d]['status'] == 'open']
            if lemma['problem'] in self.items and lemma['status'] in ('open', 'unsolved') and live \
                    and lemma.get('attempts', 0) < lemma_attempts:
                lemma['status'], lemma['queued'] = 'open', True
                self.queue.append(('lemma', lemma['problem'], name))
        for p in problems:
            for d in self.state['problems'][p]['dags'].values():
                if d['status'] == 'assembling':  # 上次拼装到一半被打断
                    d['status'] = 'open'
        self.busy = 0
        self.file_lock = threading.Lock()
        for p in problems:
            self._maybe_assemble(p)
        out = self._run_threads(self._worker, ())
        solved = [p for p in problems if self.state['problems'][p]['solved_by']]
        return dict(out or {}, solved=len(solved), problems=len(problems), solved_list=solved, tokens=self.tokens,
                    state=str(_state_path(self.run)))

    # ---- 状态 ----
    def _save(self):
        STATE_DIR.mkdir(parents=True, exist_ok=True)
        tmp = _state_path(self.run).with_suffix('.tmp')
        tmp.write_text(json.dumps(self.state, ensure_ascii=False, indent=1), encoding='utf-8')
        tmp.replace(_state_path(self.run))

    def _take(self):
        while True:
            with self.lock:
                if self.stop_reason:
                    return None
                # 已经解出的题不再派活
                self.queue = [w for w in self.queue if not self.state['problems'][w[1]]['solved_by']]
                if self.queue:
                    self.busy += 1
                    return self.queue.pop(0)
                if not self.busy:
                    self.stop_reason = '所有题目的拆解都已处理完'
                    return None
            time.sleep(5)

    def _push(self, *items):
        with self.lock:
            self.queue.extend(items)

    def _worker(self, index):
        agent = f'{self.run}-w{index}'
        (self.scratch / agent).mkdir(parents=True, exist_ok=True)
        while True:
            work = self._take()
            if work is None:
                return
            try:
                if self._may_start():
                    getattr(self, '_' + work[0])(agent, *work[1:])
            finally:
                with self.lock:
                    self.busy -= 1

    # ---- sketch ----
    def _sketch(self, agent, problem, k):
        from .verify import check_sketch
        item = self.items[problem]
        dag = f'd{k}'
        path = self.scratch / agent / f'{problem}.{dag}.sketch.lean'
        path.unlink(missing_ok=True)
        prompt = SKETCH_PROMPT.format(k=k, K=self.k, root=ROOT, agent=agent, name=problem, statement=item['statement'],
                                      opens_note=_opens_note(item), notes=_notes(item), forge=FORGE, run=self.run, file=path,
                                      strategy=STRATEGIES[(k - 1) % len(STRATEGIES)])
        began = time.time()
        code, message, used, slow = self._invoke(prompt, agent)
        check = dict(ok=False, reason='没有交出骨架')
        if path.exists():
            try:
                check = _locked_retry(check_sketch, _task(item), path.read_text(encoding='utf-8'))
            except Exception as exc:  # noqa: BLE001
                check = dict(ok=False, reason=str(exc))
        holes = []
        if check.get('ok'):
            with self.file_lock:
                for h_index, hole in enumerate(check['holes'], 1):
                    # 不同图里结构相同的子命题只证一次
                    same = next((n for n, l in self.state['lemmas'].items()
                                 if l['problem'] == problem and l['hash'] == hole['hash']), None)
                    lemma = same or f'{problem}_{dag}_h{h_index}'
                    if not same:
                        self.state['lemmas'][lemma] = dict(set=self.set_name, problem=problem, statement=hole['statement'],
                                                           hash=hole['hash'], status='open', dags=[])
                    self.state['lemmas'][lemma]['dags'].append(dag)
                    holes.append(dict(lemma=lemma, args=hole.get('args', [])))
                self.state['problems'][problem]['dags'][dag] = dict(skeleton=path.read_text(encoding='utf-8'), holes=holes,
                                                                    status='open', planner=agent)
                self._save()
        self._record(dict(mode='portfolio-sketch', task=f'{problem}/{dag}', worker=agent,
                          outcome=f'{len(holes)} holes' if check.get('ok') else 'failed', progress=bool(holes),
                          seconds=round(time.time() - began), tokens=used, exit=code, timed_out=slow,
                          reason=check.get('reason', '')[:300], message=message[-500:]))
        for h in holes:
            lemma = self.state['lemmas'][h['lemma']]
            if lemma['status'] == 'open' and not lemma.get('queued'):
                lemma['queued'] = True
                self._push(('lemma', problem, h['lemma']))
        self._maybe_assemble(problem)

    # ---- lemma ----
    def _lemma(self, agent, problem, lemma):
        from .verify import check_submission
        info = self.state['lemmas'][lemma]
        live = [d for d in info['dags'] if self.state['problems'][problem]['dags'][d]['status'] == 'open']
        if not live:  # 用到它的图都已作废
            return
        item = self.items[problem]
        path = self.scratch / agent / f'{lemma}.lean'
        path.unlink(missing_ok=True)
        prompt = LEMMA_PROMPT.format(root=ROOT, agent=agent, lemma=lemma, problem=problem, statement=info['statement'],
                                     opens_note=_opens_note(item), notes=_notes(item), file=path, forge=FORGE, run=self.run,
                                     minutes=self.lemma_seconds // 60)
        began = time.time()
        code, message, used, slow = self._invoke(prompt, agent, seconds=self.lemma_seconds)
        status, reason = 'unsolved', '没有交出证明'
        if path.exists():
            body = path.read_text(encoding='utf-8')
            try:
                result = _locked_retry(check_submission, _task(item, lemma, ': ' + info['statement'], closed=info['statement']), body)
            except Exception as exc:  # noqa: BLE001 - 静态检查拒收（例如空洞目标里带 let 的 `:=`）：这条引理没法检查
                result = dict(ok=False, reason=str(exc), uncheckable=True)
            reason = result.get('reason', '')
            if result.get('uncheckable'):
                status = 'uncheckable'
            elif result.get('ok'):
                status = 'disproved' if result['kind'] == 'disproved' else 'proved'
                if status == 'proved':
                    info['body'] = body
        with self.file_lock:
            info['status'] = status
            info['attempts'] = info.get('attempts', 0) + 1
            if status in ('disproved', 'uncheckable'):  # 拆法不成立，或这条引理没法检查：用到它的图全部作废
                for d in info['dags']:
                    self.state['problems'][problem]['dags'][d]['status'] = 'dead'
            self._save()
        self._record(dict(mode='portfolio-lemma', task=lemma, worker=agent, outcome=status, progress=status != 'unsolved',
                          seconds=round(time.time() - began), tokens=used, exit=code, timed_out=slow,
                          reason=reason[:300], message=message[-500:]))
        if status == 'proved':
            self._maybe_assemble(problem)
        elif status == 'unsolved' and info['attempts'] < self.lemma_attempts:
            self._push(('lemma', problem, lemma))  # 再派一个人从头试（放到队尾，先让别的图推进）

    # ---- assemble ----
    def _maybe_assemble(self, problem):
        with self.file_lock:
            p = self.state['problems'][problem]
            for dag, d in p['dags'].items():
                if d['status'] == 'open' and d['holes'] and all(self.state['lemmas'][h['lemma']]['status'] == 'proved' for h in d['holes']):
                    d['status'] = 'assembling'
                    self._push(('assemble', problem, dag))
            self._save()

    def _assemble(self, agent, problem, dag):
        d = self.state['problems'][problem]['dags'][dag]
        lemmas = list(dict.fromkeys(h['lemma'] for h in d['holes']))
        bodies = [self.state['lemmas'][l]['body'] for l in lemmas]
        began = time.time()
        body = assemble_body(problem, d['skeleton'], bodies, [(h['lemma'], h['args']) for h in d['holes']])
        result = _safe_check(self.set_name, problem, body, self.run)
        used, code, slow, message, how = 0, 0, False, '', 'mechanical'
        if not result.get('solved'):
            # 机械拼装失败：派一个 agent 手工拼，结果仍由评测检查器判定
            folder = self.scratch / agent
            files = []
            for l, b in zip(lemmas, bodies):
                f = folder / f'{l}.proved.lean'
                f.write_text(b, encoding='utf-8')
                files.append(str(f))
            skel = folder / f'{problem}.{dag}.skeleton.lean'
            skel.write_text(d['skeleton'], encoding='utf-8')
            out = folder / f'{problem}.{dag}.final.lean'
            out.unlink(missing_ok=True)
            prompt = ASSEMBLE_PROMPT.format(root=ROOT, agent=agent, name=problem, skeleton=skel, lemmas=', '.join(files),
                                            file=out, forge=FORGE, set=self.set_name)
            code, message, used, slow = self._invoke(prompt, agent)
            how = 'agent'
            if out.exists():
                result = _safe_check(self.set_name, problem, out.read_text(encoding='utf-8'), self.run)
        with self.file_lock:
            if result.get('solved'):
                d['status'] = 'solved'
                self.state['problems'][problem]['solved_by'] = self.state['problems'][problem]['solved_by'] or dag
            else:
                d['status'] = 'assembly_failed'
            self._save()
        self._record(dict(mode='portfolio-assemble', task=f'{problem}/{dag}', worker=agent,
                          outcome='solved' if result.get('solved') else 'failed', progress=bool(result.get('solved')),
                          seconds=round(time.time() - began), tokens=used, exit=code, timed_out=slow,
                          reason=f'{how}: ' + result.get('reason', '')[:280], message=message[-300:]))


def _safe_check(set_name, problem, body, run):
    """评测检查器；静态检查拒收（命名、禁用词）时记为没解出，不让异常打断整轮。"""
    try:
        return bench.check(set_name, problem, body, run, 'scheduler')
    except Exception as exc:  # noqa: BLE001
        return dict(ok=False, solved=False, reason=str(exc))


def summary(run):
    state = load_state(run)
    rows = []
    for p, info in state['problems'].items():
        dags = info['dags']
        lemmas = [l for l in state['lemmas'].values() if l['problem'] == p]
        rows.append(dict(problem=p, solved_by=info['solved_by'], dags=len(dags),
                         dag_status={s: sum(d['status'] == s for d in dags.values()) for s in {d['status'] for d in dags.values()}},
                         lemmas=len(lemmas), proved=sum(l['status'] == 'proved' for l in lemmas),
                         disproved=sum(l['status'] == 'disproved' for l in lemmas)))
    return dict(run=run, solved=sum(bool(r['solved_by']) for r in rows), problems=len(rows), rows=rows)
