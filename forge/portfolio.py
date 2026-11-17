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
~/.rsi-math/scratch/portfolio/<轮次>.json（仓库外，见 provenance.py；旧轮次仍在 forge/data/staging/portfolio）。
"""
import json
import re
import threading
import time
from pathlib import Path

from . import bench, provenance
from .leanrun import DATA, PROJECT, ROOT, SCRATCH
from .scheduler import FORGE, PREAMBLE_NOTE, SOURCE_NOTE, Scheduler
from .statement import StatementError

STATE_DIR = SCRATCH / 'portfolio'  # 在仓库外：状态里有证明原文，见 provenance.py
LEGACY_STATE_DIR = DATA / 'staging' / 'portfolio'

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
Helper lemmas are fine but their names must start with `{lemma}_aux` and they must come BEFORE the main theorem:
the main theorem (`{lemma}` or `{lemma}_disproof`) must be the LAST declaration in the file. No sorry, no axiom, no native_decide.
Check with `{forge} portfolio-lemma-check {run} {lemma} {file}` until it says ok. You have up to {minutes} minutes:
keep going; try several approaches before you stop. Do not edit other files.{previous}
End with one line: RESULT: proved | disproved | unsolved.
'''

PREVIOUS_NOTE = '''
An earlier agent tried this lemma and failed. Its file is {path} (read it; do not edit it). The checker said: {reason}
Reuse whatever is correct in it (proved helpers, partial arguments), fix what is wrong, or try another route.'''

SPLIT_NOTE = '''This statement is itself a lemma in a decomposition of `{problem}` that direct proof attempts failed on.
Decompose it further: every hole should be clearly easier than this lemma (a hole that restates the whole lemma is rejected).
'''

ASSEMBLE_PROMPT = '''In a Lean 4 + Mathlib project at {root} (agent `{agent}`): all lemmas of a proof plan for `{name}` are proved.
Skeleton (with sorry holes): {skeleton}
Proved lemma files (each defines `theorem <lemma> : <closed statement>` and helpers): {lemmas}
Write ONE file {file} containing all lemma proofs (copy them, renaming every lemma and helper to start with `{name}_aux`, as
the checker requires for extra theorems) followed by the final `theorem {name} ...` whose proof is the skeleton with every
sorry replaced by a use of the matching lemma. Check it with `{forge} bench-check {set} {name} {file}`
until it says solved. Do not edit other files. End with one line: RESULT: solved | failed.
'''

ASSEMBLE_LEMMA_PROMPT = '''In a Lean 4 + Mathlib project at {root} (agent `{agent}`): all parts of a decomposition of the lemma
`{name}` are proved, but mechanical assembly failed ({reason}).
Skeleton (with sorry holes): {skeleton}
Proved part files (each defines `theorem <part> : <closed statement>` and helpers): {lemmas}
Write ONE file {file} containing all part proofs (copy them, renaming every part and helper to start with `{name}_aux`, as
the checker requires for extra theorems) followed by the final `theorem {name} ...` (LAST in the file) whose proof is the
skeleton with every sorry replaced by a use of the matching part. Check it with
`{forge} portfolio-lemma-check {run} {name} {file}` until it says ok. Do not edit other files.
End with one line: RESULT: proved | failed.
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
    legacy = LEGACY_STATE_DIR / f'{run}.json'
    # 移出仓库之前开始的拆解轮次：状态还在旧位置，接着在那里跑
    return legacy if legacy.exists() and not (STATE_DIR / f'{run}.json').exists() else STATE_DIR / f'{run}.json'


def load_state(run):
    path = _state_path(run)
    return json.loads(path.read_text(encoding='utf-8')) if path.exists() else dict(run=run, problems={}, lemmas={})


def _task(item, name=None, statement=None):
    """检查用的任务：评测题本身，或者它的一个子引理（闭命题）——都带上题目的导入、前置定义和记号设置。"""
    return dict(name=name or item['name'], statement=statement if statement is not None else item['statement'],
                opens=item.get('opens', ''), preamble=item.get('preamble', ''), imports=item.get('imports', []),
                library=False)  # 子引理不进库、也不引用库：不导入 Mathlib2，就不必等别的进程重建库


def sketch_check(run, problem, path):
    from .verify import check_sketch
    state = load_state(run)
    info = state['problems'].get(problem)
    lemma = state['lemmas'].get(problem)  # 再拆一层时，“题目”是一条子引理
    if not info and not lemma:
        return dict(ok=False, reason=f'轮次 {run} 里没有题目或引理 {problem}')
    try:
        if lemma:
            item = next(i for i in bench.load(lemma['set']) if i['name'] == lemma['problem'])
            return check_sketch(_task(item, problem, ': ' + lemma['statement']), Path(path).read_text(encoding='utf-8'),
                                closed=lemma['statement'])
        item = next(i for i in bench.load(info['set']) if i['name'] == problem)
        return check_sketch(_task(item), Path(path).read_text(encoding='utf-8'))
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
        return check_submission(_task(item, lemma, ': ' + info['statement']),
                                main_last(Path(path).read_text(encoding='utf-8'), lemma), closed=info['statement'])
    except Exception as exc:  # noqa: BLE001
        return dict(ok=False, reason=str(exc))


def main_last(body, lemma):
    """把主定理（`lemma` 或 `lemma_disproof`）那一段挪到文件最后：agent 常把辅助引理写在主定理后面，内容没错只是顺序不合规。
    只在原文被静态检查拒收时才动；分段用去掉注释后的文本（块注释里顶格的行不能当成新声明）。"""
    from .statement import StatementError, analyse_submission, strip_comments
    disproof = re.search(r'^(?:theorem|lemma)\s+' + re.escape(lemma) + r'_disproof(?![\w\'])', strip_comments(body), re.M)
    try:
        analyse_submission(body, lemma, bool(disproof))
        return body
    except StatementError:
        pass
    blocks, current = [], []
    for line in strip_comments(body).splitlines():
        if line and not line[0].isspace() and current and not line.startswith(('--', '/-', '@[')) \
                and not (current[-1].startswith('@[') and not current[-1][0].isspace()):
            blocks.append(current)
            current = []
        current.append(line)
    if current:
        blocks.append(current)
    head = re.compile(r'(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+(' + re.escape(lemma) + r'(?:_disproof)?)(?![\w\'])')
    mains = [i for i, b in enumerate(blocks) if head.match(b[0])]
    if len(mains) != 1 or mains[0] == len(blocks) - 1:
        return body
    i = mains[0]
    rest = blocks[:i] + blocks[i + 1:]
    return '\n'.join('\n'.join(b) for b in rest + [blocks[i]]).rstrip('\n') + '\n'


def aux_names(name, text):
    """评测检查器要求附加定理都叫 `<题名>_aux…`：把子引理 `<题名>_d<k>_h<i>`（及其辅助引理）改名成 `<题名>_aux_d<k>_h<i>`。
    左边界：`pp_d1_h1`、`Foo.p_d1_h1` 这类只是包含题名的标识符不改。"""
    return re.sub(r"(?<![\w.'])" + re.escape(name) + r'_(d\d+_h\d+)', name + r'_aux_\1', text)


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
    """在调度器上加几种工作项：sketch、lemma、assemble，以及卡住的子引理再拆一层用的 split、split_sketch，
    放在一个共享队列里，前一步完成后把下一步放进去。"""
    split, depth = 0, 1

    def run_portfolio(self, set_name, problems, k=6, lemma_minutes=None, lemma_attempts=2, revive=False, split=0, depth=1):
        # split：一条子引理用完尝试次数还没证出、而且还有图在等它时，再把它拆成 split 张子图（递归，最多 depth 层）
        self.set_name, self.k, self.lemma_attempts = set_name, k, lemma_attempts
        self.split, self.depth = split, depth
        self.lemma_seconds = (lemma_minutes or self.task_seconds // 60) * 60
        self.items = {i['name']: i for i in bench.load(set_name) if i['name'] in set(problems)}
        missing = set(problems) - set(self.items)
        if missing:
            raise ValueError(f'评测集里没有这些题：{sorted(missing)}')
        self.state = load_state(self.run)
        legacy = DATA / 'staging' / 'agents' / self.run
        if legacy.is_dir() and not self.scratch.exists():
            self.scratch = legacy  # 旧轮次接着跑：引理文件都在旧位置
        for p in problems:
            self.state['problems'].setdefault(p, dict(set=set_name, dags={}, solved_by=None))
        self._save()
        if revive:
            # 旧版本把检查器拒收的引理记成 uncheckable 并让用到它的图作废：这些引理重新开放，
            # 只因它们作废的图（有 uncheckable 引理、没有被证伪的引理）恢复。只动这一轮的题。
            for p in problems:
                for d in self.state['problems'][p]['dags'].values():
                    holes = [self.state['lemmas'][h['lemma']]['status'] for h in d['holes']]
                    if d['status'] == 'dead' and 'uncheckable' in holes and 'disproved' not in holes:
                        d['status'] = 'open'
            for lemma in self.state['lemmas'].values():
                if lemma['status'] == 'uncheckable' and lemma['problem'] in set(problems):
                    lemma.update(status='open', attempts=0)
        for lemma in self.state['lemmas'].values():
            lemma['queued'] = False  # 排队标记只在本次运行内有效
        # 接着上次的状态跑：已有骨架的图不再重写；没证完的子引理、该拼装的图重新排队
        self.queue = [('sketch', p, i) for i in range(1, k + 1) for p in problems
                      if f'd{i}' not in self.state['problems'][p]['dags']]
        for name, lemma in self.state['lemmas'].items():
            lemma['splitting'] = False  # 和 queued 一样只在本次运行内有效
            for d in lemma.get('splits', {}).values():
                if d['status'] == 'assembling':
                    d['status'] = 'open'
            if lemma['problem'] not in self.items or lemma['status'] not in ('open', 'unsolved') or not self._live(lemma):
                continue
            if lemma.get('attempts', 0) < lemma_attempts:
                lemma['status'], lemma['queued'] = 'open', True
                self.queue.append(('lemma', lemma['problem'], name))
            elif self._may_split(lemma):
                self.queue.append(('split', lemma['problem'], name))
            elif lemma.get('splits'):
                # 上次已经拆过：没写出的子图补派规划者
                self.queue += [('split_sketch', lemma['problem'], name, i) for i in range(1, split + 1)
                               if f'd{i}' not in lemma['splits']]
        for p in problems:
            for d in self.state['problems'][p]['dags'].values():
                if d['status'] == 'assembling':  # 上次拼装到一半被打断
                    d['status'] = 'open'
        self.busy = 0
        self.file_lock = threading.Lock()
        for p in problems:
            self._maybe_assemble(p)
        for name, lemma in list(self.state['lemmas'].items()):
            if lemma['problem'] in self.items and lemma.get('splits'):
                self._maybe_assemble_lemma(name)
        out = self._run_threads(self._worker, ())
        solved = [p for p in problems if self.state['problems'][p]['solved_by']]
        return dict(out or {}, solved=len(solved), problems=len(problems), solved_list=solved, tokens=self.tokens,
                    state=str(_state_path(self.run)))

    # ---- 状态 ----
    def _save(self):
        _state_path(self.run).parent.mkdir(parents=True, exist_ok=True)
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
                    # 先做离拼完一张题目图最近的活（同分时先来先做）：工人少时别把时间花在还差很多步的图上
                    best = min(range(len(self.queue)), key=lambda i: (self._distance(self.queue[i]), i))
                    return self.queue.pop(best)
                if not self.busy:
                    self.stop_reason = '所有题目的拆解都已处理完'
                    return None
            time.sleep(5)

    def _push(self, *items):
        with self.lock:
            self.queue.extend(items)

    def _live(self, info):
        """还有没有人在等这条引理：题目的某张图还开着，或者某个父引理的某张子图还开着（父引理本身也还活着）。"""
        if any(self.state['problems'][info['problem']]['dags'][d]['status'] == 'open' for d in info['dags']):
            return True
        for parent, sdag in info.get('parents', []):
            up = self.state['lemmas'][parent]
            # 子图登记到一半（父链接已加、子图还没存）时按“还开着”算
            if up['status'] != 'proved' and up.get('splits', {}).get(sdag, {}).get('status', 'open') == 'open' and self._live(up):
                return True
        return False

    def _missing(self, holes):
        return len({h['lemma'] for h in holes if self.state['lemmas'][h['lemma']]['status'] != 'proved'})

    def _need(self, info, seen=()):
        """证出这条引理之后，离拼完某张还开着的题目图最少还差几条别的引理（没有活路时为无穷大）。"""
        best = float('inf')
        for d in info['dags']:
            dag = self.state['problems'][info['problem']]['dags'][d]
            if dag['status'] == 'open':
                best = min(best, self._missing(dag['holes']) - 1)
        for parent, sdag in info.get('parents', []):
            up = self.state['lemmas'][parent]
            split = up.get('splits', {}).get(sdag, {})
            if parent in seen or up['status'] == 'proved' or split.get('status', 'open') != 'open':
                continue
            best = min(best, self._missing(split.get('holes', [])) - 1 + self._need(up, seen + (parent,)))
        return best

    def _distance(self, work):
        """排队用的优先级：越小越先做。骨架（新的图）最先；拼装次之；引理和再拆按离拼完的距离。"""
        kind = work[0]
        if kind in ('sketch', 'assemble', 'assemble_lemma'):
            return -1
        info = self.state['lemmas'].get(work[2])
        if not info:
            return 0
        need = self._need(info)
        return need + (0.5 if kind in ('split', 'split_sketch') else 0)  # 同样距离时先直接证，再拆

    def _may_split(self, info):
        return (self.split and info['status'] == 'unsolved' and info.get('depth', 0) < self.depth
                and not info.get('splits') and not info.get('splitting'))

    def _kill_users(self, info):
        """这条引理被证伪：用到它的题目图、父引理的子图全部作废。"""
        for d in info['dags']:
            self.state['problems'][info['problem']]['dags'][d]['status'] = 'dead'
        for parent, sdag in info.get('parents', []):
            self.state['lemmas'][parent]['splits'][sdag]['status'] = 'dead'

    def _resolved(self, lemma):
        """引理证出后，看看用到它的题目图和父引理子图能不能拼装。"""
        info = self.state['lemmas'][lemma]
        self._maybe_assemble(info['problem'])
        for parent, _ in info.get('parents', []):
            self._maybe_assemble_lemma(parent)

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
                check = check_sketch(_task(item), path.read_text(encoding='utf-8'))
            except Exception as exc:  # noqa: BLE001
                check = dict(ok=False, reason=str(exc))
        holes = []
        if check.get('ok'):
            with self.file_lock:
                holes = self._register_holes(problem, f'{problem}_{dag}', check['holes'], depth=0, dag=dag)
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

    def _register_holes(self, problem, prefix, found, depth, dag=None, parent=None):
        """把骨架的空洞登记成子引理。结构相同的子命题只证一次，各处共用；子图的空洞只和同一父引理下的共用，
        因为拼装时附加定理必须叫 `<父引理>_aux…`。"""
        holes = []
        for h_index, hole in enumerate(found, 1):
            same = next((n for n, l in self.state['lemmas'].items() if l['problem'] == problem and l['hash'] == hole['hash']
                         and (not parent or n.startswith(parent[0] + '_'))), None)
            lemma = same or f'{prefix}_h{h_index}'
            if not same:
                self.state['lemmas'][lemma] = dict(set=self.set_name, problem=problem, statement=hole['statement'],
                                                   hash=hole['hash'], status='open', dags=[], depth=depth)
            info = self.state['lemmas'][lemma]
            info['depth'] = min(info.get('depth', 0), depth)  # 共用时按最浅的用法算层数
            if dag:
                info['dags'].append(dag)
            if parent:
                info.setdefault('parents', []).append(list(parent))
            holes.append(dict(lemma=lemma, args=hole.get('args', [])))
        return holes

    # ---- split：把卡住的子引理再拆一层 ----
    def _split(self, agent, problem, lemma):
        info = self.state['lemmas'][lemma]
        with self.file_lock:
            if info['status'] == 'proved' or not self._live(info) or info.get('splitting') or info.get('splits'):
                return
            info['splitting'] = True
        self._push(*[('split_sketch', problem, lemma, i) for i in range(1, self.split + 1)])

    def _split_sketch(self, agent, problem, lemma, k):
        from .verify import check_sketch
        info = self.state['lemmas'][lemma]
        if info['status'] == 'proved' or not self._live(info):
            return
        item = self.items[problem]
        sdag = f'd{k}'
        path = self.scratch / agent / f'{lemma}.{sdag}.sketch.lean'
        path.unlink(missing_ok=True)
        prompt = SKETCH_PROMPT.format(k=k, K=self.split, root=ROOT, agent=agent, name=lemma, statement=': ' + info['statement'],
                                      opens_note=_opens_note(item), notes=_notes(item) + SPLIT_NOTE.format(problem=problem),
                                      forge=FORGE, run=self.run, file=path, strategy=STRATEGIES[(k - 1) % len(STRATEGIES)])
        began = time.time()
        code, message, used, slow = self._invoke(prompt, agent)
        check = dict(ok=False, reason='没有交出骨架')
        if path.exists():
            try:
                check = check_sketch(_task(item, lemma, ': ' + info['statement']), path.read_text(encoding='utf-8'),
                                     closed=info['statement'])
            except Exception as exc:  # noqa: BLE001
                check = dict(ok=False, reason=str(exc))
        same = lambda a, b: ' '.join(a.split()) == ' '.join(b.split())
        if check.get('ok') and any(same(h['statement'], info['statement']) for h in check['holes']):
            check = dict(ok=False, reason='骨架把整条引理原样留成了空洞，等于没拆')
        holes = []
        with self.file_lock:
            if check.get('ok'):
                info.setdefault('splits', {})[sdag] = dict(skeleton=path.read_text(encoding='utf-8'), holes=[],
                                                           status='open', planner=agent)
                holes = self._register_holes(problem, f'{lemma}_{sdag}', check['holes'], depth=info.get('depth', 0) + 1,
                                             parent=(lemma, sdag))
                info['splits'][sdag]['holes'] = holes
            else:  # 记下失败，接着跑时不再重派这个规划者
                info.setdefault('splits', {})[sdag] = dict(skeleton='', holes=[], status='failed', planner=agent)
            self._save()
        self._record(dict(mode='portfolio-split', task=f'{lemma}/{sdag}', worker=agent,
                          outcome=f'{len(holes)} holes' if check.get('ok') else 'failed', progress=bool(holes),
                          seconds=round(time.time() - began), tokens=used, exit=code, timed_out=slow,
                          reason=check.get('reason', '')[:300], message=message[-500:]))
        for h in holes:
            sub = self.state['lemmas'][h['lemma']]
            with self.file_lock:
                fresh = sub['status'] == 'open' and not sub.get('queued')
                sub['queued'] = sub.get('queued') or fresh
            if fresh:
                self._push(('lemma', problem, h['lemma']))
        self._maybe_assemble_lemma(lemma)

    def _maybe_assemble_lemma(self, lemma):
        """子图的空洞全部证出：机械拼成这条引理的证明，由内核按这条引理的命题检查。"""
        from .verify import check_submission
        info = self.state['lemmas'][lemma]
        with self.file_lock:
            if info['status'] == 'proved':
                return
            ready = [(s, d) for s, d in info.get('splits', {}).items() if d['status'] == 'open' and d['holes']
                     and all(self.state['lemmas'][h['lemma']]['status'] == 'proved' for h in d['holes'])]
            for _, d in ready:
                d['status'] = 'assembling'
            self._save()
        item = self.items[info['problem']]
        for sdag, d in ready:
            subs = list(dict.fromkeys(h['lemma'] for h in d['holes']))
            body = main_last(assemble_body(lemma, d['skeleton'], [self.state['lemmas'][l]['body'] for l in subs],
                                           [(h['lemma'], h['args']) for h in d['holes']]), lemma)
            result = check_submission(_task(item, lemma, ': ' + info['statement']), body, closed=info['statement'])
            if not result.get('ok'):  # 机械拼装失败：派一个 agent 手工拼（排队，不在这里同步等）
                self._push(('assemble_lemma', info['problem'], lemma, sdag, result.get('reason', '')[:300]))
                self._record(dict(mode='portfolio-lemma-assemble', task=f'{lemma}/{sdag}', worker='-', outcome='mechanical failed',
                                  progress=False, seconds=0, tokens=0, exit=0, timed_out=False,
                                  reason=result.get('reason', '')[:300], message=''))
                continue
            with self.file_lock:
                d['status'] = 'solved' if result.get('ok') else 'assembly_failed'
                if result.get('ok') and info['status'] != 'proved':
                    info.update(status='proved', body=body, proved_by=sdag, copied=self._copy_of(body, subs))
                self._save()
            self._record(dict(mode='portfolio-lemma-assemble', task=f'{lemma}/{sdag}', worker='-', copied=info.get('copied'),
                              outcome='proved' if result.get('ok') else 'failed', progress=bool(result.get('ok')),
                              seconds=0, tokens=0, exit=0, timed_out=False, reason=result.get('reason', '')[:300], message=''))
            if result.get('ok'):
                self._resolved(lemma)
                return

    def _assemble_lemma(self, agent, problem, lemma, sdag, reason):
        from .verify import check_submission
        info = self.state['lemmas'][lemma]
        d = info['splits'][sdag]
        if info['status'] == 'proved':
            with self.file_lock:
                d['status'] = 'open'
            return
        item = self.items[problem]
        folder = self.scratch / agent
        subs = list(dict.fromkeys(h['lemma'] for h in d['holes']))
        files = []
        for l in subs:
            f = folder / f'{l}.proved.lean'
            f.write_text(self.state['lemmas'][l]['body'], encoding='utf-8')
            files.append(str(f))
        skel = folder / f'{lemma}.{sdag}.skeleton.lean'
        skel.write_text(d['skeleton'], encoding='utf-8')
        out = folder / f'{lemma}.{sdag}.final.lean'
        out.unlink(missing_ok=True)
        prompt = ASSEMBLE_LEMMA_PROMPT.format(root=ROOT, agent=agent, name=lemma, reason=reason, skeleton=skel,
                                              lemmas=', '.join(files), file=out, forge=FORGE, run=self.run)
        began = time.time()
        code, message, used, slow = self._invoke(prompt, agent)
        result = dict(ok=False, reason='没有交出拼装结果')
        if out.exists():
            body = main_last(out.read_text(encoding='utf-8'), lemma)
            result = check_submission(_task(item, lemma, ': ' + info['statement']), body, closed=info['statement'])
        ok = result.get('ok') and result.get('kind') == 'proved'
        with self.file_lock:
            d['status'] = 'solved' if ok else 'assembly_failed'
            if ok and info['status'] != 'proved':
                info.update(status='proved', body=body, proved_by=sdag, copied=self._copy_of(body, subs))
            self._save()
        self._record(dict(mode='portfolio-lemma-assemble', task=f'{lemma}/{sdag}', worker=agent, copied=info.get('copied'),
                          outcome='proved' if ok else 'failed', progress=bool(ok), seconds=round(time.time() - began),
                          tokens=used, exit=code, timed_out=slow, reason='agent: ' + result.get('reason', '')[:280],
                          message=message[-300:]))
        if ok:
            self._resolved(lemma)

    # ---- 抄写检测 ----
    def _own_files(self):
        """本轮自己的草稿和状态（新旧两个位置）：接着上次跑时，自己上一次证出的引理不算抄写的来源。"""
        return [SCRATCH / 'agents' / self.run, DATA / 'staging' / 'agents' / self.run,
                STATE_DIR / f'{self.run}.json', LEGACY_STATE_DIR / f'{self.run}.json']

    def _copy_of(self, body, lemmas=()):
        """证出的引理或题目是不是抄来的：自己和本轮开始前就有的别的文件比；用到的子引理里有抄来的，也算抄来的。
        返回来源（文件路径或 `lemma:<名字>`），不是抄的返回 None。"""
        for l in lemmas:
            if self.state['lemmas'][l].get('copied'):
                return f'lemma:{l}'
        copy = provenance.check(body, self.began, exclude=self._own_files())
        return copy['source'] if copy['copied'] else None

    # ---- lemma ----
    def _lemma(self, agent, problem, lemma):
        from .verify import check_submission
        info = self.state['lemmas'][lemma]
        if info['status'] == 'proved' or not self._live(info):  # 用到它的图都已作废，或已经由子图拼出
            return
        item = self.items[problem]
        path = self.scratch / agent / f'{lemma}.lean'
        path.unlink(missing_ok=True)
        last = info.get('last_attempt')
        previous = PREVIOUS_NOTE.format(path=last['file'], reason=last['reason'][:1500]) \
            if last and Path(last['file']).exists() else ''
        prompt = LEMMA_PROMPT.format(root=ROOT, agent=agent, lemma=lemma, problem=problem, statement=info['statement'],
                                     opens_note=_opens_note(item), notes=_notes(item), file=path, forge=FORGE, run=self.run,
                                     minutes=self.lemma_seconds // 60, previous=previous)
        began = time.time()
        code, message, used, slow = self._invoke(prompt, agent, seconds=self.lemma_seconds)
        status, reason = 'unsolved', '没有交出证明'
        if path.exists():
            body = main_last(path.read_text(encoding='utf-8'), lemma)
            try:
                result = check_submission(_task(item, lemma, ': ' + info['statement']), body, closed=info['statement'])
            except StatementError as exc:  # 提交本身不合规（剩 sorry、辅助引理名不对……）：算没证出来，可以再试
                result = dict(ok=False, reason=str(exc))
            reason = result.get('reason', '')
            if result.get('errors'):
                reason += '\n' + json.dumps(result['errors'], ensure_ascii=False)[:1200]
            if not result.get('ok'):
                # 留一份失败的提交给下一次尝试参考（工人目录下次会被覆盖，所以另存）
                keep = self.scratch / 'attempts' / f'{lemma}.{info.get("attempts", 0) + 1}.lean'
                keep.parent.mkdir(parents=True, exist_ok=True)
                keep.write_text(body, encoding='utf-8')
                with self.file_lock:  # 别的线程可能正在 _save 里序列化这个字典
                    info['last_attempt'] = dict(file=str(keep), reason=reason)
            if result.get('ok'):
                status = 'disproved' if result['kind'] == 'disproved' else 'proved'
                if status == 'proved':
                    info['body'] = body
                    info['copied'] = self._copy_of(body)
        with self.file_lock:
            info['status'] = status
            info['attempts'] = info.get('attempts', 0) + 1
            if status == 'disproved':  # 拆法不成立：用到它的图（题目图、父引理的子图）全部作废
                self._kill_users(info)
            self._save()
        self._record(dict(mode='portfolio-lemma', task=lemma, worker=agent, outcome=status, progress=status != 'unsolved', copied=info.get('copied'),
                          seconds=round(time.time() - began), tokens=used, exit=code, timed_out=slow,
                          reason=reason[:300], message=message[-500:]))
        if status == 'proved':
            self._resolved(lemma)
        elif status == 'unsolved' and info['attempts'] < self.lemma_attempts:
            self._push(('lemma', problem, lemma))  # 再派一个人接着试（放到队尾，先让别的图推进）
        elif status == 'unsolved' and self._may_split(info) and self._live(info):
            self._push(('split', problem, lemma))  # 试够了还没证出：再拆一层

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
        check = dict(before=self.began, exclude=self._own_files(),
                     inherited=next((f'lemma:{l}' for l in lemmas if self.state['lemmas'][l].get('copied')), None))
        result = _safe_check(self.set_name, problem, body, self.run, **check)
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
                result = _safe_check(self.set_name, problem, out.read_text(encoding='utf-8'), self.run, **check)
        with self.file_lock:
            copied = (result.get('copy') or {}).get('copied')
            if result.get('solved') and copied:
                # 抄来的（拼出的证明或用到的子引理大段和本轮开始前就有的文件相同）：不算解出，别的图接着做
                d.update(status='copied', copied=result['copy']['source'])
            elif result.get('solved'):
                d['status'] = 'solved'
                self.state['problems'][problem]['solved_by'] = self.state['problems'][problem]['solved_by'] or dag
            else:
                d['status'] = 'assembly_failed'
            self._save()
        self._record(dict(mode='portfolio-assemble', task=f'{problem}/{dag}', worker=agent,
                          outcome=('copied' if copied else 'solved') if result.get('solved') else 'failed',
                          progress=bool(result.get('solved')) and not copied,
                          seconds=round(time.time() - began), tokens=used, exit=code, timed_out=slow,
                          reason=f'{how}: ' + result.get('reason', '')[:280], message=message[-300:],
                          **({'copied': result['copy']['copied'], 'copy_source': result['copy']['source']} if result.get('copy') else {})))


def _safe_check(set_name, problem, body, run, **copy_check):
    """评测检查器；静态检查拒收（命名、禁用词）时记为没解出。Lean、磁盘等基础设施错误照常抛出，不当成没解出。"""
    try:
        return bench.check(set_name, problem, body, run, 'scheduler', **copy_check)
    except StatementError as exc:
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
                         disproved=sum(l['status'] == 'disproved' for l in lemmas), copied_lemmas=sum(bool(l.get('copied')) for l in lemmas)))
    return dict(run=run, solved=sum(bool(r['solved_by']) for r in rows), problems=len(rows), rows=rows)
