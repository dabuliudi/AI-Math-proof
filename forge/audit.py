"""批量论文体检：每篇论文的命题由两个互不相干的 agent 各自形式化，再让 Lean 判定两版是否等价。

为什么这样做：Lean 只能保证“证明对”，保证不了“命题译对了”（statement fidelity），这是论文形式化公认的难点。
两个 agent 独立地从原文译出同一条命题，如果内核能证明两版等价，说明两人读出的意思一致，可信度比单人译高得多；
证出不等价或判不出来的，标成“存疑”交给人看。两人犯同一个错仍然可能，所以等价只是更可信，不是保证。

流程（每一步都是调度器里的一个工作项，多个工人并行地从同一个队列里取）：
1. formalise：一个 agent 读论文全文，写出命题清单 forge/data/papers/<编号>.json（原文、Lean 命题、备注），
   需要的新定义用 `forge define` 入库。不证明、不提交到队列。
2. twin：另一个 agent 只拿到原文和定义列表（不看第一版），为每条命题独立写一版 Lean 命题。
3. compare：两版结构哈希相同就直接算一致；否则让第三个 agent 证明 `A ↔ B` 或 `¬ (A ↔ B)`，由内核检查。
4. 一致的命题提交到任务队列（之后用 `forge run --prefix` 清队列证明或证伪）；不一致和判不出的写进清单等人看。
"""
import json
import re
import time
from pathlib import Path

from . import tasks
from .leanrun import DATA, ROOT
from .scheduler import FORGE, Scheduler
from .statement import closed_form

PAPERS = DATA / 'papers'
TEXTS = DATA / 'staging' / 'papers'

FORMALISE_PROMPT = '''You are auditing a mathematics paper in a Lean 4 + Mathlib project at {root}. Agent name: `{agent}`.
The paper's full text (LaTeX formulas inline) is in {text}. Paper id: {paper}.

Task: write a worklist of the paper's main mathematical claims, each formalised as a Lean statement, to {worklist}.
Format (JSON):
{{"arxiv": "{paper}", "title": "...", "url": "https://arxiv.org/abs/{paper}", "auditor": "{agent}",
  "definitions": [{{"name": "...", "lean": "<the def>", "notes": "..."}}],
  "statements": [{{"label": "Theorem 2.1", "name": "{prefix}thm2_1", "original": "<the claim, copied from the paper>",
                   "lean": "<binders> : <conclusion>", "notes": "<how you interpreted it>"}}]}}
Rules:
- Pick at most 12 claims: theorems, propositions, lemmas and corollaries with precise statements, plus explicit numeric
  claims (tables, examples) that can be checked. Skip claims that need theory far beyond Mathlib; say so in "skipped".
- Every name starts with `{prefix}`. "original" must be the paper's own wording (LaTeX allowed), not a paraphrase.
- Formalise exactly what is printed, including hypotheses. Do not fix the paper; if it looks wrong, formalise it as
  printed and say so in notes.
- If a statement needs a new definition, add it with `{forge} define <name> <file> --agent {agent}` (file containing one
  `def`; write it under {scratch}). Prefer Mathlib's existing notions; check with `{forge} lookup "<fragment>"`.
- Check every statement typechecks: `{forge} check-statement "<binders> : <conclusion>"`.
- Do not prove anything, do not run `{forge} propose`, do not edit files other than the worklist and your scratch files.
End with one line: RESULT: <number of statements> statements.
'''

TWIN_PROMPT = '''You are formalising one claim from a mathematics paper in a Lean 4 + Mathlib project at {root}. Agent: `{agent}`.
Another agent formalised the same claim separately; your version will be compared with theirs by the Lean kernel, so
work only from the paper. Do NOT open anything under forge/data/papers/ or other agents' scratch directories.

Paper text: {text} (read the surrounding section for notation and standing assumptions).
Claim ({label}):
{original}

Library definitions made for this paper (use them where the paper uses that notion; inspect with `{forge} source <name>`):
{definitions}

Write the statement as one line `<binders> : <conclusion>` to {out}. Formalise exactly what is printed, with all
hypotheses (including standing assumptions stated earlier in the paper). Check it with
`{forge} check-statement "<binders> : <conclusion>"` until it typechecks. Do not prove it. Do not edit other files.
End with one line: RESULT: written.
'''

EQUIV_PROMPT = '''In a Lean 4 + Mathlib project at {root} (agent `{agent}`), two people formalised the same claim from a paper.
Decide with a kernel-checked proof whether their versions are equivalent.

Version A: {a}
Version B: {b}

Write ONE of these to {proof}, in the project's checking format (the file is placed inside `namespace Mathlib2`):
- `theorem {name} : {closed} := by ...`              (they are equivalent)
- `theorem {name}_disproof : ¬ ({closed}) := by ...` (they are not equivalent: give a concrete instance where they differ)
Check your file with `{forge} equiv-check {name} {proof}` until it says ok. No sorry, axiom, or native_decide.
If after a real attempt you can do neither, leave no file and explain the difference you suspect in one sentence.
End with one line: RESULT: equivalent | different | unknown.
'''


def prefix_for(paper):
    return 'x' + re.sub(r'[^0-9a-z]+', '_', paper.lower().split('v')[0]).strip('_') + '_'


def equiv_task(name, a, b):
    return dict(name=name, statement=f': ({closed_form(a)}) ↔ ({closed_form(b)})')


def equiv_check(name, path):
    """供 agent 自检：读出两版命题，校验它写的等价证明或反例。"""
    from .verify import check_submission
    pair = _pairs().get(name)
    if not pair:
        return dict(ok=False, reason=f'没有等价检查任务 {name}')
    return check_submission(equiv_task(name, pair['a'], pair['b']), Path(path).read_text(encoding='utf-8'))


PAIRS = DATA / 'staging' / 'audit_pairs.json'


def _pairs():
    return json.loads(PAIRS.read_text(encoding='utf-8')) if PAIRS.exists() else {}


class PaperAudit(Scheduler):
    """在调度器上加三种工作项。工作项放在一个共享队列里，前一步完成后把下一步放进去。"""

    def run_audit(self, papers, propose=True):
        self.propose = propose
        self.queue = [('formalise', p) for p in papers]
        self.busy = 0
        self.file_lock = __import__('threading').Lock()
        return self._run_threads(self._audit_worker, ())

    # ---- 队列 ----
    def _take(self):
        while True:
            with self.lock:
                if self.stop_reason:
                    return None
                if self.queue:
                    self.busy += 1
                    return self.queue.pop(0)
                if not self.busy:
                    self.stop_reason = '所有论文都已处理完'
                    return None
            time.sleep(5)

    def _push(self, *items):
        with self.lock:
            self.queue.extend(items)

    def _audit_worker(self, index):
        agent = f'{self.run}-w{index}'
        (self.scratch / agent).mkdir(parents=True, exist_ok=True)
        while True:
            item = self._take()
            if item is None:
                return
            try:
                if self._may_start():
                    getattr(self, '_' + item[0])(agent, *item[1:])
            finally:
                with self.lock:
                    self.busy -= 1

    # ---- 三种工作项 ----
    def _formalise(self, agent, paper):
        text = TEXTS / f'{paper}.txt'
        worklist = PAPERS / f'{paper}.json'
        began = time.time()
        if not worklist.exists():
            prompt = FORMALISE_PROMPT.format(root=ROOT, agent=agent, text=text, paper=paper, worklist=worklist,
                                             prefix=prefix_for(paper), forge=FORGE, scratch=self.scratch / agent)
            code, message, used, slow = self._invoke(prompt, agent)
        else:
            code, message, used, slow = 0, 'worklist already exists', 0, False
        statements = []
        if worklist.exists():
            try:
                statements = [s for s in json.loads(worklist.read_text(encoding='utf-8')).get('statements', [])
                              if s.get('name', '').startswith(prefix_for(paper)) and s.get('lean')]
            except json.JSONDecodeError:
                message = 'worklist is not valid JSON'
        self._record(dict(mode='audit-formalise', task=paper, worker=agent, outcome=f'{len(statements)} statements',
                          progress=bool(statements), seconds=round(time.time() - began), tokens=used, exit=code,
                          timed_out=slow, message=message[-500:]))
        self._push(*[('twin', paper, s['name']) for s in statements if not s.get('fidelity')])

    def _statement(self, paper, name):
        data = json.loads((PAPERS / f'{paper}.json').read_text(encoding='utf-8'))
        return data, next(s for s in data['statements'] if s['name'] == name)

    def _update(self, paper, name, **fields):
        with self.file_lock:
            path = PAPERS / f'{paper}.json'
            data = json.loads(path.read_text(encoding='utf-8'))
            for s in data['statements']:
                if s['name'] == name:
                    s.setdefault('fidelity', {}).update(fields)
            path.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding='utf-8')

    def _twin(self, agent, paper, name):
        from .verify import statement_hashes
        data, item = self._statement(paper, name)
        out = self.scratch / agent / f'{name}.twin.txt'
        out.unlink(missing_ok=True)
        defs = '\n'.join(f'- {d["name"]}: {d.get("notes", "")}' for d in data.get('definitions', [])) or '(none)'
        prompt = TWIN_PROMPT.format(root=ROOT, agent=agent, text=TEXTS / f'{paper}.txt', label=item.get('label', ''),
                                    original=item.get('original', ''), definitions=defs, forge=FORGE, out=out)
        began = time.time()
        code, message, used, slow = self._invoke(prompt, agent, effort='high')
        twin = out.read_text(encoding='utf-8').strip() if out.exists() else ''
        verdict = 'no_twin'
        if twin:
            hashes = statement_hashes([item['lean'], twin])
            if None in hashes:
                verdict = 'twin_invalid' if hashes[0] else 'original_invalid'
            elif hashes[0] == hashes[1]:
                verdict = 'same'
            else:
                verdict = 'pending'
        self._update(paper, name, twin=twin, twin_by=agent, verdict=verdict)
        self._record(dict(mode='audit-twin', task=name, worker=agent, outcome=verdict, progress=bool(twin),
                          seconds=round(time.time() - began), tokens=used, exit=code, timed_out=slow, message=message[-500:]))
        if verdict == 'same':
            self._accept(paper, name)
        elif verdict == 'pending':
            self._push(('equiv', paper, name))

    def _equiv(self, agent, paper, name):
        from .verify import check_submission
        _, item = self._statement(paper, name)
        a, b = item['lean'], item['fidelity']['twin']
        eq = f'{name}_eqv'
        with self.file_lock:
            pairs = _pairs()
            pairs[eq] = dict(a=a, b=b)
            PAIRS.parent.mkdir(parents=True, exist_ok=True)
            PAIRS.write_text(json.dumps(pairs, ensure_ascii=False, indent=1), encoding='utf-8')
        proof = self.scratch / agent / f'{eq}.lean'
        proof.unlink(missing_ok=True)
        task = equiv_task(eq, a, b)
        prompt = EQUIV_PROMPT.format(root=ROOT, agent=agent, a=a, b=b, proof=proof, name=eq,
                                     closed=task['statement'][2:], forge=FORGE)
        began = time.time()
        code, message, used, slow = self._invoke(prompt, agent)
        verdict, reason = 'unknown', message[-300:]
        if proof.exists():
            result = check_submission(task, proof.read_text(encoding='utf-8'))
            if result['ok']:
                verdict = 'different' if result['kind'] == 'disproved' else 'equivalent'
            reason = result['reason']
        self._update(paper, name, verdict=verdict, equivalence_proof=proof.read_text(encoding='utf-8') if verdict != 'unknown' else '',
                     note=reason[:500])
        self._record(dict(mode='audit-equiv', task=name, worker=agent, outcome=verdict, progress=verdict != 'unknown',
                          seconds=round(time.time() - began), tokens=used, exit=code, timed_out=slow, message=message[-500:]))
        if verdict == 'equivalent':
            self._accept(paper, name)

    def _accept(self, paper, name):
        """两版一致：把第一版提交到任务队列，之后由清队列的 agent 证明或证伪。"""
        if not self.propose or tasks.load(name)[0]:
            return
        data, item = self._statement(paper, name)
        result = tasks.propose(name, item['lean'], informal=item.get('label', ''), origin='paper',
                               source=data.get('url', paper), proposed_by=self.run, original=item.get('original', ''))
        self._update(paper, name, queued=result.get('status'))


# ---- 取论文 ----
class _Text(__import__('html.parser').parser.HTMLParser):
    """把 arXiv 的 HTML 版论文转成纯文本：公式取 LaTeX 原文（alttext），跳过脚本、样式、导航。"""
    SKIP = {'script', 'style', 'nav', 'header', 'footer'}

    def __init__(self):
        super().__init__()
        self.parts, self.skip = [], 0

    def handle_starttag(self, tag, attrs):
        if tag in self.SKIP:
            self.skip += 1
        elif tag == 'math' and not self.skip:
            alt = dict(attrs).get('alttext')
            if alt:
                self.parts.append(f' ${alt}$ ')
            self.skip += 1
        elif tag in ('p', 'div', 'h1', 'h2', 'h3', 'h4', 'li', 'tr', 'br'):
            self.parts.append('\n')

    def handle_endtag(self, tag):
        if tag in self.SKIP or tag == 'math':
            self.skip = max(0, self.skip - 1)

    def handle_data(self, data):
        if not self.skip:
            self.parts.append(data)


def html_to_text(html):
    parser = _Text()
    parser.feed(html)
    text = ''.join(parser.parts)
    return re.sub(r'\n\s*\n+', '\n\n', re.sub(r'[ \t]+', ' ', text)).strip()


def fetch(paper):
    """下载 arXiv 的 HTML 版全文并转成纯文本，存到 forge/data/staging/papers/<编号>.txt。没有 HTML 版的返回 None。"""
    import urllib.request
    if not re.fullmatch(r'\d{4}\.\d{4,5}(v\d+)?', paper):
        raise ValueError(f'不是 arXiv 编号：{paper}')
    out = TEXTS / f'{paper}.txt'
    if out.exists():
        return out
    request = urllib.request.Request(f'https://arxiv.org/html/{paper}', headers={'User-Agent': 'forge-paper-audit/0.1'})
    try:
        with urllib.request.urlopen(request, timeout=60) as response:
            html = response.read(20_000_000).decode('utf-8', errors='replace')
    except Exception:  # noqa: BLE001 - 没有 HTML 版或网络错误：跳过这篇
        return None
    text = html_to_text(html)
    if len(text) < 2000:
        return None
    TEXTS.mkdir(parents=True, exist_ok=True)
    out.write_text(text, encoding='utf-8')
    return out


def summary(paper):
    """一篇论文的体检结果：每条命题的忠实度判定和队列状态。"""
    data = json.loads((PAPERS / f'{paper}.json').read_text(encoding='utf-8'))
    rows = []
    for s in data.get('statements', []):
        state, task = tasks.load(s['name']) if s.get('name') else (None, {})
        rows.append(dict(name=s.get('name'), label=s.get('label'), fidelity=s.get('fidelity', {}).get('verdict', 'not_checked'),
                         status=(task or {}).get('status') or state))
    tally = {}
    for r in rows:
        tally[r['fidelity']] = tally.get(r['fidelity'], 0) + 1
    return dict(paper=paper, title=data.get('title'), statements=len(rows), fidelity=tally, rows=rows)
