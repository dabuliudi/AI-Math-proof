"""事故回归集：每次出过的问题都变成一条用例，改动分诊、导入、检查逻辑后重跑，防止同一个问题再犯。

做法来自 Claude Code 团队的代码审查实践（每次事故都加一条评测用例，评审器的任何改动都要对整套用例打分）。
这里的“事故”指 forge 自己出过的错：误收、误判、转换错误、提交不一致。

用例存在 forge/data/regressions.jsonl，每行：
  {id, incident, kind, input, expect}
kind:
  triage   —— 对 input（命题）跑分诊，expect 里的条件都要成立
  import   —— input 经大算子转换后应等于 expect.output
  lint     —— input 的文本检查提醒条数应等于 expect.warnings
  consistency —— 台账与分片一致（input 不用）
"""
import json
import re
from concurrent.futures import ThreadPoolExecutor

from . import library
from .leanrun import DATA

CASES = DATA / 'regressions.jsonl'


def load():
    if not CASES.exists():
        return []
    return [json.loads(line) for line in CASES.read_text(encoding='utf-8').splitlines() if line.strip()]


def consistency():
    """台账里的每个条目都要在分片里找得到，分片里的每个条目也都要登记在台账里。
    （事故：一次提交只带了台账、没带分片，升级分支因此少了 5 条定理。）"""
    with library.locked():  # 持入库锁读：入库进行中（分片已追加、台账还没写）的中间状态不算不一致
        in_ledger = {e['task'] for e in library.entries()}
        in_shards = set()
        for path in sorted(library.SHARDS.glob('S*.lean')):
            in_shards.update(re.findall(r'^-- forge:entry (\S+) ', path.read_text(encoding='utf-8'), re.M))
    return dict(missing_in_shards=sorted(in_ledger - in_shards), missing_in_ledger=sorted(in_shards - in_ledger))


def _check(expect, report):
    """expect 的每个键是一个条件；返回不满足的条件列表。"""
    failed = []
    for key, want in expect.items():
        if key == 'known_or_follows':
            got = bool(report.get('known') or report.get('follows_from'))
        elif key == 'auto_contains':
            got = want in report.get('auto', [])
            want = True
        elif key == 'counterexample':
            got = bool(report.get('counterexample'))
        elif key == 'vacuous':
            got = bool(report.get('vacuous'))
        else:
            got = report.get(key)
        if got != want:
            failed.append(f'{key}: 期望 {want!r}，实际 {got!r}')
    return failed


def run(jobs=3):
    from .importers import convert_big_operators
    from .statement import lint_statement
    from .verify import triage
    cases = load()
    results = []
    triage_cases = [c for c in cases if c['kind'] == 'triage']
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        reports = dict(zip([c['id'] for c in triage_cases],
                           pool.map(lambda c: triage('regress_' + re.sub(r'\W', '_', c['id']), c['input']), triage_cases)))
    for case in cases:
        if case['kind'] == 'triage':
            failed = _check(case['expect'], reports[case['id']])
        elif case['kind'] == 'import':
            got = convert_big_operators(case['input'])[0]
            failed = [] if got == case['expect']['output'] else [f'转换结果 {got!r}']
        elif case['kind'] == 'lint':
            got = len(lint_statement(case['input']))
            failed = [] if got == case['expect']['warnings'] else [f'提醒条数 {got}']
        elif case['kind'] == 'consistency':
            got = consistency()
            failed = [f'{k}: {v[:10]}' for k, v in got.items() if v]
        else:
            failed = [f'未知用例类型 {case["kind"]}']
        results.append(dict(id=case['id'], ok=not failed, failed=failed))
    return dict(ok=all(r['ok'] for r in results), passed=sum(r['ok'] for r in results), total=len(results), results=results)
