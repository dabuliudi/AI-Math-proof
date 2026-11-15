"""固定评测集：衡量“系统有没有真的变强”，而不是只看库里条目数涨没涨。

* 评测题存在 forge/data/bench/<集合>.jsonl，每行 {name, statement, hash}；hash 与分诊用的结构哈希相同。
* 评测题受保护：任何新命题、任何提交里的主定理或辅助引理，只要命题与评测题结构相同，一律拒收，
  防止把测试题当成训练题写进库里（那样分数会虚高）。
* 评测提交只判对错、不入库；每次尝试记在 forge/data/bench/runs/<集合>.<轮次>.jsonl，按轮次出成绩。
"""
import json
import time

from .leanrun import DATA
from .verify import check_submission, statement_hashes

BENCH = DATA / 'bench'
RUNS = BENCH / 'runs'


def _path(name):
    if not name.replace('_', '').replace('-', '').isalnum():
        raise ValueError('评测集名称只能含字母、数字、- 和 _')
    return BENCH / f'{name}.jsonl'


def load(name):
    path = _path(name)
    if not path.exists():
        return []
    return [json.loads(line) for line in path.read_text(encoding='utf-8').splitlines() if line.strip()]


def import_set(name, source, opens=''):
    """从 JSONL（每行 {name, statement}）导入一个评测集；求出每题的结构哈希，类型检查不过的题丢弃并报告。

    `opens`：题目依赖的记号设置（如 `Real Nat`），随题目一起保存，校验证明时自动加上。
    """
    items = [json.loads(line) for line in source.read_text(encoding='utf-8').splitlines() if line.strip()]
    hashes = statement_hashes([item['statement'] for item in items], opens=opens)
    kept, dropped = [], []
    for item, digest in zip(items, hashes):
        row = dict(name=item['name'], statement=item['statement'], hash=digest)
        if opens:
            row['opens'] = opens
        (kept if digest else dropped).append(row)
    BENCH.mkdir(parents=True, exist_ok=True)
    _path(name).write_text(''.join(json.dumps(i, ensure_ascii=False) + '\n' for i in kept), encoding='utf-8')
    return dict(set=name, imported=len(kept), dropped=[d['name'] for d in dropped])


def reserved():
    """所有评测题的结构哈希 -> “集合/题名”。"""
    out = {}
    if BENCH.exists():
        for path in BENCH.glob('*.jsonl'):
            for item in load(path.stem):
                out[item['hash']] = f'{path.stem}/{item["name"]}'
    return out


def check(name, problem, body, run, agent):
    """对一道评测题校验一份证明：只判对错，不入库，结果记入该轮次。"""
    item = next((i for i in load(name) if i['name'] == problem), None)
    if item is None:
        return dict(ok=False, reason=f'评测集 {name} 里没有 {problem}')
    task = dict(name=problem, statement=item['statement'], opens=item.get('opens', ''))
    result = check_submission(task, body)
    solved = bool(result['ok']) and result['kind'] == 'proved'
    RUNS.mkdir(parents=True, exist_ok=True)
    # 交的是反证且内核通过：说明评测集里这道题的 Lean 写法本身为假（写错的题），单独记下，不算没做出。
    record = dict(problem=problem, run=run, agent=agent, solved=solved, reason=result.get('reason', ''),
                  refuted=bool(result['ok']) and result['kind'] == 'disproved',
                  at=time.strftime('%Y-%m-%dT%H:%M:%S%z'))
    with open(RUNS / f'{name}.{run}.jsonl', 'a', encoding='utf-8') as handle:
        handle.write(json.dumps(record, ensure_ascii=False) + '\n')
    return dict(result, solved=solved)


def score(name):
    """每个轮次的成绩：解出的题数 / 总题数，以及尝试次数。轮次按名字排序，便于看趋势。"""
    total = len(load(name))
    rows = []
    for path in sorted(RUNS.glob(f'{name}.*.jsonl')) if RUNS.exists() else []:
        records = [json.loads(line) for line in path.read_text(encoding='utf-8').splitlines() if line.strip()]
        solved = sorted({r['problem'] for r in records if r['solved']})
        # 旧记录没有 refuted 字段：校验通过却不算解出，只可能是交了反证
        refuted = sorted({r['problem'] for r in records if r.get('refuted', r.get('reason', '').startswith('通过') and not r['solved'])}
                         - set(solved))
        valid = total - len(refuted)
        rows.append(dict(run=path.name[len(name) + 1:-len('.jsonl')], solved=len(solved), total=total,
                         rate=round(len(solved) / total, 4) if total else None, attempts=len(records),
                         refuted=refuted, rate_on_true=round(len(solved) / valid, 4) if valid else None))
    # 同一轮次分在几台机器上跑时，轮次名写成 “名字@机器”；这里把它们合并成一行总成绩。
    combined = {}
    for path in sorted(RUNS.glob(f'{name}.*@*.jsonl')) if RUNS.exists() else []:
        base = path.name[len(name) + 1:-len('.jsonl')].split('@')[0]
        if base.endswith('-practice'):
            continue
        records = [json.loads(line) for line in path.read_text(encoding='utf-8').splitlines() if line.strip()]
        entry = combined.setdefault(base, dict(solved=set(), attempts=0, machines=[]))
        entry['solved'].update(r['problem'] for r in records if r['solved'])
        entry['attempts'] += len(records)
        entry['machines'].append(path.name.split('@')[1][:-len('.jsonl')])
    merged = [dict(run=base, machines=sorted(e['machines']), solved=len(e['solved']), total=total,
                   rate=round(len(e['solved']) / total, 4) if total else None, attempts=e['attempts'])
              for base, e in sorted(combined.items())]
    return dict(set=name, problems=total, runs=rows, combined=merged)
