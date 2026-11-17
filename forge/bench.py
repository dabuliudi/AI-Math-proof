"""固定评测集：衡量“系统有没有真的变强”，而不是只看库里条目数涨没涨。

* 评测题存在 forge/data/bench/<集合>.jsonl，每行 {name, statement, hash}；hash 与分诊用的结构哈希相同。
* 评测题受保护：任何新命题、任何提交里的主定理或辅助引理，只要命题与评测题结构相同，一律拒收，
  防止把测试题当成训练题写进库里（那样分数会虚高）。
* 评测提交只判对错、不入库；每次尝试记在 forge/data/bench/runs/<集合>.<轮次>.jsonl，按轮次出成绩。
"""
import json
import time

from .leanrun import DATA
from .statement import StatementError, split_signature
from .verify import check_submission, constant_hashes, statement_hashes

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
    unusable = []
    for item in items:  # 命题本身不符合 `<binders> : <conclusion>` 格式（比如内部带 `:=`）的题先剔出来，不中断整批导入
        try:
            split_signature(item['statement'])
        except StatementError:
            unusable.append(item['name'])
    items = [item for item in items if item['name'] not in unusable]
    per_item = [item.get('opens', opens) for item in items]  # 每题可以自带 opens，否则用命令行给的
    # 题目可以自带模块导入（例如 Formal Conjectures 的题目模块）；求哈希时一次全部导入
    imports = sorted({m for item in items for m in item.get('imports', [])})
    origins = [item['origin'] for item in items if item.get('origin')]
    from .library import locked
    with locked():  # 导入 Mathlib2 需要库处于构建完的一致状态；别的进程入库时 .olean 会暂时缺失
        hashes = statement_hashes([item['statement'] for item in items], opens=per_item,
                                  preambles=[item.get('preamble', '') for item in items], imports=imports)
        # 题目来自某个已有常量（`origin`）时，重新写出的命题必须与原常量的类型结构相同，否则说明转写改了题意
        original = constant_hashes(origins, imports=imports) if origins else {}
    kept, dropped, unfaithful = [], [], []
    for item, digest, item_opens in zip(items, hashes, per_item):
        row = dict(name=item['name'], statement=item['statement'], hash=digest)
        if item_opens:
            row['opens'] = item_opens
        for key in ('preamble', 'imports', 'origin', 'source', 'category', 'context'):
            if item.get(key):
                row[key] = item[key]
        if not digest:
            dropped.append(row)
        elif item.get('origin') and original.get(item['origin']) != digest:
            unfaithful.append(row)
        else:
            kept.append(row)
    BENCH.mkdir(parents=True, exist_ok=True)
    _path(name).write_text(''.join(json.dumps(i, ensure_ascii=False) + '\n' for i in kept), encoding='utf-8')
    return dict(set=name, imported=len(kept), dropped=[d['name'] for d in dropped],
                unfaithful=[d['name'] for d in unfaithful], unusable=unusable)


def reserved():
    """所有评测题的结构哈希 -> “集合/题名”。"""
    out = {}
    if BENCH.exists():
        for path in BENCH.glob('*.jsonl'):
            for item in load(path.stem):
                out[item['hash']] = f'{path.stem}/{item["name"]}'
    return out


def _library_mid_build(result):
    return any('.olean' in e.get('message', '') and 'does not exist' in e.get('message', '')
               for e in result.get('errors') or [])


def check(name, problem, body, run, agent, before=None, exclude=()):
    """对一道评测题校验一份证明：只判对错，不入库，结果记入该轮次。
    给了 before（本轮开始的时间戳）就对解出的证明做抄写检测（provenance.py）：抄来的记下来源，成绩里不算解出。"""
    item = next((i for i in load(name) if i['name'] == problem), None)
    if item is None:
        return dict(ok=False, reason=f'评测集 {name} 里没有 {problem}')
    task = dict(name=problem, statement=item['statement'], opens=item.get('opens', ''), preamble=item.get('preamble', ''),
                imports=item.get('imports', []))
    result = check_submission(task, body)
    if _library_mid_build(result):
        # 别的进程正在入库重建时 Mathlib2 的 .olean 会暂时缺失，这不是证明的错；拿着库锁重查一次
        from .library import locked
        with locked():
            result = check_submission(task, body)
    solved = bool(result['ok']) and result['kind'] == 'proved'
    copy = None
    if solved and before is not None:
        from . import provenance
        copy = provenance.check(body, before, exclude=exclude)
    RUNS.mkdir(parents=True, exist_ok=True)
    # 交的是反证且内核通过：说明评测集里这道题的 Lean 写法本身为假（写错的题），单独记下，不算没做出。
    record = dict(problem=problem, run=run, agent=agent, solved=solved, reason=result.get('reason', ''),
                  refuted=bool(result['ok']) and result['kind'] == 'disproved',
                  at=time.strftime('%Y-%m-%dT%H:%M:%S%z'))
    if copy:
        record.update(copied=copy['copied'], copy_overlap=copy['overlap'], copy_source=copy['source'])
    with open(RUNS / f'{name}.{run}.jsonl', 'a', encoding='utf-8') as handle:
        handle.write(json.dumps(record, ensure_ascii=False) + '\n')
    return dict(result, solved=solved, copy=copy)


def score(name):
    """每个轮次的成绩：解出的题数 / 总题数，以及尝试次数。轮次按名字排序，便于看趋势。"""
    total = len(load(name))
    rows = []
    for path in sorted(RUNS.glob(f'{name}.*.jsonl')) if RUNS.exists() else []:
        records = [json.loads(line) for line in path.read_text(encoding='utf-8').splitlines() if line.strip()]
        solved = sorted({r['problem'] for r in records if r['solved'] and not r.get('copied')})  # 抄来的不算
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
        entry['solved'].update(r['problem'] for r in records if r['solved'] and not r.get('copied'))
        entry['attempts'] += len(records)
        entry['machines'].append(path.name.split('@')[1][:-len('.jsonl')])
    merged = [dict(run=base, machines=sorted(e['machines']), solved=len(e['solved']), total=total,
                   rate=round(len(e['solved']) / total, 4) if total else None, attempts=e['attempts'])
              for base, e in sorted(combined.items())]
    return dict(set=name, problems=total, runs=rows, combined=merged)
