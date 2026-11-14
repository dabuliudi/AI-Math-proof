"""扩展基准：用固定种子生成更难、更多样的 Nat 关系题，并行运行并汇总。

原 benchmark.py 只有 7 题且接近饱和，无法区分引擎改动的好坏；本文件提供可重复的度量基线。
题目只含 problem 字段，类别与“是否应可证”仅用于事后统计，不传入引擎。
内部开发基准，不是第三方盲测。

用法：python -m phase2.bench_ext [--workers 6] [--budget 12] [--seed 20261114] [--label 名称]
"""
import argparse
import hashlib
import json
import random
import time
import uuid
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from .compiler import ROOT
from .engine import discover

NAMES = list('abcdefgh')


def _problem(variables, assumptions, goals, rng, text=''):
    assumptions = list(assumptions)
    rng.shuffle(assumptions)
    return dict(domain='Nat', variables=sorted(variables), assumptions=assumptions, goals=goals, original_text=text)


def generate(seed):
    """返回 [(id, category, provable, problem)]。provable=False 的是对照题，证出即说明引擎或基准有错。"""
    rng = random.Random(seed)
    cases = []

    def add(category, provable, problem):
        cases.append((f'{category}-{sum(c[1] == category for c in cases)}', category, provable, problem))

    def chain(n):
        v = NAMES[:n]
        rng.shuffle(v)
        return v

    # 1. 混合 ≤ / < 链：至少一个严格不等号时端点严格小于。
    for n in (3, 4, 5, 6, 7):
        v = chain(n)
        ops = [rng.choice('≤<') for _ in range(n - 1)]
        strict = '<' in ops
        add('order_chain', True, _problem(v, [f'{a} {o} {b}' for a, o, b in zip(v, ops, v[1:])],
                                         [f'{v[0]} {"<" if strict else "≤"} {v[-1]}'], rng))
    # 2. 整除链 + 末项为正 ⇒ 起点 ≤ 末项。
    for n in (3, 4, 5, 6, 7):
        v = chain(n)
        add('dvd_chain_le', True, _problem(v, [f'{a} ∣ {b}' for a, b in zip(v, v[1:])] + [f'0 < {v[-1]}'],
                                          [f'{v[0]} ≤ {v[-1]}'], rng))
    # 3. 等式与序混合。
    for n in (4, 5, 6):
        v = chain(n)
        ops = [rng.choice(['=', '≤', '=', '<']) for _ in range(n - 1)]
        goal = '<' if '<' in ops else ('≤' if '≤' in ops else '=')
        add('eq_mixed', True, _problem(v, [f'{a} {o} {b}' for a, o, b in zip(v, ops, v[1:])],
                                      [f'{v[0]} {goal} {v[-1]}'], rng))
    # 4. 反对称：环形 ≤ 或互相整除 ⇒ 相等。
    for n in (2, 3, 4):
        v = chain(n)
        add('antisymm', True, _problem(v, [f'{a} ≤ {b}' for a, b in zip(v, v[1:] + v[:1])], [f'{v[0]} = {v[-1]}'], rng))
    for n in (2, 3):
        v = chain(n)
        add('antisymm', True, _problem(v, [f'{a} ∣ {b}' for a, b in zip(v, v[1:] + v[:1])], [f'{v[0]} = {v[-1]}'], rng))
    # 5. 带干扰假设的链：多出与目标无关的分支。
    for n in (4, 5, 6):
        v = chain(n + 2)
        main, extra = v[:n], v[n:]
        noise = [f'{extra[0]} ≤ {extra[1]}', f'{main[1]} ≤ {extra[0]}', f'{extra[1]} ∣ {main[0]}']
        add('distractors', True, _problem(v, [f'{a} ≤ {b}' for a, b in zip(main, main[1:])] + noise,
                                         [f'{main[0]} ≤ {main[-1]}'], rng))
    # 6. 多目标合取。
    for n in (4, 5, 6):
        v = chain(n)
        add('conjunction', True, _problem(v, [f'{a} ∣ {b}' for a, b in zip(v, v[1:])] + [f'0 < {v[-1]}'],
                                         [f'{v[0]} ∣ {v[-1]}', f'{v[0]} ≤ {v[-1]}', f'0 < {v[0]}'], rng))
    # 7. 正性传播：由 a < b 与整除推出正与下界。
    for n in (3, 4, 5):
        v = chain(n)
        add('positivity', True, _problem(v, [f'{v[0]} < {v[1]}'] + [f'{a} ∣ {b}' for a, b in zip(v[2:], v[1:])],
                                        [f'1 ≤ {v[1]}'] + ([f'{v[-1]} ≤ {v[1]}'] if n > 2 else []), rng))
    # 8. 对照题：在自然数上不成立，任何“proved”都是错误。
    v = chain(3)
    add('control_false', False, _problem(v, [f'{v[0]} ≤ {v[1]}', f'{v[2]} ≤ {v[1]}'], [f'{v[0]} ≤ {v[2]}'], rng))
    v = chain(3)
    add('control_false', False, _problem(v, [f'{v[0]} ∣ {v[1]}', f'{v[1]} ∣ {v[2]}'], [f'{v[0]} < {v[2]}'], rng))
    v = chain(2)
    add('control_false', False, _problem(v, [f'{v[0]} ≤ {v[1]}'], [f'{v[0]} = {v[1]}'], rng))
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--workers', type=int, default=6)
    parser.add_argument('--budget', type=int, default=12)
    parser.add_argument('--seed', type=int, default=20261114)
    parser.add_argument('--label', default='')
    args = parser.parse_args()
    base = ROOT / 'phase2'
    cases = generate(args.seed)
    folder = base / 'benchmarks' / ('ext-' + time.strftime('%Y%m%d-%H%M%S') + '-' + uuid.uuid4().hex[:6])
    folder.mkdir(parents=True)
    engine_hashes = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(base.glob('*.py'))}
    (folder / 'inputs.json').write_text(json.dumps(dict(
        seed=args.seed, budget=args.budget, label=args.label, engine_hashes=engine_hashes,
        cases=[dict(id=i, category=c, provable=p, problem=q) for i, c, p, q in cases]), ensure_ascii=False, indent=2), encoding='utf-8')
    # 先串行跑一题，让规则目录缓存就绪，避免并发重复抽取。
    started = time.perf_counter()

    def run(case):
        cid, category, provable, problem = case
        t = time.perf_counter()
        try:
            result = discover(problem, budget=args.budget, run_root=folder / 'runs')
        except Exception as exc:  # 引擎崩溃单独计数，不当作 unknown 混过去
            result = dict(status='error', reason=repr(exc), formal_goal_verified=False, metrics={})
        return dict(id=cid, category=category, provable=provable, wall=time.perf_counter() - t, result=result)

    results = [run(cases[0])]
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        results += list(pool.map(run, cases[1:]))
    wall = time.perf_counter() - started
    (folder / 'results.json').write_text(json.dumps(results, ensure_ascii=False, indent=2), encoding='utf-8')
    provable = [r for r in results if r['provable']]
    solved = [r for r in provable if r['result']['status'] == 'proved']
    by_category = {}
    for r in results:
        entry = by_category.setdefault(r['category'], dict(cases=0, proved=0))
        entry['cases'] += 1
        entry['proved'] += r['result']['status'] == 'proved'
    compiles = [r['result'].get('metrics', {}).get('compile_attempts', 0) for r in results]
    summary = dict(
        label=args.label, seed=args.seed, budget=args.budget, workers=args.workers,
        cases=len(results), provable_cases=len(provable), solved=len(solved),
        solve_rate=round(len(solved) / len(provable), 4),
        false_proofs=sum(r['result']['status'] == 'proved' for r in results if not r['provable']),
        errors=sum(r['result']['status'] == 'error' for r in results),
        total_compiles=sum(compiles),
        compiles_per_solved=round(sum(r['result']['metrics']['compile_attempts'] for r in solved) / len(solved), 3) if solved else None,
        failed_compiles=sum(r['result'].get('metrics', {}).get('failed_compilations', 0) for r in results),
        wall_seconds=round(wall, 1),
        by_category=by_category,
        unsolved=[dict(id=r['id'], reason=r['result'].get('reason')) for r in provable if r['result']['status'] != 'proved'],
        ai_calls=0, external_blind_independence='NOT VERIFIED')
    (folder / 'summary.json').write_text(json.dumps(summary, ensure_ascii=False, indent=2), encoding='utf-8')
    print(json.dumps(summary, ensure_ascii=False, indent=2))
    print(folder)


if __name__ == '__main__':
    main()
