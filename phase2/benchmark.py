"""只把problem交给引擎；类别不影响策略。保留每一轮及聚合指标。"""
import json
import uuid
import random
import hashlib
from pathlib import Path
from .engine import discover
from .compiler import ROOT


def main():
    base=ROOT/'phase2'; suite=json.loads((base/'benchmarks/suite.json').read_text(encoding='utf-8'))
    # 持久化引擎版本后才生成额外题目；它不是第三方独立留出集。
    engine_hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in base.glob('*.py')}
    seed=726819; rng=random.Random(seed)
    for i in range(2):
        variables=['x'+str(j) for j in range(5)]; rng.shuffle(variables)
        assumptions=[f'{a} ≤ {b}' for a,b in zip(variables,variables[1:])]; rng.shuffle(assumptions)
        suite['cases'].append(dict(id=f'generated-{i}',category='post_freeze_generated_order_chain',problem=dict(domain='Nat',variables=sorted(variables),assumptions=assumptions,goals=[f'{variables[0]} ≤ {variables[-1]}'])))
    folder=base/'benchmarks'/('run-'+uuid.uuid4().hex); folder.mkdir()
    (folder/'inputs.json').write_text(json.dumps(dict(seed=seed,engine_hashes=engine_hashes,**suite),ensure_ascii=False,indent=2),encoding='utf-8')
    results=[]
    for case in suite['cases']:
        result=discover(case['problem'],budget=12,run_root=folder/'runs')
        results.append(dict(id=case['id'],category=case['category'],result=result))
        (folder/'results.json').write_text(json.dumps(results,ensure_ascii=False,indent=2),encoding='utf-8')
        print(case['id'],result['status'],result.get('metrics'),flush=True)
    n=len(results); metrics=[r['result'].get('metrics',{}) for r in results]
    summary=dict(cases=n,proved=sum(r['result']['status']=='proved' for r in results),unknown=sum(r['result']['status']=='unknown' for r in results),
        first_success_rate=sum(m.get('first_compile_solved_target',False) for m in metrics)/n,
        final_success_rate=sum(r['result']['formal_goal_verified'] for r in results)/n,
        average_compiles=sum(m.get('compile_attempts',0) for m in metrics)/n,average_repairs=sum(m.get('repair_attempts',0) for m in metrics)/n,
        average_mathlib_reuse=sum(m.get('reused_mathlib_theorems',0) for m in metrics)/n,
        average_core_reuse=sum(m.get('reused_lean_core_theorems',0) for m in metrics)/n,
        average_intermediate_lemmas=sum(m.get('intermediate_lemmas',0) for m in metrics)/n,
        average_dag_depth=sum(m.get('dag_depth',0) for m in metrics)/n,
        human_interventions=0,ai_calls=0,ai_cost=0,ai_status='no AI call',source_alignment='unconfirmed',external_blind_independence='NOT VERIFIED')
    (folder/'summary.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2),encoding='utf-8')
    print(folder,flush=True)


if __name__=='__main__': main()
