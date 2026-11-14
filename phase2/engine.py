import json
import time
import uuid
from dataclasses import asdict
from pathlib import Path
from .compiler import Compiler,IMPORT,ROOT
from .evidence import Journal,DynamicDAG,digest
from .model import Problem
from .retrieval import load_rules,rank_rules
from .planner import Planner


def discover(data,budget=12,timeout=45,run_root=None):
    if not 1<=budget<=40 or not 1<=timeout<=120: raise ValueError('预算超出范围')
    problem=Problem.parse(data)
    folder=Path(run_root or ROOT/'phase2/runs')/uuid.uuid4().hex
    journal=Journal(folder); journal.save('problem.json',data)
    compiler=Compiler(journal,timeout); journal.save('environment.json',compiler.metadata())
    engine_hashes={str(p.relative_to(ROOT/'phase2')):digest(p.read_text(encoding='utf-8')) for p in (ROOT/'phase2').glob('*.py')}
    journal.save('engine-hashes.json',engine_hashes)
    journal.event('run_started',mode='blind_generic_search',ai='no AI call',budget=budget,source_alignment='unconfirmed',supported_fragment='Nat relational Horn + conjunction')
    graph=DynamicDAG(journal); facts={}; declarations=[]; names=[]; history=[]
    for i,a in enumerate(problem.assumptions):
        key=f'h{i}'; graph.add(key,a.text(),origin='Input Assumption',status='assumed'); facts.setdefault(a,key)
    journal.event('goals_opened',goals=[a.text() for a in problem.goals],origin='Rule Engine: generic conjunction decomposition')
    try:
        rules=rank_rules(load_rules(compiler),problem.goals)
    except RuntimeError as exc:
        result=dict(status='unknown',reason=str(exc),formal_goal_verified=False,source_alignment='unconfirmed',run=str(folder))
        journal.save('result.json',result); return result
    journal.save('retrieval.json',rules)
    planner=Planner(rules,problem)
    def reference(node):
        return node if node.startswith('h') else f'({node} {problem.arguments()})'
    def check(name,statement,proof):
        declaration=f'theorem {name} {problem.context()} : {statement} := by\n  exact {proof}\n'
        source=IMPORT+'\n'.join(declarations+[declaration])+'\n'+'\n'.join('#print axioms '+n for n in names+[name])+'\n'
        result=compiler.check(source,names+[name],statement); history.append(result)
        if result['accepted']:
            declarations.append(declaration); names.append(name)
        return result
    status='unknown'; reason='budget_exhausted'; failed=0; repairs=0; following_failure=False
    start=time.perf_counter()
    while compiler.counter<budget:
        unresolved=[g for g in problem.goals if g not in facts]
        if not unresolved:
            parents=[facts[g] for g in problem.goals]
            statement=' ∧ '.join(problem.lean(g) for g in problem.goals)
            proof=reference(parents[-1])
            for parent in reversed(parents[:-1]): proof=f'And.intro {reference(parent)} ({proof})'
            graph.add('p2_target',statement,parents,origin='Lemma Composition',rule='generic conjunction/goal closure')
            result=check('p2_target',statement,proof)
            graph.update('p2_target','verified' if result['accepted'] else 'failed',compile_log=result['log'])
            status='proved' if result['accepted'] else 'unknown'; reason='lean_accepted' if result['accepted'] else 'final_compilation_failed'; break
        candidates=planner.candidates(facts,unresolved)
        journal.event('planning_round',unresolved=[g.text() for g in unresolved],matched=len(candidates),matching_work=planner.last_scan,match_budget=planner.match_budget,plan=planner.last_plan)
        if not candidates:
            reason='matching_budget_exhausted' if planner.last_scan>=planner.match_budget else ('goal_not_derivable_in_fragment_closure' if planner.last_plan.get('fixpoint') and planner.last_plan.get('unreachable') else 'no_new_fact_in_current_fragment'); break
        candidate=candidates[0]; rule=candidate['rule']; key=f'p2_n{compiler.counter+1:03d}'
        if following_failure: repairs+=1
        graph.add(key,candidate['conclusion'].text(),candidate['parents'],origin='Rule Engine + '+rule['origin'],rule=rule['name'],
                  binding=candidate['binding'],retrieval_source={k:rule[k] for k in ('path','line','type')})
        arguments=[]
        for binder in rule['binders']:
            if 'type' in binder: arguments.append('Nat')
            elif 'instance' in binder: arguments.append('_')
            elif 'var' in binder: arguments.append(problem.term_lean(candidate['binding'][binder['var']]))
            else: arguments.append(reference(candidate['parents'][binder['premise']]))
        proof='@'+rule['name']+' '+ ' '.join(arguments)
        result=check(key,problem.lean(candidate['conclusion']),proof)
        graph.update(key,'verified' if result['accepted'] else 'failed',compile_log=result['log'])
        if result['accepted']:
            following_failure=False
            facts[candidate['conclusion']]=key
            journal.event('goal_progress',solved=[g.text() for g in problem.goals if g in facts])
        else:
            failed+=1; following_failure=True; category=planner.feedback(candidate,result)
            journal.event('error_feedback',node=key,category=category,action='exclude_failed_instantiation_then_search_alternative',compile_log=result['log'])
    snapshot=graph.snapshot(); journal.save('dag.json',snapshot)
    used=set()
    def visit(key):
        if key in used:return
        used.add(key)
        for e in graph.edges:
            if e['target']==key:visit(e['source'])
    if status=='proved':visit('p2_target')
    reused={n.get('rule') for n in graph.nodes.values() if n['id'] in used and n['id'].startswith('p2_n')}
    mathlib_names={r['name'] for r in rules if r['module'].startswith('Mathlib.')}
    result=dict(status=status,reason=reason,formal_goal_verified=status=='proved',source_alignment='unconfirmed',candidate_verified=False,
        approval_status='pending',run=str(folder),ai='no AI call',ai_calls=0,ai_tokens=None,ai_cost=0,human_interventions=0,
        metrics=dict(compile_attempts=compiler.counter,failed_compilations=sum(not r['accepted'] for r in history),repair_attempts=repairs,
            first_compile_solved_target=bool(history and history[0]['accepted'] and history[0]['goal']==' ∧ '.join(problem.lean(g) for g in problem.goals)),
            reused_declarations=len(reused),reused_mathlib_theorems=len(reused & mathlib_names),
            reused_lean_core_theorems=len(reused-mathlib_names),generated_lemmas=len([n for n in used if n.startswith('p2_n')]),
            intermediate_lemmas=len([n for n in used if n.startswith('p2_n') and graph.nodes[n]['statement'] not in {g.text() for g in problem.goals}]),
            dag_depth=snapshot['depths'].get('p2_target',0),exploration_depth=snapshot['depth'],elapsed=time.perf_counter()-start),
        successful_proof_nodes=sorted(used),generation_origin='Rule Engine, runtime search over real library types; no target-specific proof template')
    journal.event('run_finished',**result); journal.save('result.json',result)
    return result
