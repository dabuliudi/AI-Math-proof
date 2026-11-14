"""重放本次会话编写的Lemma3方案，记录来源/成本；不声称自动发现证明。"""
import hashlib
import json
import re
import sqlite3
from pathlib import Path
from datetime import datetime,timezone
from pypdf import PdfReader
from mathlib2.formalization import ROOT,SOURCE as L1,templates
from mathlib2.lemma3 import REFS
from mathlib2.store import Store
from mathlib2.workbench import state,_save,compile_for
from mathlib2.alignment import digest,valid_record
from mathlib2.planner import validate_graph

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(name,obj): (ROOT/'reports'/name).write_text(json.dumps(obj,ensure_ascii=False,indent=2),encoding='utf-8')
def depth(g,local=False):
    ids={n['id'] for n in g['nodes'] if not local or n.get('object_type')=='Lemma'}
    ns=[n for n in g['nodes'] if n['id'] in ids]; es=[e for e in g['edges'] if e['from'] in ids and e['to'] in ids]
    values={}
    for n in validate_graph(ns,es): values[n['id']]=max([values[e['from']]+1 for e in es if e['to']==n['id']]+[0])
    return max(values.values(),default=0)
def loc(source): return sum(bool(l.strip()) and not l.strip().startswith(('import ','open ','#','--')) for l in source.splitlines())

store=Store(str(ROOT/'data/mathlib2.sqlite'))
try:
    backup=ROOT/'data/before-lemma3.sqlite'
    if not backup.exists():
        db=sqlite3.connect(backup); store.db.backup(db); db.close()
    tables=('sources','candidates','events','verified','proof_runs','workbench_history')
    old={t:{tuple(r) for r in store.db.execute('SELECT * FROM '+t)} for t in tables}
    old_states={i:store.db.execute('SELECT payload FROM workbench_state WHERE candidate_id=?',(i,)).fetchone()[0] for i in (85,87)}
    files=list((ROOT/'reports').glob('lemma1*'))+list((ROOT/'reports').glob('lemma2*'))+[ROOT/'lean/Research/Lemma1.lean',ROOT/'lean/Research/Lemma2.lean']
    old_files={str(p):sha(p) for p in files if p.is_file()}
    pdf=ROOT/'2408.15180v2.pdf'
    assert sha(pdf)=='40bea6e9f3a5ec4f7b3c89730c3c1934d84279ad31f95d834171f0ee58e29574'
    pages={i+1:p.extract_text() for i,p in enumerate(PdfReader(pdf).pages)}
    text=pages[7]; start=text.index('Lemma 3.'); boundary=text.index('A formal proof',start); end=text.index('5 e.g.',boundary)
    dump('lemma3-source.json',{'pdf_sha256':sha(pdf),'statement':{'page':7,'start':start,'end':boundary,'text':text[start:boundary]},
        'proof_source':{'page':7,'start':boundary,'end':end,'text':text[boundary:end]},'definitions_context':{i:pages[i] for i in (2,6)}})
    rows=[r for r in store.rows('candidates') if r['payload'].get('parser_version')=='0.3.0' and r['payload'].get('title','').startswith('Lemma 3.')]
    assert len(rows)==1
    row=rows[0]; cid=row['id']; c=row['payload']; s=state(store,cid); where=c['location']
    assert pages[where['page']][where['start']:where['end']]==c['original_statement']
    assert s['normalized_statement']==c['normalized_statement']
    template=templates()['mason_lemma3']; source=template['source']; lines=source.splitlines()
    (ROOT/'lean/Research/Lemma3.lean').write_text(source,encoding='utf-8')
    specs=REFS+[
        ('degree_radical_le','RingTheory/Polynomial/Radical.lean',22),('natDegree_radical_le','RingTheory/Polynomial/Radical.lean',25),
        ('UniqueFactorizationMonoid.dvd_radical_iff_of_irreducible','RingTheory/Radical.lean',223),
        ('UniqueFactorizationMonoid.primeFactors','RingTheory/Radical.lean',67),
        ('UniqueFactorizationMonoid.radical','RingTheory/Radical.lean',155),
        ('UniqueFactorizationMonoid.primeFactors_val_eq_normalizedFactors','RingTheory/Radical.lean',121),
        ('Polynomial.natDegree_multiset_prod','Algebra/Polynomial/BigOperators.lean',319)]
    references=[]
    for n,p,l in specs:
        path=ROOT/'lean/.lake/packages/mathlib/Mathlib'/p; raw=path.read_text(encoding='utf-8').splitlines()
        assert n.split('.')[-1] in raw[l-1],(n,l)
        references.append(dict(name=n,path=str(path.relative_to(ROOT)),line=l,sha256=sha(path),
            declaration='\n'.join(raw[l-1:l+2]),used=(n,p,l) in REFS,
            origin='Mathlib 定理复用' if (n,p,l) in REFS else '检索参考（未直接用于证明）'))
    dump('lemma3-retrieval.json',{'results':references,'exact_paper_names_not_found':['natDegree_radical_eq_zero_iff','radical_isUnit_iff','prime_dvd_radical_iff'],
        'note':'degree_radical_le及natDegree_radical_le给上界，不足以单独推出本题下界；因子相关声明作为备选。'})
    retrieval_md=['# Lemma 3 Mathlib 检索报告','','本地固定版本源码；used 表示是否在新证明中显式调用。因子分解路线作为备选，最终采用单位性质路线。','']
    for ref in references:
        retrieval_md += [f"## {ref['name']}", '', f"来源：{ref['path']}:{ref['line']}；{ref['origin']}。", '', '```lean', ref['declaration'], '```', '']
    (ROOT/'reports/lemma3-retrieval.md').write_text('\n'.join(retrieval_md),encoding='utf-8')
    report='reports/lemma3-alignment.md'
    paths={r['path'] for r in references}|{'2408.15180v2.pdf','lean/lake-manifest.json','lean/lean-toolchain'}
    certificate=dict(conclusion='confirmed',candidate_id=cid,source_id=row['source_id'],template_id='mason_lemma3',
        reviewer='assistant_independent_semantic_review',human_reviewed=False,created=datetime.now(timezone.utc).isoformat(),
        revision=s['revision'],original_sha256=digest(c['original_statement']),normalized_sha256=digest(s['normalized_statement']),
        lean_source_sha256=digest(source),report_path=report,report_sha256=sha(ROOT/report),
        files=[{'path':p,'sha256':sha(ROOT/p)} for p in sorted(paths)],proof_origin=template['provenance'])
    assert valid_record(certificate,{**c,'candidate_id':cid},s,'mason_lemma3')
    s.update(alignment_record=certificate,candidate_alignment='confirmed',candidate_verified=False,verification_status='unknown')
    _save(store,cid,s,'independent_semantic_alignment',certificate)
    result=compile_for(store,cid,'mason_lemma3')
    names=template['audit_names']; starts=[next(i for i,l in enumerate(lines) if l.startswith('theorem '+n+' ')) for n in names]
    nodes=[dict(id=n,title=n,object_type='Lemma',generation_origin='AI 生成（本次助手编写，非项目API调用）',
        location={'path':'lean/Research/Lemma3.lean','line':i+1}) for n,i in zip(names,starts)]
    nodes += [dict(id=r['name'],title=r['name'],object_type='Mathlib Reference',generation_origin=r['origin'],
        location={'path':r['path'],'line':r['line']}) for r in references if r['used']]
    edges=[]; steps=[]
    reasons=[
        'a非零时degree等于natDegree；次数零的域上多项式为单位。',
        'rad(a)为单位时rad(rad(a))=1；幂等性给rad(a)=1；排除a=0后a为单位。',
        '假设rad(a)的natDegree为零，经前两个引理推出a为单位，与natDegree(a)≥1矛盾。',
        '自然数不为零等价于至少为1。',
        'degree正与natDegree正互转；radical非零允许将所得下界还原为degree下界。']
    for j,(name,a) in enumerate(zip(names,starts)):
        b=starts[j+1] if j+1<len(starts) else next(i for i,l in enumerate(lines) if l.startswith('#'))
        block='\n'.join(lines[a:b])
        for node in nodes:
            dep=node['id']; token=dep if node['object_type']=='Lemma' else dep.split('.')[-1]
            if dep==name: continue
            occurrences=[i for i in range(a,b) if re.search(r'\b'+re.escape(token)+r'\b',lines[i])]
            if occurrences:
                i=occurrences[0]
                edges.append({'from':dep,'to':name,'basis':'explicit','source':'实际编译脚本显式引用',
                    'origin':'已有 Lemma 组合' if node['object_type']=='Lemma' else 'Mathlib 定理复用',
                    'evidence':{'path':'lean/Research/Lemma3.lean','line':i+1,'quote':lines[i],
                                'dependency_declaration':node['location'],'mathematical_reason':reasons[j],
                                'paper_context':{'page':7,'start':start,'end':end}},
                    'confidence':1.0,'human_confirmed':False,'used_in_lean':result['accepted']})
        steps.append({'name':name,'source':block,'location':{'path':'lean/Research/Lemma3.lean','start_line':a+1,'end_line':b},
            'generation_origin':'AI 生成（当前对话助手新编写）','planning_origin':'助手在本轮分解，非项目内置规划器自动发现',
            'tactic_origin':'预置规则：rw/simp/decide及Lean Nat/逻辑基础API','external_ai_api_calls':0,
            'human_authored_this_run':False,'audit':result.get('declaration_audits',{}).get(name)})
    graph={'nodes':nodes,'edges':edges,'status':'acyclic','unresolved':[],
        'scope':'显式数学主干依赖，排除Lean基础逻辑/NatAPI及隐式实例；未连接Lemma1/2'}
    graph['topological_order']=[n['id'] for n in validate_graph(nodes,edges)]
    graph.update(proof_depth=depth(graph),local_proof_depth=depth(graph,True))
    dump('lemma3-dag.json',graph); dump('lemma3-steps.json',steps)
    alias={n['id']:'n'+str(i) for i,n in enumerate(nodes)}
    md=['# Lemma 3 多层Proof DAG','','来源及逐边原文证据见lemma3-dag.json；不是所有内核传递依赖。','','```mermaid','flowchart LR']
    md += [f'{alias[n["id"]]}["{n["id"]}"]' for n in nodes]
    md += [f'{alias[e["from"]]} --> {alias[e["to"]]}' for e in edges]+['```']
    (ROOT/'reports/lemma3-dag.md').write_text('\n'.join(md),encoding='utf-8')
    l1=json.loads((ROOT/'reports/lemma1-alignment-result.json').read_text(encoding='utf-8'))['compile']
    l2=json.loads((ROOT/'reports/lemma2-result.json').read_text(encoding='utf-8'))
    costs=[]
    for label,code,new,refs,mid,g,record in [
        ('Lemma1',L1,L1,1,0,{'nodes':[{'id':'lib'},{'id':'goal','object_type':'Lemma'}],'edges':[{'from':'lib','to':'goal','basis':'explicit'}]},l1),
        ('Lemma2',l2['compile']['source'],l2['compile']['source'][len(L1):],4,2,l2['dag'],l2['compile']),
        ('Lemma3',source,source,9,4,graph,result)]:
        costs.append(dict(experiment=label,physical_lines=len(code.splitlines()),new_lean_lines=loc(new),
            reused_mathlib_theorems=refs,new_intermediate_lemmas=mid,proof_depth=depth(g),local_proof_depth=depth(g,True),
            compile_elapsed_seconds=record['elapsed'],compile_log=record['log_artifact'],
            compile_source_sha256=record['sha256'],generation_time='unknown',tokens='unknown',external_ai_api_calls=0))
    dump('lemma3-costs.json',{'metrics':costs,'definitions':{'new_lean_lines':'非空且非import/open/#print行；Lemma2剔除Lemma1前缀',
        'reused_mathlib_theorems':'显式命名数学主干声明，不含定义、隐式实例与基础Nat/逻辑API',
        'proof_depth':'已列出的数学主干DAG最长路径边数，不含Mathlib内部证明',
        'elapsed':'指定真实编译日志，不是总探索耗时或可直接比拟的性能基准'}})
    md=['# Lemma 1–3 实际成本对比','','口径与限制见lemma3-costs.json及语义报告。','','|实验|新增Lean行|复用Mathlib定理|新增中间引理|总/局部深度|编译秒|','|---|---:|---:|---:|---|---:|']
    for cst in costs: md.append(f"|{cst['experiment']}|{cst['new_lean_lines']}|{cst['reused_mathlib_theorems']}|{cst['new_intermediate_lemmas']}|{cst['proof_depth']}/{cst['local_proof_depth']}|{cst['compile_elapsed_seconds']:.3f}|")
    (ROOT/'reports/lemma3-costs.md').write_text('\n'.join(md),encoding='utf-8')
    preserved={t:old[t].issubset({tuple(r) for r in store.db.execute('SELECT * FROM '+t)}) for t in tables}
    preserved['lemma1_2_states']=all(old_states[i]==store.db.execute('SELECT payload FROM workbench_state WHERE candidate_id=?',(i,)).fetchone()[0] for i in old_states)
    preserved['lemma1_2_files']=all(sha(Path(p))==h for p,h in old_files.items()); assert all(preserved.values())
    final={k:state(store,cid)[k] for k in ['candidate_alignment','candidate_verified','verification_status','approval_status']}
    attempts=[]
    for path in sorted((ROOT/'reports').glob('lemma3-*.json')):
        log=json.loads(path.read_text(encoding='utf-8'))
        if isinstance(log,dict) and log.get('template_id')=='mason_lemma3' and 'attempt_id' in log:
            attempts.append({k:log.get(k) for k in ('attempt_id','status','reason','log_artifact','elapsed','sha256')})
    dump('lemma3-result.json',dict(candidate_id=cid,alignment=certificate,compile=result,dag=graph,steps=steps,
        costs=costs,final_state=final,history_preserved=preserved,external_ai_api_calls=0,compile_history=attempts))
    print(json.dumps(dict(candidate_id=cid,**final,depth=graph['proof_depth'],preserved=preserved),ensure_ascii=False))
    assert result['accepted'] and result['candidate_verified'],result['reason']
finally: store.db.close()
