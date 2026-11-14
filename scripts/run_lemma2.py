"""对已核读的Lemma2执行对齐绑定、真实编译与依赖审计；不批准入库。"""
import hashlib
import json
import sqlite3
from datetime import datetime,timezone
from pathlib import Path
from mathlib2.formalization import ROOT,SOURCE,templates
from mathlib2.store import Store
from mathlib2.workbench import state,_save,compile_for
from mathlib2.alignment import digest,valid_record
from mathlib2.planner import validate_graph

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def dump(name,value): (ROOT/'reports'/name).write_text(json.dumps(value,ensure_ascii=False,indent=2),encoding='utf-8')

store=Store(str(ROOT/'data/mathlib2.sqlite'))
try:
    backup=ROOT/'data/before-lemma2.sqlite'
    if not backup.exists():
        dst=sqlite3.connect(backup); store.db.backup(dst); dst.close()
    tables=('sources','candidates','events','verified','proof_runs','workbench_history')
    old={t:{tuple(r) for r in store.db.execute('SELECT * FROM '+t)} for t in tables}
    lemma1_state=store.db.execute('SELECT payload FROM workbench_state WHERE candidate_id=85').fetchone()[0]
    history_paths=list((ROOT/'reports').glob('lemma1*'))+[ROOT/'lean/Research/Lemma1.lean']
    history_hashes={str(p):sha(p) for p in history_paths if p.is_file()}
    original='Lemma 2.For any nonzeroa∈k[t],a/rad(a)dividesW(a, b) =ab ′ −a ′b.'
    rows=[r for r in store.rows('candidates') if r['payload'].get('original_statement')==original and r['payload'].get('parser_version')=='0.3.0']
    assert len(rows)==1
    row=rows[0]; cid=row['id']; c=row['payload']; s=state(store,cid); doc=store.document(row['source_id'])
    assert doc['sha256']=='40bea6e9f3a5ec4f7b3c89730c3c1934d84279ad31f95d834171f0ee58e29574'
    assert sha(ROOT/'2408.15180v2.pdf')==doc['sha256']
    assert dict(doc['pages'])[4][1364:1429]==original
    assert s['normalized_statement']==c['normalized_statement'],'规范化文本已修改，不能沿用本次核读'
    t=templates()['mason_lemma2']; assert t['source'].startswith(SOURCE)
    (ROOT/'lean/Research/Lemma2.lean').write_text(t['source'],encoding='utf-8')
    specs=[('divRadical_dvd_derivative','RingTheory/Polynomial/Radical.lean',31,True),
        ('divRadical_dvd_wronskian_left','RingTheory/Polynomial/Radical.lean',58,False),
        ('divRadical_dvd_wronskian_right','RingTheory/Polynomial/Radical.lean',66,False),
        ('EuclideanDomain.divRadical_dvd_self','RingTheory/Radical.lean',426,True),
        ('EuclideanDomain.divRadical','RingTheory/Radical.lean',399,True),
        ('Polynomial.wronskian','RingTheory/Polynomial/Wronskian.lean',39,True),
        ('mul_sub','Algebra/Ring/Defs.lean',322,True),('mul_assoc','Algebra/Group/Defs.lean',200,True)]
    refs=[]
    for name,relative,line,used in specs:
        path=ROOT/'lean/.lake/packages/mathlib/Mathlib'/relative
        lines=path.read_text(encoding='utf-8').splitlines()
        assert name.split('.')[-1] in lines[line-1],(name,line)
        refs.append(dict(name=name,path=str(path.relative_to(ROOT)),line=line,source_excerpt='\n'.join(lines[line-1:line+2]),
                         sha256=sha(path),used_in_proof=used,match_kind='source_checked_declaration',
                         reuse='used' if used else 'alternative_not_used'))
    dump('lemma2-retrieval.json',refs)
    report='reports/lemma2-alignment.md'
    files=set(r['path'] for r in refs)|{'2408.15180v2.pdf','lean/lake-manifest.json','lean/lean-toolchain',
        'lean/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/FieldDivision.lean',
        'lean/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Derivative.lean',
        'lean/.lake/packages/mathlib/Mathlib/Algebra/Divisibility/Basic.lean','reports/lemma1-alignment.md'}
    certificate=dict(conclusion='confirmed',candidate_id=cid,source_id=row['source_id'],template_id='mason_lemma2',
        reviewer='assistant_independent_semantic_review',human_reviewed=False,created=datetime.now(timezone.utc).isoformat(),
        revision=s['revision'],original_sha256=digest(original),normalized_sha256=digest(s['normalized_statement']),
        lean_source_sha256=digest(t['source']),report_path=report,report_sha256=sha(ROOT/report),
        files=[{'path':f,'sha256':sha(ROOT/f)} for f in sorted(files)],proof_origin=t['provenance'])
    assert valid_record(certificate,{**c,'candidate_id':cid},s,'mason_lemma2')
    s.update(alignment_record=certificate,candidate_alignment='confirmed',candidate_verified=False,verification_status='unknown')
    _save(store,cid,s,'independent_semantic_alignment',certificate)
    result=compile_for(store,cid,'mason_lemma2')
    local_names=t['audit_names']; lines=t['source'].splitlines()
    nodes=[dict(id=n,title=n,object_type='Lemma',location={'path':'lean/Research/Lemma2.lean',
        'line':next(i+1 for i,l in enumerate(lines) if l.startswith('theorem '+n+' '))}) for n in local_names]
    nodes += [dict(id=r['name'],title=r['name'],object_type='Mathlib Reference',location={'path':r['path'],'line':r['line']}) for r in refs if r['used_in_proof']]
    pairs=[('divRadical_dvd_derivative',local_names[0],7,'Proof Dependency'),
        ('EuclideanDomain.divRadical',local_names[0],7,'Definition Usage'),
        ('mul_sub',local_names[1],16,'Proof Dependency'),('mul_assoc',local_names[1],16,'Proof Dependency'),
        ('EuclideanDomain.divRadical_dvd_self',local_names[2],20,'Proof Dependency'),
        ('EuclideanDomain.divRadical',local_names[2],20,'Definition Usage'),
        (local_names[0],local_names[3],26,'Proof Dependency'),(local_names[1],local_names[3],25,'Proof Dependency'),
        (local_names[2],local_names[3],26,'Proof Dependency'),('Polynomial.wronskian',local_names[3],24,'Definition Usage')]
    edges=[{'from':a,'to':b,'basis':'explicit','source':'trusted_source_reference_and_lean_elaboration',
        'edge_type':kind,'evidence':{'path':'lean/Research/Lemma2.lean','line':line,'quote':lines[line-1]},
        'confidence':1.0,'human_confirmed':False,'used_in_lean':result['accepted'],
        'paper_context':{'page':4,'start':1364,'end':1429}} for a,b,line,kind in pairs]
    order=[n['id'] for n in validate_graph(nodes,edges)]
    graph={'nodes':nodes,'edges':edges,'status':'acyclic','topological_order':order,'unresolved':[],
           'scope':'本次脚本显式直接依赖；不是全部内核传递依赖或整篇论文引用','compile_log':result['log_artifact']}
    dump('lemma2-dag.json',graph)
    aliases={n['id']:'n'+str(i) for i,n in enumerate(nodes)}
    mermaid=['# Lemma 2 实际 Proof DAG','','仅编译成功的本次脚本直接依赖；完整证据见 lemma2-dag.json。','','```mermaid','flowchart LR']
    mermaid += [f'{aliases[n["id"]]}["{n["id"]}"]' for n in nodes]
    mermaid += [f'{aliases[e["from"]]} -->|{e["edge_type"]}| {aliases[e["to"]]}' for e in edges]
    mermaid += ['```','', '论文非零假设和定义对齐见 lemma2-alignment.md。未采用现成 divRadical_dvd_wronskian_left/right。']
    (ROOT/'reports/lemma2-dag.md').write_text('\n'.join(mermaid),encoding='utf-8')
    preserved={table:old[table].issubset({tuple(r) for r in store.db.execute('SELECT * FROM '+table)}) for table in tables}
    preserved['lemma1_state']=lemma1_state==store.db.execute('SELECT payload FROM workbench_state WHERE candidate_id=85').fetchone()[0]
    preserved['lemma1_files']=all(sha(Path(p))==h for p,h in history_hashes.items())
    assert all(preserved.values()),preserved
    final={k:state(store,cid)[k] for k in ['candidate_alignment','candidate_verified','verification_status','approval_status']}
    dump('lemma2-result.json',dict(candidate_id=cid,alignment=certificate,compile=result,dag=graph,
        retrieval=refs,final_state=final,history_preserved=preserved,ai_api_calls=0))
    print(json.dumps(dict(candidate_id=cid,**final,axioms=result['axioms'],log=result['log_artifact'],preserved=preserved),ensure_ascii=False))
    assert result['accepted'] and result['candidate_verified'],result['reason']
finally: store.db.close()
