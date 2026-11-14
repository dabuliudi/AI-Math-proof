"""落实本次已完成的人工式语义核读；只适用于绑定论文及未改写的Lemma1。"""
import hashlib
import json
import sqlite3
from pathlib import Path
from datetime import datetime,timezone
from mathlib2.formalization import ROOT,templates
from mathlib2.workbench import state,_save,compile_for
from mathlib2.alignment import digest,valid_record
from mathlib2.store import Store

store=Store(str(ROOT/'data/mathlib2.sqlite'))
try:
    backup=ROOT/'data/before-lemma1-alignment.sqlite'
    if not backup.exists():
        dst=sqlite3.connect(backup)
        store.db.backup(dst); dst.close()
    p=ROOT/'2408.15180v2.pdf'
    assert hashlib.sha256(p.read_bytes()).hexdigest()=='40bea6e9f3a5ec4f7b3c89730c3c1934d84279ad31f95d834171f0ee58e29574'
    rows=[r for r in store.rows('candidates') if r['payload'].get('parser_version')=='0.3.0' and
          r['payload'].get('original_statement')=='Lemma 1.For a nonzero polynomiala∈k[t],a/rad(a)dividesa ′.']
    assert len(rows)==1,'须唯一匹配已核对论文原文，不能按编号猜测'
    row=rows[0]; cid=row['id']; c=row['payload']; s=state(store,cid)
    assert s['normalized_statement']==c['normalized_statement'],'规范化表述已修改，必须重新核读'
    doc=store.document(row['source_id'])
    assert doc['sha256']==hashlib.sha256(p.read_bytes()).hexdigest()
    assert dict(doc['pages'])[4][946:1004]==c['original_statement']
    paths=['2408.15180v2.pdf','lean/lake-manifest.json','lean/lean-toolchain']+[
        'lean/.lake/packages/mathlib/Mathlib/'+f for f in ['RingTheory/Polynomial/Radical.lean',
        'RingTheory/Radical.lean','Algebra/Polynomial/FieldDivision.lean','Algebra/Polynomial/Derivative.lean',
        'Algebra/Divisibility/Basic.lean']]
    report_path='reports/lemma1-alignment.md'
    certificate=dict(conclusion='confirmed',candidate_id=cid,source_id=row['source_id'],template_id='mason_lemma1',
        reviewer='assistant_independent_semantic_review',human_reviewed=False,created=datetime.now(timezone.utc).isoformat(),
        revision=s['revision'],original_sha256=digest(c['original_statement']),normalized_sha256=digest(s['normalized_statement']),
        lean_source_sha256=digest(templates()['mason_lemma1']['source']),report_path=report_path,
        report_sha256=hashlib.sha256((ROOT/report_path).read_bytes()).hexdigest(),
        files=[{'path':f,'sha256':hashlib.sha256((ROOT/f).read_bytes()).hexdigest()} for f in paths],
        comparison='faithful_nonzero_restriction_of_stronger_mathlib_theorem',proof_origin='Theorem Reuse')
    assert valid_record(certificate,{**c,'candidate_id':cid},s,'mason_lemma1')
    s.update(alignment_record=certificate,candidate_alignment='confirmed',candidate_verified=False,verification_status='unknown')
    _save(store,cid,s,'independent_semantic_alignment',certificate)
    result=compile_for(store,cid,'mason_lemma1')
    output=dict(alignment=certificate,compile=result,
        final_state={k:state(store,cid)[k] for k in ['candidate_alignment','candidate_verified','verification_status','approval_status','semantic_review_status']})
    (ROOT/'reports/lemma1-alignment-result.json').write_text(json.dumps(output,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps({'candidate_id':cid,**output['final_state'],'axioms':result['axioms'],
                      'returncode':result['returncode'],'log':result['log_artifact']},ensure_ascii=False))
    assert result['accepted'] and result['candidate_verified'],result['reason']
finally: store.db.close()
