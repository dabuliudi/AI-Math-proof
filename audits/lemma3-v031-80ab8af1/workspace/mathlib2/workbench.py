"""研究工作流：持久化阶段独立于提取，任何前端不直接决定证明真值。"""
import hashlib
import json
import re
from datetime import datetime, timezone
from .candidate import view
from .structures import VERSION
from .planner import document_graph, validate_graph
from .retrieval import search_mathlib


def _row(store,cid):
    row=next((r for r in store.rows('candidates') if r['id']==cid),None)
    if row is None:
        raise ValueError('候选不存在；请重新选择当前文献')
    return row


def state(store,cid):
    row=_row(store,cid)
    p=row['payload']
    value=dict(extraction_status='extracted',semantic_review_status='needs_review',review_status='needs_review',
        retrieval_status='not_run',planning_status='not_run',formalization_status=p.get('formalization_status','not_formalized'),
        verification_status=row['status'],approval_status='pending',
        normalized_statement=p.get('normalized_statement',p.get('statement','')),revision=0,
        candidate_alignment='unconfirmed',candidate_verified=False)
    r=store.db.execute('SELECT payload FROM workbench_state WHERE candidate_id=?',(cid,)).fetchone()
    if r:
        value.update(json.loads(r[0]))
    if any(r['candidate_id']==cid for r in store.rows('verified')):
        value['approval_status']='approved'
    return value


def _save(store,cid,value,action,details):
    with store.db:
        store.db.execute('INSERT OR REPLACE INTO workbench_state VALUES (?,?)',(cid,json.dumps(value,ensure_ascii=False)))
        store.db.execute('INSERT INTO workbench_history(candidate_id,action,payload,created) VALUES (?,?,?,?)',
            (cid,action,json.dumps(details,ensure_ascii=False),datetime.now(timezone.utc).isoformat()))


def history(store,cid):
    return [r for r in store.rows('workbench_history') if r['candidate_id']==cid]


def candidates_for(store,sid):
    approved={r['candidate_id'] for r in store.rows('verified')}
    rows=[r for r in store.rows('candidates') if r['source_id']==sid and
          (r['payload'].get('kind')!='document' or r['payload'].get('parser_version')==VERSION)]
    result=[]
    for r in rows:
        c=view(r,approved)
        c.update(state(store,r['id']))
        if c['verification_status']=='proved':
            c['stage']='Human Approved' if c['approval_status']=='approved' else 'Lean Verified'
        result.append(c)
    return result


def summary(store):
    sources=store.rows('sources')
    candidates=[c for s in sources for c in candidates_for(store,s['id'])]
    docs=[store.document(s['id']) for s in sources]
    result=dict(source_count=len(sources),object_count=sum(len(d['objects']) for d in docs if d),
        candidate_count=len(candidates),pending_review_count=sum(c['semantic_review_status']=='needs_review' for c in candidates),
        formalized_count=sum(c['formalization_status']=='formalized' for c in candidates),
        verified_count=sum(c['verification_status']=='proved' for c in candidates),
        approved_count=len(store.rows('verified')))
    result.update({alias:result[key] for alias,key in {'sources':'source_count','objects':'object_count',
        'candidates':'candidate_count','pending_review':'pending_review_count','formalized':'formalized_count',
        'verified':'verified_count','approved':'approved_count'}.items()})
    return result


def review(store,cid,decision,reviewer,note,normalized=None):
    if decision not in {'approved','rejected','needs_review'}:
        raise ValueError('无效审核状态')
    if not reviewer.strip() or not note.strip():
        raise ValueError('请填写审核人和具体审核意见')
    s=state(store,cid)
    if s['approval_status']=='approved':
        raise ValueError('已入库版本不可覆盖；请创建新的候选版本再审核')
    before=dict(s)
    if normalized is not None and normalized != s['normalized_statement']:
        if not normalized.strip():
            raise ValueError('规范化表述不能为空')
        s.update(normalized_statement=normalized,revision=s['revision']+1,formalization_status='stale',
                 verification_status='unknown',retrieval_status='stale',planning_status='stale',
                 candidate_alignment='stale',candidate_verified=False)
        # 旧证明依旧在 proof_runs 中，但不能再批准当前编辑版本。
    s.update(semantic_review_status=decision,review_status=decision)
    _save(store,cid,s,'semantic_review',dict(before=before,after=s,reviewer=reviewer,note=note))


def search_for(store,cid,query):
    s=state(store,cid)
    try:
        results=search_mathlib(query)
    except Exception as exc:
        s['retrieval_status']='failed'
        _save(store,cid,s,'retrieval_failed',{'error':str(exc)})
        raise
    s.update(retrieval_status='completed',retrieval_results=results,retrieval_query=query)
    _save(store,cid,s,'retrieval',{'query':query,'count':len(results)})
    return results


def graph_for(store,sid):
    candidates=candidates_for(store,sid)
    doc=store.document(sid)
    graph=document_graph(candidates,doc['pages'] if doc else ())
    for edge in graph['edges']:
        edge.update(source='paper',confidence=.95 if edge['basis']=='explicit' else .45,
            human_confirmed=False,used_in_lean=False)
        edge['edge_type']='Definition Usage' if edge.get('relation')=='definition_use' else 'Explicit Theorem Dependency'
        if edge['basis']!='explicit' and edge.get('relation')!='definition_use':
            edge['edge_type']='Inferred Dependency'
    for c in candidates:
        s=state(store,c['candidate_id'])
        for r in s.get('retrieval_results',[])[:5]:
            ident='mathlib:'+r['name']
            if not any(n['id']==ident for n in graph['nodes']):
                graph['nodes'].append(dict(id=ident,title=r['name'],object_type='Mathlib Reference',location={'path':r['path'],'line':r['line']}))
            graph['edges'].append(dict(from_=ident, **{'from':ident,'to':c['candidate_id']},basis='rule_hypothesis',
                dependency_type='Inferred Dependency',edge_type='Mathlib Reuse',source='mathlib_search',
                evidence={'quote':r['declaration'],'location':{'path':r['path'],'line':r['line']}},
                confidence=.4,human_confirmed=False,used_in_lean=False))
        runs=proof_history(store,c['candidate_id'])
        for run in runs[-1:]:
            p=run['payload']
            ident='formal:'+str(run['id'])
            graph['nodes'].append(dict(id=ident,title=p.get('target','形式化实验'),object_type='Formalized Statement',
                location={'path':p.get('artifact')},verification_status='proved' if p.get('accepted') else 'unknown'))
            graph['edges'].append({'from':c['candidate_id'],'to':ident,'basis':'rule_hypothesis',
                'dependency_type':'Inferred Dependency','edge_type':'Proof Dependency','source':'formalization_mapping',
                'evidence':{'quote':'独立语义对齐已确认；真人入库审核仍待完成' if p.get('candidate_alignment')=='confirmed' else '论文至形式化的映射仍须核对','location':c['location']},
                'confidence':.5,'human_confirmed':s['semantic_review_status']=='approved','used_in_lean':False})
            for ref in p.get('reused_declarations',[]):
                rid='mathlib:'+ref['name']
                if not any(n['id']==rid for n in graph['nodes']):
                    graph['nodes'].append(dict(id=rid,title=ref['name'],object_type='Mathlib Reference',location=ref))
                graph['edges'].append({'from':rid,'to':ident,'basis':'explicit','dependency_type':'Explicit Dependency',
                    'edge_type':'Mathlib Reuse','source':'compiled_template','evidence':{'quote':p['source'],'location':ref},
                    'confidence':1.0,'human_confirmed':False,'used_in_lean':bool(p.get('accepted'))})
    try:
        graph['topological_order']=[n['id'] for n in validate_graph(graph['nodes'],graph['edges'])]
    except ValueError as exc:
        graph.update(status='invalid',error=str(exc))
    return graph


def plan_for(store,sid):
    graph=graph_for(store,sid)
    for c in candidates_for(store,sid):
        s=state(store,c['candidate_id'])
        s['planning_status']='completed' if graph['status']=='acyclic' else 'blocked'
        _save(store,c['candidate_id'],s,'planning',{'status':graph['status'],'unresolved':len(graph['unresolved'])})
    return graph


def proof_history(store,cid):
    return [r for r in store.rows('proof_runs') if r['candidate_id']==cid]


def compile_for(store,cid,template_id):
    from .formalization import templates,check_template
    from .alignment import valid_record
    p=_row(store,cid)['payload']
    s=state(store,cid)
    template=templates()[template_id]
    original=p.get('original_statement',p.get('statement',''))
    match=bool(template.get('source_match') and re.search(template['source_match'],original,re.I|re.S))
    # 内置模板可作为实验运行；只有源命题匹配且人已审核，才关联为论文候选的证明。
    result=check_template(template_id)
    result.update(revision=s['revision'],normalized_sha256=hashlib.sha256(s['normalized_statement'].encode()).hexdigest(),
                  candidate_alignment='reviewed' if match and s['semantic_review_status']=='approved' else 'unconfirmed')
    aligned=match and s['semantic_review_status']=='approved' and template.get('scope')=='target'
    # 编辑过的规范化命题需要模板适配；不能证明原模板后声称任意修改被证明。
    aligned=aligned and s['normalized_statement']==p.get('normalized_statement',p.get('statement',''))
    certificate=s.get('alignment_record')
    independently_confirmed=valid_record(certificate,{**p,'candidate_id':cid},s,template_id)
    aligned=independently_confirmed if certificate else aligned
    if certificate and not independently_confirmed:
        result['candidate_alignment']='unconfirmed'
    if independently_confirmed:
        result.update(candidate_alignment='confirmed',alignment_report=certificate['report_path'],
                      alignment_report_sha256=certificate['report_sha256'],alignment_reviewer=certificate['reviewer'])
    result['candidate_verified']=bool(result.get('accepted') and aligned)
    with store.db:
        store.db.execute('INSERT INTO proof_runs(candidate_id,payload,created) VALUES (?,?,?)',
            (cid,json.dumps(result,ensure_ascii=False),datetime.now(timezone.utc).isoformat()))
    s.update(formalization_status='formalized',verification_status='proved' if result['candidate_verified'] else 'unknown',
             last_compile_accepted=result.get('accepted',False),lean_statement=template['target'],
             candidate_alignment=result['candidate_alignment'],candidate_verified=result['candidate_verified'])
    _save(store,cid,s,'lean_compile',{'accepted':result.get('accepted',False),'candidate_verified':result['candidate_verified']})
    return result


def approve_verified(store,cid,reviewer,note):
    s=state(store,cid)
    runs=proof_history(store,cid)
    if not runs:  # 原教学模式沿用旧审核门禁。
        return store.approve(cid,reviewer,note)
    result=runs[-1]['payload']
    if not reviewer.strip() or not note.strip():
        raise ValueError('请填写审核人及原文—形式化一致性审核意见')
    if s['semantic_review_status']!='approved' or s['verification_status']!='proved' or not result.get('candidate_verified') or result['revision']!=s['revision']:
        raise ValueError('当前版本必须完成语义审核且真实Lean验证通过，不能批准历史证明或仅提取结果')
    with store.db:
        store.db.execute('INSERT INTO verified VALUES (?,?,?,?)',(cid,reviewer,note,datetime.now(timezone.utc).isoformat()))
    s['approval_status']='approved'
    _save(store,cid,s,'human_approval',{'reviewer':reviewer,'note':note,'proof_run':runs[-1]['id']})
