"""统一候选视图：提取阶段与数学验证状态分开。"""
import re
from .structures import VERSION


def from_object(obj, sid):
    claim = obj['object_type'] in {'Definition','Theorem','Lemma','Proposition','Corollary','Conjecture'}
    stage = 'Candidate' if claim and obj['recognition_status'] == 'recognized' else 'Extracted'
    audit_fields = ('original_statement','normalized_statement','lean_statement','semantic_risk','semantic_status',
        'proposed_corrections','boundary_checks','normalization','condition_inventory','classification','filter_reason',
        'candidate_eligible','relevance_score','mathematical_completeness','extraction_confidence','source_traceability','quality_tier','quality_policy',
        'assumptions','quantifiers','domain_constraints','definitions','boundary_cases','potential_counterexamples','source_location',
        'review_status','semantic_review_status','extraction_status','normalization_changes','semantic_field_method',
        'statement_text','proof_body','code_fragments')
    return {**{k:obj[k] for k in audit_fields if k in obj}, 'parser_version':VERSION,
            'source_id': sid, 'title': obj['title'], 'statement': obj['body'],
            'object_type': obj['object_type'], 'original_text': obj['original_text'],
            'location': {k: obj[k] for k in ('page','line','paragraph','start','end')},
            'mathematical_domain': 'number_theory (keyword_hint)' if re.search(r'\bdivisor|\bperfect|\babundant|\bprime', obj['body'], re.I) else 'unknown',
            'dependencies': [], 'extraction_method': obj['extraction_method'], 'confidence': obj['confidence'],
            'formalization_status': 'not_formalized', 'verification_status': 'unknown',
            'retrieval_status':'not_run', 'planning_status':'not_run','approval_status':'pending',
            'stage': stage, 'recognition_status': obj['recognition_status'], 'reason': obj['reason'],
            'context_before': obj['context_before'], 'context_after': obj['context_after'],
            'proof_steps': obj.get('proof_steps', []), 'boundary_status': obj.get('boundary_status'),
            'object_key': obj['object_key'], 'kind': 'document', 'depends_on': []}


def view(row, approved=()):
    p = dict(row['payload'])
    verified = row['status'] == 'proved'
    p.update(candidate_id=row['id'], source_id=row['source_id'], verification_status=row['status'])
    p.setdefault('title', p.get('label', '旧版候选'))
    p.setdefault('original_text', '')
    p.setdefault('location', {})
    p.setdefault('object_type', 'Conjecture')
    p.setdefault('formalization_status', 'formalized' if p.get('strategy') else 'not_formalized')
    p.setdefault('stage', 'Formalized' if p.get('strategy') else 'Extracted')
    for key, default in [('extraction_status','legacy'),('semantic_review_status','pending'),
                         ('retrieval_status','not_run'),('planning_status','not_run'),('approval_status','pending')]:
        p.setdefault(key,default)
    if verified:
        p['stage'] = 'Lean Verified'
    if row['id'] in approved and verified:
        p['stage'] = 'Human Approved'
    return p
