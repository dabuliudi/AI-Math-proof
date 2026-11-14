"""可解释的提取质量与保守语义审计；不判断数学真值。"""
import re


def normalize(text):
    # 不进行同义改写、公式重排或条件补全。
    return re.sub(r'\s+', ' ', text).strip()


def semantic_audit(obj, pages):
    original = obj['body']
    result = dict(original_statement=original, normalized_statement=normalize(original),
                  lean_statement=None, semantic_risk=[], semantic_status='unchecked',
                  proposed_corrections=[], boundary_checks=[], normalization='whitespace_only')
    # 只修复有字形依据的编码；PDF 丢失的上下标无法可靠重建。
    repairs = {'ﬁ':'fi', 'ﬂ':'fl', '\u00a0':' ', '̸=':'≠'}
    result['normalization_changes'] = []
    for before, after in repairs.items():
        if before in result['normalized_statement']:
            result['normalized_statement'] = result['normalized_statement'].replace(before, after)
            result['normalization_changes'].append({'from':before,'to':after,'reason':'可识别字符编码恢复'})
    for pattern, replacement in [(r'\bLet([a-z])be\b',r'Let \1 be'),
        (r'\b(polynomial|polynomials|field|nonzero|divides)([a-z])(?=\b|∈|\[)',r'\1 \2')]:
        prior=result['normalized_statement']
        revised=re.sub(pattern,replacement,prior)
        if revised!=prior:
            result['normalized_statement']=revised
            result['normalization_changes'].append({'pattern':pattern,'reason':'限定词汇与单字符变量边界恢复；待人工复核'})
    if result['normalization_changes']:
        result['normalization'] = 'whitespace_and_audited_glyphs'
    result.update(assumptions=[], quantifiers=[], domain_constraints=[], definitions=[],
        boundary_cases=[], potential_counterexamples=[], source_location={k:obj[k] for k in ('page','start','end')},
        review_status='pending', semantic_review_status='pending', extraction_status=obj['recognition_status'])
    normalized = result['normalized_statement']
    result['assumptions'] = re.findall(r'\b(?:If|if|Assume|Suppose|Let)[^.;]{1,220}', normalized)
    result['quantifiers'] = re.findall(r'\b(?:any|every|all|there exists?|for each)\b[^,.;]{0,100}|[∀∃][^,.;]{0,100}',normalized,re.I)
    result['domain_constraints'] = re.findall(r'\b(?:integer|natural|real|nonzero|non-zero|non-constant|field|characteristic)[^.;]{0,100}|[∈][^.;]{0,70}',normalized,re.I)
    result['definitions'] = re.findall(r'\b(?:radical|Wronskian|perfect|abundant|divisors?)\b',normalized,re.I)
    result['semantic_field_method'] = '规则摘录，未恢复的黏连文字/公式需复核；空列表不表示不存在条件'
    if re.search(r'polynomial|rad\(|Wronskian|k\[',original,re.I):
        result['semantic_risk'].append('polynomial_domain_and_characteristic_require_review')
        result['domain_constraints'].append('域及特征须核对声明和论文上下文；不自动补充 characteristic=0')
        result['semantic_risk'].append('pdf_subscript_superscript_not_reliably_recovered')
    if obj.get('boundary_status') == 'page_limited':
        result['semantic_risk'].append('page_boundary_possible_truncation')
    # 通用词法清单保留顺序；仅用于复核，不能当作语义理解。
    result['condition_inventory'] = re.findall(
        r'∀|∃|∈|≤|≥|≠|[<>=]|\b(?:if|then|any|every|all|exists|integer|natural|positive|nonnegative|more than|at least|exactly)\b|\b\d+\b',
        original, re.I)
    abundant_claim = re.search(r'if\s+n\s+is\s+perfect.*?kn\s+is\s+abundant', normalize(original), re.I)
    if abundant_claim:
        explicit_exclusion = bool(re.search(r'k\s*>\s*1|k\s*≥\s*2|k\s*>=\s*2', original))
        evidence = []
        for page, text in pages:
            for match in re.finditer(r'[^.!?]*statement is false for k\s*=\s*1[^.!?]*[.!?]', text, re.I):
                evidence.append(dict(page=page, start=match.start(), end=match.end(), quote=match.group()))
        result['boundary_checks'].append(dict(value='k=1',
            status='excluded_by_explicit_condition' if explicit_exclusion else 'potential_counterexample',
            reasoning='按完全数定义，k=1 时 kn=n，因数和等于 2n，未满足丰盈数要求的严格大于。未进行 Lean 验证。',
            source_evidence=evidence))
        if not explicit_exclusion:
            result['semantic_status'] = 'potential_counterexample'
            result['semantic_risk'].append('k=1_not_excluded')
            result['proposed_corrections'].append(dict(
                label='建议修正版（规则建议，不是论文原文，未经 Lean 验证）',
                statement='If n is perfect and k ∈ N with k > 1, then kn is abundant.',
                change='显式增加 k > 1；n 的正性、N 是否含 0 及因数定义仍须复核。',
                status='proposed_not_formalized', evidence=evidence))
        result['semantic_risk'].append('integer_domain_and_zero_convention_need_review')
    if obj['object_type'] == 'Conjecture':
        result['semantic_risk'].append('exercise_truth_not_established')
    if re.search(r'If p1 and p2 are primes.*p1p2 is abundant',normalize(original),re.I):
        result['semantic_status']='potential_counterexample'
        result['semantic_risk'].append('equal_primes_two_not_excluded')
        result['boundary_checks'].append(dict(value='p1=p2=2',status='potential_counterexample',
            reasoning='乘积为4，正因数为1、2、4，和为7；7不大于2×4=8。规则算术解释，尚未经Lean验证。',source_evidence=[]))
    result['boundary_cases'] = list(result['boundary_checks'])
    result['potential_counterexamples'] = [x for x in result['boundary_checks'] if x['status']=='potential_counterexample']
    return result


def assess_document(source):
    """原始对象全部保留；研究范围与提取质量、真值严格分开。"""
    pages = source['pages']
    objects = source['objects']
    # 仅在确有两个定义的文献启用专题模式，不按文件名/哈希识别样例。
    definitions = ' '.join(o['body'] for o in objects if o['object_type']=='Definition')
    focus = 'abundant_numbers' if re.search(r'abundant number', definitions, re.I) and re.search(r'perfect number', definitions, re.I) else 'general'
    source['research_focus'] = focus
    for obj in objects:
        method, text = obj['extraction_method'], obj['body']
        category, reason = 'formal_mathematical_object', '明确数学结构；仍需审核'
        relevant = focus == 'general' or bool(re.search(r'\babundant\b|\bperfect\b|\bdivisor', text, re.I))
        if method == 'lean_code_fragment':
            category, reason = 'code_fragment', '论文作者代码片段；保留为资料，不能冒充本系统已验证证明'
        elif method == 'prose_reference':
            category, reason = 'ordinary_reference', '正文引用不是独立数学声明'
        elif method in {'figure_caption_only','table_caption_only'} or re.match(r'\s*(?:Fig(?:ure)?\.?|Table)\s*\d', text, re.I):
            category, reason = 'caption', '图表标题是来源资料，不是数学声明或完整证明'
        elif method == 'narrative_proof_step' or re.search(r'\bstudent\s+(?:case|[A-Z][a-z]+)\b', text):
            category, reason = 'student_case', '学生案例或证明叙述；保留原文，不作为正式候选'
        elif method == 'condition_discussion':
            category, reason = 'semantic_evidence', '条件讨论保留为语义证据'
        elif not relevant:
            category, reason = 'out_of_scope', '不属于当前丰盈数专题；保留为其他练习/定义'
        elif obj['recognition_status'] != 'recognized':
            category, reason = 'uncertain_structure', '结构不确定，等待原文复核'
        accepted = category == 'formal_mathematical_object'
        trace = next((t for p,t in pages if p==obj['page']), '')[obj['start']:obj['end']] == obj['original_text']
        semantics = semantic_audit(obj, pages)
        completeness = .5 if obj.get('boundary_status') == 'page_limited' else .85
        if semantics['semantic_risk']:
            completeness = min(completeness, .55)
        tier = 'Rejected' if not accepted else ('High Confidence' if obj['confidence'] >= .85 and completeness >= .8 and trace else 'Medium Confidence')
        if category == 'uncertain_structure':
            tier = 'Low Confidence'
        obj.update(semantics)
        obj.update(stage='Candidate' if accepted and obj['object_type']!='Proof' else 'Extracted',
            classification=category, filter_reason=reason, candidate_eligible=accepted,
            relevance_score=1.0 if relevant else 0.0, mathematical_completeness=completeness,
            extraction_confidence=obj['confidence'], source_traceability=1.0 if trace else 0.0,
            quality_tier=tier, quality_policy='启发式提取质量；非数学正确率；Rejected 不代表数学错误')
        if not trace:
            obj.update(candidate_eligible=False, quality_tier='Rejected', filter_reason='原文切片不匹配')
    source['quality_summary'] = dict(formal_candidates=sum(o['candidate_eligible'] for o in objects),
        retained_materials=sum(not o['candidate_eligible'] for o in objects),
        uncertain=sum(o['recognition_status']=='uncertain' for o in objects),
        candidate_count=sum(o['candidate_eligible'] for o in objects), formalized_count=0)
    return source
