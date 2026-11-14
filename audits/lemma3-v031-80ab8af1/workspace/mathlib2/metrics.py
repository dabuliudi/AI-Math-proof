"""有限、固定标注集的可复算指标，不从模型输出生成答案标签。"""
from .quality import normalize


def ratio(numerator, denominator):
    return {'numerator':numerator,'denominator':denominator,
            'value':numerator/denominator if denominator else None}


def evaluate(source, candidates, graph, truth):
    if source['sha256'] != truth['paper_sha256']:
        raise ValueError('测试论文哈希与标注集不匹配')
    pages = dict(source['pages'])
    key = lambda x: (x['page'],x['start'],x['end'])
    expected = {key(o):o for o in truth['objects']}
    predictions = {key(c['location']):c for c in candidates if key(c['location']) in expected}
    positives = {k for k,v in expected.items() if v['eligible']}
    hits = set(predictions) & positives
    types_correct = sum(predictions[k]['object_type']==expected[k]['type'] for k in hits)
    caption_keys = {k for k,v in expected.items() if v['category']=='caption'}
    condition_total, missing = 0, 0
    for k in positives:
        for condition in expected[k]['conditions']:
            condition_total += 1
            c = predictions.get(k,{})
            normalized = c.get('normalized_statement',normalize(c.get('statement','')))
            missing += int(condition not in normalized)
    trace = sum(pages[c['location']['page']][c['location']['start']:c['location']['end']]==c['original_text'] for c in candidates)
    refs = {(x.get('page'),x.get('start'),x.get('end'),x['reference']) for x in graph['unresolved']}
    expected_refs = {(x['page'],x['start'],x['end'],x['reference']) for x in truth['unresolved']}
    ids = {expected[k]['id']:c['candidate_id'] for k,c in predictions.items()}
    inferred_expected = {(ids[a],ids[b]) for a,b in truth['inferred_definition_uses'] if a in ids and b in ids}
    inferred = {(e['from'],e['to']) for e in graph['edges'] if e['basis']=='rule_hypothesis'}
    explicit = [e for e in graph['edges'] if e['basis']=='explicit']
    by_id = {c['candidate_id']:c for c in candidates}
    observed_explicit = {(by_id[e['from']]['title'],by_id[e['to']]['title'],by_id[e['to']]['location']['page']) for e in explicit}
    image_expected = {(e['from'],e['to'],e['page']) for e in truth['image_only_explicit_dependencies']}
    explicit_hits = len(observed_explicit & image_expected)
    return dict(scope=truth['scope'], human_reviewed=truth['human_reviewed'],
        formal_precision=ratio(len(hits),len(predictions)), formal_recall=ratio(len(hits),len(positives)),
        object_type_accuracy=ratio(types_correct,len(hits)), caption_false_positive_rate=ratio(len(caption_keys & set(predictions)),len(caption_keys)),
        condition_omission_rate=ratio(missing,condition_total), source_traceability=ratio(trace,len(candidates)),
        unresolved_reference_precision=ratio(len(refs & expected_refs),len(refs)),
        unresolved_reference_recall=ratio(len(refs & expected_refs),len(expected_refs)),
        inferred_dependency_precision=ratio(len(inferred & inferred_expected),len(inferred)),
        inferred_dependency_recall=ratio(len(inferred & inferred_expected),len(truth['inferred_definition_uses'])),
        # 图内依赖未自动抽取，不能以 0/0 或 unresolved 命中数宣称依赖识别准确。
        explicit_dependency_precision=ratio(explicit_hits,len(explicit)),
        image_explicit_dependency_recall=ratio(explicit_hits,len(image_expected)),
        limitations=['人工独立复核尚未完成；这些是草案标注指标',
            '精确率与召回率仅针对标注范围和丰盈数研究范围；无关练习仍然可能是数学对象',
            '条件遗漏指标只比较11项文字条件在规范化字段的保留，不评价 Lean 语义一致性',
            '图内学生证明不自动入库；图内依赖召回为0，显式依赖精确率无可评估预测'])
