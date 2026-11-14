from concurrent.futures import ThreadPoolExecutor
from .documents import process_document, save_candidates
from .lean import LeanWorker
from .planner import topological
from .provider import provider
from .retrieval import search


def run(store, path, limit=4, worker=None):
    if not 1 <= limit <= 8:
        raise ValueError('候选预算必须为 1–8')
    sid, source, reused = process_document(store, path)
    if source['stages']['text'] not in {'parsed','partial'}:
        return {'source_id': sid, 'extracted': 0, 'results': [], 'stages': source['stages'], 'error': source.get('error'), 'reused': reused}
    ai = provider()
    text = '\n'.join(p[1] for p in source['pages'])
    # 通用文献解析完全独立于 AI 提供者；只有明确教学标记进入旧版证明演示。
    document_results = []
    if 'MATHLIB2_DEMO_NAT' not in text:
        extracted, graph = save_candidates(store, sid, source)
        document_results = [{'id': c['candidate_id'], 'label': c['title'], 'status': 'unknown', 'stage': c['stage']} for c in extracted]
        if ai.name.startswith('mock'):
            return {'source_id': sid, 'extracted': len(source['objects']), 'provider': 'rules（本地规则，无 AI 调用）',
                'results': document_results,
                'stages': source['stages'], 'reused': reused, 'dag': graph, 'quality_summary':source.get('quality_summary',{})}
    try:
        candidates = ai.generate(text, limit)
        store.event(None, 'conjecture_generation', {'source_id': sid, 'provider': ai.name,
                    'budget': limit, 'count': len(candidates), 'status': 'completed'})
    except Exception as exc:
        store.event(None, 'conjecture_generation', {'source_id': sid, 'provider': ai.name,
                    'status': 'failed', 'error_type': type(exc).__name__})
        raise
    worker = worker or LeanWorker()
    retrieval = search('Nat add_zero', worker.project / '.lake/packages/mathlib/Mathlib') if candidates else []
    nodes = []
    for i, item in enumerate(candidates):
        deps = [0] if item['strategy'] == 'reuse' and i > 0 else []
        nodes.append({'id': i, 'depends_on': deps, **item})
    results, prior = list(document_results), {}
    for node in topological(nodes):
        node['source_trace'] = {'source_id': sid, 'sha256': source['sha256'],
                               'extracted_objects': source['objects'], 'alignment': '待人工审核；生成猜想可能超出原文'}
        node['retrieval'] = retrieval
        node['formalization_status'] = 'formalized'
        cid = store.add('candidates', node, sid, dedup_key=f"generated:{sid}:{node['statement']}:{node['strategy']}")
        store.event(cid, 'planning', {'node': node['id'], 'depends_on': node['depends_on'], 'method': '规则 DAG；非自动数学分解'})
        dep = prior.get(node['depends_on'][0]) if node['depends_on'] else None
        with ThreadPoolExecutor(max_workers=2) as pool:
            proof_future = pool.submit(worker.check, node['statement'], node['strategy'], dependency=dep)
            ref_future = pool.submit(worker.check, node['statement'], node['neg_strategy'], negate=True)
            proof, refutation = proof_future.result(), ref_future.result()
        store.event(cid, 'proving', {**proof, 'attempt_budget': 1})
        store.event(cid, 'counterexample_search', {**refutation, 'attempt_budget': 1,
                    'method': '尝试在 n=0 构造矛盾并证明原命题的否定；未找到不代表成立'})
        status = store.finish(cid, proof, refutation)
        if status == 'proved':
            prior[node['id']] = node
        results.append({'id': cid, 'label': node['label'], 'status': status})
    source['stages'].update(candidates='extracted' if results else 'none', lean='attempted')
    store.save_document(sid, source)
    return {'source_id': sid, 'extracted': len(source['objects']), 'provider': ai.name, 'results': results, 'stages': source['stages'], 'reused': reused}
