import hashlib
from pathlib import Path
from .ingest import ingest
from .structures import VERSION
from .candidate import from_object, view
from .planner import document_graph
from .quality import assess_document


def process_document(store, path):
    digest = hashlib.sha256(Path(path).read_bytes()).hexdigest()
    existing = store.source_by_hash(digest)
    if existing:
        cached = store.document(existing['id'], VERSION)
        if cached:
            return existing['id'], cached, True
    source = assess_document(ingest(path))
    sid = existing['id'] if existing else store.add('sources', source)
    source['source_id'] = sid
    for obj in source['objects']:
        key = f"{sid}:{VERSION}:{obj['page']}:{obj['start']}:{obj['end']}:{obj['object_type']}"
        obj.update(source_id=sid, object_key=key)
    store.save_document(sid, source)
    return sid, source, False


def save_candidates(store, sid, source):
    for obj in source['objects']:
        if not obj.get('candidate_eligible', False):
            continue
        store.add('candidates', from_object(obj, sid), sid, dedup_key=obj['object_key'])
    candidates = [view(r) for r in store.rows('candidates') if r['source_id'] == sid and r['payload'].get('parser_version') == VERSION and r['payload'].get('kind') == 'document']
    graph = document_graph(candidates, source['pages'])
    for c in candidates:
        c['dependencies'] = [e for e in graph['edges'] if e['to'] == c['candidate_id']]
        # 仅更新规划字段，不把派生 view 写回覆盖人工编辑或实际验证状态。
        payload = next(r['payload'] for r in store.rows('candidates') if r['id']==c['candidate_id'])
        payload.update(dependencies=c['dependencies'], planning_status=graph['status'])
        store.db.execute('UPDATE candidates SET payload=? WHERE id=?', (__import__('json').dumps(payload, ensure_ascii=False),c['candidate_id']))
        c['planning_status']=graph['status']
    store.db.commit()
    source['stages']['candidates'] = 'extracted' if candidates else 'none'
    store.save_document(sid, source)
    return candidates, graph
