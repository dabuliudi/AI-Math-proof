def topological(nodes):
    by_id = {n['id']: n for n in nodes}
    if len(by_id) != len(nodes):
        raise ValueError('DAG 节点重复')
    visiting, done, order = set(), set(), []
    def visit(key):
        if key not in by_id:
            raise ValueError('DAG 依赖不存在')
        if key in visiting:
            raise ValueError('DAG 存在环')
        if key in done:
            return
        visiting.add(key)
        for dep in by_id[key]['depends_on']:
            visit(dep)
        visiting.remove(key)
        done.add(key)
        order.append(by_id[key])
    for key in by_id:
        visit(key)
    return order


def validate_graph(nodes, edges):
    ids = {n['id'] for n in nodes}
    if len(ids) != len(nodes):
        raise ValueError('DAG 节点重复')
    dependencies = {key: [] for key in ids}
    for edge in edges:
        if edge['from'] not in ids or edge['to'] not in ids:
            raise ValueError('DAG 依赖不存在')
        if edge.get('basis') not in {'explicit', 'rule_hypothesis', 'ai_hypothesis', 'human'}:
            raise ValueError('依赖边必须标明证据来源')
        dependencies[edge['to']].append(edge['from'])
    return topological([{'id': k, 'depends_on': v} for k,v in dependencies.items()])


def ancestors(graph, target, include_inferred=True):
    """反向依赖闭包；可排除推测关系，不将定义使用等同于证明依赖。"""
    if target not in {n['id'] for n in graph['nodes']}:
        raise ValueError('目标节点不存在')
    found=set()
    pending=[target]
    while pending:
        current=pending.pop()
        for e in graph['edges']:
            if e['to']==current and (include_inferred or e['basis'] in {'explicit','human'}) and e['from'] not in found:
                found.add(e['from']); pending.append(e['from'])
    return found-{target}


def document_graph(candidates, pages=()):
    import re
    nodes = [{'id': c['candidate_id'], 'title': c['title'], 'location': c['location'],
              'source_id': c['source_id'], 'object_type': c['object_type']} for c in candidates]
    labels = {}
    for c in candidates:
        m = re.match(r'(?:#+\s*)?(Theorem|Lemma|Proposition|Corollary)\s+(\d+(?:\.\d+)*)', c['title'], re.I)
        if m:
            labels.setdefault((c['source_id'], m[1].title(), m[2]), []).append(c['candidate_id'])
    edges, unresolved, associations = [], [], []
    proof_targets = {}
    for c in candidates:
        m = re.match(r'(?:#+\s*)?Proof of (Theorem|Lemma|Proposition|Corollary)\s+(\d+(?:\.\d+)*)',c['title'], re.I)
        if m:
            targets = labels.get((c['source_id'],m[1].title(),m[2]),[])
            if len(targets)==1:
                proof_targets[c['candidate_id']] = targets[0]
                associations.append({'proof':c['candidate_id'],'claim':targets[0],'relation':'proof_of','basis':'explicit','location':c['location']})
    for c in candidates:
        for m in re.finditer(r'\b(?:by|using|from|apply|applying|according to|follows from)\s+(?:the\s+)?(Lemma|Theorem|Proposition|Corollary)\s+(\d+(?:\.\d+)*)', c['statement'], re.I):
            targets = labels.get((c['source_id'], m[1].title(),m[2]), [])
            evidence = {'quote': m.group(), 'location': c['location'], 'relative_start': m.start(), 'relative_end': m.end(),
                        'page':c['location'].get('page'), 'start':c['location'].get('start',0)+m.start(), 'end':c['location'].get('start',0)+m.end()}
            if len(targets) == 1:
                edges.append({'from': targets[0], 'to': proof_targets.get(c['candidate_id'], c['candidate_id']), 'basis': 'explicit', 'dependency_type':'Explicit Dependency', 'evidence': evidence})
            else:
                unresolved.append({'node': c['candidate_id'], 'reference': m.group(), 'status': 'uncertain', 'dependency_type':'Unresolved Reference', 'evidence': evidence})
    # 定义词在命题中的使用只是候选定义依赖；与有编号的显式引用分开。
    definitions = {}
    for c in candidates:
        if c['object_type'] == 'Definition':
            m = re.search(r'\bAn? (\w+) number is\b', c['statement'], re.I)
            if m:
                definitions.setdefault((c['source_id'],m[1].lower()),[]).append(c)
    for c in candidates:
        if c['object_type'] not in {'Theorem','Lemma','Proposition','Corollary','Conjecture'}:
            continue
        for (sid,term), targets in definitions.items():
            if sid != c['source_id'] or len(targets) != 1:
                continue
            m = re.search(r'\b'+re.escape(term)+r'\b',c['statement'],re.I)
            if m:
                edges.append({'from':targets[0]['candidate_id'],'to':c['candidate_id'],
                    'basis':'rule_hypothesis','dependency_type':'Inferred Dependency','relation':'definition_use',
                    'status':'uncertain','reason':'命题使用了定义词；规则推测，尚未由作者编号引用或人工确认',
                    'evidence':{'quote':m.group(),'page':c['location'].get('page'),
                                'start':c['location'].get('start',0)+m.start(),'end':c['location'].get('start',0)+m.end()},
                    'definition_location':targets[0]['location']})
    for page, text in pages:
        for m in re.finditer(r'\b(?:Lemma|Theorem|Proposition|Corollary)\s+\d+(?:\.\d+)*', text):
            kind, number = m.group().split()
            if not any(k[1:] == (kind, number) for k in labels):
                unresolved.append({'reference':m.group(), 'status':'uncertain', 'dependency_type':'Unresolved Reference', 'page':page,
                                   'start':m.start(), 'end':m.end(), 'context':text[max(0,m.start()-150):m.end()+150],
                                   'reason':'只有正文引用，未找到唯一的声明；不建立依赖边'})
    # 循环不静默删除；返回诊断并隔离全部边，不展示伪 DAG。
    try:
        validate_graph(nodes, edges)
        return {'nodes': nodes, 'edges': edges, 'associations':associations, 'unresolved': unresolved, 'status': 'acyclic'}
    except ValueError as exc:
        return {'nodes': nodes, 'edges': [], 'rejected_edges': edges, 'unresolved': unresolved, 'status': 'invalid', 'error': str(exc)}
