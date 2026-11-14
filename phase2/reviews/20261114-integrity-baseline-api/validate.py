"""核对报告与既有证据；不导入产品代码，不编译Lean，不访问网络或写数据库。"""
import hashlib
import json
import re
from pathlib import Path

OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[2]
def load(path): return json.loads(path.read_text(encoding='utf-8'))
def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()
passed=[]
def check(name, condition):
    if not condition: raise AssertionError(name)
    passed.append(name)

before=load(OUT/'protected-before.json')
check('988个既有文件逐字节保持',len(before)==988 and all((ROOT/p).exists() and digest(ROOT/p)==h for p,h in before.items()))
live=load(OUT/'database-current-rows.json')
check('主库未在调查后变化',digest(Path(live['path']))==live['sha256'])
inventory=load(OUT/'database-inventory.json')
check('14个数据库完整性检查',len(inventory)==14 and all(r['integrity']==['ok'] and not r['foreign_key_check'] for r in inventory))
index=load(OUT/'database-diff-index.json')
check('8个备份逐记录数量与主键一致',len(index)==8 and all(
    v['after_count']==v['before_count']+len(v['added'])-len(v['deleted']) and
    len({json.dumps(x['key'],sort_keys=True) for k in ('added','modified','deleted') for x in v[k]})==sum(len(v[k]) for k in ('added','modified','deleted'))
    for r in index for v in load(OUT/r['report'])['tables'].values()))
near=next(r for r in index if r['baseline'].startswith('audits/'))
diff=load(OUT/near['report'])['tables']
check('近期仅4修改4新增0删除',sum(len(v['modified']) for v in diff.values())==4 and sum(len(v['added']) for v in diff.values())==4 and not any(v['deleted'] for v in diff.values()))
check('修改字段及候选精确对应', {x['key']['candidate_id'] for x in diff['workbench_state']['modified']}=={73,74,75,76} and all(
    {f['path'] for f in x['fields']}=={'/payload/candidate_alignment','/payload/candidate_verified'} and
    all(not f['before_present'] and f['after_present'] for f in x['fields'])
    for x in diff['workbench_state']['modified']))
history=load(OUT/'history-and-timeline.json')
check('Lemma1至3全部关联历史一致',all(v['unchanged'] for v in history['lemma123'].values()))
check('当前与上次验收副本逻辑一致',history['live_matches_post_acceptance_copy'])
check('无孤立来源或候选引用',not any(load(OUT/'origin-evidence.json')['orphan_reference_checks'].values()))
manifest=load(OUT/'baseline/manifest.json');batch=Path(manifest['original_batch'])
frozen=load(OUT/'baseline/frozen-seven.json')
check('精确冻结七题及顺序',len(frozen['cases'])==7 and frozen['cases']==load(batch/'inputs.json')['cases'] and digest(OUT/'baseline/frozen-seven.json')==manifest['frozen_inputs_sha256'])
check('引擎与旧批次证据哈希一致',all(digest(ROOT/'phase2'/n)==h for n,h in manifest['original_engine_hashes'].items()) and all(digest(ROOT/n)==h for n,h in manifest['historical_artifact_hashes'].items()))
check('库提取器、缓存、来源版本未变',digest(ROOT/'phase2/Extract.lean')==manifest['extractor_sha256'] and digest(ROOT/'phase2/library.json')==manifest['library_sha256'] and all(digest(Path(n))==h for n,h in manifest['library_source_hashes'].items()))
cases=load(OUT/'baseline/case-evidence.json')
check('基准聚合6成功1未知39编译33轮',sum(c['status']=='proved' for c in cases)==6 and sum(c['status']=='unknown' for c in cases)==1 and sum(len(c['compile_logs']) for c in cases)==39 and sum(c['search_rounds'] for c in cases)==33)
for c in cases:
    folder=Path(c['run']);previous='';planned={};verified=set()
    events=[json.loads(s) for s in (folder/'events.jsonl').read_text(encoding='utf-8').splitlines()]
    for e in events:
        actual=e.pop('hash')
        assert e['previous_hash']==previous
        assert actual==hashlib.sha256(json.dumps(e,ensure_ascii=False,sort_keys=True).encode()).hexdigest()
        previous=actual;p=e['payload']
        if e['kind']=='dag_node_planned':
            n=p['node'];assert all(parent in verified for parent in p['parents']);planned[n['id']]=e['sequence']
            if n['status']=='assumed':verified.add(n['id'])
        if e['kind']=='compile_started': assert planned[p['declarations'][-1]]<e['sequence']
        if e['kind']=='dag_node_updated' and p['status']=='verified':verified.add(p['node'])
    nodes={n['id']:i for i,n in enumerate(c['dag']['nodes'])}
    assert all(nodes[e['source']]<nodes[e['target']] for e in c['dag']['edges'])
    assert len(c['intermediates'])==c['metrics']['intermediate_lemmas']
    for log in c['compile_logs']:
        actual=load(folder/log['log'])
        assert actual['returncode']==0 and actual['accepted']
        assert hashlib.sha256(actual['source'].encode()).hexdigest()==actual['source_sha256']
        assert Path(actual['artifact']).read_text(encoding='utf-8')==actual['source']
        assert all(a['accepted'] and set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in actual['audits'].values())
check('七题事件哈希、先规划后编译、无环DAG与中间引理一致',True)
check('39份历史编译源码、返回码和记录公理一致（未重新编译）',True)
bad=[]
for doc in OUT.glob('*.md'):
    for target in re.findall(r'\]\(([^)]+)\)',doc.read_text(encoding='utf-8')):
        if target.startswith(('http','#')):continue
        target=re.sub(r':\d+$','',target)
        path=Path(target) if Path(target).is_absolute() else doc.parent/target
        if not path.exists():bad.append(str(path))
check('报告文件链接有效',not bad)
result=dict(passed=len(passed),checks=passed,failed=0,lean_recompiled=False,api_calls=0,
            note='本轮仅检查既有证据，不将历史成功冒充新运行，不验证尚未实施的AI能力。')
(OUT/'validation.json').write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf-8')
print(json.dumps(result,ensure_ascii=False,indent=2))
