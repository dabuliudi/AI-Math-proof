"""只读调查与报告数据导出。不得导入Store、应用或证明引擎。"""
import hashlib
import json
import sqlite3
from datetime import datetime, timezone, timedelta
from pathlib import Path

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[2]
BATCH = ROOT/'phase2/benchmarks/run-b63d1f87b59f467a994af289b0ab8390'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def save(name, value):
    path=OUT/name
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(value,ensure_ascii=False,indent=2),encoding='utf-8')

def files_snapshot():
    paths=[]
    for name in ('mathlib2','tests','scripts','reports','data','lean/Research','phase2','audits'):
        paths += [p for p in (ROOT/name).rglob('*') if p.is_file() and OUT not in p.parents and '__pycache__' not in p.parts]
    paths += [p for p in ROOT.iterdir() if p.is_file()]
    return {str(p.relative_to(ROOT)):sha(p) for p in sorted(set(paths))}

def read_db(path):
    before=sha(path)
    db=sqlite3.connect(path.as_uri()+'?mode=ro',uri=True,timeout=5)
    db.row_factory=sqlite3.Row
    try:
        db.execute('PRAGMA query_only=ON')
        db.execute('BEGIN')
        schemas=[dict(r) for r in db.execute('SELECT type,name,tbl_name,sql FROM sqlite_master ORDER BY type,name')]
        tables={}
        for row in schemas:
            if row['type']!='table': continue
            name=row['name']; quoted='"'+name.replace('"','""')+'"'
            columns=[dict(r) for r in db.execute('PRAGMA table_info('+quoted+')')]
            keys=[r['name'] for r in sorted(columns,key=lambda r:r['pk']) if r['pk']]
            records=[dict(r) for r in db.execute('SELECT * FROM '+quoted)]
            tables[name]=dict(columns=columns,keys=keys,records=records)
        integrity=[r[0] for r in db.execute('PRAGMA integrity_check')]
        fk=[list(r) for r in db.execute('PRAGMA foreign_key_check')]
        db.rollback()
    finally:
        db.close()
    if before!=sha(path): raise RuntimeError('调查期间数据库变化：'+str(path))
    return dict(path=str(path),sha256=before,mtime_utc=datetime.fromtimestamp(path.stat().st_mtime,timezone.utc).isoformat(),
                bytes=path.stat().st_size,schemas=schemas,tables=tables,integrity=integrity,foreign_key_check=fk)

def decode(row):
    row=dict(row)
    if isinstance(row.get('payload'),str):
        try: row['payload']=json.loads(row['payload'])
        except json.JSONDecodeError: pass
    return row

def fields(a,b,path=''):
    result=[]
    if isinstance(a,dict) and isinstance(b,dict):
        for k in sorted(a.keys()|b.keys()):
            at=path+'/'+k.replace('~','~0').replace('/','~1')
            if k not in a or k not in b:
                result.append(dict(path=at,before_present=k in a,after_present=k in b,before=a.get(k),after=b.get(k)))
            else: result+=fields(a[k],b[k],at)
    elif a!=b:
        result.append(dict(path=path,before_present=True,after_present=True,before=a,after=b))
    return result

def compare(old,new):
    result={}
    for name in sorted(old['tables'].keys()|new['tables'].keys()):
        a=old['tables'].get(name,dict(keys=[],records=[],columns=[]))
        b=new['tables'].get(name,dict(keys=[],records=[],columns=[]))
        keys=a['keys'] or b['keys']
        if not keys: raise RuntimeError('没有稳定主键：'+name)
        def index(table):return {tuple(r.get(k) for k in keys):r for r in table['records']}
        ai=index(a);bi=index(b);added=[];deleted=[];modified=[]
        for key in sorted(ai.keys()|bi.keys(),key=repr):
            k=dict(zip(keys,key))
            if key not in ai:added.append(dict(key=k,after=bi[key]))
            elif key not in bi:deleted.append(dict(key=k,before=ai[key]))
            elif ai[key]!=bi[key]:
                diff=fields(decode(ai[key]),decode(bi[key]))
                modified.append(dict(key=k,before=ai[key],after=bi[key],fields=diff,serialization_only=not diff))
        result[name]=dict(before_count=len(ai),after_count=len(bi),schema_changed=a['columns']!=b['columns'],
                          added=added,modified=modified,deleted=deleted)
    return dict(before=old['path'],after=new['path'],before_sha256=old['sha256'],after_sha256=new['sha256'],
                sqlite_schema_changed=old['schemas']!=new['schemas'],tables=result)

def main():
    before=files_snapshot();save('protected-before.json',before)
    paths=sorted((ROOT/'data').glob('*.sqlite*'))
    paths+=sorted((ROOT/'audits').glob('*/workspace/data/mathlib2.sqlite'))
    paths+=sorted((ROOT/'phase2/legacy-regression').glob('*/workspace/data/mathlib2.sqlite'))
    dbs={p.relative_to(ROOT).as_posix():read_db(p) for p in paths if p.is_file() and p.suffix not in ('.wal','.shm')}
    live=dbs['data/mathlib2.sqlite']
    inventory=[]
    for name,db in dbs.items():
        inventory.append(dict(path=name,sha256=db['sha256'],bytes=db['bytes'],mtime_utc=db['mtime_utc'],
            table_counts={t:len(v['records']) for t,v in db['tables'].items()},integrity=db['integrity'],foreign_key_check=db['foreign_key_check'],
            role='live' if name=='data/mathlib2.sqlite' else ('test_or_development_branch' if any(s in name for s in ('agent-ui','offline-check','v021-development')) else 'backup_or_audit_copy')))
    save('database-inventory.json',inventory)
    save('database-current-rows.json',live)
    summaries=[]
    for name,old in dbs.items():
        if name=='data/mathlib2.sqlite' or any(s in name for s in ('agent-ui','offline-check','v021-development')):continue
        tag=name.replace('/','__').replace('\\','__')
        report=compare(old,live);filename='database-diffs/'+tag+'.json';save(filename,report)
        summaries.append(dict(baseline=name,report=filename,hash=old['sha256'],tables={t:dict(before=v['before_count'],after=v['after_count'],added=len(v['added']),modified=len(v['modified']),deleted=len(v['deleted']),schema_changed=v['schema_changed']) for t,v in report['tables'].items()}))
    save('database-diff-index.json',summaries)
    prior=json.loads((ROOT/'phase2/legacy-before.json').read_text(encoding='utf-8'))['data\\mathlib2.sqlite']
    save('database-baseline-availability.json',dict(phase2_start_hash=prior,exact_hash_matches=[n for n,d in dbs.items() if d['sha256']==prior],
        limitation='开始时只有哈希；不能用另一时间点副本冒充精确开始快照。'))
    nearest=dbs['audits/lemma3-v031-80ab8af1/workspace/data/mathlib2.sqlite']
    post=dbs['phase2/legacy-regression/f7b2b657d5694e42bcc9375d3960dd33/workspace/data/mathlib2.sqlite']
    history={}
    for name in ('candidates','workbench_state','proof_runs','workbench_history','events','verified'):
        key='id' if name=='candidates' else 'candidate_id'
        a=[r for r in nearest['tables'][name]['records'] if r[key] in (85,87,89)]
        b=[r for r in live['tables'][name]['records'] if r[key] in (85,87,89)]
        history[name]=dict(rows=len(b),unchanged=a==b)
    changed=compare(nearest,live)
    extra=changed['tables']['workbench_history']['added']
    timeline=[]
    for x in extra:
        row=decode(x['after']);dt=datetime.fromisoformat(row['created'])
        timeline.append(dict(**row,china_time=dt.astimezone(timezone(timedelta(hours=8))).isoformat()))
    save('history-and-timeline.json',dict(lemma123=history,added_history=timeline,
        live_matches_post_acceptance_copy=all(not (v['added'] or v['modified'] or v['deleted']) for v in compare(post,live)['tables'].values()),
        affected_candidates=[decode(r) for r in live['tables']['candidates']['records'] if r['id'] in (73,74,75,76)],
        note='created为应用写入的时间字段，并非独立进程审计时间；代码路径匹配不能确认操作人。'))
    # Freeze exactly the seven executed inputs, not a freshly generated suite.
    frozen=json.loads((BATCH/'inputs.json').read_text(encoding='utf-8'))
    save('baseline/frozen-seven.json',dict(protocol='fixed-v1; no proof/strategy/DAG answers supplied',cases=frozen['cases']))
    results=json.loads((BATCH/'results.json').read_text(encoding='utf-8'));cases=[];artifact_hashes={}
    for path in BATCH.rglob('*'):
        if path.is_file():artifact_hashes[str(path.relative_to(ROOT))]=sha(path)
    for row in results:
        result=row['result'];folder=Path(result['run'])
        dag=json.loads((folder/'dag.json').read_text(encoding='utf-8'))
        events=[json.loads(s) for s in (folder/'events.jsonl').read_text(encoding='utf-8').splitlines()]
        rounds=[e['payload'] for e in events if e['kind']=='planning_round']
        item=next(c for c in frozen['cases'] if c['id']==row['id']);goaltexts=item['problem']['goals']
        adopted=set(result['successful_proof_nodes'])
        intermediate=[n for n in dag['nodes'] if n['id'] in adopted and n['id'].startswith('p2_n') and n['statement'] not in goaltexts]
        compiles=[]
        for path in sorted(folder.glob('attempt-*.json')):
            c=json.loads(path.read_text(encoding='utf-8'))
            compiles.append({k:c[k] for k in ('log','returncode','status','accepted','elapsed','goal','source_sha256','audits')})
        retrieval=[e['payload'] for e in events if e['kind']=='retrieval']
        cases.append(dict(id=row['id'],problem=item['problem'],budget=dict(proof_compiles=12,each_compile_seconds=45,matching_work_per_round=12000,retrieval_compile_seconds=180,total_wall_seconds=None),
            run=result['run'],status=result['status'],reason=result['reason'],dag=dag,intermediates=intermediate,
            search_rounds=len(rounds),matching_work=sum(r['matching_work'] for r in rounds),matched_candidates=sum(r['matched'] for r in rounds),
            historical_elapsed=result['metrics']['elapsed'],event_elapsed=events[-1]['monotonic']-events[0]['monotonic'],
            complete_process_wall_seconds=None,started=events[0]['time'],finished=events[-1]['time'],retrieval=retrieval,
            compile_logs=compiles,metrics=result['metrics'],ai_calls=result['ai_calls'],ai_cost=result['ai_cost']))
    save('baseline/case-evidence.json',cases)
    manifest=dict(original_batch=str(BATCH),seed=frozen['seed'],frozen_inputs_sha256=sha(OUT/'baseline/frozen-seven.json'),
        original_engine_hashes=frozen['engine_hashes'],current_engine_matches=all(sha(ROOT/'phase2'/n)==h for n,h in frozen['engine_hashes'].items()),
        extractor_sha256=sha(ROOT/'phase2/Extract.lean'),library_sha256=sha(ROOT/'phase2/library.json'),
        library_source_hashes=json.loads((ROOT/'phase2/library.json').read_text(encoding='utf-8'))['source_hashes'],
        lean_toolchain=(ROOT/'lean/lean-toolchain').read_text().strip(),manifest_sha256=sha(ROOT/'lean/lake-manifest.json'),
        environment=json.loads((Path(results[0]['result']['run'])/'environment.json').read_text(encoding='utf-8')),
        historical_artifact_hashes=artifact_hashes,api_status='no AI call',overwrite_existing=False)
    save('baseline/manifest.json',manifest)
    after=files_snapshot()
    save('preservation.json',dict(checked=len(before),changed=[k for k in before.keys()&after.keys() if before[k]!=after[k]],
        removed=sorted(before.keys()-after.keys()),added=sorted(after.keys()-before.keys()),all_unchanged=before==after,
        sqlite_access='sqlite3 URI mode=ro + query_only=ON; SELECT/read PRAGMA only; no Store imported',
        database_and_sidecars=[k for k in before if 'sqlite' in k]))
    print(json.dumps(dict(databases=len(dbs),compared_backups=len(summaries),cases=len(cases),preserved=before==after),ensure_ascii=False))

if __name__=='__main__': main()
