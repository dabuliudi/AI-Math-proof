"""真实论文回归及形式化实验，不自动批准生产知识库。"""
import json
from pathlib import Path
from mathlib2.store import Store
from mathlib2.pipeline import run
from mathlib2.workbench import candidates_for,search_for,plan_for,compile_for,summary

store=Store('data/mathlib2.sqlite')
try:
    tables=('sources','candidates','events','verified')
    before={t:[tuple(r) for r in store.db.execute('SELECT * FROM '+t)] for t in tables}
    reports=[]
    for filename in ('s40753-021-00140-1.pdf','2408.15180v2.pdf'):
        r=run(store,filename)
        sid=r['source_id']; doc=store.document(sid)
        cs=candidates_for(store,sid)
        assert all(dict(doc['pages'])[o['page']][o['start']:o['end']]==o['original_text'] for o in doc['objects'])
        repeated=run(store,filename)
        assert repeated['reused'] and repeated['results']==r['results']
        item={'file':filename,'sha256':doc['sha256'],'source_id':sid,'objects':len(doc['objects']),
              'candidates':len(cs),'uncertain':sum(o['recognition_status']=='uncertain' for o in doc['objects']),
              'source_trace_all_exact':True,'repeat_stable':True,'candidate_details':cs}
        if filename.startswith('2408'):
            c=next(c for c in cs if c['title'].startswith('Lemma 1.'))
            item['retrieval']=search_for(store,c['candidate_id'],'divRadical_dvd_derivative')
            item['lemma1_experiment']=compile_for(store,c['candidate_id'],'mason_lemma1')
        item['dag']=plan_for(store,sid)
        reports.append(item)
    preserved={t:all(r in set(tuple(x) for x in store.db.execute('SELECT * FROM '+t)) for r in before[t]) for t in tables}
    assert all(preserved.values()),preserved
    data={'papers':reports,'old_rows_unchanged':preserved,'summary':summary(store),
          'human_approval':'未代替用户审核；生产候选仍待人工对齐审核。编译实验与候选验证状态分开。'}
    Path('reports/regression-v03.json').write_text(json.dumps(data,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps({'papers':[{k:p[k] for k in ('file','objects','candidates','uncertain')} for p in reports],
                      'old_rows_unchanged':preserved,'lemma1_accepted':reports[1]['lemma1_experiment']['accepted']},ensure_ascii=False))
finally: store.db.close()
