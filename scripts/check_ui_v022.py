"""仅对独立测试数据库运行实际 Streamlit 页面检查。"""
import json
import os
import subprocess
import sys
import time
import urllib.request
from pathlib import Path
from mathlib2.store import Store
from mathlib2.pipeline import run

ROOT = Path(__file__).resolve().parents[1]
base = 'http://127.0.0.1:8766'
db = ROOT/'data/agent-ui-v022-check.sqlite'
os.environ['MATHLIB2_PROVIDER']='mock'
store = Store(str(db))
run(store,str(ROOT/'s40753-021-00140-1.pdf'))
store.db.close()
env = {**os.environ,'MATHLIB2_DB':str(db),'PYTHONUTF8':'1'}


def request(payload):
    req=urllib.request.Request(base+'/_stcore/agent/interact',data=json.dumps(payload).encode(),headers={'Content-Type':'application/json'})
    result=json.load(urllib.request.urlopen(req,timeout=45))
    assert result['status']=='ready',result
    return result


def nodes(tree):
    yield tree
    for c in tree.get('children',[]):
        yield from nodes(c)


with (ROOT/'reports/ui-server-v022.log').open('w',encoding='utf-8') as log:
    process=subprocess.Popen([sys.executable,'-m','streamlit','run','app.py','--server.headless=true',
        '--server.address=127.0.0.1','--server.port=8766','--server.enableAgentApi=true','--browser.gatherUsageStats=false'],
        cwd=ROOT,env=env,stdout=log,stderr=log)
    try:
        for _ in range(40):
            if process.poll() is not None:
                raise RuntimeError('测试服务器提前退出，查看日志')
            try:
                urllib.request.urlopen(base+'/_stcore/health',timeout=1).close()
                break
            except OSError:
                time.sleep(.25)
        schema=json.load(urllib.request.urlopen(base+'/_stcore/agent/openapi.json'))
        (ROOT/'reports/ui-openapi-v022.json').write_text(json.dumps(schema),encoding='utf-8')
        snap=request({})
        sid=snap['session_id']
        snap=request({'session_id':sid,'widget_state':{'input_mode':'当前文献'},'trigger':{'key':'run_document'}})
        elements=list(nodes(snap['tree']))
        assert not any(n['type'] in ('exception','error') for n in elements)
        table=next(n for n in elements if n.get('props',{}).get('alt')=='当前文献候选列表')
        assert table['data']['row_count']==4
        selector=next(n for n in elements if str(n.get('key','')).startswith('candidate_'))
        snap=request({'session_id':sid,'widget_state':{selector['key']:selector['props']['options'][2]}})
        assert 'potential_counterexample' in json.dumps(snap)
        assert '潜在边界反例' in json.dumps(snap,ensure_ascii=False)
        assert not any(n['type'] in ('exception','error') for n in nodes(snap['tree']))
        (ROOT/'reports/ui-snapshot-v022.json').write_text(json.dumps(snap,ensure_ascii=False,indent=2),encoding='utf-8')
        print(json.dumps({'status':'ready','candidate_rows':4,'boundary_warning':True,'exceptions':0,'isolated_database':str(db)}))
    finally:
        process.terminate()
        process.wait(timeout=15)
