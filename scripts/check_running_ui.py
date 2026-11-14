import json
import urllib.request
from pathlib import Path
from mathlib2.pipeline import run
from mathlib2.store import Store

store=Store('data/agent-ui-test.sqlite')
run(store,'data/uploads/0357be8b67904937aa2d2491b7f8f0f2.pdf')
store.db.close()
snapshot=json.loads(Path('reports/agent-snapshot.json').read_text(encoding='utf-8'))
sid=snapshot['session_id']
def request(**kwargs):
    req=urllib.request.Request('http://127.0.0.1:8765/_stcore/agent/interact',data=json.dumps({'session_id':sid,**kwargs}).encode(),headers={'Content-Type':'application/json'})
    value=json.load(urllib.request.urlopen(req,timeout=60))
    assert value['status']=='ready',value
    return value

def nodes(tree):
    yield tree
    for child in tree.get('children',[]):
        yield from nodes(child)

snapshot=request()
select=next(n for n in nodes(snapshot['tree']) if n.get('key')=='source_select')
snapshot=request(widget_state={'source_select':select['props']['options'][0],'input_mode':'当前文献'})
snapshot=request(trigger={'key':'run_document'})
elements=list(nodes(snapshot['tree']))
assert not any(n['type'] in ('exception','error') for n in elements)
table=next(n for n in elements if n.get('props',{}).get('alt')=='当前文献候选列表')
assert table['data']['row_count']==25,table
Path('reports/agent-final-snapshot.json').write_text(json.dumps(snapshot,ensure_ascii=False,indent=2),encoding='utf-8')
print(json.dumps({'status':snapshot['status'],'candidate_rows':table['data']['row_count'],'exceptions':0,'workflow':'已有真实 PDF → 规则解析 → 页面候选列表'},ensure_ascii=False))
