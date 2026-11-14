"""从已有运行记录导出阅读版证据，不运行或批准任何证明。"""
import json
import sqlite3
from pathlib import Path

root = Path(__file__).resolve().parents[2]
p = root / 'phase2'
batch = p / 'benchmarks/run-b63d1f87b59f467a994af289b0ab8390'
rows = json.loads((batch / 'results.json').read_text(encoding='utf-8'))
result = next(r['result'] for r in rows if r['id'] == 'multilayer')
folder = Path(result['run'])
dag = json.loads((folder / 'dag.json').read_text(encoding='utf-8'))
events = [json.loads(s) for s in (folder / 'events.jsonl').read_text(encoding='utf-8').splitlines()]
starts = {e['payload']['declarations'][-1]: e['sequence'] for e in events if e['kind'] == 'compile_started'}
used = set(result['successful_proof_nodes'])
def link(path, label):
    return f'[{label}]({Path(path).as_posix()})'
lines = ['# 运行时多层 Proof DAG 实例', '',
         '输入：自然数 a,b,c,d,e,f；假设 a∣b、b∣c、c∣d、d∣e、e∣f、0<f；目标 (a∣f)∧(a≤f)。', '',
         '节点和边来自编译前写入的 planned 事件。本文件只是运行后的可视化，不是规划输入。', '',
         link(folder/'events.jsonl','原始事件')+' · '+link(folder/'dag.json','完整DAG')+' · '+link(folder/'attempt-009.lean','完整Lean源码'), '',
         '```mermaid', 'graph TD']
for node in dag['nodes']:
    label = node['statement'].replace('"', "'")
    lines.append(f'  {node["id"]}["{node["id"]}: {label}"]')
for edge in dag['edges']:
    lines.append(f'  {edge["source"]} --> {edge["target"]}')
for node in dag['nodes']:
    if node['id'] not in used:
        lines.append(f'  style {node["id"]} fill:#eeeeee,stroke:#888888')
lines += ['```', '', '灰色节点是真实编译通过但未进入最终数学证明依赖链的探索分支。全部15节点、12条边均保留。', '',
          '|节点|数学结论|来源|规划事件|编译开始事件|最终采用|', '|---|---|---|---:|---:|---|']
for n in dag['nodes']:
    lines.append(f'|{n["id"]}|{n["statement"]}|{n.get("rule",n["origin"])}|{n["planned_event"]}|{starts.get(n["id"],"输入假设")}|{"是" if n["id"] in used else "否"}|')
lines += ['', '全部边为 proof_dependency；每条边的数学依据如下。被引用库定理的完整类型及源码位置列于后文。', '', '|前提|结论|依据|', '|---|---|---|']
for e in dag['edges']:
    lines.append(f'|{e["source"]}|{e["target"]}|{e["evidence"]}|')
lines += ['', '## 实际复用声明', '', '包含未采用探索分支的声明，不与最终复用计数混淆。']
seen = set()
for n in dag['nodes']:
    if 'retrieval_source' not in n or n['rule'] in seen:
        continue
    seen.add(n['rule']); src=n['retrieval_source']
    lines += ['', f'### {n["rule"]}', '', link(src['path']+':'+str(src['line']), '源码第'+str(src['line'])+'行'), '', '```lean', src['type'], '```']
lines += ['', '最终证明使用 Dvd.dvd.trans（Mathlib）和 Nat.le_of_dvd（Lean Core），再用 And.intro 闭合合取。', '',
          '最终采用5个新生成声明，其中3个是不同于最终子目标的中间引理；数学DAG深度6。3个无关分支仍保留在最终源文件并接受公理审计。', '',
          'DAG表示数学事实的前提依赖，不是Lean内核全部常量、类型类实例和隐式参数的传递依赖图。所有中间Lean声明显式携带完整输入上下文；这些上下文参数未逐个扩展成数学依赖边。', '',
          '所有实例化和排序来自开发者编写的通用 Rule Engine；没有项目AI调用，也没有按本题定制证明。']
(p/'PROOF_EXAMPLE.md').write_text('\n'.join(lines)+'\n',encoding='utf-8')

baseline=root/'audits/lemma3-v031-80ab8af1/workspace/data/mathlib2.sqlite'
with sqlite3.connect(baseline.as_uri()+'?mode=ro',uri=True) as old, sqlite3.connect((root/'data/mathlib2.sqlite').as_uri()+'?mode=ro',uri=True) as current:
    details={}
    for cid in (73,74,75,76,85,87,89):
        a=json.loads(old.execute('SELECT payload FROM workbench_state WHERE candidate_id=?',(cid,)).fetchone()[0])
        b=json.loads(current.execute('SELECT payload FROM workbench_state WHERE candidate_id=?',(cid,)).fetchone()[0])
        details[str(cid)]={k:dict(before=a.get(k),after=b.get(k)) for k in set(a)|set(b) if a.get(k)!=b.get(k)}
    history={}
    for table,key in [('candidates','id'),('workbench_state','candidate_id'),('proof_runs','candidate_id'),('workbench_history','candidate_id'),('events','candidate_id'),('verified','candidate_id')]:
        sql=f'SELECT * FROM {table} WHERE {key} IN (85,87,89) ORDER BY 1'
        a=old.execute(sql).fetchall();b=current.execute(sql).fetchall()
        history[table]=dict(rows=len(b),exact_equal=a==b)
    artifact=dict(baseline=str(baseline),state_differences=details,lemma123_history=history,
                  new_history=current.execute('SELECT id,candidate_id,action,created FROM workbench_history WHERE id>38').fetchall(),
                  attribution='NOT VERIFIED：未将时间相关性当作因果证据；保留现有数据，不回滚。')
    (p/'history-detail.json').write_text(json.dumps(artifact,ensure_ascii=False,indent=2),encoding='utf-8')
print('已导出DAG与只读历史比较。')
