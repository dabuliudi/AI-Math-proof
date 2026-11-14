"""原生交互图，选择节点/边查看证据；绘图不改变验证状态。"""
import streamlit as st


def render_graph(graph,candidates):
    nodes=graph.get('nodes',[])
    edges=graph.get('edges',[])
    st.caption('实线：明确引用；虚线：推测。定义使用不等于证明依赖。图上的连线不表示 Lean 已验证。')
    if graph.get('status')=='invalid':
        st.error('检测到无效或循环依赖：'+graph.get('error','请查看高级诊断'))
    if not nodes:
        st.info('当前文献没有可规划节点，请先运行数学结构解析。')
        return
    types=sorted({n.get('object_type','Reference') for n in nodes})
    data=[{'id':str(n['id']),'name':str(n['title'])[:45],'value':str(n['id']),
           'category':types.index(n.get('object_type','Reference')),'symbolSize':42} for n in nodes]
    links=[{'source':str(e['from']),'target':str(e['to']),'name':e.get('dependency_type',e.get('relation','依赖')),
        'lineStyle':{'type':'solid' if e.get('basis') in {'explicit','human'} else 'dashed','width':2},
        'value':e.get('dependency_type',e.get('relation','依赖'))} for e in edges]
    event=st.echarts_chart({'tooltip':{},'legend':[{'data':types,'bottom':0}],
        'series':[{'type':'graph','layout':'force','roam':True,'draggable':True,'selectedMode':'single',
        'data':data,'links':links,'categories':[{'name':t} for t in types],
        'force':{'repulsion':500,'edgeLength':160},'label':{'show':True,'position':'right','fontSize':11},
        'edgeSymbol':['none','arrow'],'edgeSymbolSize':[4,10]}]},height=460,key='proof_graph',on_select='rerun',
        alt='数学对象依赖图，可缩放、拖动和选择节点及边')
    selected=[]
    if hasattr(event,'selection'):
        selected=event.selection.selected
    selected_node=None
    selected_edge=None
    for group in selected:
        indices=group.get('data_indices',[])
        if not indices: continue
        if group.get('data_type')=='edge' and indices[-1]<len(edges): selected_edge=edges[indices[-1]]
        elif indices[-1]<len(nodes): selected_node=nodes[indices[-1]]
    target=st.selectbox('目标节点 / 反向追踪',[n['id'] for n in nodes],format_func=lambda i:next(n['title'][:100] for n in nodes if n['id']==i),key='dag_target')
    if selected_node: st.info('已选择节点：'+selected_node['title'])
    else: selected_node=next(n for n in nodes if n['id']==target)
    match=next((c for c in candidates if c['candidate_id']==selected_node['id']),None)
    if match:
        st.code(match.get('original_statement') or match.get('statement',''),language=None)
        st.caption('来源定位：'+str(match.get('location',{})))
    else: st.json(selected_node)
    ancestors=set()
    frontier=[target]
    while frontier:
        for e in edges:
            if e['to'] in frontier and e['from'] not in ancestors:
                ancestors.add(e['from'])
        new=[x for x in ancestors if x not in frontier]
        old=set(frontier)
        frontier=list(set(frontier)|ancestors)
        if set(frontier)==old: break
    ancestors.discard(target)
    st.caption('反向依赖：'+(', '.join(str(x) for x in sorted(ancestors,key=str)) or '尚无已记录依赖'))
    if edges:
        ix=st.selectbox('依赖边证据',list(range(len(edges))),format_func=lambda i:f"{edges[i]['from']} → {edges[i]['to']} · {edges[i].get('dependency_type','依赖')}",key='dag_edge')
        evidence=selected_edge or edges[ix if ix is not None else 0]
        st.markdown('**依赖证据与确认状态**')
        st.json(evidence)
    unresolved=graph.get('unresolved',[])
    st.subheader(f'未解决引用 · {len(unresolved)}')
    if unresolved:
        st.dataframe([{'引用':r.get('reference'),'页码':r.get('page'),'原因':r.get('reason','缺少唯一声明')} for r in unresolved],hide_index=True,alt='未解决的数学引用')
    else: st.caption('当前规则没有报告未解决引用；不代表不存在漏检。')
    with st.expander('高级 · 完整图结构'):
        st.json(graph)
