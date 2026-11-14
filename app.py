"""Mathlib2 Research Workbench：界面只消费真实后端状态。"""
import hashlib
import os
from pathlib import Path
import streamlit as st
from mathlib2.store import Store
from mathlib2.pipeline import run
from mathlib2 import workbench as wb
from mathlib2.formalization import templates
from mathlib2.ui_graph import render_graph
from mathlib2.research_ai import configured

st.set_page_config(page_title='Mathlib2 Research Workbench', layout='wide')
store = Store(os.environ.get('MATHLIB2_DB','data/mathlib2.sqlite'))
sources = store.rows('sources')
source_ids = [s['id'] for s in sources]
PAGES = ['研究首页','文献管理','候选审核','Proof DAG','Mathlib 检索','Lean Lab','知识库']
if 'pending_page' in st.session_state:
    st.session_state['research_page'] = st.session_state.pop('pending_page')
if 'pending_source' in st.session_state:
    st.session_state['source_select'] = st.session_state.pop('pending_source')
if st.session_state.get('source_select') not in source_ids:
    st.session_state['source_select'] = source_ids[-1] if source_ids else None
st.sidebar.title('Mathlib2')
st.sidebar.caption('Research Workbench · v0.3')
page = st.sidebar.selectbox('工作空间',PAGES,key='research_page')
selected = st.sidebar.selectbox('当前文献',source_ids,key='source_select',format_func=lambda sid:
    f"{sid} · {Path(next(s['payload'].get('path','未命名') for s in sources if s['id']==sid)).name}")
st.sidebar.caption('本地规则与受信任 Lean 实验。'+('研究 AI 地址已配置；本流程尚未调用。' if configured() else '未配置真实 AI。'))
source = store.document(selected) if selected is not None else None
candidates = wb.candidates_for(store,selected) if selected is not None else []
st.title(page)
if st.session_state.pop('notice',None):
    st.success('操作已保存。可在修改历史或证明历史中核查。')


def rerun():
    store.db.close()
    st.rerun()


def go(label,destination,key):
    if st.button(label,key=key):
        st.session_state['pending_page']=destination
        rerun()


def fail(step,exc):
    st.error(f'{step}未完成：{exc}')
    st.info('已保存的原文和历史记录不受影响。修正上述问题后可在本页重试，无需重新上传。')


def pick(key):
    if not candidates:
        st.info('当前没有可操作的候选。请先导入文献并运行解析；旧版文献需要生成新版解析。')
        go('前往文献管理','文献管理','empty_'+key)
        return None
    cid=st.selectbox('目标数学对象',[c['candidate_id'] for c in candidates],key=key,
        format_func=lambda i: next(f"{c['object_type']} · {c['title'][:100]}" for c in candidates if c['candidate_id']==i))
    return next(c for c in candidates if c['candidate_id']==cid)


def original(c):
    loc=c.get('source_location') or c.get('location',{})
    st.caption(f"原文定位：第 {loc.get('page','—')} 页 · 字符 [{loc.get('start','—')}, {loc.get('end','—')})")
    st.code(c.get('original_statement') or c.get('original_text') or c.get('statement',''),language=None)
    if source and loc.get('page') is not None:
        with st.expander('对应页面原文'):
            st.text(dict(source['pages']).get(loc['page'],'本页原文不可用'))


def status_rows(c):
    keys=['extraction_status','semantic_review_status','retrieval_status','planning_status','formalization_status','verification_status','approval_status']
    st.dataframe([{'阶段':k,'状态':c.get(k,'not_run')} for k in keys],hide_index=True,alt='独立工作流状态')


if page=='研究首页':
    st.caption('从原文到可审计证明，每一步都保留证据。')
    counts=wb.summary(store)
    labels={'sources':'文献','objects':'数学片段','candidates':'正式候选','pending_review':'待审核','formalized':'已形式化','verified':'Lean 已验证','approved':'已批准'}
    with st.container(horizontal=True):
        for key,label in labels.items():
            st.metric(label,counts.get(key,0),border=True)
    with st.expander('首次使用 · 五个步骤',expanded=not sources):
        st.markdown('1. **导入文献**：上传 PDF、Markdown 或 TEX，运行解析。\n2. **审核候选**：核对原文、条件、风险，编辑规范化文本并保存理由。\n3. **检索与规划**：查找真实 Mathlib 声明，查看依赖与未解析引用。\n4. **Lean Lab**：查看受信任实验的来源和目标，实际编译并检查公理。\n5. **知识库**：人工核对语义一致性后批准入库。候选批准和知识库批准是两步。')
    if not sources:
        st.info('尚未导入论文，统计来自空数据库。先添加第一篇文献。')
        go('导入第一篇论文','文献管理','start_import')
    elif not source:
        st.warning('当前来源尚无本版解析；历史数据保留。')
        go('生成新版解析','文献管理','upgrade_parse')
    else:
        st.subheader(source.get('title') or source.get('filename','当前研究任务'))
        st.caption('作者：'+str(source.get('authors','未可靠识别'))+' · 领域：'+str(source.get('research_focus','unknown')))
        graph=wb.graph_for(store,selected)
        st.info(f"当前文献有 {len(candidates)} 个候选、{len(graph.get('unresolved',[]))} 个未解析引用。优先核对候选的定义域和原文，再运行适用的 Lean 实验。")
        with st.container(horizontal=True):
            go('审核数学候选','候选审核','next_review')
            go('查看证明依赖','Proof DAG','next_dag')
            go('进入 Lean Lab','Lean Lab','next_lean')
        stages=source.get('stages',{})
        steps=[('文献导入',stages.get('file','not_run'),'选择文献管理'),('正文解析',stages.get('text','not_run'),'解析失败可重新运行'),('数学结构识别',stages.get('structure','not_run'),'核对识别资料')]
        for label,key in [('候选审核','review_status'),('数学语义检查','semantic_review_status'),('Mathlib 检索','retrieval_status'),('DAG 规划','planning_status'),('Lean 形式化','formalization_status'),('Lean 内核验证','verification_status'),('人工审核入库','approval_status')]:
            values=[c.get(key,'not_run') for c in candidates]
            steps.append((label,', '.join(sorted(set(values))) or '无候选','前往对应页面处理未完成对象'))
        st.dataframe([{'工作流':a,'真实状态':b,'下一步':c} for a,b,c in steps],hide_index=True,alt='十阶段工作流与恢复指引')

elif page=='文献管理':
    st.caption('上传成功只表示文件已接收；运行后分别报告正文、结构和候选状态。')
    upload=st.file_uploader('导入文献（10 MB 以下）',type=['pdf','md','tex','txt'],key='document_upload')
    if upload:
        st.success(f'文件已接收：{upload.name}，尚未确认解析成功。')
    mode=st.selectbox('处理输入',['上传文件','当前文献','nat.md 教学样例'],key='input_mode')
    budget=st.slider('教学 / AI 候选预算',1,8,4)
    if st.button('运行完整流程',key='run_document',type='primary'):
        try:
            if mode=='上传文件':
                if upload is None: raise ValueError('请先选择文件')
                content=upload.getvalue()
                if len(content)>10_000_000: raise ValueError('文件超过10 MB')
                path=Path('data/uploads')/(hashlib.sha256(content).hexdigest()+Path(upload.name).suffix.lower())
                path.parent.mkdir(parents=True,exist_ok=True)
                if not path.exists(): path.write_bytes(content)
            elif mode=='当前文献':
                if selected is None: raise ValueError('请先导入文献')
                path=Path(next(s['payload']['path'] for s in sources if s['id']==selected))
            else: path=Path('samples/nat.md')
            with st.status('正在读取原文、识别结构并持久化…',expanded=True) as progress:
                result=run(store,str(path),budget)
                progress.update(label='处理已返回，以下状态反映实际结果',state='complete' if not result.get('error') else 'error')
            st.session_state['last_result']=result
            st.session_state['pending_source']=result['source_id']
            rerun()
        except Exception as exc: fail('文献处理',exc)
    st.dataframe([{'编号':s['id'],'文件':Path(s['payload'].get('path','')).name,'哈希':s['payload'].get('sha256','')} for s in sources],hide_index=True,alt='已导入文献列表')
    if source:
        st.dataframe([{'阶段':k,'状态':v} for k,v in source['stages'].items()],hide_index=True,alt='各处理阶段的独立状态')
        st.caption(f"本版片段 {len(source['objects'])} · 正式候选 {len(candidates)} · 重复字节文件复用来源与本版解析。")
        st.caption(f"不确定片段 {sum(o.get('recognition_status')=='uncertain' for o in source['objects'])} · 已形式化 {sum(c.get('formalization_status')=='formalized' for c in candidates)}")
        pages=list(range(len(source['pages'])))
        ix=st.selectbox('原文预览页',pages,format_func=lambda i:f'第 {i+1} 页',key=f'page_{selected}')
        if ix is not None: st.code(source['pages'][ix][1],language=None)
        materials=[o for o in source['objects'] if not o.get('candidate_eligible')]
        with st.expander(f'保留的原始资料与不确定片段（{len(materials)}）'):
            if materials:
                mi=st.selectbox('资料详情',list(range(len(materials))),format_func=lambda i:materials[i]['title'][:90],key=f'material_{selected}')
                if mi is not None: st.code(materials[mi]['original_text'],language=None)
        with st.expander('高级 · 解析历史与执行详情'):
            st.json([r for r in store.rows('document_parses') if r['source_id']==selected])
            st.json(st.session_state.get('last_result',{}))
    elif sources: st.warning('请选择当前文献并运行新版解析。')

elif page=='候选审核':
    left,right=st.columns([1,2])
    with left:
        kind=st.multiselect('对象类型',sorted({c['object_type'] for c in candidates}),key='kind_filter')
        if kind: candidates=[c for c in candidates if c['object_type'] in kind]
        st.dataframe([{'编号':c['candidate_id'],'类型':c['object_type'],'标题':c['title'],'质量':c.get('quality_tier','—'),'审核':c.get('review_status','pending'),'验证':c.get('verification_status','unknown')} for c in candidates],hide_index=True,alt='当前文献候选列表')
        c=pick(f'candidate_{selected}')
    with right:
        if c:
            st.subheader(c['title'])
            original(c)
            if c.get('potential_counterexamples') or c.get('semantic_status')=='potential_counterexample':
                st.warning('潜在边界反例需要核查；此提示不是 Lean 证伪结果。')
            if c.get('proposed_corrections'):
                with st.expander('独立修正建议（不是论文原文，未经证明）'):
                    st.json(c['proposed_corrections'])
            for label,key in [('前提条件','assumptions'),('量词','quantifiers'),('定义域','domain_constraints'),('边界情况','boundary_cases'),('潜在反例','potential_counterexamples'),('语义风险','semantic_risk')]:
                st.markdown('**'+label+'**')
                st.write(c.get(key) or '未可靠识别，待复核')
            with st.form('candidate_review'):
                normalized=st.text_area('规范化表述（不会覆盖原文）',c.get('normalized_statement') or c.get('statement',''),height=160)
                decision=st.selectbox('审核决定',['needs_review','approved','rejected'],format_func=lambda x:{'needs_review':'待复核','approved':'批准候选','rejected':'拒绝候选'}[x])
                reviewer=st.text_input('审核人')
                note=st.text_area('审核理由')
                confirm=st.checkbox('确认拒绝或修改规范化表述；原文及历史仍保留')
                if st.form_submit_button('保存候选审核'):
                    try:
                        changed=normalized!=(c.get('normalized_statement') or c.get('statement',''))
                        if (changed or decision=='rejected') and not confirm: raise ValueError('请勾选操作确认')
                        wb.review(store,c['candidate_id'],decision,reviewer,note,normalized)
                        st.session_state['notice']=True; rerun()
                    except Exception as exc: fail('候选审核',exc)
            with st.expander('修改历史与高级状态'):
                st.json(wb.history(store,c['candidate_id']))
                status_rows(c)

elif page=='Proof DAG':
    if selected is None:
        st.info('导入文献后才有可规划的数学对象。')
        go('导入文献','文献管理','dag_import')
    else:
        if st.button('建立 / 更新证明规划',key='run_planner',type='primary'):
            try:
                wb.plan_for(store,selected)
                st.success('已保存本次规划，尚未确认的依赖仍保留原状态。')
            except Exception as exc: fail('DAG 规划',exc)
        render_graph(wb.graph_for(store,selected),candidates)

elif page=='Mathlib 检索':
    c=pick('search_candidate')
    if c:
        query=st.text_input('数学表达式 / Lean 类型 / 关键词',c.get('normalized_statement') or c['title'],key='math_query')
        if st.button('搜索本地 Mathlib',key='search_mathlib',type='primary'):
            try:
                with st.spinner('检索真实声明与源码位置…'):
                    hits=wb.search_for(store,c['candidate_id'],query)
                st.session_state[f'hits_{c["candidate_id"]}']=hits
            except Exception as exc: fail('Mathlib 检索',exc)
        hits=st.session_state.get(f'hits_{c["candidate_id"]}',wb.state(store,c['candidate_id']).get('retrieval_results',[]))
        if not hits: st.info('尚无本次检索结果。输入声明、类型或关键词后搜索；词法相似不代表数学等价。')
        for i,hit in enumerate(hits):
            with st.container(border=True):
                st.subheader(hit.get('name') or hit.get('declaration') or f'结果 {i+1}')
                st.caption(str(hit.get('match_kind','keyword_only'))+' · '+str(hit.get('namespace',''))+' · 数学等价性尚未确立')
                st.code(hit.get('declaration') or hit.get('text') or str(hit),language='lean4')
                st.caption(f"源码：{hit.get('path',hit.get('file',''))} · 行 {hit.get('line','—')}")
                st.write(hit.get('suggestion','核对完整类型、前提与定义后决定能否复用。'))

elif page=='Lean Lab':
    c=pick('lean_candidate')
    if c:
        left,right=st.columns(2)
        with left:
            st.subheader('目标与来源')
            original(c)
            st.markdown('**规范化表述**')
            st.text(c.get('normalized_statement') or c.get('statement',''))
            st.caption('请核对实验目标与当前候选是否一致。相关引理通过不等于主定理通过。')
        with right:
            available=templates()
            tid=st.selectbox('受信任形式化实验',list(available),format_func=lambda k:available[k].get('label',k),key='lean_template')
            if tid is not None:
                template=available[tid]
                st.caption('来源：'+str(template.get('provenance','受信任本地模板；无 AI 调用')))
                st.info('生成按钮只展示内置声明/证明模板。真实 AI 自动生成暂未接入。')
                if st.button('载入声明与证明候选',key='load_template'):
                    st.session_state['loaded_template']=tid
                if st.session_state.get('loaded_template')==tid:
                    st.code(template.get('source',''),language='lean4')
                    if st.button('实际编译并保存证明版本',key='compile_lean',type='primary'):
                        try:
                            with st.spinner('运行真实 Lean 编译器并审计公理…'):
                                result=wb.compile_for(store,c['candidate_id'],tid)
                            if result.get('accepted'): st.success('该实验编译通过。候选验证状态取决于目标对齐审核。')
                            else: st.error('实验未通过：'+str(result.get('reason',result.get('status','查看下方完整日志'))))
                        except Exception as exc: fail('Lean 编译',exc)
            history=wb.proof_history(store,c['candidate_id'])
            if not history: st.info('暂无编译记录；载入适用实验后运行。失败可在此重试，无需重传论文。')
            for i,item in enumerate(reversed(history)):
                record=item.get('payload',item)
                with st.expander(f"证明记录 {len(history)-i} · {record.get('status',record.get('reason','查看详情'))}",expanded=i==0):
                    st.caption('Lean版本：'+str(record.get('toolchain','记录未包含版本')))
                    st.code(record.get('stdout','')+'\n'+record.get('stderr',''),language=None)
                    st.code(record.get('source',''),language='lean4')
                    st.caption('公理：'+str(record.get('axioms',[])))
                    st.json(record)

elif page=='知识库':
    st.info('批准候选不等于批准入库。只有实际 Lean 验证且人工审核一致性的命题可以进入正式知识库。')
    st.dataframe([{'编号':c['candidate_id'],'标题':c['title'],'候选审核':c.get('review_status','pending'),'验证':c.get('verification_status','unknown'),'入库':c.get('approval_status','not_approved')} for c in candidates],hide_index=True,alt='候选与已验证知识状态')
    eligible=[c for c in candidates if c.get('verification_status')=='proved' and c.get('approval_status') not in {'approved','human_approved'}]
    with st.form('review'):
        cid=st.selectbox('选择已证明候选',[c['candidate_id'] for c in eligible])
        reviewer=st.text_input('入库审核人')
        note=st.text_area('原文、定义域与形式化一致性意见')
        confirm=st.checkbox('已核对编译证据与原文一致性')
        if st.form_submit_button('批准进入知识库',disabled=not eligible):
            try:
                if not confirm: raise ValueError('请确认原文与编译证据一致性')
                wb.approve_verified(store,cid,reviewer,note)
                st.session_state['notice']=True; rerun()
            except Exception as exc: fail('知识库审批',exc)
    with st.expander('审核记录和原有角色日志'):
        st.json(store.rows('verified'))
        ids={c['candidate_id'] for c in candidates}
        st.json([e for e in store.rows('events') if e['candidate_id'] in ids])
store.db.close()
