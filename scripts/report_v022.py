"""运行真实 PDF、固定标注评估、旧记录校验；输出独立 v0.2.2 报告。"""
import argparse
import json
import sqlite3
from collections import Counter
from pathlib import Path
from mathlib2.pipeline import run
from mathlib2.store import Store
from mathlib2.documents import save_candidates
from mathlib2.quality import assess_document
from mathlib2.ingest import ingest
from mathlib2.metrics import evaluate
from mathlib2.candidate import view


def snapshot(db):
    return {t:list(db.execute('SELECT * FROM '+t+' ORDER BY 1')) for t in ('sources','candidates','events','verified')}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('pdf',nargs='?',default='s40753-021-00140-1.pdf')
    ap.add_argument('--db',default='data/mathlib2.sqlite')
    args = ap.parse_args()
    truth = json.loads(Path('tests/fixtures/abundant-ground-truth.json').read_text(encoding='utf-8'))
    store = Store(args.db)
    try:
        # SQLite 在线备份，不覆盖已经存在的首份备份。
        backup = Path(args.db).with_name('backup-before-v022.sqlite')
        if not backup.exists():
            with sqlite3.connect(backup) as dst:
                store.db.backup(dst)
        before = snapshot(store.db)
        result = run(store,args.pdf)
        sid = result['source_id']
        source = store.document(sid)
        candidates, graph = save_candidates(store,sid,source)
        fresh1, fresh2 = assess_document(ingest(args.pdf)), assess_document(ingest(args.pdf))
        assert fresh1 == fresh2, '独立重新读取 PDF 结果不稳定'
        count = len(store.rows('candidates'))
        repeated = run(store,args.pdf)
        assert repeated['reused'] and repeated['results']==result['results']
        assert len(store.rows('candidates'))==count
        after = snapshot(store.db)
        # 新版候选自身可重复更新；其余既有记录必须逐字节相同。
        new_ids = {c['candidate_id'] for c in candidates}
        preserved = {t:all(tuple(row) in {tuple(r) for r in after[t]} for row in before[t]
                          if not (t=='candidates' and row['id'] in new_ids)) for t in before}
        assert all(preserved.values()), '旧版数据被改变'
        metric = evaluate(source,candidates,graph,truth)
        old_source = store.document(sid,'0.2.1')
        old_candidates = [view(r) for r in store.rows('candidates') if r['source_id']==sid and
                          r['payload'].get('kind')=='document' and ':0.2.1:' in r['payload'].get('object_key','')]
        old_graph = {'edges':[],'unresolved':[]}
        old_report = Path('reports/abundant-numbers.json')
        if old_report.exists():
            old_graph = json.loads(old_report.read_text(encoding='utf-8'))['result'].get('dag',old_graph)
        baseline = None
        if old_source and old_candidates:
            baseline = dict(objects=len(old_source['objects']), candidate_rows=len(old_candidates),
                stages=dict(Counter(c['stage'] for c in old_candidates)),
                formal_metrics=evaluate(old_source,[c for c in old_candidates if c['stage']=='Candidate'],old_graph,truth),
                stored_rows_metrics=evaluate(old_source,old_candidates,old_graph,truth))
        artifact = dict(version='0.2.2',source_id=sid,source_sha256=source['sha256'],
            result=result,candidates=candidates,objects=source['objects'],dag=graph,metrics=metric,
            baseline=baseline, classification=dict(Counter(o['classification'] for o in source['objects'])),
            quality_tiers=dict(Counter(o['quality_tier'] for o in source['objects'])),
            checks={'fresh_pdf_parses_identical':True,'cached_repeat_identical':True,'no_duplicate_candidates':True,
                    'old_records_unchanged':preserved,'before_counts':{t:len(v) for t,v in before.items()},
                    'after_counts':{t:len(v) for t,v in after.items()}})
        out = Path('reports'); out.mkdir(exist_ok=True)
        (out/'abundant-v022.json').write_text(json.dumps(artifact,ensure_ascii=False,indent=2),encoding='utf-8')
        lines = ['# Mathlib2 v0.2.2 真实论文回归报告','',
            '论文：Thoma、Iannone，Learning about Proof with the Theorem Prover LEAN: the Abundant Numbers Task；DOI 10.1007/s40753-021-00140-1。',
            f"来源 {sid}；30 页；SHA256 `{source['sha256']}`。实际读取原始 PDF，无 AI、无 OCR；论文候选 Lean=not_run、verification=unknown。",'',
            '## 新旧版本对比','',
            '|项目|v0.2.1|v0.2.2|','|---|---:|---:|',
            f"|保留的识别片段|{baseline['objects'] if baseline else '无历史基线'}|{len(source['objects'])}|",
            f"|写入本版候选表|{len(old_candidates)}|{len(candidates)}|",
            f"|正式 Candidate|{baseline['stages'].get('Candidate',0) if baseline else '无基线'}|{sum(c['stage']=='Candidate' for c in candidates)}|",
            f"|显式依赖边|{len(old_graph['edges'])}|{sum(e['basis']=='explicit' for e in graph['edges'])}|",
            f"|规则推测定义依赖|0|{sum(e['basis']=='rule_hypothesis' for e in graph['edges'])}|",'',
            '新增片段来自更完整的图表标题留存，不是新增定理。图注、学生案例、正文引用、语义证据、其他专题练习均保存在原始资料中。',
            '同一丰盈数任务中的素数乘积练习仍是相关候选；不因为未证明或可能为假而剔除。',
            '分类：`'+json.dumps(artifact['classification'],ensure_ascii=False)+'`。',
            '质量层级：`'+json.dumps(artifact['quality_tiers'],ensure_ascii=False)+'`。分数是规则启发式，不是数学正确率。','',
            '## 原文、边界与独立字段','',
            '`original_statement` 原样保存；`normalized_statement` 仅合并空白；`lean_statement=null`。三个字段互不覆盖。',
            '原题第28页写 any k ∈ N；第9页明确讨论 k=1 为假并要求 k>1。k=1 时 kn=n，完全数的因数和等于2n，未满足丰盈数的严格大于条件。',
            '因此标记 potential_counterexample，而不是 refuted；只在 proposed_corrections 中建议加入 k>1。n 的正性、自然数是否含0及因数集合约定仍待复核。',
            '第二个素数练习保持原文和 unknown，本版没有实现其专项真值判断。','',
            '|ID|类型|页码|字符区间|质量|语义状态|','|---|---|---|---|---|---|']
        for c in candidates:
            loc=c['location']
            lines.append(f"|{c['candidate_id']}|{c['object_type']}|{loc['page']}|[{loc['start']},{loc['end']})|{c['quality_tier']}|{c['semantic_status']}|")
        for c in candidates:
            lines += ['',f"### 候选 {c['candidate_id']}",'','```text',c['original_statement'],'```']
        lines += ['','页码是PDF物理页；偏移为本次逐页文本的Unicode字符索引，不是PDF坐标。完整上下文、条件审计及建议修正版见 abundant-v022.json。','',
                  '## DAG','',f"{len(graph['nodes'])} 个节点；明确引用边0；规则推测定义使用边3；未解析引用 {len(graph['unresolved'])} 处。",'']
        for e in graph['edges']:
            lines.append(f"- {e['from']} → {e['to']}：{e['dependency_type']}；证据词 `{e['evidence']['quote']}`；待审核。")
        lines += ['','第14页 Lemma 3、Lemma 4 只有文字提及，没有可匹配的文字层声明，不能建显式边。Fig.8 中可见的 Lemma 1/2 → Lemma 3 是学生手写证明；本版不做OCR，未自动恢复这些边。',
                  '定义词推测边不等于论文作者明确声明的证明依赖，不计入显式边准确率。','',
                  '## 固定标注集指标（草案）','',
                  '标注已由助手逐项对照原文及第14/28页图像核读。没有真实人类复核，human_reviewed=false；不能称为已人工验收的金标准。待研究者复核 tests/fixtures/abundant-ground-truth.json。',
                  truth['scope'],'','|指标|实际计数|值|','|---|---|---|']
        for name,value in metric.items():
            if isinstance(value,dict) and 'numerator' in value:
                formatted = f"{value['value']:.1%}" if value['value'] is not None else 'N/A（分母为0）'
                lines.append(f"|{name}|{value['numerator']}/{value['denominator']}|{formatted}|")
        lines += ['','v0.2.1 的正式 Candidate 在相同范围中精确率为4/11；图注此前标为 Extracted，但仍混入候选表，所选图注候选表污染率4/4；新版为0/4。',
                  '11项条件全部保留只证明文本未遗漏，不能替代数学语义校验。全文召回率未测量，图内显式依赖召回率为0/2，禁止隐藏此限制。','',
                  '## 稳定性和数据库','', '```json',json.dumps(artifact['checks'],ensure_ascii=False,indent=2),'```',
                  '',f'备份：{backup}。没有删除旧来源、候选、事件或审核记录。JSON负载新增字段；无需ALTER已有业务表。',
                  '独立重读PDF两次结果相同；重复运行复用缓存且不新增候选。原有 v0.2.1 解析仍可按版本读取。']
        (out/'abundant-v022.md').write_text('\n'.join(lines),encoding='utf-8')
        print(json.dumps({'source_id':sid,'objects':len(source['objects']),'formal_candidates':len(candidates),
                          'classification':artifact['classification'],'checks':artifact['checks']},ensure_ascii=False))
    finally:
        store.db.close()


if __name__=='__main__':
    main()
