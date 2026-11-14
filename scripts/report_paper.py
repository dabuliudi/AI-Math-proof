"""从真实 PDF 生成可复查报告，绝不使用替代文本。"""
import argparse
import json
from collections import Counter
from pathlib import Path
from mathlib2.pipeline import run
from mathlib2.store import Store
from mathlib2.candidate import view


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('pdf')
    parser.add_argument('--db', default='data/mathlib2.sqlite')
    args = parser.parse_args()
    store = Store(args.db)
    try:
        result = run(store,args.pdf)
        source = store.document(result['source_id'])
        candidates = [view(r) for r in store.rows('candidates') if r['source_id']==result['source_id'] and r['payload'].get('kind')=='document']
        artifact = {'result':result, 'source_sha256':source['sha256'], 'source_path':source['path'], 'candidates':candidates}
        folder = Path('reports')
        folder.mkdir(exist_ok=True)
        (folder/'abundant-numbers.json').write_text(json.dumps(artifact,ensure_ascii=False,indent=2),encoding='utf-8')
        counts = Counter(c['object_type'] for c in candidates)
        lines = ['# Abundant Numbers 真实论文解析报告', '',
                 '论文：Learning about Proof with the Theorem Prover LEAN: the Abundant Numbers Task；Athina Thoma、Paola Iannone；DOI 10.1007/s40753-021-00140-1。', '',
                 f"来源 ID：{result['source_id']}；PDF 页数：{len(source['pages'])}；SHA256：`{source['sha256']}`。",
                 f"规则识别 {len(candidates)} 个片段，类型计数：{dict(counts)}。",
                 f"不确定对象：{sum(c.get('recognition_status')=='uncertain' for c in candidates)}。",
                 '全部验证状态为 unknown，全部未形式化；未调用 AI 或 Lean 为这些论文对象作证明。', '',
                 '## 原文核对与关键边界', '',
                 '第 28 页 Appendix 2 的原始任务确实写 any k ∈ N；第 9 页讨论 k=1 为假、随后要求 k>1。系统保留两个独立的原文对象，未把原题改写成更正后的命题。',
                 '完全数和丰盈数定义采用所有因数的和与 2n 比较。没有替换为真因数和，也没有自行补写整数正性条件。',
                 '第 14 页 Fig.8 是手写证明图，文字层仅保留图注和对 Lemma 3、4 的提及。未使用 OCR，故没有伪造引理内容。第 15 页作者叙述中的步骤被保存为 uncertain 原文分句；顺序不是逻辑依赖。',
                 '字符偏移基于该次 pypdf 输出的每页原始字符串，Python Unicode 字符索引，区间为 [start,end)，不是 PDF 字节偏移或排版坐标。页码为物理页码，首张为 1。', '',
                 '## 候选与来源', '', '|编号|类型|阶段|页码|字符区间|标题（摘要）|','|---|---|---|---|---|---|']
        for c in candidates:
            loc=c['location']
            title=c['title'].replace('|','/').replace('\n',' ')[:130]
            lines.append(f"|{c['candidate_id']}|{c['object_type']}|{c['stage']}|{loc['page']}|{loc['start']}–{loc['end']}|{title}|")
        lines += ['', '## 关键对象原文', '']
        for c in candidates:
            if c['extraction_method'] in {'condition_discussion','narrative_proof_step'} or (c['location']['page']==28 and ('perfect' in c['statement'] or 'abundant number' in c['statement'])):
                lines += [f"### 候选 {c['candidate_id']} · 第 {c['location']['page']} 页", '', '```text', c['original_text'], '```', '']
        graph=result.get('dag',{})
        lines += ['## DAG 结果', '',f"节点 {len(graph.get('nodes',[]))}，可靠依赖边 {len(graph.get('edges',[]))}。",
                  '没有仅因共现创建依赖边。下列引用保留为 uncertain，等待图片转录或人工指认：', '',
                  '```json',json.dumps(graph.get('unresolved',[]),ensure_ascii=False,indent=2),'```','',
                  '完整候选、上下文、步骤、DAG 和偏移见同目录 abundant-numbers.json。', '',
                  '## 局限', '', '规则分数不是语义正确率；未编号的叙述可能漏检。跨页内容不自动拼接，扫描页及手写图不做 OCR；数字公式的文本顺序须人工核对。缺少声明正文时宁可不建立边。']
        (folder/'abundant-numbers.md').write_text('\n'.join(lines),encoding='utf-8')
        print(json.dumps({'source_id':result['source_id'],'objects':len(candidates),'types':dict(counts),'edges':len(graph.get('edges',[]))},ensure_ascii=False))
    finally:
        store.db.close()


if __name__ == '__main__':
    # 保持原有命令入口；新版报告单独输出，避免混合历史候选或覆盖旧报告。
    from report_v022 import main as current_main
    current_main()
