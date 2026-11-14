# Mathlib2 v0.2.2 真实论文回归报告

论文：Thoma、Iannone，Learning about Proof with the Theorem Prover LEAN: the Abundant Numbers Task；DOI 10.1007/s40753-021-00140-1。
来源 8；30 页；SHA256 `c60c9c32ab6e8daf04e31c624d385ad92a6b97973518050cfcaaedbcfdc5a5da`。实际读取原始 PDF，无 AI、无 OCR；论文候选 Lean=not_run、verification=unknown。

## 新旧版本对比

|项目|v0.2.1|v0.2.2|
|---|---:|---:|
|保留的识别片段|25|39|
|写入本版候选表|25|4|
|正式 Candidate|11|4|
|显式依赖边|0|0|
|规则推测定义依赖|0|3|

新增片段来自更完整的图表标题留存，不是新增定理。图注、学生案例、正文引用、语义证据、其他专题练习均保存在原始资料中。
同一丰盈数任务中的素数乘积练习仍是相关候选；不因为未证明或可能为假而剔除。
分类：`{"caption": 25, "semantic_evidence": 1, "ordinary_reference": 1, "student_case": 1, "out_of_scope": 7, "formal_mathematical_object": 4}`。
质量层级：`{"Rejected": 35, "Medium Confidence": 4}`。分数是规则启发式，不是数学正确率。

## 原文、边界与独立字段

`original_statement` 原样保存；`normalized_statement` 仅合并空白；`lean_statement=null`。三个字段互不覆盖。
原题第28页写 any k ∈ N；第9页明确讨论 k=1 为假并要求 k>1。k=1 时 kn=n，完全数的因数和等于2n，未满足丰盈数的严格大于条件。
因此标记 potential_counterexample，而不是 refuted；只在 proposed_corrections 中建议加入 k>1。n 的正性、自然数是否含0及因数集合约定仍待复核。
第二个素数练习保持原文和 unknown，本版没有实现其专项真值判断。

|ID|类型|页码|字符区间|质量|语义状态|
|---|---|---|---|---|---|
|54|Definition|28|[713,789)|Medium Confidence|unchecked|
|55|Definition|28|[790,859)|Medium Confidence|unchecked|
|56|Conjecture|28|[867,922)|Medium Confidence|potential_counterexample|
|57|Conjecture|28|[923,974)|Medium Confidence|unchecked|

### 候选 54

```text
3. An abundant number is an integer n whose divisors add up to more than 2n.
```

### 候选 55

```text
A perfect number is an integer n whose divisors add up to exactly 2n.
```

### 候选 56

```text
(a) If n is perfect, then kn is abundant for any k ∈ N.
```

### 候选 57

```text
(b) If p1 and p2 are primes, then p1p2 is abundant.
```

页码是PDF物理页；偏移为本次逐页文本的Unicode字符索引，不是PDF坐标。完整上下文、条件审计及建议修正版见 abundant-v022.json。

## DAG

4 个节点；明确引用边0；规则推测定义使用边3；未解析引用 2 处。

- 54 → 56：Inferred Dependency；证据词 `abundant`；待审核。
- 55 → 56：Inferred Dependency；证据词 `perfect`；待审核。
- 54 → 57：Inferred Dependency；证据词 `abundant`；待审核。

第14页 Lemma 3、Lemma 4 只有文字提及，没有可匹配的文字层声明，不能建显式边。Fig.8 中可见的 Lemma 1/2 → Lemma 3 是学生手写证明；本版不做OCR，未自动恢复这些边。
定义词推测边不等于论文作者明确声明的证明依赖，不计入显式边准确率。

## 固定标注集指标（草案）

标注已由助手逐项对照原文及第14/28页图像核读。没有真实人类复核，human_reviewed=false；不能称为已人工验收的金标准。待研究者复核 tests/fixtures/abundant-ground-truth.json。
第28页 Appendix2 的11个定义/练习片段；4个选定图注负例；第9页条件讨论和第15页学生叙述；第14页2处文字引用及2条图内明确依赖。仅此小样本，不表示全文召回率。

|指标|实际计数|值|
|---|---|---|
|formal_precision|4/4|100.0%|
|formal_recall|4/4|100.0%|
|object_type_accuracy|4/4|100.0%|
|caption_false_positive_rate|0/4|0.0%|
|condition_omission_rate|0/11|0.0%|
|source_traceability|4/4|100.0%|
|unresolved_reference_precision|2/2|100.0%|
|unresolved_reference_recall|2/2|100.0%|
|inferred_dependency_precision|3/3|100.0%|
|inferred_dependency_recall|3/3|100.0%|
|explicit_dependency_precision|0/0|N/A（分母为0）|
|image_explicit_dependency_recall|0/2|0.0%|

v0.2.1 的正式 Candidate 在相同范围中精确率为4/11；图注此前标为 Extracted，但仍混入候选表，所选图注候选表污染率4/4；新版为0/4。
11项条件全部保留只证明文本未遗漏，不能替代数学语义校验。全文召回率未测量，图内显式依赖召回率为0/2，禁止隐藏此限制。

## 稳定性和数据库

```json
{
  "fresh_pdf_parses_identical": true,
  "cached_repeat_identical": true,
  "no_duplicate_candidates": true,
  "old_records_unchanged": {
    "sources": true,
    "candidates": true,
    "events": true,
    "verified": true
  },
  "before_counts": {
    "sources": 8,
    "candidates": 53,
    "events": 120,
    "verified": 0
  },
  "after_counts": {
    "sources": 8,
    "candidates": 57,
    "events": 120,
    "verified": 0
  }
}
```

备份：data\backup-before-v022.sqlite。没有删除旧来源、候选、事件或审核记录。JSON负载新增字段；无需ALTER已有业务表。
独立重读PDF两次结果相同；重复运行复用缓存且不新增候选。原有 v0.2.1 解析仍可按版本读取。