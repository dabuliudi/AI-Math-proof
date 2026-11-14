# Abundant Numbers 真实论文解析报告

论文：Learning about Proof with the Theorem Prover LEAN: the Abundant Numbers Task；Athina Thoma、Paola Iannone；DOI 10.1007/s40753-021-00140-1。

来源 ID：8；PDF 页数：30；SHA256：`c60c9c32ab6e8daf04e31c624d385ad92a6b97973518050cfcaaedbcfdc5a5da`。
规则识别 25 个片段，类型计数：{'Proof': 13, 'Example': 1, 'Conjecture': 8, 'Definition': 3}。
不确定对象：14。
全部验证状态为 unknown，全部未形式化；未调用 AI 或 Lean 为这些论文对象作证明。

## 原文核对与关键边界

第 28 页 Appendix 2 的原始任务确实写 any k ∈ N；第 9 页讨论 k=1 为假、随后要求 k>1。系统保留两个独立的原文对象，未把原题改写成更正后的命题。
完全数和丰盈数定义采用所有因数的和与 2n 比较。没有替换为真因数和，也没有自行补写整数正性条件。
第 14 页 Fig.8 是手写证明图，文字层仅保留图注和对 Lemma 3、4 的提及。未使用 OCR，故没有伪造引理内容。第 15 页作者叙述中的步骤被保存为 uncertain 原文分句；顺序不是逻辑依赖。
字符偏移基于该次 pypdf 输出的每页原始字符串，Python Unicode 字符索引，区间为 [start,end)，不是 PDF 字节偏移或排版坐标。页码为物理页码，首张为 1。

## 候选与来源

|编号|类型|阶段|页码|字符区间|标题（摘要）|
|---|---|---|---|---|---|
|29|Proof|Extracted|4|66–166|Fig. 1 LEAN online interface - Multiple screenshots of a complete and correct proof illustrating the|
|30|Example|Extracted|8|2196–2226|Fig.4 The abundant number task|
|31|Proof|Extracted|9|563–677| If a student realised that the statement is false for k = 1, they|
|32|Proof|Extracted|13|66–136|Fig.5 LEAN user student Leonardo - formal-rhetorical part of the proof|
|33|Proof|Extracted|13|137–208|Fig.6 No LEAN user student Nathan - formal-rhetorical part of the proof|
|34|Proof|Extracted|13|1049–1117|Fig.7 No LEAN user student Ned - formal-rhetorical part of the proof|
|35|Proof|Extracted|14|66–136|Fig.8 LEAN user student Leonardo - formal-rhetorical part of the proof|
|36|Proof|Extracted|15|66–165|Fig. 9 No LEAN user student Nathan - formal-rhetorical part of the proof. (During the interview the|
|37|Proof|Extracted|15|798–915| He then replaces kn and n with the sum of their divisors (since|
|38|Proof|Extracted|15|949–1015|Fig.10 LEAN user student Louis - problem centred part of the proof|
|39|Proof|Extracted|17|1358–1430|Fig.14 No LEAN user student Nataly - formal-rhetorical part of the proof|
|40|Proof|Extracted|18|66–138|Fig.15 No LEAN user student Norman - formal-rhetorical part of the proof|
|41|Proof|Extracted|20|66–136|Fig.17 No LEAN user student Nataly - problem-centred part of the proof|
|42|Proof|Extracted|20|1220–1290|Fig.18 No LEAN user student Norman - problem-centred part of the proof|
|43|Conjecture|Candidate|28|278–306|1. Prove that|
|44|Definition|Candidate|28|351–412|The f is called fine if it has a root|
|45|Conjecture|Candidate|28|467–574|(a) Let f,g : R → R be fine functions. Prove that f + g is a fine function.|
|46|Conjecture|Candidate|28|575–712|(b) f : R → R be a fine function. Let g : R → R be a function defined by|
|47|Definition|Candidate|28|713–789|3. An abundant number is an integer n whose divisors add up to more than 2n.|
|48|Definition|Candidate|28|790–859|A perfect number is an integer n whose divisors add up to exactly 2n.|
|49|Conjecture|Candidate|28|867–922|(a) If n is perfect, then kn is abundant for any k ∈ N.|
|50|Conjecture|Candidate|28|923–974|(b) If p1 and p2 are primes, then p1p2 is abundant.|
|51|Conjecture|Candidate|28|975–1049|4. Let A ⊂ R and f : A → R. The function f is preserved in A if f( A )⊂ A.|
|52|Conjecture|Candidate|28|1057–1167|(a) Prove that if f is strictly decreasing function, then there is a fine set A such|
|53|Conjecture|Candidate|28|1168–1347|(b) Let f,g : R → R be functions and a ⊂ R. Suppose x × y ∈ A for all|

## 关键对象原文

### 候选 31 · 第 9 页

```text
 If a student realised that the statement is false for k = 1, they
were then prompted to provide a proof for k> 1.
```

### 候选 37 · 第 15 页

```text
 He then replaces kn and n with the sum of their divisors (since
n is perfect) and moves on to multiply each one byk.
```

### 候选 47 · 第 28 页

```text
3. An abundant number is an integer n whose divisors add up to more than 2n.
```

### 候选 48 · 第 28 页

```text
A perfect number is an integer n whose divisors add up to exactly 2n.
```

### 候选 49 · 第 28 页

```text
(a) If n is perfect, then kn is abundant for any k ∈ N.
```

## DAG 结果

节点 25，可靠依赖边 0。
没有仅因共现创建依赖边。下列引用保留为 uncertain，等待图片转录或人工指认：

```json
[
  {
    "reference": "Lemma 3",
    "status": "uncertain",
    "page": 14,
    "start": 1597,
    "end": 1604,
    "context": "lso concerned, once a\nclass of objects are introduced, with defining exactly where the objects belong to.\nThis is clear in the start of the proofs of Lemma 3 and Lemma 4. Figure 9 shows\nthe final outcome of the final proof written by Nathan. In this case the student had\nresorted to examples first of all to",
    "reason": "只有正文引用，未找到唯一的声明；不建立依赖边"
  },
  {
    "reference": "Lemma 4",
    "status": "uncertain",
    "page": 14,
    "start": 1609,
    "end": 1616,
    "context": "d, once a\nclass of objects are introduced, with defining exactly where the objects belong to.\nThis is clear in the start of the proofs of Lemma 3 and Lemma 4. Figure 9 shows\nthe final outcome of the final proof written by Nathan. In this case the student had\nresorted to examples first of all to understand ",
    "reason": "只有正文引用，未找到唯一的声明；不建立依赖边"
  }
]
```

完整候选、上下文、步骤、DAG 和偏移见同目录 abundant-numbers.json。

## 局限

规则分数不是语义正确率；未编号的叙述可能漏检。跨页内容不自动拼接，扫描页及手写图不做 OCR；数字公式的文本顺序须人工核对。缺少声明正文时宁可不建立边。