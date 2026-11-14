# Lemma 3 数学语义逐项验收 — PASS

本报告以当前原始PDF重新提取的第2、6、7页及第7页重新渲染图为依据，不沿用旧摘要推定条件。完整原始页文本、PDF哈希与声明偏移见paper-source.json；页图为paper-page7.png。

论文第7页完整声明：

> Lemma 3. For any field k and a polynomial a ∈ k[X] of degree ≥ 1, the degree of its radical rad(a) is also at least one.

论文第2页Definition 1限定非零f∈k[X]，rad(f)是不计重数的所有首一不可约因子的乘积。第6页§4.2将定义推广到可消去、可交换、带零、唯一分解、带规范化的乘法幺半群，使用normalizedFactors→toFinset→prod。该页明确说明常数包括零的radical等于1。这些是定义的背景，不是要求域额外满足零特征。

当前真实文件D:/mathproof/lean/Research/Lemma3.lean第31行起的最终声明：

```lean
theorem mathlib2_mason_lemma3 {k : Type*} [Field k] [DecidableEq k]
    (a : k[X]) (h : (1 : WithBot ℕ) ≤ a.degree) :
    (1 : WithBot ℕ) ≤ (radical a).degree
```

|检查项|原文|Lean对应|判定|
|---|---|---|---|
|定义域|任意域k|`{k : Type*} [Field k]`|PASS|
|量词|任意k、任意a∈k[X]|隐式全称k、实例Field及显式a|PASS|
|多项式类型|一元k[X]|`Polynomial k`的记号`k[X]`|PASS|
|特征条件|未限制特征|没有CharZero或其他特征条件|PASS|
|前提|deg(a)≥1|`(1 : WithBot ℕ) ≤ a.degree`|PASS|
|结论|deg(rad(a))≥1|`(1 : WithBot ℕ) ≤ (radical a).degree`|PASS|
|radical含义|不同首一不可约因子乘积|UniqueFactorizationMonoid.radical，非Ideal.radical|PASS|
|非零条件|由正次数隐含；Definition 1原始适用域为非零|`degree≥1`排除a=0；无需额外假设|PASS|
|零多项式|不满足前提|degree(0)=⊥；natDegree(0)=0；两者均不能≥1|PASS|
|常数边界|不满足次数前提|非零常数degree=0，不能≥1|PASS|
|重因子/首一条件|无额外要求|没有IsSquarefree、Monic要求|PASS|
|等号边界|包括degree=1|使用≤，未改成严格大于1|PASS|
|DecidableEq|论文未列此数学假设|定义/实例所需技术参数；经典逻辑可提供，不排除任何域|PASS，技术差异已记录|
|degree和natDegree|原文写degree|最终目标确为degree；局部引理用natDegree并显式转换|PASS|
|强化或弱化|原命题|没有将任意域改成特定域；没有删去次数前提或加入数学实质前提|PASS|

Lean中的次数为WithBot ℕ，非零多项式degree可通过degree_eq_natDegree转换为natDegree的嵌入。当前证明先用natDegree_pos_iff_degree_pos将前提转为natDegree≥1；得到radical的natDegree≥1后，使用radical_ne_zero和degree_eq_natDegree转换回degree。零的两种次数定义没有被混为一谈。

论文证明说明从素因子集合一致性出发，建立非零a与rad(a)同时为单位，再利用域上多项式单位与零次数的对应。当前实现用radical幂等性、单位的radical等于1、radical_eq_one_iff建立“rad(a)为单位⇒a为单位”，只取目标所需方向；随后反证并进行次数转换。这是不同的库定理组合路线，逻辑上足以证明同一个声明，不要求逐行复刻作者的论证。

当前候选89的original_statement还包含第一段证明说明。它不是一个精确仅含声明的文本片段；原始声明与证明在本次paper-source.json中分别定位。此数据清洁问题不改变当前Lean目标的数学等价性，也不应靠修改原文字段掩盖。

本轮数学等价性判断来自重新核读。现有alignment_record的哈希校验只能证明记录与文件仍相符，不能单独证明数学等价；本次没有更新该记录，也没有批准知识库入库。
