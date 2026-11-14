# Mason–Stothers Lemma 1 独立数学语义对齐验收

结论：**论文 Lemma 1 与当前 Lean 声明在其原始非零多项式定义域上忠实对应，可以确认对齐。** Mathlib 原始定理的适用范围更广，不能说它与论文在全部输入上的假设完全相同。当前包装声明保留论文非零假设，消除了这一范围差异。证明来源始终为 **Theorem Reuse**，不是新的独立证明。

审核者：本次助手依照用户明确要求，独立核读论文与源码。此报告不是外部数学家签名，也不冒充真人知识库审批。Lean验证形式化声明，本文负责自然语言与形式化之间的语义比较；Lean本身不能检验英语理解是否正确。

## 1. 原始命题与语境

论文文件：2408.15180v2.pdf，Jineon Baek、Seewoo Lee，Formalizing Mason–Stothers Theorem and its Corollaries in Lean 4。

第4页 Lemma 1 完整数学表述：

> For a nonzero polynomial a ∈ k[t], a/rad(a) divides a′.

逐页文字层原样切片（第4页，Unicode字符区间[946,1004)）：

```text
Lemma 1.For a nonzero polynomiala∈k[t],a/rad(a)dividesa ′.
```

已核对第4页渲染图，而非只凭文字层猜测撇号或分数。第2页Definition 1规定k是任意域，rad(f)为f的所有不同首一不可约因子的乘积；第2页Theorem 1解释撇号是关于t的形式导数。第6页§4.2进一步解释规范化因子及去重，第8页明确解释除法是多项式欧几里得除法，并给出作者的divRadical及引理Lean表述。

第4页前面的Davenport定理才要求特征零；该条件不能跨章节错误附加给Lemma1。Lemma1没有要求a为首一、非常数、平方自由，也不要求互素的第二个多项式。

## 2. 本地 Mathlib 原始声明与定义

固定工程：Lean/Mathlib v4.24.0；精确文件、清单及哈希见配套JSON，避免只依赖版本名。

`Mathlib/RingTheory/Polynomial/Radical.lean` 第20行环境、31行声明：

```lean
variable {k : Type*} [Field k] [DecidableEq k]
theorem divRadical_dvd_derivative (a : k[X]) :
    divRadical a ∣ derivative a := by
  -- 原文件中是完整证明；此展示仅摘录声明，未作为编译源码。
```

原文件证明对零、单位、素数幂和互素乘积作归纳，不依赖CharZero。此次复用该声明，未复制为所谓AI独立证明。

`Mathlib/RingTheory/Radical.lean` 第67、155、399行：

```lean
def primeFactors (a : M) : Finset M := (normalizedFactors a).toFinset
def radical (a : M) : M := (primeFactors a).prod id
def divRadical (a : E) : E := a / radical a
```

前两者属于UniqueFactorizationMonoid命名空间，第三个属于EuclideanDomain。对域上的多项式，规范化取唯一的首一伴随多项式；FieldDivision.lean中的monic_normalize、normalize_eq_self_iff_monic及因子成员性质支持这一识别。toFinset去掉重数，乘积得到与Definition1相同的radical，而非理想的根基，也不是把重因子保留下来的乘积。

radical_dvd_self和radical_ne_zero保证除数非零且整除原多项式；radical_mul_divRadical明确给出radical a * divRadical a = a。因此这里的欧几里得商是精确商，不是带余数后丢失信息的近似，也不是系数逐项相除。

`Mathlib/Algebra/Polynomial/Derivative.lean` 第42行定义形式导数，第55行coeff_derivative给出次数n的系数为原n+1次系数乘n+1。`Mathlib/Algebra/Divisibility/Basic.lean` 第53行dvd_def将p ∣ q解释为存在同一多项式环中的r，使q = p*r。

## 3. 逐项比较

|项目|论文|当前Lean声明|判断|
|---|---|---|---|
|系数域|任意域k|[Field k]|一致；无CharZero限制|
|多项式类型|k[t]|Polynomial k，即k[X]|变量名称不同，均为一元多项式环|
|量词|对任意非零a|参数a及a≠0假设|一致|
|radical|不同首一不可约因子之积|规范化因子去重后的乘积|一致|
|商|a/rad(a)|多项式欧几里得除法|rad(a)整除a，故为同一精确商|
|导数|形式导数a′|Polynomial.derivative a|一致，正特征也允许导数为零|
|整除|在k[t]中整除|存在r:k[X]使a′=(a/rad(a))*r|一致；不是k(t)中平凡的域整除|
|非零条件|a≠0|显式保留(_ha : a≠0)|一致，即使证明不需要使用该假设|
|判等实例|未讨论算法实现|[DecidableEq k]|Lean实例要求；经典逻辑可为任意k提供，不排除数学上的域|

非零常数被允许：rad(a)=1，导数=0，a整除0，结论成立。正特征下某些非常数导数也为0，整除0仍成立，无需增加可分性或导数非零假设。

## 4. 差异与原文细节

1. Mathlib引理不要求a≠0。Mathlib定义rad(0)=1，divRadical(0)=0，导数0；因此其扩展到零也成立。论文Definition1和Lemma1仅在非零处陈述。我们确认的是当前受限包装声明，**不是声称原始API的适用范围与论文逐字一致**。
2. DecidableEq是额外的形式化实例参数；使用经典逻辑即可取得。它不构成有效可计算性的额外数学承诺，也不改变本报告采用的经典数学解释。
3. 第4页纸面证明先写a=u∏pᵢ^eᵢ，随后将a/rad(a)写为∏pᵢ^(eᵢ−1)，没有在该等式右侧保留单位u。按第2页的首一radical约定，严格等式应保留u；两表达式相差单位，整除性质相同。因此这一纸面证明中的单位因子简写不改变Lemma1的结论。当前Lean代码没有照抄该不严格等式，实际使用精确定义a/rad(a)。原文和提取文本均未修改。
4. 论文用t、X、x记同一多项式不定元，形式化统一用X；不存在换为多元多项式或有理函数的情况。

## 5. 当前实际编译源码

```lean
import Mathlib.RingTheory.Polynomial.Radical
open Polynomial UniqueFactorizationMonoid EuclideanDomain
theorem mathlib2_mason_lemma1 {k : Type*} [Field k] [DecidableEq k]
    (a : k[X]) (_ha : a ≠ 0) :
    a / radical a ∣ derivative a := by
  classical
  simpa only [divRadical] using (divRadical_dvd_derivative a)
#print axioms mathlib2_mason_lemma1
```

这仅将divRadical定义展开后应用已有定理。没有sorry/admit、新公理或独立新证明的主张。重新运行的真实退出码、编译器版本、输出、公理及源码哈希存入lemma1-alignment-result.json所指向的编译日志。

## 6. 允许的状态变化

对齐记录绑定candidate_id、原文、规范化文本、revision、模板源码、PDF、Mathlib关键定义文件及lake-manifest哈希。任何绑定内容变化后，重新编译不能继续沿用此确认。

语义对齐已确认时candidate_alignment=confirmed；只有本次真实Lean编译且公理门禁也通过，candidate_verified才能为true。失败尝试仍完整保留。生产知识库的human approval保持pending，不因助手核读自动变成真人批准。
