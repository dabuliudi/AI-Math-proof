# Mason–Stothers Lemma 2：独立语义对齐与证明实验

## 结论与证明来源

当前声明忠实表达论文Lemma2。定义域为任意域k上的一元多项式，a≠0，b任意；a/rad(a)在k[X]中整除W(a,b)。不存在CharZero、a/b互素、b≠0或导数非零的前提。

本实验分类 **New Proof：新编写的组合证明脚本**，不是新数学结果、不是全球独创性声明。脚本明确复用Lemma1（其来源仍是Theorem Reuse），并利用整除见证构造线性组合，不直接应用或复制现成Wronskian整除定理的实现。没有外部AI API调用。

语义审核者为助手；不是外部数学家签字。对齐确认与Lean验证不代替真人知识库审批。approval_status保持pending。

## 原始声明与定位

论文：Formalizing Mason–Stothers Theorem and its Corollaries in Lean 4，Jineon Baek、Seewoo Lee；本地2408.15180v2.pdf。

第4页，Lemma2原始文字层，字符区间[1364,1429)：

```text
Lemma 2.For any nonzeroa∈k[t],a/rad(a)dividesW(a, b) =ab ′ −a ′b.
```

完整数学含义：对任意a,b∈k[t]且a≠0，a/rad(a)整除W(a,b)=ab′−a′b。b的类型和任意性由同页Definition2“两多项式a,b∈k[t]”及Lemma2语境确定。不能把前面的Davenport定理特征零假设带入本引理。

第2页Definition1：k任意域，rad(a)为不同首一不可约因子之积。第4页Definition2规定Wronskian的次序和符号为ab′−a′b。已核对同页渲染图；此处“divides W(a,b) = ...”是对W的展开说明，而不是声称多项式商与W相等。

## 逐项语义比较

|要素|论文|Lean|结论|
|---|---|---|---|
|系数域|任意域k|[Field k]|一致，任意特征|
|多项式|k[t]中的a,b|a b : k[X]|一致，一元多项式而非有理函数|
|非零|a≠0|ha : a≠0|保留原假设|
|b|任意多项式|无非零、互素等额外条件|一致|
|radical|不同首一不可约因子乘积|UniqueFactorizationMonoid.radical|规范化因子去重，含义相同|
|商|a/rad(a)|EuclideanDomain的多项式商|rad(a)整除a，故为精确商|
|导数|形式导数|Polynomial.derivative|一致，不是分析导数|
|Wronskian|ab′−a′b|Polynomial.wronskian a b|定义展开完全相同|
|整除|存在多项式见证|∃r:k[X], W(a,b)=(a/rad(a))*r|一致|
|判等|未讨论计算实现|DecidableEq k|Lean定义所需实例，经典逻辑可提供；不限制数学上的域|

边界检查：b=0、b为常数、a为非零常数、正特征导致a′或b′为零均被允许。结论可为“非零商整除零”，不构成问题。a=0不属于纸面命题，当前目标仍不将其加入原命题。

## 检索发现与采用路线

Mathlib有直接等价结论的更强版本divRadical_dvd_wronskian_left（Polynomial/Radical.lean:58），不要求a≠0；右侧版本在66行，不能与本任务互换。若选择直接调用前者，应分类Theorem Reuse。

本次没有选择直接复用路线。已知作者在Mathlib中的直接证明使用整除乘积与dvd_sub；当前脚本采用显式见证构造并单独建立适用于任意Ring的线性组合引理，不复制该实现。由于直接复用可行，本任务并非被迫拆分；为检验Lemma1复用和真实依赖规划，主动使用以下三个子目标：

1. q=a/rad(a)整除a：复用EuclideanDomain.divRadical_dvd_self并展开divRadical。
2. q整除a′：调用原样重验的mathlib2_mason_lemma1 a ha。
3. 若q∣x且q∣y，则q∣xr−ys：取x=qu、y=qv，见证u*r−v*s；仅用分配律和结合律。此子引理不需要交换环。

最后取x=a、y=a′、r=b′、s=b，展开Wronskian，得到目标。

## 审计与文件

- 源码：lean/Research/Lemma2.lean。其中包含不变的Lemma1声明以便独立编译重验，没有覆盖原Lemma1文件。
- 检索报告：lemma2-retrieval.json，保存真实声明、源码位置、哈希、采用/未采用标记。
- 实际Proof DAG：lemma2-dag.json及lemma2-dag.md；边区分定义展开与证明使用，包含来源和位置。仅列显式直接依赖，不冒充内核全部传递依赖。
- 完整运行记录：lemma2-result.json，关联每次唯一命名的编译日志、公理逐声明审计、原文与规范化哈希、历史保留检查。
- 测试结果：tests-lemma2.txt。

New Proof只描述新编写的组合脚本。局部商整除引理和Lemma1仍标Theorem Reuse。首次实际编译成功，未制造虚假失败案例；若后续运行失败，唯一命名日志照常保留，状态不会标为已验证，优先检查工具链、模块缓存、名称/API及完整编译错误。

结论绑定论文、候选版本、模板源码、引用的Mathlib定义和报告哈希；改变规范化文本、模板或关键定义后必须重新审核。真人知识库审批不在本次自动执行范围内。
