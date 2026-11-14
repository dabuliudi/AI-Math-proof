# Mason–Stothers Lemma 3：数学语义与证明来源验收

结论：当前Lean声明忠实对应论文Lemma3的degree≥1结论。分类为New Proof（本次新编写的Lean组合脚本，不主张新数学结果）。首次实际编译成功；完整逐声明公理审计及后续重验见lemma3-result.json关联的日志。

## 原文与完整证明说明

来源是2408.15180v2.pdf第7页。已读取文字层并核对渲染图lemma3-page7.png。声明原文为：

> For any field k and a polynomial a ∈ k[X] of degree ≥ 1, the degree of its radical rad(a) is also at least one.

论文随后给出的是形式化证明说明：取a的素因子p，利用a与rad(a)有相同素因子，得到p∣rad(a) iff p∣a；继而证明非零a为单位当且仅当rad(a)为单位；最后特化到k[X]，用非零多项式为单位当且仅当次数为0，推出Lemma3。纸面还展示prime_dvd_radical_iff、radical_isUnit_iff及natDegree_radical_eq_zero_iff声明。

完整声明及其后全部证明说明、代码声明（直到脚注前）原样存入lemma3-source.json，有页码、字符区间及PDF哈希。当前数据库候选89的original_statement还包含第一段证明说明；本次不覆盖原字段，另行区分statement与proof_source，不把这些说明误当额外数学假设。

## 定义、量词与边界

∀域k，∀a∈k[X]，deg(a)≥1 ⇒ deg(rad(a))≥1。次数正自动排除a=0和常数，无需新增非零假设。没有CharZero、平方自由、首一或可分性要求。

radical采用论文第2页Definition1及第6页定义：不同首一不可约因子的乘积。Mathlib的normalizedFactors→toFinset→prod与此一致，不是理想radical。k[X]为一元多项式环；k任意特征。DecidableEq k是定义所需实例，可由经典逻辑提供。

Lean degree : WithBot ℕ，零多项式次数是⊥；natDegree : ℕ将零多项式次数设为0。我们同时证明natDegree版及**degree版最终目标**，通过degree_eq_natDegree、natDegree_pos_iff_degree_pos和WithBot.coe_le_coe连接，不能默默把两者对零的定义当成一样。radical_ne_zero保障结果侧的degree转换。

若a=0，degree≥1前提为假，natDegree≥1也为假；Mathlib的rad(0)=1不造成反例。非零常数前提为假。正特征及重复不可约因子不影响结论。

## 新构造路线与分层

本次没有复制作者Lean实现，也没有调用论文所列的最终零次数等价定理（本地版本检索未找到同名声明）。选择以下路径：

1. 非零多项式且natDegree=0，则IsUnit。由degree/natDegree桥接及isUnit_iff_degree_eq_zero证明。
2. 非零a且rad(a)为单位，则a为单位。使用radical的幂等性rad(rad(a))=rad(a)、单位radical=1及radical_eq_one_iff。不重新实现作者的逐素因子证明。
3. 若natDegree(a)≥1，假设natDegree(rad(a))=0，步骤1和2推出a为单位，从而natDegree(a)=0，与前提矛盾。
4. 将非零自然数次数转换为≥1，得到natDegree版本。
5. 将纸面degree前提转换为natDegree前提，再将结论转换回degree。

新增4个中间声明（前三个实质子引理，加一个natDegree桥接目标），最终第5个声明是论文degree目标。依赖边从实际源码的声明引用提取，随后通过真实Lean重验；拓扑排序和深度可复算。

## Lemma 1、2的关系

本引理不需要导数或Wronskian。Lemma1、2不能直接给出radical次数的下界；没有证据表明它们参与本次证明，因此本DAG不连入这两个节点。它们在Mason–Stothers主定理中属于另一条整除证明支线；Lemma3用于后续非恒定radical的正次数分析。数学相关不等于本证明的依赖。

## 每步生成来源及自动化边界

- 本次证明分解、Lean语句及报告：**AI生成，指当前对话中的助手编写**；不是项目里某个模型API被调用的记录。
- 具体库声明：**Mathlib定理复用**，声明名、真实源码行及哈希见检索JSON。
- 中间引理连接：**已有Lemma组合**，指本次已编译的局部声明，不含未使用的Lemma1/2。
- 常规Nat不等式、改写、decide及依赖图抽取：**预置规则/既有Lean基础设施**，不是新的数学发现。
- 人工编写：本次没有真人数学家补写证明；复用库代码的原作者在源码许可证中注明，不冒称助手原创。

候选代码在本次会话中生成后固化为可重复执行模板；按钮重跑模板不等于再次AI推理。external_ai_api_calls=0，autonomous_reasoning_engine=false。当前系统没有通用自动证明分解器；本实验验证了助手编写的分层方案能被系统持久化、编译和审计，不能据此宣称系统已自主发现证明。

## 成本口径和验收

成本报告见lemma3-costs.json/md。新增Lean行数统计非空且非import/open/#print行，另列物理行；Lemma2剔除原样复用的Lemma1前缀。复用数量统计显式命名的数学主干Mathlib声明，不含全部隐式实例、simp内部依赖及Lean基础Nat/逻辑API；全部口径注明，不作为真实token、GPU或人力成本。

证明深度是数学主干DAG最长路径的**边数**，同时列只算局部新声明的深度；不包含Mathlib内部传递证明。历史日志数包括测试重跑，不能冒称独立搜索轮数。编译耗时来自保存的真实日志，首次缓存与机器负载使横向比较受限。会话生成时间、token与人工耗时没有可靠计量，标unknown。

最终状态仅在语义对齐及真实编译/公理审计均通过后更新。所有旧论文、Lemma1/2代码与历史保留；不自动批准知识库入库。审核者为助手，真人批准仍pending。
