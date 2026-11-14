# Mathlib2 v0.3.1 — Lemma 3 独立技术验收

结论：**Lemma 3 的数学对应、真实Lean编译和允许公理范围通过验收；不能据此验收为系统自主证明规划能力提升。**

本轮首先只读核查原始材料，再在独立验收目录保存新证据。原始应用代码、测试代码、数据库及历史实验记录没有修改。对219个既有文件进行前后哈希比较，变更数为0；受保护目录没有新增文件。测试运行于独立副本，副本应用和测试源码与原件逐字节相同。见[preservation.json](preservation.json)。

## 验收状态

|交付项|状态|证据与限制|
|---|---|---|
|1. 数学语义对齐|PASS|重新读取原PDF第2、6、7页，逐项比较域、量词、定义、特征和次数；见semantic-report.md|
|2. Mathlib检索|PASS|真实Lean完整类型、源位置及实际证明项交叉验证；补齐基础定理与命题性实例，见mathlib-report.md|
|3. 证明来源分类|PASS|当前是固定模板执行+库复用+局部引理组合；历史逐行作者身份及“绝未复制”排他断言为NOT VERIFIED|
|4. Proof DAG|PASS（限定范围）|原14节点15边全部真实使用且无环；补充115节点264边的完整本地直接依赖图；Mathlib内部全部传递闭包NOT VERIFIED|
|5. Lean源码路径|PASS|D:/mathproof/lean/Research/Lemma3.lean，当前内容与历史编译源码一致|
|6. 本轮真实编译|PASS|三个原始Lean文件重新编译，返回码均0；不是引用历史成功日志|
|7. 公理审计|PASS|Lemma 3五个声明的传递公理集合均只有propext、Classical.choice、Quot.sound|
|8. 回归测试及历史保留|PASS|13项相关测试全部通过，无跳过；Lemma 1/2数据库记录与实验前备份一致|
|9. 新增代码行数|PASS|既有Lemma 3为44物理行、30实质行；本轮产品代码新增/修改均0，仅新增隔离验收材料|
|10. 问题清单|PASS（已披露）|见下方；自主规划能力与历史作者排他性证据不能宣称通过|

PASS仅适用于所注明的检查范围。没有将“没有发现问题”当作对所有历史事实的证明，也没有更改候选状态或批准知识库入库。

## A. Lemma 3 是否真正通过 Lean 验证？

**PASS：是。** 使用原文件直接重编译，Lean返回码0，耗时6.342秒，stderr为空。五个声明均执行#print axioms并通过允许公理检查，无sorry、admit、sorryAx或自定义未经批准公理。

最终声明是任意域k上，对a∈k[X]，degree(a)≥1推出degree(radical a)≥1。没有加入零特征假设。DecidableEq是技术实例，可由经典逻辑提供；最终目标确实用degree，而非悄悄替换成natDegree。

详见[逐项语义报告](semantic-report.md)、[原始论文重新提取记录](paper-source.json)、[第7页原页渲染](paper-page7.png)、[五个声明的公理汇总](hashes-and-axioms.json)。

## B. 证明属于哪种来源？

**PASS：当前执行方式是Developer Template + Mathlib Reuse + Lemma Composition。** 证明分解与Lean源码已在mathlib2/lemma3.py的SOURCE中预先写好。run_lemma3.py和check_template运行时读该字符串、写入文件、执行Lean，并不调用项目AI网关生成证明。

开发期来源依据历史会话及元数据记为AI助手编写；这不等于项目运行时自主生成。Lean策略、改写、实例合成属于现有规则基础设施。本次执行没有真人补写证明的证据，也没有项目AI API调用。逐行标签见[证明来源报告](provenance-report.md)及[30行来源JSON](provenance-steps.json)。

未直接导入论文作者的独立仓库；但**确实复用了包含论文作者贡献的Mathlib源码**。RingTheory/Radical.lean头部列有Jineon Baek、Seewoo Lee等，因此不能声称“完全没有使用作者代码”。是否在最初创作时逐字复制公开实现，单靠author_code_copied=false无法证明，结论为NOT VERIFIED；本轮没有把该自述字段当作独立证据。

## C. DAG 是否真实反映最终证明依赖？

**PASS：原数学主干图真实，但不是完整内核依赖图。** 本次没有仅重复字符串匹配，而是让Lean从已编译声明的ConstantInfo.value及type提取常量。原图全部15条边都出现在对应证明项中，全部14节点都能反向追溯到最终目标；无环、无推测边、无展示用孤立节点。Lemma 1和Lemma 2未参与本证明。

原图明确排除了基础逻辑、Nat API和隐式实例。本次扩充为**115节点、264边**的本地直接依赖DAG，区分类型依赖与证明项依赖，Mathlib和Lean基础声明作为边界叶节点。所有节点的完整声明、源码位置、依赖类别与参与情况均已列出。没有把库内部所有传递证明都展开，因此不声称给出整个Mathlib内核闭包。

- [完整DAG报告：全部节点及边](dag-report.md)
- [原15条边的逐边验收、数学理由及源码引用](backbone-dag-audited.json)
- [全部本地直接依赖DAG](complete-local-dag.json)
- [完整声明与来源位置](all-direct-declarations.json)
- [Lean证明项提取原始日志](inspection-v2-compile.json)

paper_context在旧图中只是论文第7页整体上下文，并非作者逐条引用了本次Lean分解。本报告明确区分论文原文证据和本次形式化证明的依赖证据。

## D. 是否展示了比 Lemma 1、2 更强的自动规划能力？

**NOT VERIFIED：没有足够证据支持；当前执行机制没有展示这种提升。**

Lemma 3有更多中间引理和更深的DAG，只能证明系统能够编译、记录和展示更复杂的预先写好方案。audit_names、REFS和完整SOURCE都是开发期指定的；DAG是对已完成证明做引用抽取。运行时没有从未解决目标中选择候选、探索分解、根据失败反馈修改证明的过程。编译速度也受缓存影响，不能作为规划能力指标。

## E. 距离 AI 自主数学形式化还差什么？

当前尚缺可审计的运行时闭环：从新文献恢复语义与假设，检索并选择可用声明，动态提出分解和证明代码，调用Lean，根据错误修改方案，在预算内持续搜索，并分别记录模型请求/响应、版本、每次失败和成功条件。还需要未预置答案的新任务基准、来源与数据泄漏控制，以及独立语义复核与人工批准门槛。

这些是未实现或未验收的能力，不能用本轮固定模板编译成功代替。

## Mathlib 检索结果与完整声明

原报告9项是显式数学主干，并非所有实际出现的Mathlib定理。本轮从实际证明项取出**18个直接Mathlib定理/命题性实例**：原9项、基础顺序定理lt_of_lt_of_le，以及8个实例定理。完整量词、隐式参数、实例条件、文件、行号、复用方式和用途都在[检索报告](mathlib-report.md)与[机器可读声明清单](mathlib-theorems.json)。没有发现虚构声明或只因关键词相似便认定复用的情况。

其余Lean核心定理与定义/实例也保存在all-direct-declarations.json。18不是所有库内传递定理的数量；9也不是“完全未依赖其他基础设施”的数量。

## 本轮真实编译记录

Lean：4.24.0，x86_64-w64-windows-gnu，commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b。

Mathlib：manifest指定v4.24.0，revision f897ebcf72cd16f89ab4577d0c826cd14afaafc7；本地git HEAD匹配，git status为空。见[工具链记录](toolchain.json)。

在D:/mathproof/lean作为工作目录运行：

```powershell
& 'D:\mathproof\.tools\lean-4.24.0-windows\bin\lake.exe' env lean -M 2048 'D:\mathproof\lean\Research\Lemma3.lean'
```

|原始文件|返回码|本轮秒数|stderr|完整stdout/stderr与命令|
|---|---:|---:|---|---|
|Lemma1.lean|0|5.793|空|[compile-lemma1.json](compile-lemma1.json)|
|Lemma2.lean|0|6.180|空|[compile-lemma2.json](compile-lemma2.json)|
|Lemma3.lean|0|6.342|空|[compile-lemma3.json](compile-lemma3.json)|

Lemma 3五个声明的公理均为propext、Classical.choice、Quot.sound。#print axioms检查传递公理依赖，故不是只搜索本地源码是否出现sorry。三个文件当前源码与历史保存的source逐字对应，规范化换行后的SHA256也一致。Windows文件原始字节的CRLF哈希与LF字符串哈希分别保存，未把这种换行差异误判为篡改。

## 回归与保留验证

重新运行原有test_alignment、test_formalization、test_lemma2和test_lemma3：**13项，21.493秒，全部通过，无跳过**。其中三个Lemma的集成测试都实际调用Lean。现有基础设施故障单元测试会模拟版本查询超时，它只验证错误处理，没有用于数学证明验收；所有数学验证均来自真实编译。

测试源码和应用源码完整复制且哈希一致。隔离执行器仅将Lake的工作目录指回已安装依赖环境，待编译新文件、临时数据库、测试输出和新实验日志全部位于独立副本；没有替换编译器结果。该隔离方式与直接编译原始文件构成两套独立证据。

- [完整回归输出](regression-v2.txt)
- [回归配置、真实进程命令和结果](regression-v2.json)
- [本轮前后文件保留检查](preservation.json)
- [与before-lemma3.sqlite比较Lemma 1/2历史](lemma12-history-comparison.json)
- [源码哈希及公理汇总](hashes-and-axioms.json)

与Lemma 3开始前的备份相比，Lemma 1/2的2条候选、2条状态、5条proof_runs及12条workbench_history均逐行相同；未覆盖或删除。当前候选85、87、89仍保留confirmed、candidate_verified=true及pending入库状态。本轮没有写入这些状态。

## 代码量

|实验|文件物理行|实质Lean行|相对前一复用前缀的新增行|
|---|---:|---:|---:|
|Lemma 1|8|5|5|
|Lemma 2|32|21|16（包含的Lemma 1前缀5行不重复计）|
|Lemma 3|44|30|30|

实质行排除空行、import、open和#print；包含声明及证明。这是文件统计，不是模型token或自主推理成本。本轮产品源代码新增0、修改0；独立目录中的Lean检查探针和验收报告不属于产品实现。

## 尚存问题与失败保留

1. **自动规划能力NOT VERIFIED。** 当前证明与分解固定，深DAG不证明系统自主生成方案。
2. **历史创作来源的排他断言NOT VERIFIED。** author_code_copied、human_authored等字段只是元数据，无逐行签名或完整生成记录；不能证明从未人工编辑或复制。
3. **语义确认不是算法判等。** run_lemma3.py硬编码conclusion=confirmed，valid_record只做哈希绑定。当前语义PASS依据本轮重新核读，不能推广到新候选。
4. **原DAG证据范围有限。** 构图是固定名字的源码引用匹配；used_in_lean统一取整文件accepted，不足以一般性证明每条边实际使用。本轮针对现有15条边已通过真实证明项补验。
5. **候选文本边界不够干净。** original_statement夹带首段证明说明，本轮分段记录但未修改原数据。
6. **旧检索展示不是完整声明。** 旧生成器截取连续三行，可能遗漏section级假设或截断声明。本次报告改以真实Lean类型补齐，仅新增验收材料，没有修改生成器。
7. **全部库内传递依赖图NOT VERIFIED。** 已完整列出本地五个声明的直接依赖；库内部未逐层展开。传递公理审计已执行。
8. 本轮验收探针最初使用不支持的pp.width选项，探针返回码1，日志保留在[inspection-compile.json](inspection-compile.json)。修正仅发生于新的InspectLemma3-v2.lean，原始Lemma文件未改，第二次探针成功。
9. 首轮隔离测试执行器将Popen替换为函数，触发Windows asyncio继承接口错误，原始失败保留在[regression.txt](regression.txt)。改为真实Popen的子类后重新执行13项全部通过，未修改原测试和应用源码，也未伪造数学结果。

独立验收目录为D:/mathproof/audits/lemma3-v031-80ab8af1。所有成功与失败的新证据均与原历史分离，未自动批准入库。
