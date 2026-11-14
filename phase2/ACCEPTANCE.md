# Phase 2 无 AI 运行时证明发现：交付与验收

验收日期：2026-11-14（Asia/Shanghai）。按用户选择，本轮实施并验证无 AI 的通用搜索，真实 AI 实验明确保持 NOT VERIFIED。

**结论：受限自然数关系语言内的运行时搜索、动态数学 DAG、Lean 生成/编译/公理检查及替代候选反馈已经运行通过。没有验收为任意论文的自主形式化系统。**

## 1. 交付范围与状态

|项目|状态|实际证据及边界|
|---|---|---|
|独立架构和接口|PASS|[实施前技术方案](DESIGN.md)、[使用与模块说明](README.md)；所有新增实现位于 phase2|
|Problem Parser|PASS（限定）|解析 Nat 关系与合取的结构化输入；拒绝任意Lean代码、策略/DAG/答案字段。不是自然语言语义理解|
|真实库检索与类型匹配|PASS（限定）|Lean读取当前导入环境，抽取163条适配规则：98条Mathlib、65条Lean Core；保存原始类型、源码行、哈希和绑定|
|运行时中间引理与DAG|PASS（限定）|先写planned事件，再编译；只组合假设或已通过Lean的事实。不是从最终证明反推规划过程|
|代码生成及真实验证|PASS|6份最终证明独立重新编译，返回码全部0；全体声明执行#print axioms|
|错误反馈|PASS（限定）|真实故障测试：不存在的声明导致编译失败，保留日志后搜索另一候选并成功；未实现任意错误的文本修复|
|无专用答案模板|PASS（当前代码范围）|引擎不导入旧实验模板、不按benchmark ID或目标定理名分支；使用开发者编写的通用统一、排序、实例化与合取规则|
|基准测试|PASS（内部）|7题，6 proved、1 unknown；题目JSON无答案；第三方严格盲测独立性 NOT VERIFIED|
|原文语义对齐|NOT VERIFIED|original_text仅保留；source_alignment=unconfirmed，candidate_verified=false|
|AI驱动规划和调用成本|NOT VERIFIED|项目模型调用0；HTTP建议协议未接入搜索闭环、未调用真实服务|
|旧版代码和实验文件|PASS|204个非数据库受检文件哈希不变，无删除和新增；旧版13项相关回归通过|
|数据库字节级不变|FAIL|原数据库SHA256与本轮开始时不同，详见第7节；不能报告为全部文件未变|
|Lemma 1–3历史保留|PASS（与此前验收副本比较）|三个候选、状态、证明运行、审核及历史记录逐行相同；未自动批准知识库|

## 2. 数学与来源审计

当前语言把变量解释为全称量化自然数；输入assumptions全部保留为每个Lean声明的前提；goals列表解释为合取。支持≤、<、∣、=，只接受变量和有限自然数常量。未将自然数关系自动推广成整数、多项式或任意域。

提取器用Lean类型系统把适配的多态定理特化到Nat、合成实例，并拒绝实例合成偷偷约束数值变量的情况。检索仅覆盖固定导入环境内且符合当前语法的声明，**不是全Mathlib完备检索**。缓存保存规则类型，不保存基准证明。

证明来源为 **Rule Engine + Mathlib Reuse / Lean Core Reuse + Lemma Composition**。规则实现和测试集由开发者编写；每题使用哪些规则、变量绑定、哪些中间事实及实际DAG在运行时决定。没有项目AI调用；不能把本次开发助手的代码编写等同于系统运行时AI推理。没有使用Mason–Stothers作者证明作为本阶段答案模板。

三条旧Lemma不参与新引擎证明。这里相较旧版固定模板增加的是受限语言内的真实运行时搜索能力，不是对任意数学问题的自动规划能力。

## 3. 当前基准的实际结果

最终批次：[汇总](benchmarks/run-b63d1f87b59f467a994af289b0ab8390/summary.json)、[逐题结果与运行目录](benchmarks/run-b63d1f87b59f467a994af289b0ab8390/results.json)、[冻结输入和引擎哈希](benchmarks/run-b63d1f87b59f467a994af289b0ab8390/inputs.json)。每题预算12次证明编译。

|问题|状态|证明编译次数|最终复用Mathlib/Core声明数|最终中间引理数|数学DAG深度|
|---|---|---:|---:|---:|---:|
|reuse|proved|2|1 / 0|0|1|
|composition|proved|3|1 / 1|1|3|
|intermediate|proved|5|1 / 0|1|3|
|multilayer|proved|9|1 / 1|3|6|
|unresolved|unknown|12|0 / 0|0|0|
|generated-0|proved|4|2 / 0|1|3|
|generated-1|proved|4|2 / 0|1|3|

- 首次编译得到完整目标公式：1/7，14.29%；最终成功率：6/7，85.71%。
- 平均证明编译次数：39/7=5.57；正常基准编译失败0、修复0。独立验收的6次重编译另计，不并入39次。
- 平均最终Mathlib复用声明数1.14，Core复用0.29，中间引理1，DAG深度2.71；不同题重复复用的声明分别计数。
- 单次实验人工干预0；项目AI调用0、成本0、token=null。开发者建设引擎和调试的工作不算进“运行期间人工干预0”。
- unresolved是未证明的负对照；预算耗尽仍为unknown，既不是refuted，也不说明Mathlib本身无法解决某类数学。

新增两个生成题在引擎哈希固定后按种子生成并打乱变量/假设顺序；仍属内部测试，不是第三方保密盲测。首次单态提取实验[旧批次](benchmarks/run-f3cbca873f2540d7bca4fba44f462d85/summary.json)也保留；随后通用多态特化升级改变了检索空间，因此不能把两轮调试称为严格一次性盲测。

## 4. 完整DAG、Lean源码与检索证据

见[多层实例的完整节点、边、来源及Lean声明](PROOF_EXAMPLE.md)。该实例15个节点、12条边，其中3个是编译通过但未进入最终依赖链的探索分支。最终采用5个生成声明，其中3个是中间引理；深度6。

实际采用 Dvd.dvd.trans（Mathlib）串联整除关系，再使用 Nat.le_of_dvd（Lean Core）获得大小关系，最后 And.intro 闭合合取。此选择来自运行时检索/排序，没有预写在题目中。

- [真实生成的最终Lean源码](benchmarks/run-b63d1f87b59f467a994af289b0ab8390/runs/7a05a163ef664fc684dfdd4e783371f4/attempt-009.lean)
- [原始编译、公理、源码SHA256](benchmarks/run-b63d1f87b59f467a994af289b0ab8390/runs/7a05a163ef664fc684dfdd4e783371f4/attempt-009.json)
- [规划先于编译的事件链](benchmarks/run-b63d1f87b59f467a994af289b0ab8390/runs/7a05a163ef664fc684dfdd4e783371f4/events.jsonl)
- [当次完整检索目录](benchmarks/run-b63d1f87b59f467a994af289b0ab8390/runs/7a05a163ef664fc684dfdd4e783371f4/retrieval.json)

DAG是数学前提依赖图，不是Lean内核全部常量、上下文参数和类型类实例的传递依赖图。无关探索分支被明确保留和标记，不计入最终证明的中间引理数。

## 5. 独立真实编译和公理审计

[独立验收记录](verification/dfb9ee9b38a5477d89a593d22bad0e96/acceptance.json)检查引擎哈希、提取器与manifest绑定、事件哈希链、节点先规划后编译、前提已成立、源码SHA256和目标/上下文未被替换；随后对六份最终源文件再次启动真实Lean进程。

工具链：Lean 4.24.0，commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b；Mathlib v4.24.0，rev f897ebcf72cd16f89ab4577d0c826cd14afaafc7。[环境记录](verification/dfb9ee9b38a5477d89a593d22bad0e96/environment.json)。

命令形态：`D:\mathproof\.tools\lean-4.24.0-windows\bin\lake.exe env lean -M 2048 <该次独立源文件绝对路径>`；工作目录 `D:\mathproof\lean`。每条日志记录完整命令、返回码、stdout、stderr、耗时和SHA256。

|问题|返回码|独立编译秒数|审计声明数|实际公理并集|日志|
|---|---:|---:|---:|---|---|
|reuse|0|26.603|2|空|[001](verification/dfb9ee9b38a5477d89a593d22bad0e96/attempt-001.json)|
|composition|0|5.760|3|propext|[002](verification/dfb9ee9b38a5477d89a593d22bad0e96/attempt-002.json)|
|intermediate|0|5.780|5|propext|[003](verification/dfb9ee9b38a5477d89a593d22bad0e96/attempt-003.json)|
|multilayer|0|5.798|9|propext|[004](verification/dfb9ee9b38a5477d89a593d22bad0e96/attempt-004.json)|
|generated-0|0|5.778|4|空|[005](verification/dfb9ee9b38a5477d89a593d22bad0e96/attempt-005.json)|
|generated-1|0|5.761|4|空|[006](verification/dfb9ee9b38a5477d89a593d22bad0e96/attempt-006.json)|

无sorry、admit、sorryAx或额外未批准公理。允许集合为propext、Classical.choice、Quot.sound；实际上述六份源文件只涉及空集或propext。所有成功和失败尝试均保留。

## 6. 测试与代码量

- 新增测试：**9/9通过，无跳过，127.561秒**。[完整输出](development/tests-final.txt)。包含真实编译、独立重验、故障后替代搜索、未证明目标不能报成功、输入边界、统一、DAG/哈希链和无AI配置检查。
- 旧版Lemma 1–3相关回归：**13/13通过，无跳过，22.178秒**。[输出](legacy-regression/f7b2b657d5694e42bcc9375d3960dd33/tests.txt)、[副本哈希和真实进程记录](legacy-regression/f7b2b657d5694e42bcc9375d3960dd33/result.json)。复制当前源码和数据运行；只将编译依赖目录指向原Lean工程，未伪造编译返回结果。旧测试中的超时模拟仍只是异常单元测试。
- 本轮未重跑整个Streamlit端到端测试集，不声称已覆盖所有旧功能。
- 新模块根目录Python文件及Extract.lean合计586物理行；新增测试162物理行。报告生成脚本、数据、日志、生成证明和README不计入上述产品代码行数。旧版产品源码修改0行。

## 7. 历史与数据库变化披露

[本轮开始哈希与结束对比](legacy-preservation.json)：205个文件，204个未变、1个数据库变化、无缺失、无新增。**不能通过“数据库逐字节未改变”验收。**

由于开始时只有数据库哈希，没有另存逐行快照，具体行差异以此前独立验收保存的数据库副本为比较基线，不能冒称该副本就是本轮开始时的字节级数据库。只读比较见[数据库报告](database-comparison.json)及[逐字段与Lemma历史比较](history-detail.json)。

发现候选73、74、75、76的workbench_state新增candidate_alignment=unconfirmed和candidate_verified=false；workbench_history增加4条planning记录，时间为北京时间2026-11-14 19:34:46。其他表相同，schema相同，integrity_check=ok。候选85、87、89及其相关历史、证明记录、批准表均与此前验收副本逐行相同；verified表仍为空。

变化来源目前NOT VERIFIED，不能凭时间推断是哪一个进程或操作造成。新Phase 2引擎没有SQLite访问接口；此次旧回归在独立副本执行。已保留当前记录，没有恢复旧数据库或覆盖用户可能做出的操作。

## 8. 未完成的完整Phase 2能力

1. 自然语言/论文到数学目标的可靠语义解析与独立确认。
2. 函数项、算术表达式、多项式、存在量词和更丰富的类型/定义。
3. 真正由模型提出子目标、改变分解结构、理解错误并修复证明的闭环；当前只有无AI前向有界搜索和合取分解。
4. 真实模型配置、版本和prompt/output/token/成本日志的服务验收；HTTP接口目前只是未执行建议协议。
5. 严格外部盲测、复杂论文泛化与搜索效率。当前多层实例先探索3个无用事实，说明目标排序仍有改进空间。
6. 更全面故障路径验收，例如系统性工具链缺失/超时及检索失败；检索异常返回的结果字段尚不如正常结束路径完整，集成方需按unknown处理，不能直接假定metrics等字段存在。

## 9. Windows启动

在PowerShell直接执行，无需修改脚本执行策略或配置API密钥：

```powershell
cd D:\mathproof; $env:PYTHONUTF8='1'; .\.venv\Scripts\python.exe -B -m phase2 phase2/examples/problem.json --budget 12
```

本轮入口是独立CLI；旧Streamlit页面和启动脚本保留。测试与基准重跑命令见README；每次都会创建新的实验目录。

上述命令已实际运行，退出码0，2次证明编译后结构目标proved；candidate_verified仍为false，approval_status=pending。[命令输出](development/cli-demo.txt)、[本次独立运行结果](runs/0eb48bfb463843e88f12737490086006/result.json)。
