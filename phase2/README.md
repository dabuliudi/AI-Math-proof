# Phase 2：受限范围内的运行时证明发现

本模块独立于v0.3.1。它从输入关系和运行时检索的Lean类型构造证明，不使用Mason–Stothers模板，不修改旧数据库，不自动批准入库。

本轮实际结果与限制见[验收报告](ACCEPTANCE.md)，多层证明节点、边、来源及源码见[完整DAG实例](PROOF_EXAMPLE.md)。验收发现原数据库哈希有变化，已单独披露逐行比较和未确认的变化来源；不能把“新引擎不访问数据库”理解为整个工作期间数据库文件未变。

当前实现是**无AI的有界符号搜索**，不是通用论文理解或LLM数学研究系统。支持自然数变量/常数、≤、<、∣、=及合取；不支持函数项、加乘表达式、多项式、存在量词和任意自然语言。原文与结构输入分别保存，source_alignment始终unconfirmed；formal_goal_verified只表示结构目标通过Lean，candidate_verified保持false，入库pending。

## 启动

在PowerShell中执行：

```powershell
cd D:\mathproof
$env:PYTHONUTF8='1'
.\.venv\Scripts\python.exe -B -m phase2 phase2/examples/problem.json --budget 12
```

无需密钥，无新增大型Python依赖。使用现有固定Lean/Mathlib 4.24.0及缓存。当前仅支持Windows本地工具链路径。旧Streamlit入口和界面不变，Phase 2入口是独立CLI。

输入只能包含domain、variables、assumptions、goals、original_text，不接受proof、strategy或dag字段。goals列表表示合取，assumptions表示整个证明上下文；中间声明携带所有原变量及假设，不冒充无条件定理。

## 模块与真实流程

完整实施前方案见DESIGN.md。

- model.py：受限Problem Parser及安全的Lean表达式生成。
- Extract.lean、retrieval.py：读取真实环境定理类型，通用地特化到Nat，用Lean合成实例；实例不得约束Nat值变量。记录完整类型、模块、源码行与哈希，缓存通用目录而非题目答案。
- planner.py：变量统一、候选实例搜索、通用目标相似度排序和失败排除。匹配预算每轮12000；编译总预算1–40。
- evidence.py：追加JSONL事件、哈希链、动态DAG。先写planned节点/边，再启动编译。
- engine.py：合取子目标、假设叶节点、待证明中间命题、成功后复用、最终目标编译和预算控制。
- compiler.py：独立源码文件、真实Lean进程、超时、逐声明#print axioms及公理门禁。
- provider.py：no-AI提供者和可选HTTP建议协议；真实模型服务及AI驱动搜索尚未验收，当前引擎不调用它。
- benchmark.py：只有问题的内部基准及引擎版本固定后生成的题目。

通用策略包括项统一、假设复用、规则实例化、合取构造及优先接近目标的候选；这些是开发者编写的Rule Engine，不声称由AI在运行中发明。Mathlib定理及Lean Core定理复用分别计数。不按题目ID或目标定理名称硬编码答案。

## 每次运行的证据

phase2/runs/<独立ID>下保存：problem.json、environment.json、engine-hashes.json、retrieval.json、events.jsonl、dag.json、result.json，以及每次attempt-XXX.lean/json。源文件、成功/失败日志都保留。库类型抽取失败时保存retrieval-compile.json。

事件顺序为：goals_opened→planning_round→dag_node_planned→compile_started→compile_finished→dag_node_updated；目标证明依赖只能来自输入假设或已经编译通过的事实。DAG中也保留未被最终证明采用的探索分支，不把它们计为最终证明的中间引理。

错误反馈当前采用“排除失败实例，搜索替代”的有界策略，不支持理解任意Lean错误并重写任意证明。故障测试通过损坏检索名称触发真实Lean报错再搜索替代；这不计入正常基准成功率。没有将编译失败或预算耗尽标成refuted。

## 无答案基准与测试

```powershell
.\.venv\Scripts\python.exe -B -m phase2.benchmark
$env:MATHLIB2_PHASE2_INTEGRATION='1'
.\.venv\Scripts\python.exe -B -m unittest discover -s phase2/tests -v
```

每轮基准建立新的benchmarks/run-<ID>目录，包含输入、引擎哈希、每题独立实验、结果和汇总，不覆盖旧批次。suite.json只有命题和事后类别，类别不会传入引擎。生成题的种子在inputs.json。

“未解决”对照题没有证明结果，不能说它揭示了Mathlib本身的数学极限。本基准是开发者内部基准，不是独立第三方盲测；测试域在开发前已限定为Nat关系。本轮没有模型训练数据去污染证据，也不对任意未见论文泛化作声明。

## 指标口径

首次成功率：第一次证明编译就得到整个结构目标；不含库目录抽取。最终成功率：最终目标连同所有声明通过真实Lean和公理检查。平均编译次数包含失败、探索支路及最终重验。修复次数指一次错误之后尝试替代候选，不是LLM文本改写次数。

中间引理数仅计最终DAG使用且不同于输入子目标的新增结论；generated_lemmas另计所有最终采用的新声明。深度是依赖边数，包含假设叶与最后目标闭合边，不包含库内部证明深度。Mathlib和Lean Core复用分别计数。人工干预次数只计单次运行期间，不包含开发者编写通用引擎和测试集的工作。AI调用0，成本0，token字段null表示未调用，不是有调用但消耗未知。

## 可选AI协议（NOT VERIFIED）

未来建议网关配置为MATHLIB2_PHASE2_API_URL、MATHLIB2_PHASE2_MODEL、MATHLIB2_PHASE2_API_KEY。不要在聊天或代码中填写密钥。HTTPAdvice会记录prompt、目标、请求/报告模型、版本、原始响应、usage、cost和时间；缺失计量为null。建议不会被作为任意Lean代码执行，generated_lean_code和compile_result为null并明确advice_only_not_executed。

当前CLI强制无AI模式；此接口不是已完成的AI自主规划器。接入真实模型并把结构化规划建议纳入闭环，仍是后续阶段。
