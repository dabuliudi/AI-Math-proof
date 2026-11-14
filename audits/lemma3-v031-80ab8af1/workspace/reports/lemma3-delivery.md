# Mason–Stothers Lemma 3 实验交付报告

本轮已完成论文核读、语义对齐、库检索、分层证明、真实 Lean 编译、公理审计及回归测试。候选89（source_id=9）为 candidate_alignment=confirmed、candidate_verified=true、verification_status=proved、approval_status=pending。语义核读者是本次对话助手，非真人审核批准。

## 数学结论

原论文2408.15180v2.pdf第7页Lemma 3：对任意域k及a∈k[X]，若deg(a)≥1，则deg(rad(a))≥1。radical为不计重数的首一不可约因子乘积。任意特征均适用，没有额外CharZero、首一、平方自由假设。

原文声明位于第7页字符区间[1071,1181)，完整证明说明位于[1181,2043)。区间按pypdf文字层Unicode字符计数。候选原字段包含首段证明说明，因此本次另存声明与证明分段，没有覆盖历史原文。

最终Lean声明使用degree : WithBot ℕ；中间natDegree版本有显式转换，未混淆零多项式的两种次数。非零条件由degree≥1推出。DecidableEq k是定义所需技术实例，可由经典逻辑提供。语义结论、边界条件和定义比较详见[语义报告](lemma3-alignment.md)，原文及定义上下文见[来源JSON](lemma3-source.json)。

## 证明来源与结构

分类：New Proof，含义是本轮新编写的Lean组合脚本，不是新数学发现。未复制论文作者的Lean实现，也未直接调用与Lemma 3同结论的整条库定理。复用了现有Mathlib关于单位、radical幂等性及次数的声明。

这份方案由当前对话助手分解、编写，再固化为项目可复跑模板。它不是项目自主推理引擎产生的方案；项目模型API调用次数为0。逐步标注AI生成、Mathlib定理复用、已有局部Lemma组合和预置规则，见[步骤来源](lemma3-steps.json)。本轮没有真人补写证明。

证明链为：非零且natDegree零推出单位；radical为单位推出原非零多项式为单位；通过反证证明radical的natDegree非零；转换为natDegree≥1；最后转换为degree≥1。共4个中间声明和1个最终声明。

Lemma 1、2涉及导数及Wronskian，对本次radical正次数证明不构成依赖，未强行连边。其历史数据、代码、已保存报告及候选状态都保留。

[Mathlib检索报告](lemma3-retrieval.md)包含9个显式使用的数学主干声明，以及次数上界、不可约因子、normalizedFactors与乘积次数等备选来源。源码位置及哈希见[检索JSON](lemma3-retrieval.json)。

[Proof DAG](lemma3-dag.md)有14个节点、15条边，最长路径4条边；只算本次局部声明的最长路径为3条边。每条边保存实际源码引用、声明位置和数学理由，详见[DAG JSON](lemma3-dag.json)。这是显式数学主干图，不声称枚举Lean内核所有传递依赖和隐式实例。

## 真实编译与公理审计

- 源码：[Lemma3.lean](../lean/Research/Lemma3.lean)
- 工具链：Lean 4.24.0，Windows x86_64，commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b。
- 最终实验编译退出码：0；耗时7.765秒（包含版本查询等开销）。
- 源码SHA256：49af9433eadc7bff6dac94937889ae2f090fa414d72c8f7fb3eea5f6ace1050b。
- 五个声明的#print axioms均通过，依赖均为propext、Classical.choice、Quot.sound。没有sorry、admit、sorryAx或额外自定义公理。
- [原始编译与审计日志](lemma3-0cd93ed19024460a85f4de6f484162c5.json)保存命令、返回码、stdout/stderr、逐声明审计、源码及哈希。
- [完整实验结果](lemma3-result.json)关联语义证书、编译、DAG、步骤、成本与历史保留检查。证书绑定原文、规范化表述、Lean源码、报告及依赖文件哈希；修改后不能沿用旧验收。

## 成本对比

|实验|新增Lean行|显式复用Mathlib声明|新增中间引理|DAG深度|指定日志编译秒|
|---|---:|---:|---:|---:|---:|
|Lemma 1|5|1|0|1|12.531|
|Lemma 2|16|4|2|2|12.172|
|Lemma 3|30|9|4|4|7.765|

新增行数排除空行、import、open、审计打印；Lemma 2剔除原样复用Lemma 1的前缀。复用数不含定义、基础Nat/逻辑API、simp内部依赖和隐式实例。深度为列出的数学主干最长路径边数，不含Mathlib内部证明。编译耗时受缓存及负载影响，不能据此推断证明难度或效率提升；生成耗时与token未可靠计量，标unknown。机器可读口径及日志索引见[成本JSON](lemma3-costs.json)。

## 测试及已解决问题

最终完整回归：**51项测试，66.236秒，全部通过，无跳过**。已启用MATHLIB2_INTEGRATION=1，实际运行原有自然数示例、Lemma 1/2/3编译、真实PDF、数据库、工作流与Streamlit页面测试。新增测试覆盖原文位置、定义域、证明来源、DAG证据、源码哈希、成本、证书失效、人工批准门槛和五个声明的公理审计。实际输出见[测试日志](tests-lemma3.txt)。

本轮没有隐去失败：

1. 检索定位最初把dvd_radical_iff_of_irreducible记为第224行，断言拒绝该定位；核对后修正为真实声明的第223行。
2. 两次版本查询在15秒时超时，尚未开始证明编译，未标成功。等待上限调整为60秒（受调用预算限制），并新增timeout_phase以区分版本查询和证明编译；原始失败日志保留于lemma3-result.json的compile_history索引中。
3. 第一轮回归在上述未知状态下有两项状态检查失败，保留[该轮日志](tests-lemma3-before-retry.txt)。
4. 后续一轮测试记录有约14小时的异常时间跨度，原教学样例两项证明返回unknown；没有据此断言数学反例，也没有修改原教学证明。保留[该轮日志](tests-lemma3-interrupted-run.txt)。重新运行后51项全部通过；异常时间跨度的系统原因未确认。

没有数据库结构迁移或删除旧记录。运行前保存data/before-lemma3.sqlite；实验检查sources、candidates、events、verified、proof_runs和workbench_history的既有行仍在，Lemma 1/2状态与已有文件哈希未改变。真实编译追加proof_runs及历史，不批准入库。

## Windows 启动与复现

PowerShell启动工作台：

```powershell
& 'D:\mathproof\run-demo.cmd'
```

浏览器打开http://127.0.0.1:8501。Lean Lab可选择Lemma 3模板；重跑模板不等于再次AI推理。

本工作区重跑完整实验（追加真实记录，不批准入库）：

```powershell
cd D:\mathproof
$env:PYTHONUTF8='1'
$env:PATH='D:\mathproof\.tools\lean-4.24.0-windows\bin;'+$env:PATH
.\.venv\Scripts\python.exe scripts/run_lemma3.py
```

回归测试：

```powershell
$env:MATHLIB2_INTEGRATION='1'
.\.venv\Scripts\python.exe -m unittest discover -s tests -v
```

无需AI凭据。脚本依赖本工作区已导入的论文、候选及固定Mathlib版本；不是任意新论文的通用自动证明程序。
