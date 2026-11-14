# v0.3 解析与语义回归

本次直接读取工作区两篇真实PDF，不使用替代文字，不调用AI。测试日期2026-11-12。解析版本0.3.0，旧版0.2.2文档缓存和候选不删除。

|文献|识别片段|本版候选|保留资料|不确定结构|已形式化（刚解析时）|
|---|---:|---:|---:|---:|---:|
|Abundant Numbers|39|4|35|28|0|
|Mason–Stothers|50|16|34|3|0|

丰盈数4候选为2定义和2猜想。Mason16候选为6定理、3引理、2定义、3证明、1猜想和1推论。该计数来自本次实际运行，并非强行匹配旧版数字。新增代码资料和识别的Proof (Proof of Theorem 1)导致新版与旧计数不同。

## 实际修复

- uncertain现在直接统计recognition_status=uncertain，原先仅数Low Confidence会漏掉已拒收图注等不确定结构。候选数量和已形式化数量单独提供。
- 识别论文Lean代码，保留为Code资料；不把作者的theorem/def转录当成系统数学候选或独立新证明。普通正文小写theorem/lemma不能仅凭词命中代码规则。
- 原文切片、statement_text、proof_body、code_fragments分离；Mason Lemma1位于PDF第4页，后续Proof段不再属于该引理statement。
- 保留original_statement与原文偏移；normalized_statement仅执行空白整理、可辨字形恢复和有限单字符变量边界修复，记录normalization_changes。例如polynomiala∈k[t]恢复为polynomial a∈k[t]。这不是一般数学OCR；无法确定的上/下标标风险，绝不猜测。
- 新增assumptions、quantifiers、domain_constraints、definitions、boundary_cases、potential_counterexamples、source_location、review_status。规则摘录的空数组不表示数学条件不存在。
- 丰盈数k=1风险保留。素数乘积练习增加p1=p2=2风险：4的正因数和1+2+4=7，并不大于8。这是可读的规则算术说明，不是Lean证伪，verification仍unknown。
- 多项式对象标记域、特征、公式格式需要复核，绝不擅自补characteristic=0。原文第2页和第8页说明任意域，Lemma1第4页有非零假设；不要把后文Davenport所需特征零传播给Lemma1。
- 重复解析仅更新规划字段，不覆盖人工编辑的normalized_statement或已审核状态；旧版候选按parser_version隔离。

## 验证

新增 tests/test_semantics_v03.py：4项通过，3.169秒，包括两份真实PDF的双次读取一致性、全部对象的原文切片定位、两个边界条件、语义字段、Code/Proof分离和人工编辑重跑保留。

原有test_structures.py的5项与test_quality.py的4项均通过。第一次新增测试因受限Windows临时目录访问失败；正常临时目录权限下重跑4项全部通过，不将权限失败隐瞒为成功。

## 尚有限制

跨页公式、PDF阅读顺序、上下标恢复、嵌套证明边界仍可能不完整。代码块缺少可靠排版边界时可能保留旁边说明文字；这些只是来源资料，不执行。语义条件字段为规则摘录，尚非真正AI数学理解，也不能替代真人的原文对齐审核。
