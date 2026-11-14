# v0.2.1 最终验证记录

日期：2026-11-11（北京时间）。

- 20 项 unittest 全部通过，无跳过；包含真实 PDF 读取、原文切片、定义与任务、证明步骤、真实 Lean 四候选、扫描型 PDF、普通 PDF、损坏文件、重复解析与入库、旧 schema 迁移、DAG 环与明确引用、Streamlit 上传及来源隔离。最终运行耗时 15.264 秒。
- 原始输出见 tests-v021.txt。唯一告警是 Streamlit AppTest 主线程缺少 ScriptRunContext 的预期提示；运行中的服务控制台没有新增告警或异常。
- mypy 检查 app.py 通过；compileall 通过；pip check 通过。
- lake build 成功（55 jobs，复用构建缓存），原有三个 Lean 声明公理仅含 propext、Quot.sound，无 sorryAx。真实集成测试重新执行了 Lean worker，得到 proved / proved / refuted / unknown。
- 本机临时 Streamlit 服务 agent API 返回 ready；真实论文页面候选行数 25、异常数 0。测试服务已停止。快照见 agent-final-snapshot.json。
- 实际上传 PDF 共 30 页，来源 ID 8 复用，提取 25 个对象（3 Definition、8 Conjecture、13 Proof 证据片段、1 Example 图注），14 个 uncertain。它们均未形式化，verification_status 均为 unknown。
- DAG 有 25 个来源节点、0 条可靠依赖边；Lemma 3、Lemma 4 保留为 uncertain 的未解析引用。测试材料中的明确引用和 proof_of 关联已通过测试，不以测试材料冒充真实论文已解析依赖。
- 原库 8 条来源、28 条候选、120 条事件全部逐行比对一致；新增加 25 个论文候选。已验证库原为空，仍为空，没有自动批准。详细比对见 database-preservation.json；升级前完整备份为 data/backup-before-v021.sqlite。

本次没有使用真实 AI 服务，没有做 OCR，没有把手写图转录成自动提取结果，也没有证明该论文的数学命题。第 28 页原题的 any k ∈ N 与第 9 页讨论的 k>1 均按原文独立保留。
