# 本地验证记录

日期：2026-11-11（北京时间）。

- Python 3.12；依赖安装成功，`pip check` 通过。
- `compileall` 通过。
- Lean 4.24.0，Mathlib 提交 `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`。
- `lake build` 成功（55 个构建任务）；三个导出证明的公理均为 `[propext, Quot.sound]`，无 `sorryAx`。
- 开启 `MATHLIB2_INTEGRATION=1` 后，9 项测试全部通过，无跳过，耗时约 11 秒。
- 实际 CLI 运行得到 `proved / proved / refuted / unknown`。对应候选编号为 13–16，写入本地 `data/mathlib2.sqlite`；后续运行会产生新编号。
- Streamlit AppTest 已验证首屏和完整流程按钮；默认 mock 只负责固定候选，Lean 编译从未模拟。

教学命题范围：自然数加零、两次加零、错误全称命题 `n+1=n`、有限策略无法判定的 `n*n=n`。最后一个命题实际上为假，但本次反例策略仅试 n=0，因此系统正确保留 unknown。

尚未验证：真实外部 AI 服务（未配置凭据）；任意研究论文的自动语义形式化；扫描型 PDF/OCR；全 Mathlib 索引。PDF 文本提取为可选功能，本次样例验证使用 Markdown 与 LaTeX。
