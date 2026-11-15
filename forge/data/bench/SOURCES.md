# 评测集来源

## minif2f_test.jsonl

- 内容：miniF2F 的 test 部分，244 题中的 243 题（高中数学竞赛题：AMC、AIME、IMO 与 MATH 数据集题目）。
- 原始基准：miniF2F（Zheng, Han, Polu, 2021，OpenAI，MIT 许可）。
- Lean 4 版本取自 DeepSeek-Prover-V1.5 仓库的 `datasets/minif2f.jsonl`（MIT 许可，Copyright (c) 2023 DeepSeek），
  https://github.com/deepseek-ai/DeepSeek-Prover-V1.5 ，于 2026-11-15 下载。
- 题目依赖 `open BigOperators Real Nat Topology Rat`，已记录在每行的 `opens` 字段，校验时自动加上。
- 为适配本库的 Mathlib（v4.24）做了一处纯语法转换：31 题里的旧写法 `∑ x in s, f` / `∏ x in s, f` 改为 `∑ x ∈ s, f`；
  带类型标注的 `∑ k : T in s, f` 改为 `∑ k ∈ (s : Finset T), f`。含义不变。
- 未收录 1 题：`amc12a_2020_p15`，用到了 v4.24 里已移除的 `Complex.abs`。
- 只收 test 部分，作为保留评测：这些命题不能进入 Mathlib2（`propose` 会判为 `reserved`，提交里的辅助引理也不行）。
  valid 部分没有导入，可以作为开发时的练习题。
