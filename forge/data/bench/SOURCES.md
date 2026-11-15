# 评测集来源

## minif2f_test.jsonl

- 内容：miniF2F 的 test 部分，244 题中的 243 题（高中数学竞赛题：AMC、AIME、IMO 与 MATH 数据集题目）。
- 原始基准：miniF2F（Zheng, Han, Polu, 2021，OpenAI，MIT 许可）。
- Lean 4 版本取自 DeepSeek-Prover-V1.5 仓库的 `datasets/minif2f.jsonl`（MIT 许可，Copyright (c) 2023 DeepSeek），
  https://github.com/deepseek-ai/DeepSeek-Prover-V1.5 ，于 2026-11-15 下载。
- 题目依赖 `open BigOperators Real Nat Topology Rat`，已记录在每行的 `opens` 字段，校验时自动加上。
- 为适配本库的 Mathlib（v4.24）做了一处语法转换：31 题里的旧写法 `∑ x in s, f` / `∏ x in s, f` 改为 `∑ x ∈ s, (f)`；
  带类型标注的 `∑ k : T in s, f` 改为 `∑ k ∈ (s : Finset T), (f)`。主体必须加括号：新写法优先级更高，
  不加括号时有 6 题的题意被改变（2026-11-15 发现并修正，受影响的运行记录移到 `runs/archive/`）。
- 未收录 1 题：`amc12a_2020_p15`，用到了 v4.24 里已移除的 `Complex.abs`。
- 只收 test 部分，作为保留评测：这些命题不能进入 Mathlib2（`propose` 会判为 `reserved`，提交里的辅助引理也不行）。
  valid 部分没有导入，可以作为开发时的练习题。

## 已知写错的题（命题为假）

基线 `mf2f-baseline-1` 中 Codex 对下面 8 题给出了内核验证的反证，说明这个版本里的 Lean 写法与原题不符：

| 题目 | 问题 |
|---|---|
| imo_1982_p1 | 自然数截断减法使条件变弱 |
| aime_1994_p3 | 原题“对所有 x 成立”被写成只对一个固定的 x 成立 |
| mathd_numbertheory_618 | n = 0 时结论不成立（p(0) = p(1) = 41） |
| algebra_ineq_nto1onlt2m1on | n = 1 时为 1 < 1，缺少 n ≥ 2 |
| amc12a_2020_p10 | Lean 中 log 0 = 0，n = 1 也满足条件 |
| amc12a_2020_p7 | 只约束了 a 0 … a 6，却用到 a (k²)（k² 最大 36）；与本库的语法转换无关 |
| algebra_cubrtrp1oncubrtreq3_rcubp1onrcubeq5778 | 内核验证的反证，细节见对应运行记录 |
| amc12a_2021_p25 | 内核验证的反证，细节见对应运行记录 |

这些题保留在评测集里不删，`bench-score` 会单独报告 `refuted` 和扣除它们之后的 `rate_on_true`。

## putnam_noanswer.jsonl

- 内容：PutnamBench 的 Lean 4 部分（William Lowell Putnam 数学竞赛题，1962 年起）中**不需要填答案**的题，共 312 题。
- 来源：https://github.com/trishullab/PutnamBench （`lean4/` 目录，Apache-2.0 许可），2026-11-15 下载默认分支。
- 原仓库用 Lean v4.33.1，本库是 v4.24.0。672 题里：
  - 346 题需要先给出一个答案定义（`putnam_XXXX_solution`），本集合暂不收录；
  - 剩下 326 题中，5 题带有额外的定义、2 题文件结构特殊、6 题命题内部含 `:=`（如 `let`），都暂不收录；
  - 1 题在 v4.24 的 Mathlib 上通不过类型检查；
  - 其余 312 题原样收录，每题自带的 `open` 设置记在 `opens` 字段。
- 官方排行榜（`docs/results.json`）的数字统计的是全部 672 题（含需要填答案的题），与本集合的分母不同，比较时要注意。

## putnam_wsol.jsonl

- 内容：PutnamBench Lean 4 部分的“填好答案”版本（对应官方排行榜的 `lean-wsolution` 赛道，分母是全部 672 题），共收录 562 题。
- 需要填答案的题：`abbrev 题名_solution : 类型 := sorry` 后面紧跟的注释就是官方答案，转换时把它填进去；
  这条定义以及题目自带的辅助定义（def/abbrev）作为该题的 `preamble`（前置定义）保存。校验证明时前置定义放在最前面，
  agent 不能修改；前置定义里若残留 `sorry`，主定理会因依赖 `sorryAx` 被拒（已测试）。
- 672 题中：61 题暂时转不了（答案注释格式特殊、前置部分有无法处理的注释等），33 题在 Mathlib v4.24 上通不过类型检查，
  16 题命题格式不兼容（如内部含 `:=`），其余 562 题收录。转换代码在 `forge/importers.py`（`putnam_problem`）。
- 与官方排行榜比较时，分母要换算：本集合的成绩只覆盖 672 题中的 562 题。

## fc_pilot.jsonl（难题集试点）

- 内容：从 [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)（DeepMind，Apache-2.0，提交 `e028240`，2026-11-14）
  抽的 40 题：30 题 `research solved`、10 题 `textbook`，都是原仓库里还没有证明（`sorry`）、也没有标注网上已有 Lean 证明（`formal_proof`）的。
  固定随机种子 7 抽样，导入 37 题（2 题类型检查不过，1 题命题内部含 `:=`）。
- 用途：校准难度。先跑一轮低预算基线，删掉一次就解出的题，留下解出率 20%–50% 的那部分作为正式难题集（dev / held-out）。
- 与其他评测集的不同：不抄写定义。Formal Conjectures 作为 Lean 依赖加入 `lean/lakefile.toml`（与本库同一个 Mathlib 提交），
  每题的 `imports` 是题目所在模块，校验时直接导入；`preamble` 只有文件里的 `open` 设置。
- 忠实性：每题记下原常量名 `origin`。导入时用内核算出重写后命题的结构哈希，与原常量的类型逐一比较，不一致的判为 `unfaithful` 并拒收
  （已测试：把一题的 `p > 7` 改成 `p > 5` 会被拒）。
- 泄题防护：原仓库里的题目定理本身以 `sorry` 结束，直接引用它会因依赖 `sorryAx` 被拒（已测试）。
- 题目模块需要先编译：`cd lean && lake build <模块名>`；第一次约 80 秒（编译 Formal Conjectures 的公共部分），之后每个题目文件几秒。
