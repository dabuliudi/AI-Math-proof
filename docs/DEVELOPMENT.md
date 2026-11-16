# 开发流程

这份文档规定代码怎样进入 `main`。人和 agent（Claude、Codex）都按它做。

参考了两处：Anthropic 的 [Solving code review at Anthropic](https://claude.dev/blog/solving-code-review-at-anthropic/)（风险分级、审查轮数上限、批准绑定提交），
和 Lauren Tan 的 [pstack](https://github.com/cursor/plugins/tree/main/harness/pstack)（每个任务一个 worktree、小 PR 和 PR 栈、先证明再声称）。

## 为什么改

以前所有改动直接推 `main`，常常攒了半天的改动才一起提交，没有 CI，也没有审查。一个改动出问题时很难定位，也很难单独回滚。
这个项目尤其怕一种错：**一个 bug 让假证明或假提升被记成"已证明""已解出""变好了"**。所以判定代码的审查要求最高。

## 三条车道

| 车道 | 在哪里 | 怎么进 `main` |
|---|---|---|
| 代码 | 每个任务一个 git worktree，分支从 `origin/main` 切出 | PR，按风险分级审查，squash 合并 |
| 库和实验数据 | 主检出 `~/AI4math`（调度器和实验在这里跑） | `forge snapshot` 开数据 PR，CI 重放通过后自动合并 |
| 实验本身 | 主检出，或单独的 worktree | 结果随数据 PR 进库；结论写进代码 PR 或 ROADMAP |

主检出**只跑实验、只通过 `forge snapshot` 提交**，不在里面改代码。代码合进 `main` 后，在主检出没有任务运行时执行 `git pull --ff-only` 拿到新代码。

## 一次改动

1. **开工就开 worktree。** `git worktree add ../AI4math-wt/<名字> -b <type>/<名字> origin/main`。并行的 agent 各用各的 worktree，不共享工作区。
2. **先写完成条件。** 一句能判对错的话，例如"`forge bench-score fc_pilot` 的解出数不变，新增的单测先失败后通过"。"改好一点"不算。
3. **小步提交。** 每完成一个能验证的单元就提交。一个提交就是将来的一个 PR：能单独合并，按讲故事的顺序排。
4. **开 PR 要早。** 第一个能验证的单元做完就开 PR（直接开成 ready，不开 draft），后续工作开成栈式 PR（子 PR 的 base 是父分支）。
   - 代码 diff 超过约 400 行，或者工作超过半天还没开 PR，就要拆。五个窄 PR 好过一个胖 PR。
5. **开 PR 前自检**，结果写进 PR 的 Verification：
   - `python -m unittest discover -s forge/tests -t .` 通过；
   - 用真实产物证明，不用代理指标：改了 Lean 侧就真的 `lake build`，改了调度就真的跑一道题，改了评测就给出前后的数字；
   - 删掉叙述性注释、没用的防御代码和无关改动；
   - 用一个没写过这段代码的子 agent 在新上下文里审一遍 diff（Claude 用 `/code-review`）。
6. **按风险分级审查和合并**（下一节）。
7. **出问题就整个 PR revert**，不在 `main` 上叠补丁。

## 风险分级

分级看改动碰到了哪些路径，不看是谁写的。`python scripts/risk_tier.py` 给出当前分支的级别，CI 也会在每个 PR 上算一次。规则在该脚本的 `RULES` 里。

| 级别 | 范围 | 合并条件 |
|---|---|---|
| 低 | 机器写入的库（`lean/Mathlib2/`）、实验与评测结果（`forge/data/`、`phase2/benchmarks/`）、文档 | CI 通过即可合并，不需要人 |
| 中 | 其余代码：调度器、提示词、导入器、界面、脚本 | CI 通过；`/code-review` 的发现全部修掉或写明理由关闭；项目负责人批准一次 |
| 高 | 判定代码：校验与准入（`verify` `statement` `leanrun` `library`）、审计、评测打分、改进循环的采纳规则、组合拆解的判解、评测集本身、Lean 工具链版本、CI 和本流程 | 同"中"，另加：`/code-review` 用 high 强度；一个独立的 agent 按完成条件重新验证并贴出证据；项目负责人读过 diff 再批准 |

规则：

- **机器的批准不算人的批准。** 让 agent 写这个 PR 的人，就是必需的审查人。
- **批准只对一个提交有效。** 批准后又推了新提交，要重新批准。批准记在 PR 评论里，写明批准的提交 SHA。
- **审查最多三轮。** 第三轮还有新问题，就停下来重新考虑方案，而不是继续打补丁。第一轮之后只审新的 diff，不重复已经提过的问题；发现一类 bug 时修掉这一类的所有实例。
- 高风险 PR 里只能有判定代码的改动，不要顺带别的。

## 数字和评测结论

宣称"变好了"的 PR（解出数、成本、速度）在 Verification 里回答这几个问题：

1. 对比的两边是不是同一组题、同一个模型和推理强度、同一个库版本？
2. 跑了几次？差距比每次运行之间的波动大吗？（例如 9/18 对 8/18 只差一道题，单次运行不能说明变好了。）
3. 有没有题出错、超时或者没跑完，却被算进了分母或分子？
4. 解出的题都经过了内核检查和公理检查吗？

答不上来的写"不确定"，不要写"变好了"。

## PR 的写法

标题用 Conventional Commits：`type(scope): subject`，例如 `fix(portfolio): count a problem as solved only after the assembled proof passes the axiom check`。
正文按 [PR 模板](../.github/pull_request_template.md)：Why、What changed、Scope、Blast radius、Verification，没内容的段落删掉。正文是给审查人的一分钟简报，不是实验日志；长日志放链接。

## 夜间无人值守

开跑前写清楚：完成条件、在哪个 worktree 或检出里跑、哪些可以不问直接提交。
无人值守时 agent 可以提交、推分支、开 PR、合并低风险 PR，但**不合并中、高风险 PR**，留到早上批准。走到死胡同就停下来写清楚原因，不要改目标。

## agent 不能做的事

- 直接推 `main`。数据也走 PR。
- force-push `main`、删别人的分支、绕过失败的 CI。
- 在一个 PR 里同时改判定代码和用它产出的结果。
