# Forge 开发进度与接续说明

给接手的会话（包括限额刷新后被心跳唤醒的同一会话）看的。先读这个文件，再读 `forge/README.md` 和 `forge/AGENT_GUIDE.md`。

## 目标与期限

实现四个 idea（审论文 / AI 原生的 Mathlib2 库 / 检索与拆成引理 DAG / 海量 agent 提问并证明或证伪、供数学家挑选），
不重复造轮子，优先复用已有项目。**2026-11-15 上午 11:00（本地时间）前结束开发和优化**：到点后只做收尾，不再开新工作。

## 现状怎么查

```bash
./forge.sh status          # 库与队列
./forge.sh audit           # 独立审计，必须全部通过
.venv/bin/python -m unittest discover -s forge/tests -t .                       # 单元测试
FORGE_INTEGRATION=1 .venv/bin/python -m unittest discover -s forge/tests -t .   # 含真实 Lean
git status --short
```

分支 `mac-runnable`，forge 的改动**尚未提交**（用户没有要求提交，不要擅自提交或推送）。

## 已完成

- 内核侧校验（`lean/Forge.lean`）、分诊、准入、队列、骨架拆解与拼装、检索（本地 BM25、按名称 `lookup`、
  复用 LeanSearch 的 `find`、复用 Loogle 的 `pattern`）、依赖图、排序、目录、独立审计、论文命题清单与忠实度复核。
- 受控的新定义（`forge define`）：只允许一条 `def`，不许遮蔽根级名称，入库后可在命题里直接用。
- 第一、二轮战役：59 条猜想全部解决；论文 arXiv:2408.15180v2 的 9 条命题形式化、证出、复核。

- 第二篇论文 `s40753-021-00140-1.pdf`：21 条命题（`ab_…`）已全部处理（14 证明、3 证伪、2 自动化、1 Mathlib 已有、1 由其他 agent 证出）。
- 给数学家的挑选页面：`./forge.sh site` 生成 `forge/data/picker.html`，已发布为私有 Artifact
  https://claude.ai/artifact/CfyQ44CYqVbRpVJZ3d1VqL （库更新后重新生成并用同一路径重新发布即可保持链接不变）。
- 心跳：会话内的定时任务，每小时第 17、47 分钟在空闲时唤醒；11:00 后只收尾并自删。

## 收工状态（2026-11-15 11:55）

- 开发期限已过，心跳已删除。库 684 条定理（673 证明、11 证伪）、11 条定义、约 19900 行；`forge audit` 695/695 通过，只用三条标准公理；
  forge 测试 22 项（含真实 Lean）、仓库 `tests` 51 项、`phase2/tests` 9 项全部通过。
- 队列里留着 59 道未证的题，可以直接接着做：第十三轮图论与集合系统 `gr_…` 31 道；论文六 arXiv:2611.07141v1（k-Fibonacci 与 Ford 圆）28 条 `p6_…`，
  尚未证明、尚未独立复核，对这篇论文目前没有任何结论。
- 任何能跑 shell 的 agent（不限于 Claude）读 `forge/AGENT_GUIDE.md` 后都能用 `./forge.sh` 领题和提交；正确性只由 Lean 内核判定。

## 开跑前加固（2026-11-15 中午，已完成）

- 分诊新增：空真检查（`vacuous`）、由库内某条定理一步推出的检查（`known`，写明出处）；评测题保护（`reserved`）。
- 入库改为组提交（并行校验、合并构建、失败逐条回退）；`./forge.sh audit --replay` 做独立内核重放。
- 固定评测：`bench-import` / `bench-check` / `bench-score`。评测题尚未导入（需要下载，等用户同意）。
- 下一步：导入评测集 → 写调度器（外部 agent、预算、熔断）→ 改挑选台（面向非专业读者，shadcn）。

## 接下来按顺序做

1. 处理 agent 的报告：修它们指出的工具问题，补测试。
2. 队列里若还有 `open` 任务，再派证明 agent；领取超时未归还的任务会在一小时后自动回收。
3. 库有更新后重新生成并发布挑选页面。
4. 时间允许就再跑一轮猜想（更难，或换领域：线性代数、群论、组合、分析）。
5. 收尾（最迟 10:30 开始）：`audit`、全部测试、`forge catalog`、更新 `forge/README.md` 的实跑记录和局限、
   更新本文件，向用户如实汇报四个 idea 各自完成到哪、没完成的是什么。

## 约定

- 派子 agent 时把任务写清楚：读 `AGENT_GUIDE.md`、用自己的 agent 名、草稿放各自的 scratchpad 子目录、只通过 `./forge.sh` 改状态。
- 不改命题来让它通过；不把未验证的东西说成已验证。
- 如果当前 token 限额耗尽，停在哪算哪；限额刷新后由心跳提示继续，从上面的“现状怎么查”开始。
