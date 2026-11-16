# RSI Math

**一个会自己变强的数学 AI，每一步都由 Lean 验证。**

它拿真实论文的命题和未解决的问题当考题：证得出的进定理库，证不出的拆成小引理留给下一轮，
改进自己的提示词和工具时必须在固定难题集上真的变好才采纳。衡量它的只有一条曲线：同一组难题的解出率随轮次上升。

方向与路线图见 [ROADMAP.md](ROADMAP.md)。

> 早期开发中。接口、目录和数据格式随时可能变。改动通过 PR 进入 `main`，流程见 [docs/DEVELOPMENT.md](docs/DEVELOPMENT.md)。
> 命令行和内部代码目前仍叫 `forge`（流水线的内部名），对外统一叫 RSI Math。

## 核心目的（项目创始人原话，不得改写）

1. 用lean4审核目前人类已有的、能用lean4实现和验证的数学论文，全部用lean4实现并验证一遍；

2. 用lean4尝试构建新的问题，实现一个AI native版本的mathlib证明大全——mathlib2——比现有人类数学家构建的mathlib要大一两个数量级；

3. 当人类尝试定义新的问题的时候，先从mathlib和mathlib2中搜索已有近似证明，尝试拆分成DAG的lemma形式，用mathlib2更加快速便捷地实现部分证明；

4. 最后用大量、超大量的AI Agent尝试大量、巨大量、无限提出新的问题，并且并行in parallel用已有mathlib2去验证或者证伪这些新问题，最后由数学家 cherry pick出其中有价值的问题和完整证明方案出来。

这四条是项目的目的；路线图、评测和工程决定都是为它们服务的手段。和这四条冲突的计划要改计划，不改目的。

## 现在能做什么

| | 现状 |
|---|---|
| 定理库 Mathlib2 | 1030 条定理（919 证明、111 证伪）、128 条定义，全部由 Lean 内核检查并可整库重放 |
| 论文体检 | 6 篇论文逐条形式化并证明，发现 1 处计算错误；另有 19 篇新论文在做双人形式化（238 条命题） |
| 评测 | miniF2F 234/243；PutnamBench 抽样 40/40（Codex gpt-6.1-sol） |
| 调度 | 用 Codex 等外部 agent 批量证明、跑评测、复核论文，可多台电脑分工 |

所有数字都是自测，细节和局限见 [forge/README.md](forge/README.md)。

## 安装（macOS / Linux）

需要：Git、Python 3.11+、约 10 GB 磁盘。

```bash
# 1. 安装 Lean 的版本管理器 elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
```

装完重开终端，或者运行 `source ~/.elan/env`，让 `lake` 命令生效。

```bash
# 2. 取代码
git clone https://github.com/dabuliudi/AI-Math-proof.git && cd AI-Math-proof
```

```bash
# 3. 下载 Mathlib 预编译缓存（约 5 GB），编译本项目的库
cd lean && lake exe cache get && lake build Forge Mathlib2 && cd ..
```

```bash
# 4. 确认装好：能看到定理数量即可
./forge.sh status
```

Windows 用 `forge.cmd` 代替 `./forge.sh`，步骤见 [forge/WINDOWS.md](forge/WINDOWS.md)。

## 常用命令

| 命令 | 作用 |
|---|---|
| `./forge.sh status` | 库和任务队列的概况 |
| `./forge.sh search "关键词"` | 在库里找定理 |
| `./forge.sh propose --name 名字 --statement "命题"` | 提一个新命题（自动分诊，合格的进队列） |
| `./forge.sh run --run 名字 --workers 3` | 让 Codex 清队列（需要本机装好并登录 Codex） |
| `./forge.sh audit --replay` | 用 Lean 内核把整个库从头检查一遍 |
| `./forge.sh regress` | 跑事故回归集 |

## 目录

```
forge/        流水线：分诊、入库、调度、评测、复核（Python）
lean/         Lean 工程；Mathlib2 库在 lean/Mathlib2/
forge/data/   任务队列、台账、评测集、运行记录
docs/         早期工作台的文档
```

## 更多

- [forge/README.md](forge/README.md)：设计、每一轮实跑记录、已知局限
- [forge/AGENT_GUIDE.md](forge/AGENT_GUIDE.md)：给 AI agent 看的操作手册
- [forge/WINDOWS.md](forge/WINDOWS.md)：Windows 安装与两台电脑分工
- [docs/workbench.md](docs/workbench.md)：早期的 Streamlit 工作台与 Lemma 3 实验
