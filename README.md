# AI-Math-proof

让 AI 大规模地做数学：AI 提出命题、写出证明，Lean 计算机逐步检查，检查通过的进入定理库 **Mathlib2**，数学家从中挑选有价值的。

> 早期开发中。接口、目录和数据格式随时可能变。

## 现在能做什么

| | 现状 |
|---|---|
| 定理库 Mathlib2 | 997 条定理（895 证明、102 证伪），全部由 Lean 内核检查并可整库重放 |
| 论文体检 | 6 篇论文逐条形式化并证明；发现 1 处计算错误 |
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
git clone -b mac-runnable https://github.com/dabuliudi/AI-Math-proof.git && cd AI-Math-proof
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
