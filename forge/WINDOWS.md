# 在 Windows 电脑上跑 forge

目标：让 Windows 本和 Mac 一起跑。分工固定为：

- **Mac 是主机**：只有它往 Mathlib2 库里写（清队列、`submit`、入库构建），库和队列以 Mac 上的为准。
- **Windows 只跑评测**：用 `--shard` 拿一半评测题，成绩写进带 `@win` 的轮次文件，推到 GitHub 后由 Mac 拉回来合并。

这样两台机器永远不会同时改同一个文件，git 合并不会冲突。

> 先说清预期：两台电脑用的是**同一个 Codex 账号**，Codex 的额度和限速是两台共用的。
> Windows 本能分担的是本机的 Lean 检查（CPU 和内存），整体能快多少取决于账号限速，不一定能翻倍。

下面的命令都在 **PowerShell** 里执行。可以把这份文件交给 Windows 上的 Claude Code 或 Codex，让它照着一步步做，遇到报错再处理。

## 1. 准备工具（只做一次）

| 工具 | 怎么装 | 装好后检查 |
|---|---|---|
| Git | https://git-scm.com/download/win | `git --version` |
| Python 3.12 | https://www.python.org/downloads/ （安装时勾选 Add to PATH） | `python --version` |
| Lean（elan） | 按 Lean 官网的 Windows 安装说明装 elan：https://lean-lang.org/install/ | 重新打开 PowerShell 后 `elan --version` |
| Codex 命令行 | 已装 ChatGPT/Codex 桌面版并登录过即可；见第 4 步找到它的位置 | `codex --version` 或第 4 步的完整路径 |

## 2. 取代码

```powershell
cd D:\
git clone https://github.com/dabuliudi/AI-Math-proof.git mathproof
cd D:\mathproof
```

仓库是公开的，clone 不需要登录。以后同步 Mac 上的新进展：`git pull`。

## 3. 装 Python 环境和 Lean 依赖

```powershell
cd D:\mathproof
python -m venv .venv
.\.venv\Scripts\python.exe -m pip install -e .
cd lean
lake exe cache get        # 下载 Mathlib 预编译缓存，约 5 GB，第一次要等一会儿
lake build Forge Mathlib2 # 编译 forge 的内核侧命令和 Mathlib2 库
cd ..
.\forge.cmd status        # 能看到 theorems 数量就说明装好了
```

再做一次完整核对（约 2 分钟），确认 Windows 上编出来的库和 Mac 上一致：

```powershell
.\forge.cmd audit
```

## 4. 让 forge 找到 Codex

```powershell
where.exe codex
```

- 能找到：不用做别的。
- 找不到：找到 Codex 可执行文件的完整路径（桌面版通常在 ChatGPT 的安装目录里，文件名 `codex.exe`），然后：

```powershell
setx FORGE_CODEX "C:\完整路径\codex.exe"
```

重新打开 PowerShell 生效。再试一次小任务，确认 Codex 能被调起来：

```powershell
& $env:FORGE_CODEX exec --ephemeral -s read-only -C D:\mathproof "Run .\forge.cmd status and reply with only the number of theorems."
```

**关于沙箱**：调度器默认让 Codex 在 `workspace-write` 沙箱里运行（只能改项目目录）。如果 Codex 在 Windows 上报沙箱不受支持：

- 推荐：改用 WSL2（Windows 自带的 Linux 子系统），在里面按 Mac/Linux 的方式装，命令换成 `./forge.sh`；
- 或者在这台专门跑任务的电脑上加 `--sandbox danger-full-access`。这样 Codex 能改电脑上的任何文件，只在你确定这台电脑上没有重要资料时这么做。

## 5. 分工跑评测

两台机器用**同一个轮次名**、不同的 `@机器` 后缀，各拿一半题：

Mac 上：

```bash
./forge.sh run --run mf2f-r2@mac --bench minif2f_test --all --shard 1/2 --workers 5
```

Windows 上：

```powershell
.\forge.cmd run --run mf2f-r2@win --bench minif2f_test --all --shard 2/2 --workers 5
```

两边各自跑完后，Windows 上把成绩推回去：

```powershell
git add forge/data/bench/runs forge/data/runs
git commit -m "Benchmark run mf2f-r2@win"
git push
```

Mac 上 `git pull`，然后：

```bash
./forge.sh bench-score minif2f_test   # "combined" 里的 mf2f-r2 就是两台合起来的总成绩
```

## 不要在 Windows 上做的事

- 不要在 Windows 上 `submit`、清队列（`run` 不带 `--bench`）或 `define`：这些会改库和队列，和 Mac 上的版本冲突。
- 不要把 Windows 上的 `lean/Mathlib2`、`forge/data/ledger.jsonl`、`forge/data/tasks` 的改动推上去。
