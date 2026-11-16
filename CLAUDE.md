# RSI Math

项目目的见 README 的「核心目的」，不得改写。

## 开发流程

按 [docs/DEVELOPMENT.md](docs/DEVELOPMENT.md) 做。要点：

- 不直接推 `main`。每个任务一个 worktree，从 `origin/main` 切分支，第一个能验证的单元做完就开 PR。
- 主检出 `~/AI4math` 只跑实验，库和结果只通过 `forge snapshot` 开数据 PR 进 `main`。
- 合并条件看 `python scripts/risk_tier.py`：低风险 CI 通过即合；中、高风险要 `/code-review` 和项目负责人批准。
- 审查最多三轮。批准只对一个提交有效。
- 先证明再声称：用真实运行的输出，不用"能编译"。

## 常用命令

- 测试：`python -m unittest discover -s forge/tests -t .`
- 库一致性：`python -m forge consistency`
- 风险级别：`python scripts/risk_tier.py`
