# Mathlib2 Research Workbench v0.3

## Forge：定理铸造厂（新）

以 Lean 内核为唯一裁判的并行流水线：论文命题、人提的问题、agent 提的猜想进同一个队列；
分诊去掉已知的、重复的和平凡的，随机测试先找反例；agent 通过命令行领任务、校验、提交；
通过准入的定理进入可互相引用的 Lean 库 `lean/Mathlib2/`。说明见 [forge/README.md](forge/README.md)，
agent 操作手册见 [forge/AGENT_GUIDE.md](forge/AGENT_GUIDE.md)，当前库目录见 [forge/data/CATALOG.md](forge/data/CATALOG.md)。

macOS / Linux 入口：`./forge.sh status`（Forge）、`./run-demo.sh`（下文的 Streamlit 工作台）。

## Mason–Stothers Lemma 3 基准实验

完整交付、实际51项回归结果及失败记录见[实验交付报告](reports/lemma3-delivery.md)。

论文第7页命题：任意域上的多项式若次数至少为1，其 radical 次数也至少为1。最终 Lean 目标使用 `degree`，并明确证明与 `natDegree` 的转换。证明由本次对话助手编写，随后固化为可复跑模板；项目没有自动发现该证明，也没有产生模型 API 调用记录。分类为 **New Proof（新增组合脚本，不是新数学结果）**，库定理仍标为 Mathlib 复用。Lemma 1、2 没有参与本证明，原历史保留，知识库入库仍需人工批准。

- [语义对齐报告](reports/lemma3-alignment.md) / [论文完整声明及证明定位](reports/lemma3-source.json)
- [Mathlib 检索](reports/lemma3-retrieval.md) / [多层 Proof DAG](reports/lemma3-dag.md) / [逐步来源](reports/lemma3-steps.json)
- [Lean 源码](lean/Research/Lemma3.lean) / [实际编译、公理审计及历史保留证据](reports/lemma3-result.json)
- [三个实验的成本对比](reports/lemma3-costs.md) / [回归测试输出](reports/tests-lemma3.txt)

在本工作区复跑实验（追加新的真实验证记录，重新核验来源文件；不批准入库）：

```powershell
cd D:\mathproof
$env:PYTHONUTF8='1'
.\.venv\Scripts\python.exe scripts/run_lemma3.py
```

完整回归使用下文测试命令并设置 `MATHLIB2_INTEGRATION=1`。Lean Lab 可选择 Lemma 3 模板重编译；重跑模板不表示再次 AI 推理。

本次升级说明、实际验收和限制见 [v0.3 交付报告](reports/delivery-v03.md)。七个工作空间包括研究首页、文献管理、候选审核、交互 Proof DAG、Mathlib 检索、Lean Lab 和知识库。以下 v0.2.2 说明保留为兼容背景；新版入口及状态以本节为准。

**启动：** 在 PowerShell 执行 `& 'D:\mathproof\run-demo.cmd'`，打开 http://127.0.0.1:8501 。

**真实多项式实验：** [Lemma1.lean](lean/Research/Lemma1.lean) 已实际编译通过；属于 Theorem Reuse，复用 Mathlib 的 `divRadical_dvd_derivative`，不是 AI 独立新证明。固定 Lean/Mathlib v4.24.0。新环境先补充模块缓存：

```powershell
cd D:\mathproof\lean
$env:PATH='D:\mathproof\.tools\lean-4.24.0-windows\bin;'+$env:PATH
lake exe cache get Mathlib.RingTheory.Polynomial.Radical
lake env lean Research/Lemma1.lean
```

首次 Mathlib 声明检索扫描本地源码，可能需一分钟以上；同一进程内缓存。匹配分为精确声明名、部分表达式、关键词；数学等价性不能由字符串匹配决定。

**工作流：** 导入两篇论文 → 核对候选的原文和定义域 → 保存审核人及意见 → 搜索 `divRadical_dvd_derivative` → 建立DAG → 在 Lean Lab 选择适用Lemma1及内置模板并真实编译 → 核对证明及语义一致性后人工入库。修改规范化表述后旧证明失效，需重新编译。无AI时模板按钮不会冒充AI生成。

**可选研究AI网关：** 独立模块 research_ai.py 使用 `MATHLIB2_RESEARCH_API_URL`、`MATHLIB2_RESEARCH_API_KEY`、`MATHLIB2_RESEARCH_MODEL` 环境变量。网关接收task/statement/model并返回suggestions字符串数组；不执行返回代码，不修改验证状态。本次没有真实API调用，界面主要使用规则与可信模板。

**新增数据库表：** workbench_state、workbench_history、proof_runs。首次升级自动保存 `<数据库路径>.before-v03.bak`。旧表记录不删除；恢复时关闭所有应用，另存当前数据库后将备份复制为原数据库路径（会回到升级前状态，勿丢弃新版数据库）。原文不可覆盖，审核及规范化修改存入新表。

**复现：** `python scripts/report_v03.py` 生成两篇论文实际回归JSON；`MATHLIB2_INTEGRATION=1` 后运行 unittest discover，包括真实Lean。详细命令见下方测试说明。测试和工具必须使用本项目 `.venv\Scripts\python.exe`。

本地优先的数学文献解析与 Lean 验证原型。新增无需大模型的通用结构提取，保留 v0.1 教学演示及真实 Lean 验证。提取数学文字不等于理解命题，也不等于证明成功。

v0.2.2 增加资料过滤、原文/规范化/Lean 三字段、提取质量分层和边界风险审计。真实论文现有 39 个资料片段，4 个正式候选；图表标题、学生案例、普通引用和无关练习保留在“原始资料”中。定义使用产生 3 条明确标为推测的依赖边；显式依赖仍为 0，Lemma 3、4 等待图像转录。

原题 any k ∈ N 不变；k=1 被标为 potential_counterexample，建议增加 k>1 的版本单独存放，不能当作论文原文或 Lean 证伪。质量分数只反映提取质量。

## Windows 一键启动

当前工作区已安装依赖和便携式 Lean，在 PowerShell 直接执行：

```powershell
& 'D:\mathproof\run-demo.cmd'
```

网页入口是 **http://127.0.0.1:8501**。`DEMO.md` 是本地说明文件，不是网站域名。若 8501 已被占用，请使用已有 Mathlib2 服务，或在终端手工指定其他空闲端口。

也可以双击 run-demo.cmd。此入口无需修改 PowerShell 脚本执行策略；关闭终端会停止服务。

## 新环境安装

需要 Python 3.11+ 和 Git。Python 安装：

```powershell
cd D:\mathproof
python -m venv .venv
.\.venv\Scripts\python.exe -m pip install -e '.[pdf]'
```

论文规则解析不需要 Lean、AI API 或 API 密钥。可选 PDF 依赖是 pypdf 和 fontTools；fontTools 用于实际论文的字体解码。若需复现本工作区的 Python 依赖版本，可使用 requirements-lock.txt。

Lean 教学演示使用固定 Lean/Mathlib v4.24.0。通过官方 Lean 安装方法准备 Lake，或使用本地 `.tools/lean-4.24.0-windows/bin`。首次设置：

```powershell
$env:PATH="D:\mathproof\.tools\lean-4.24.0-windows\bin;"+$env:PATH
cd D:\mathproof\lean
$env:MATHLIB_NO_CACHE_ON_UPDATE='1'
lake update
lake exe cache get Mathlib.Data.Nat.Init
lake build
cd ..
```

只拉取演示所需模块缓存，避免全库缓存下载。首次初始化需要网络和足够磁盘空间。保留 lake-manifest.json 以固定依赖提交。Linux/macOS 对应使用 `.venv/bin/python`、系统 Lake，并使用 `export MATHLIB_NO_CACHE_ON_UPDATE=1`。

## 使用流程

1. 上传 PDF / LaTeX / Markdown / TXT；选择“上传文件”并运行。也可选择侧栏历史文献，再选“当前文献”运行。
2. 页面分别展示文件接收、正文解析、结构识别、候选提取、Lean 运行状态。扫描型或无文字 PDF 标记 needs_ocr；损坏 PDF 标记 failed；零命中为 no_objects。
3. 当前文献的候选列表显示对象类型、页码、识别状态、阶段和验证状态。详情含完整原文、前后文、字符区间和 proof_steps。
4. DAG 预览列出节点、明确依赖、proof_of 关联及未解析引用。仅共现不建边；找不到声明或有歧义时记录 uncertain。
5. 选择“nat.md 教学样例”仍可运行四个固定候选与真实 Lean。规则论文候选默认不调用 Lean。
6. 只有真实 Lean 已证明且人工核对原文一致性的候选才能进入已批准知识库。

本次已上传论文仍对应 source_id=8。旧记录不删除；解析记录按版本与旧 source payload 分开保存。重复上传相同文件字节，复用同一来源、同一版本的解析和候选，不重复插入。旧版已有的重复来源行仍保留。页面默认显示当前版本候选，旧版候选可在只读展开区查看。

## 支持范围与状态

识别 Definition、Theorem、Lemma、Proposition、Corollary、Proof、Example、Conjecture；支持编号标题、Markdown 标题、LaTeX 环境，及有限的显式定义句、编号练习、证明图注和叙述步骤。普通正文单独提到 Theorem 不生成定理。

- **Extracted**：已定位的证据/不确定片段。
- **Candidate**：规则识别出的数学对象，尚未形式化。
- **Formalized**：已有 Lean 表述/策略草稿，不代表编译通过。
- **Lean Verified**：Lean 实际接受目标且公理审计通过。
- **Human Approved**：已验证并经人工批准。

验证状态仍为 proved / refuted / unknown。证明失败不是证伪。refuted 必须有原命题否定的 Lean 证明。可接受公理仅为 propext、Classical.choice、Quot.sound；sorryAx、自定义公理、缺失审计输出、非零退出均不能证明成功。原有 Lean worker 未修改。

位置以每页 pypdf 原始字符串的 Unicode 字符计数，区间 [start,end)。PDF 页码从 1 开始，不是期刊印刷页码。规则置信度不是数学正确率。跨页内容不自动续接；图注不代替手写图；没有 OCR。全文/公式阅读顺序仍需人工复核。未知漏检数不能报告为零。

## Mock 与 HTTP 提供者

默认 `MATHLIB2_PROVIDER=mock`。仅包含 `MATHLIB2_DEMO_NAT` 标记的自编教学文献走固定四候选流程；其他文献走通用规则提取，不再返回空候选作为唯一结果。

HTTP 提供者保留。显式设置 `MATHLIB2_PROVIDER=http` 时，通用提取后还会调用配置的服务，发送至多 30000 字符文献文本。没有配置 API，本次也没有测试真实模型。配置示例：

```powershell
$env:MATHLIB2_PROVIDER='http'
$env:MATHLIB2_API_URL='https://your-gateway.example/generate'
$env:MATHLIB2_API_KEY='你的密钥'
$env:MATHLIB2_MODEL='模型标识'
```

这要求一个接受 `task/source/limit/model` 并返回以下 JSON 的网关，不是所有厂商接口的直接适配器：

```json
{"candidates":[{"statement":"∀ n : Nat, n + 0 = n","strategy":"omega","neg_strategy":"at_zero","label":"加零不变"}]}
```

HTTP 超时 45 秒，无自动重试；密钥以 Bearer 发送，不存入 SQLite。Lean 仍限制单变量自然数算术与白名单策略 omega/simp/reuse；每候选正反各一次，双路并发，编译 30 秒、1024 MB、200000 心跳。通用文献候选不受 1–8 个 AI 候选预算限制。

## 测试及真实论文报告

```powershell
cd D:\mathproof
$env:PYTHONUTF8='1'
$env:PATH="D:\mathproof\.tools\lean-4.24.0-windows\bin;"+$env:PATH
$env:MATHLIB2_INTEGRATION='1'
.\.venv\Scripts\python.exe -m unittest discover -s tests -v
$env:MATHLIB2_PROVIDER='mock'
.\.venv\Scripts\python.exe scripts/report_v022.py s40753-021-00140-1.pdf
```

真实 PDF 测试直接读取已上传文件，不以模拟文字替代；换机器可设置 `MATHLIB2_PAPER`。缺少文件时明确跳过。扫描页、普通 PDF、损坏 PDF 为专门构造的异常测试材料，不冒充真实论文。mypy 用于开发类型检查：`python -m mypy app.py --ignore-missing-imports --follow-imports=silent`。

- [新版架构及数据库变化](reports/architecture-v022.md)
- [真实论文对比、语义及指标报告](reports/abundant-v022.md)
- [完整候选、来源及 DAG JSON](reports/abundant-v022.json)
- [完整测试输出](reports/tests-v022.txt)
- [测试说明及实际页面检查](reports/validation-v022.md)
- [五分钟演示脚本](DEMO.md)

核心模块为 ingest、structures、documents、candidate、planner、store；CLI `python -m mathlib2.cli demo 文件` 和 `inspect` 保持可用。数据库可用 `MATHLIB2_DB`（UI）或 `--db`（CLI）切换。项目是本机科研原型，不提供多用户权限和数据库防篡改签名。

新增 quality、metrics 模块。小型标注集在 tests/fixtures/abundant-ground-truth.json，由助手对照原文和页图核读，human_reviewed=false，仍需研究者独立复核。所报精确率/召回率只适用于标注范围和丰盈数专题；图内显式依赖召回率0/2，不能用定义词匹配率替代。没有新增大型依赖。
