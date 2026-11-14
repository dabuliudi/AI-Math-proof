# Mathlib2 Phase 2.1-A：独立 API Gateway

本模块只向模型请求**数学规划JSON**，不执行Lean、不构建DAG、不修改旧搜索引擎、不访问SQLite、不批准入库。代码位于独立的`mathlib2_gateway`包。

当前支持两类可配置协议：`responses`和`chat_completions`。服务地址和模型名称均由环境变量指定，可更换兼容服务及模型；**不意味着所有供应商的私有协议或模型参数都自动兼容**。其他协议可实现`Provider`抽象接口，加入受控注册表及配置校验，不需要修改原证明引擎。

当前交付状态见[验收说明](ACCEPTANCE.md)和[安全检查](SECURITY.md)。真实API实测尚缺本机配置；本地fixture测试不能充当模型调用证据。

## 1. 依赖与运行

使用现有Python虚拟环境，唯一额外导入为jsonschema；本机已有4.26.0。若其他机器缺少依赖：

```powershell
cd D:\mathproof
.\.venv\Scripts\python.exe -m pip install -r mathlib2_gateway/requirements.txt
```

不需要安装供应商SDK；请求使用标准库HTTP。先按下节配置环境，再执行：

```powershell
cd D:\mathproof
$env:PYTHONUTF8='1'
.\.venv\Scripts\python.exe -B -m mathlib2_gateway
```

默认目标是自然数序关系的传递性，只要求提出计划。也可用`--goal '完整数学目标'`，长度最多2000字符。本阶段不会向模型发送七题历史证明、DAG、数据库或论文文件。

退出码0表示收到通过本地Schema与目标一致性校验的规划；**不表示计划数学正确或Lean验证成功**。退出码2表示配置阻止、请求失败、预算耗尽或输出不合格，详情留在运行目录。

## 2. 服务配置

所有配置只通过进程环境变量读取，不读`.env`、系统凭证文件或Codex登录凭证。不把服务Key写进源码、命令行参数或日志。

|变量（前缀MATHLIB2_GW_）|用途/默认值|
|---|---|
|PROVIDER|responses（默认）或chat_completions|
|BASE_URL|API根路径，不含末尾/responses或/chat/completions；responses默认https://api.openai.com/v1，chat必须指定|
|MODEL|必填；供应商实际支持的模型标识，不自动选择或更换模型|
|API_KEY|必填；只用于Authorization头。不要在聊天中提供|
|OUTPUT_MODE|json_schema默认；可显式选择json_object或prompt_json|
|CHAT_TOKEN_FIELD|max_completion_tokens默认；兼容服务若要求旧字段，可显式设max_tokens|
|INPUT_USD_PER_MILLION|必填；当前模型每百万输入token美元价格|
|OUTPUT_USD_PER_MILLION|必填；当前模型每百万输出token美元价格|
|PRICE_SOURCE|必填；价格页或账单文档引用|
|PRICE_AS_OF|必填；价格适用日期YYYY-MM-DD|
|MAX_ATTEMPTS|3；含初次请求，范围1–5|
|REQUEST_TIMEOUT|30秒；范围0.1–120|
|TOTAL_TIMEOUT|90秒；范围0.1–600|
|MAX_INPUT_TOKENS|8192；每次预占输入token额度，同时用于请求UTF-8字节预筛|
|MAX_OUTPUT_TOKENS|1200；发送到服务的输出上限|
|MAX_TOTAL_TOKENS|30000；当前运行全部尝试的保守预占额度|
|MAX_COST_USD|0.10；当前运行配置价下的保守预占上限，最大允许10|
|ALLOW_LOCAL_HTTP|默认关闭；1只允许localhost/127.0.0.1/::1的HTTP地址|

`json_schema`请求服务端严格结构输出，但仍在本地验证；`json_object`只请求JSON；`prompt_json`仅提示输出JSON，适用于没有原生JSON模式的兼容模型。后两者不冒充服务端严格Schema支持，且仍必须通过相同本地校验。不自动降级模式、不偷偷更换服务。

原生非这两种协议的服务需要新的Provider适配器；不能仅更换URL就声称支持。网络默认直接连接，不继承HTTP_PROXY等代理变量；需要代理的部署须单独实现和验证，不会偷偷把密钥交给环境代理。

### Windows隐藏输入密钥的小规模实测入口

以下命令运行新目录中的独立配置脚本。它会逐项询问服务信息，密钥隐藏输入；**会尝试一次真实付费请求**。价格由你按选定服务填写，预占预算0.10美元、最多1次请求；运行结束恢复进程环境，不持久化密钥。

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File D:\mathproof\mathlib2_gateway\configure-and-smoke.ps1 -Provider chat_completions
```

若服务支持Responses，改为`-Provider responses`。若兼容Chat服务只支持旧参数，可追加`-ChatTokenField max_tokens`；没有原生JSON模式时可显式追加`-OutputMode prompt_json`。这些选项须以供应商文档为准，不自动试错花费预算。

此命令只为该PowerShell进程设置执行策略，不修改全局策略。也可自行在当前PowerShell窗口设置环境变量并运行Python命令；另一个已打开的进程不会自动继承本窗口新变量。

## 3. 数据结构及真假边界

模型规划必须包含`goal`、`strategy`、`steps`、`uncertainties`；步骤含`id`、`objective`、`reason`，1–8个且ID不重复。禁止额外字段、重复JSON键、非有限数值。`goal`必须与输入逐字一致。

解析成功只说明JSON结构合格及目标字符串未变；步骤的逻辑正确性、引理名称、假设充分性仍未验证。服务可能在自然语言中错误声称“已证明”，也不能改变网关的权威状态：

```json
{
  "status": "plan_generated",
  "generation_origin": "AI Generated",
  "lean_status": "not_run",
  "formal_goal_verified": false,
  "candidate_verified": false,
  "approval_status": "pending"
}
```

上面只是接口示例，不是本轮真实模型结果。模拟测试固定标记`Synthetic Fixture`及`synthetic_fixture`，`real_model_responses=0`。

## 4. 请求日志与审计

每次新建`mathlib2_gateway/runs/<UUID>/`：

- config.json：不含密钥的配置、模型、价格来源和适用日期。
- goal.json、request-template.json：原始目标和实际请求体，包含prompt和Schema。
- attempt-NNN-request.json：出站前落盘，包含请求ID与请求内容，不含Authorization头。
- attempt-NNN-response.json：HTTP状态、允许记录的响应头、响应体、模型元信息、用量、耗时、错误、费用估算及解析结果；每次失败独立保留。
- events.jsonl：时间、序号、前一个事件哈希和本事件哈希；它便于发现不一致，不是第三方签名或防篡改存储。
- result.json：最终状态、计划、所有尝试与费用汇总、Lean未运行状态。
- source-hashes.json：本次网关源码SHA256。配置缺失时没有网络请求，仅保存preflight-error.json和result.json。

原始响应按256KiB限制读取，超限标truncated并失败；不会声称保存了超限部分。已知密钥、Authorization/Bearer及常见JSON转义回显会脱敏，因此日志响应体可能与线上的原始字节不同。异常进程中断时可能只有request记录，必须视为结果/费用未知，不能伪造response或0成本。

`model_requested`与`model_reported`分别记录；服务未返回model_version则为null。system_fingerprint单独记录，不能代替版本号。`real_model_responses`表示live模式收到了符合该协议的生成响应及服务身份字段，不是供应商模型身份的独立鉴定。

## 5. 超时、重试与预算

只重试网络故障、408、429和指定5xx；401/403、配额耗尽、拒绝、输出截断、Schema不合格不自动重试。尊重Retry-After；没有该字段时使用1、2、4、8秒有界退避。Retry-After超过剩余总时间时停止。

HTTP请求在独立子进程执行，父进程控制整次请求截止时间，避免慢速分块响应无限拖延；进程回收最多额外约1秒。不会跟随重定向，也不会关闭TLS证书验证。网络超时不保证供应商停止计算或不计费。

每次派发前预占`MAX_INPUT_TOKENS + MAX_OUTPUT_TOKENS`及按配置价格计算的对应金额；预算不足就不发送。预占不退款，未知用量也不退款。返回用量超过配置输入/输出预占上限时标异常并停止。

**这是本地请求准入预算，不是跨任意供应商的账单硬上限保证。** 字节预筛不是供应商tokenizer；隐藏prompt、不同分词、实际模型路由、额外计费或价格配置错误都可能使账单不同。需要严格账单上限时还须设置服务端额度。默认无价格配置即阻止请求，不以“未知价格=免费”继续。

估算使用全部输入token的普通输入价，不扣缓存折扣，便于保守记账；实际usage和缓存token独立保留。费用区分：`reserved_usd`、`known_estimated_cost_usd`、`estimated_total_usd`、`actual_billed_usd`。任一尝试缺少用量，总估算为null；实际账单未知一直为null。只有未发生出站请求时，0成本可以确定。

预算按一次网关运行计算，重复启动是新预算；没有全账户跨进程资金账本。脚本小试验默认只发一次，避免无意重复花费。

## 6. 测试

离线测试（真实模型测试默认跳过）：

```powershell
cd D:\mathproof
$env:PYTHONUTF8='1'
.\.venv\Scripts\python.exe -B -m unittest discover -s mathlib2_gateway/tests -v
```

已配置服务后，单独进行真实数学规划集成测试：

```powershell
$env:MATHLIB2_GW_LIVE_TEST='1'
.\.venv\Scripts\python.exe -B -m unittest discover -s mathlib2_gateway/tests -p test_live.py -v
```

每次运行该测试会产生真实费用，不能当免费回放。没有配置时该显式测试会失败并留下阻止记录，不能以skip代替通过。测试桩结果全部放在`evidence/synthetic`，不与live日志合并。

## 7. 官方接口依据

Responses的结构输出配置使用`text.format`，Chat协议使用`response_format`。本地仍处理拒绝、截断和校验失败，依据[官方Structured Outputs说明](https://developers.openai.com/api/docs/guides/structured-outputs.md)。

模型用量及状态字段依据[Responses创建接口](https://developers.openai.com/api/reference/resources/responses/methods/create)，Chat的输出上限参数按[Chat Completions接口](https://developers.openai.com/api/reference/resources/chat/subresources/completions/methods/create.md)提供显式选择。兼容服务是否支持这些字段仍需实测。

速率限制与配额耗尽区别参考[官方错误代码](https://developers.openai.com/api/docs/guides/error-codes.md)。未硬编码任何模型价格，也未宣称用户账户可访问某个型号。
