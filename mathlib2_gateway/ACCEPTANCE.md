# Phase 2.1-A API Gateway交付报告

**接口源码及离线测试已完成；真实模型验收等待用户在本机配置服务。** 用户自行保管密钥，接口不要求在聊天中传递密钥。本轮停在Gateway阶段，没有进入Tool Calling。

## 交付项

|项目|状态|交付证据|
|---|---|---|
|供应商抽象|PASS|[Provider接口和两种适配器](providers.py)：responses、chat_completions；模型和地址均可配置|
|环境变量与安全配置|PASS|[config.py](config.py)、[配置说明](README.md)、[隐藏输入并执行小试验的脚本](configure-and-smoke.ps1)|
|真实HTTP请求实现|PASS（本地协议集成）|[transport.py](transport.py)，真实TCP测试覆盖两种协议、503重试、302拒绝及超时；不等于真实模型生成验收|
|结构化JSON|PASS（测试范围）|[contracts.py](contracts.py)：Schema、本地约束、目标逐字一致性；三种显式输出模式|
|日志与模型信息|PASS（测试范围）|[audit.py](audit.py)：独立UUID、请求先落盘、完整有限响应、模型请求名/返回名/版本、用量、耗时、错误和脱敏|
|重试与预算|PASS（本地准入）|[gateway.py](gateway.py)：尝试数、总时间、Token和费用保守预占；未知消费不退款|
|单元测试|PASS|18项通过|
|本地HTTP集成|PASS|4项通过；明确synthetic_fixture，不冒充模型调用|
|真实API数学规划测试|BLOCKED / NOT VERIFIED|1项跳过；没有本机服务/模型/密钥/价格配置，不进行未授权猜测或读取其他凭证|
|原项目保护|PASS|1015个既有受检文件全部哈希相同，无旧代码/数据库写入|
|安全检查|PASS（限定范围）|[完整报告](SECURITY.md)，明确网络、凭证、日志及费用保证的限制|

实际执行共23项测试，**22通过、1跳过**，耗时2.734秒。[完整日志](evidence/tests-final.txt)。测试失败情形使用fixture响应验证错误处理，其请求/响应全部单独保存于evidence/synthetic，不纳入真实AI统计。

## 实测阻止记录与费用

已实际执行CLI预检查，退出码2，原因是环境变量未配置；请求被阻止，没有发送模型请求。[CLI输出](evidence/preflight-cli.txt)、[独立阻止结果](runs/b465918bf9994fdf9c3221d90f21009e/result.json)。

- 实际模型请求派发：0。
- 实际模型生成响应：0。
- 本轮真实API费用：0（未发生出站请求）。
- 真实模型Token用量：未产生，不伪造usage记录。
- 真实模型版本、计划内容和服务账单：尚无证据。

见[成本统计](evidence/cost-summary.json)。本轮没有“真实API成功日志”，因为真实调用没有发生；现有的是配置阻止日志及明确标记的本地协议测试日志。

配置真实服务后，Gateway将记录reported模型、可用版本字段、usage及估算费用；未返回字段为null。按配置价格计算的费用始终标estimated，不能称实际账单金额。配置预算是本地准入控制，不是供应商账单上限保证。

## 接口边界与下一步

调用入口为`generate_plan(goal, config)`或`run_from_env(goal)`，返回带规划和完整状态的字典。Python集成时使用标准`if __name__ == '__main__'`入口，因为Windows HTTP超时隔离使用spawn进程；不要在模块导入顶层发起请求。

成功状态是`plan_generated`，始终同时有`lean_status=not_run`、`formal_goal_verified=false`、`candidate_verified=false`、`approval_status=pending`。模型可以提出错误步骤或虚构引理名；Gateway没有把这些内容当作已检索定理或已证明节点。

原有搜索引擎与DAG Builder未修改。原七题Benchmark和Lemma 1–3历史不覆盖、不重新运行、不自动批准。[文件保护证据](evidence/preservation.json)。

后续只需用户在本机选定服务、模型并配置密钥/价格，执行README中的一次小规模规划请求或真实集成测试，再补充真实调用验收。**在本阶段验收前，不继续实现Tool Calling或完整Math Agent。**
