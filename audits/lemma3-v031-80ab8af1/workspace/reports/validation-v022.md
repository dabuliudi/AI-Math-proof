# v0.2.2 实际验证记录

## 自动测试

完整 unittest：26项通过，19.184秒，含真实 Lean/Mathlib 集成；没有跳过项。完整输出见 tests-v022.txt。

覆盖原有四候选、真实proved/ proved/ refuted/ unknown流程、公理/sorry门禁、SQL持久化与人工审核限制；新测试覆盖资料过滤、三字段保真、严格/非严格边界、显式/推测/未解析依赖、循环与歧义、版本隔离、实际PDF重复读取和固定标注指标、上传页面与边界提示。

扫描PDF、普通无数学PDF、损坏PDF为异常测试合成材料。真实论文测试读取原始PDF，SHA256=c60c9c32ab6e8daf04e31c624d385ad92a6b97973518050cfcaaedbcfdc5a5da，不使用替代样例。

初次文献测试因Windows受限临时目录权限失败；允许访问后5项文献测试通过，后续完整26项通过。没有把环境失败算作通过。

## 构建与类型检查

- mypy app.py --ignore-missing-imports --follow-imports=silent：无问题。
- compileall（mathlib2、app.py、scripts、tests）：通过。
- lake -d lean build：55项任务成功；Demo三个声明公理仅propext、Quot.sound。构建日志属于教学工程，不是论文候选证明。

## 实际运行页面（2026-11-12）

Streamlit真实服务127.0.0.1:8766，通过本地Agent API运行当前文献流程，显示4个候选；切换主命题详情后potential_counterexample及边界提示可见，异常0。使用独立数据库data/agent-ui-v022-check.sqlite，测试结束服务已关闭。

日志 ui-server-v022.log 无异常或新警告；页面快照 ui-snapshot-v022.json；协议 ui-openapi-v022.json。可复现命令：`.\.venv\Scripts\python.exe scripts/check_ui_v022.py`。此检查验证实际运行逻辑，不是浏览器视觉布局验收。

AppTest另行验证真实PDF上传、来源切换、重复解析、资料详情和批准按钮状态。AppTest运行时的一条missing ScriptRunContext是其独立测试模式提示，不是运行页面异常。

## 数据与论文验收

旧来源8条、候选53条、事件120条、审核0条逐行保留。升级后候选57条；0.2.1解析仍可读取。独立重读论文两次结果相同；重复运行不新增候选。详情见abundant-v022.md/json。

正式候选4个，均unknown、not_formalized、Lean not_run。3条DAG边均为推测定义使用；显式引用0条，Lemma3/4仍未解析。没有将失败搜索视为证伪。

## 尚未完成人工验收的部分

标注集由助手对照原文及页图核读，human_reviewed=false。真实人类独立复核仍待用户/研究者完成。本次不能冒称已完成用户要求的人工验收。

有限标注范围内正式候选precision/recall均4/4，图注误入0/4，文字条件遗漏0/11，切片定位4/4。图像明确依赖召回0/2，显式依赖precision为N/A。以上指标不是全文准确率，更不代表数学语义已理解或证明成立。
