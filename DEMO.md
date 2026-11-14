# v0.3 工作台演示

启动后：文献管理导入两篇PDF → 候选审核对照Lemma1与定义 → 检索divRadical_dvd_derivative → Proof DAG查看明确/推测关系 → Lean Lab载入模板、实际编译并查看公理 → 经真人核对后入库。无需API密钥。详细说明见 reports/delivery-v03.md。

以下保留旧版教学演示：

# 五分钟演示：v0.2.2

前置：已安装依赖；若展示真实 Lean，先完成工具链及 Mathlib 缓存初始化。一键执行 `& 'D:\mathproof\run-demo.cmd'`，访问 http://127.0.0.1:8501 。

1. 0:00–1:00：选择侧栏文献 8（真实论文），输入选“当前文献”，运行。查看文本 parsed、结构 recognized、候选 extracted、Lean not_run；重复运行不增加来源或候选。
2. 1:00–2:00：原文预览第 28 页，查看丰盈数、完全数定义。候选详情显示页码、完整原文和字符区间。
3. 2:00–3:00：查看4个正式候选和35份保留资料，打开主命题的 potential_counterexample 提示，比较原文、仅空白规范化的文本及单独建议的 k>1 修正版。Lean 命题仍为空。DAG有3条规则推测定义依赖、0条显式边，Lemma 3、4未解析；不把规则推测当作已验证证明。
4. 3:00–4:00：选择 nat.md 教学样例运行，展示 proved / proved / refuted / unknown 以及真实 Lean 输出。四类角色日志保留。来源筛选切换后，真实论文与教学样例不会混在同一列表。
5. 4:00–5:00：核对教学已证明候选原文，填写审核人及意见入库；真实论文候选仍不能批准。查看 Mathlib 词法检索与已批准知识检索。收尾说明 OCR、跨页语义和自动数学理解仍是下一阶段工作。

CLI 也支持 `.\.venv\Scripts\python.exe -m mathlib2.cli demo 文件路径`。不要把 DEMO.md 当作网页地址输入浏览器。
