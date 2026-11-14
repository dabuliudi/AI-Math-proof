# 数据库完整性只读调查

调查日期：2026-11-14，时区Asia/Shanghai。产品代码、现有实验及数据库均未修改。本次仅在本报告目录生成调查材料。

**结论：没有发现已比较备份中的记录被删除；Lemma 1–3及其证明历史保持一致。最近一次差异是丰盈数论文4个候选的状态字段补齐与4条规划历史新增。写入代码路径有依据，具体调用者和触发进程仍不能确认。**

## 1. 比较范围与证据限制

共读取14个数据库文件，全部`integrity_check=ok`。其中8份正式备份/验收副本与当前库逐表、逐主键对比；5份测试/开发分支只做清点和完整性检查，不把分支中的独立测试数据误当作主库删除记录。另1份是当前主库。清单包含路径、大小、SHA256、文件修改时间、表行数和完整性结果：[完整清单](database-inventory.json)。

只使用SQLite URI `mode=ro`、`query_only=ON`、读事务及只读PRAGMA；未导入会执行迁移的Store类，没有VACUUM、修复、覆盖、恢复或调用旧工作台规划函数。逐表原始读取结果另存为[当前库调查快照JSON](database-current-rows.json)，它是调查材料，不是替换数据库的文件。

Phase 2开始时保存的主库SHA256是：

```text
5e355630a01bff5422913f9a01c9ce2641c7356ded9d986a62ac68b449eec18c
```

本次清点的14份数据库没有任何一份与它完全一致。因此，**精确重建Phase 2开始时的完整数据库字节和所有行：BLOCKED（缺少该时间点完整快照）**。不能用事后副本代替开始快照，也不能把文件mtime当作每条记录的提交时间。[精确基线可用性](database-baseline-availability.json)。

以下“近期差异”以此前Lemma 3独立验收副本为基线。当前主库与Phase 2结束时旧回归测试使用的副本逐行相同，没有发现该次验收之后又出现新的逻辑变化。

## 2. 近期逐表差异

基线：`audits/lemma3-v031-80ab8af1/workspace/data/mathlib2.sqlite`。

|表|基线行数|当前行数|新增|修改|删除|
|---|---:|---:|---:|---:|---:|
|sources|9|9|0|0|0|
|candidates|92|92|0|0|0|
|events|120|120|0|0|0|
|verified|0|0|0|0|0|
|document_parses|5|5|0|0|0|
|math_objects|171|171|0|0|0|
|workbench_state|20|20|0|4|0|
|workbench_history|38|42|4|0|0|
|proof_runs|9|9|0|0|0|

数据库结构未改变。每条差异的主键、完整before/after原值及JSON字段路径见[近期逐记录差异](database-diffs/audits__lemma3-v031-80ab8af1__workspace__data__mathlib2.sqlite.json)。缺失字段与JSON null明确区分。

### 修改的4条记录

都位于`workbench_state`，不是候选原文或Lean证明表。

|candidate_id|文献ID|原候选主题|字段变化|
|---|---:|---|---|
|73|8|Abundant number定义|新增candidate_alignment="unconfirmed"、candidate_verified=false|
|74|8|Perfect number定义|同上|
|75|8|完全数倍数与丰盈数命题|同上|
|76|8|两个素数乘积的练习命题|同上|

四条记录的其余字段逐值一致。这里仅报告数据库中已有的数学文字，不判断或修改其中命题的正确性。

### 新增的4条记录

都位于`workbench_history`，action=`planning`，payload均为`{"status":"acyclic","unresolved":2}`。

|history id|candidate_id|created UTC|北京时间|
|---|---:|---|---|
|39|73|2026-11-14T11:34:46.376715+00:00|2026-11-14 19:34:46.376715|
|40|74|2026-11-14T11:34:46.380715+00:00|2026-11-14 19:34:46.380715|
|41|75|2026-11-14T11:34:46.384780+00:00|2026-11-14 19:34:46.384780|
|42|76|2026-11-14T11:34:46.388785+00:00|2026-11-14 19:34:46.388785|

这12.07毫秒内的四条应用时间字段与一次按文献批量保存规划相符。主库文件mtime也在这一秒；它们不是独立的操作者身份或进程证据。[时间线与相关候选原记录](history-and-timeline.json)。

## 3. 变化来源：哪些已确认，哪些尚未确认

**已确认的代码事实：**

1. [workbench.py第18行](D:/mathproof/mathlib2/workbench.py:18)的`state()`构造默认状态，包含unconfirmed和false，随后合并已有状态。旧行缺少这两个键时，会读出补齐后的值；读出本身不写库。
2. [workbench.py第151行](D:/mathproof/mathlib2/workbench.py:151)的`plan_for()`逐个处理所选文献的候选，并调用`_save(...,'planning',...)`。
3. [workbench.py第35行](D:/mathproof/mathlib2/workbench.py:35)的`_save()`替换状态行，并插入带当前UTC时间的历史行。这与本次字段及历史差异吻合。
4. [app.py第194行](D:/mathproof/app.py:194)“建立 / 更新证明规划”按钮会调用该路径。单纯显示DAG调用的是`graph_for()`，这一展示分支没有该保存循环。

**推断：**这很可能是一次旧工作台针对文献8的规划保存，或其他代码主动调用了同一函数。不能仅凭数据库中的action字符串排除直接SQL写入等其他来源。

**NOT VERIFIED：**谁点击、是否自动化点击、哪个进程或命令实际调用、是否存在外部直接写入。检查了本项目相关的5份本地Codex会话日志，在2026-11-14 11:33–11:36 UTC窗口没有找到事件记录；这属于证据缺口，不是“某人没做”的证明。数据库表也没有actor、session_id、process_id、request_id字段用于追溯。

源码行、文件哈希、检查日志范围和孤立引用检查见[来源证据](origin-evidence.json)。本轮没有为了复现来源而执行`plan_for()`，没有新增测试写入。

## 4. Lemma 1–3与其他历史实验

与此前独立验收副本比较，候选85、87、89涉及的以下行全部逐值相同：

|表|相关行数|结论|
|---|---:|---|
|candidates|3|相同|
|workbench_state|3|相同|
|proof_runs|9|相同|
|workbench_history|21|相同|
|events|0|相同|
|verified|0|相同；无人被自动批准|

全部92个候选原记录、171个数学对象、9个证明运行、120条事件和所有原始文献记录均与最近旧副本相同；非Lemma候选只有73–76上述状态变化，其他候选状态未变。更早备份中已有的proof_runs和历史记录也均保留，未检测到删除。

额外逐表检查source_id和candidate_id引用，未发现孤立引用。此检查不等价于证明全部候选数学语义正确；完整性与数学正确性仍分开。

## 5. 全部备份的逐记录对比索引

下表为“该备份→当前库”的累计变化，**不能全部归因于Phase 2**。每个链接提供全部表、逐条主键、完整旧/新记录和字段级差异；未变化的表也列出行数。

|基线|新增总行数|修改总行数|删除总行数|逐记录报告|
|---|---:|---:|---:|---|
|before-v0.2.1|312|28|0|[JSON](database-diffs/data__backup-before-v021.sqlite.json)|
|before-v0.2.2|261|0|0|[JSON](database-diffs/data__backup-before-v022.sqlite.json)|
|before-v0.3|182|0|0|[JSON](database-diffs/data__mathlib2.sqlite.before-v03.bak.json)|
|before-Lemma1-alignment|28|7|0|[JSON](database-diffs/data__before-lemma1-alignment.sqlite.json)|
|before-Lemma2|22|6|0|[JSON](database-diffs/data__before-lemma2.sqlite.json)|
|before-Lemma3|16|5|0|[JSON](database-diffs/data__before-lemma3.sqlite.json)|
|Lemma3独立验收副本|4|4|0|[JSON](database-diffs/audits__lemma3-v031-80ab8af1__workspace__data__mathlib2.sqlite.json)|
|Phase2结束时回归副本|0|0|0|[JSON](database-diffs/phase2__legacy-regression__f7b2b657d5694e42bcc9375d3960dd33__workspace__data__mathlib2.sqlite.json)|

最早备份的28条candidates修改包含schema演进带来的列差异；不能把“整行有差异”直接解释为原数学内容被修改。结构差异与payload字段差异在机器报告中分别列出。[总索引](database-diff-index.json)。

## 6. 只读保证与未完成项

本次调查前后，988个既有受检文件哈希全部一致，包含所有数据库、旧实验、代码与Phase 2基准；没有新增既有目录内文件。新材料只写本调查目录。[保护检查](preservation.json)。

本轮结论：逻辑记录保留 **PASS**；近期变化逐记录列明 **PASS**；精确开始快照恢复 **BLOCKED**；调用者身份归因 **NOT VERIFIED**。后续若需要严格归因，应先取得当时进程/操作审计日志，或在未来版本中经设计加入actor和request_id；本轮未修改日志结构或补写历史。
