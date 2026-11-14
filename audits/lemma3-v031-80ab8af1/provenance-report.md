# 证明来源审计 — PASS（分类明确），历史排他性作者证明 NOT VERIFIED

当前执行模式确定为 Developer Template + Mathlib Reuse + Lemma Composition。全部30个实质源码行均在运行前写入mathlib2/lemma3.py的SOURCE；check_template读取该字符串并调用Lean，run_lemma3.py没有运行时生成数学证明的模型调用。

历史对话将最初编写归于AI助手，源码元数据也如此声明。它可以称“AI助手编写后固化的脚本”，不能称“项目运行时AI自主规划/生成”。当前验收没有运行AI网关，项目运行路径不调用research_ai.suggest；本对话助手本身是AI，与项目内AI API记录不同。

|问题|结论|依据|
|---|---|---|
|运行前是否有模板|PASS：有，且是完整证明|mathlib2/lemma3.py SOURCE|
|运行时新证明步骤|PASS：没有|脚本读固定source；只生成文件、依赖图及报告|
|项目模型调用|PASS：这条执行路径为0|formalization/check_template、run_lemma3及compile_for无AI网关调用|
|Lemma 1/2是否使用|PASS：未使用|五个证明项的直接依赖及局部闭包均无二者|
|是否直接导入作者独立仓库|PASS：当前导入图未见|import Mathlib.RingTheory.Polynomial.Radical|
|是否完全没用作者代码|FAIL：若作这种绝对声称|Mathlib/RingTheory/Radical.lean头注明Jineon Baek、Seewoo Lee等；本证明复用其库定理|
|最初是否逐字复制公开仓库证明|NOT VERIFIED|没有逐行创作日志或独立仓库比对；author_code_copied=false是自述元数据，不是证据|
|是否有隐藏人工模板|NOT VERIFIED：无法证明历史作者身份；已确认存在公开固定模板|当前源码没有隐藏动态模板分支；不能把固定源码归因于运行时推理|

## 每行来源

所有行在本轮验收前已存在；Human Written没有独立签名证据。Rule Engine标签仅指Lean已有策略/ elaboration执行，不代表项目自行搜索发现证明。

|行|源码|运行时类别|
|---:|---|---|
|4|`theorem mathlib2_unit_of_natDegree_zero {k : Type*} [Field k]`|Developer Template|
|5|`(a : k[X]) (ha : a ≠ 0) (hz : a.natDegree = 0) : IsUnit a := by`|Developer Template; Rule Engine (Lean elaboration/tactics; not autonomous project planner)|
|6|`apply isUnit_iff_degree_eq_zero.mpr`|Developer Template; Mathlib Reuse; Rule Engine (Lean elaboration/tactics; not autonomous project planner)|
|7|`rw [degree_eq_natDegree ha, hz]`|Developer Template; Mathlib Reuse; Rule Engine (Lean elaboration/tactics; not autonomous project planner)|
|8|`rfl`|Developer Template; Rule Engine (Lean elaboration/tactics; not autonomous project planner)|
|10|`theorem mathlib2_unit_of_radical_unit {k : Type*} [Field k] [DecidableEq k]`|Developer Template|
|11|`(a : k[X]) (ha : a ≠ 0) (hu : IsUnit (radical a)) : IsUnit a := by`|Developer Template; Rule Engine (Lean elaboration/tactics; not autonomous project planner)|
|12|`have hr : radical a = 1 := by`|Developer Template; Rule Engine (Lean elaboration/tactics; not autonomous project planner)|
|13|`calc`|Developer Template; Rule Engine (Lean elaboration/tactics; not autonomous project planner)|
|14|`radical a = radical (radical a) := radical_radical.symm`|Developer Template; Mathlib Reuse; Rule Engine (Lean elaboration/tactics; not autonomous project planner)|
|15|`_ = 1 := radical_of_isUnit hu`|Developer Template; Mathlib Reuse; Rule Engine (Lean elaboration/tactics; not autonomous project planner)|
|16|`exact (radical_eq_one_iff.mp hr).resolve_left ha`|Developer Template; Mathlib Reuse; Rule Engine (Lean elaboration/tactics; not autonomous project planner)|
|18|`theorem mathlib2_radical_natDegree_ne_zero {k : Type*} [Field k] [DecidableEq k]`|Developer Template|
|19|`(a : k[X]) (h : 1 ≤ a.natDegree) : (radical a).natDegree ≠ 0 := by`|Developer Template; Rule Engine (Lean elaboration/tactics; not autonomous project planner)|
|20|`have hn : a.natDegree ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one h)`|Developer Template; Mathlib Reuse; Rule Engine (Lean elaboration/tactics; not autonomous project planner)|
|21|`have ha : a ≠ 0 := fun hz => hn (by simp [hz])`|Developer Template; Rule Engine (Lean elaboration/tactics; not autonomous project planner)|
|22|`intro hz`|Developer Template; Rule Engine (Lean elaboration/tactics; not autonomous project planner)|
|23|`have hu := mathlib2_unit_of_natDegree_zero (radical a) radical_ne_zero hz`|Developer Template; Mathlib Reuse; Lemma Composition; Rule Engine (Lean elaboration/tactics; not autonomous project planner)|
|24|`have hau := mathlib2_unit_of_radical_unit a ha hu`|Developer Template; Lemma Composition; Rule Engine (Lean elaboration/tactics; not autonomous project planner)|
|25|`exact hn (natDegree_eq_zero_of_isUnit hau)`|Developer Template; Mathlib Reuse; Rule Engine (Lean elaboration/tactics; not autonomous project planner)|
|27|`theorem mathlib2_mason_lemma3_nat {k : Type*} [Field k] [DecidableEq k]`|Developer Template|
|28|`(a : k[X]) (h : 1 ≤ a.natDegree) : 1 ≤ (radical a).natDegree := by`|Developer Template; Rule Engine (Lean elaboration/tactics; not autonomous project planner)|
|29|`exact Nat.one_le_iff_ne_zero.mpr (mathlib2_radical_natDegree_ne_zero a h)`|Developer Template; Lemma Composition; Rule Engine (Lean elaboration/tactics; not autonomous project planner)|
|31|`theorem mathlib2_mason_lemma3 {k : Type*} [Field k] [DecidableEq k]`|Developer Template|
|32|`(a : k[X]) (h : (1 : WithBot ℕ) ≤ a.degree) :`|Developer Template|
|33|`(1 : WithBot ℕ) ≤ (radical a).degree := by`|Developer Template; Rule Engine (Lean elaboration/tactics; not autonomous project planner)|
|34|`have hnat : 1 ≤ a.natDegree := Nat.succ_le_of_lt`|Developer Template; Rule Engine (Lean elaboration/tactics; not autonomous project planner)|
|35|`(natDegree_pos_iff_degree_pos.mpr (lt_of_lt_of_le (by decide) h))`|Developer Template; Mathlib Reuse; Rule Engine (Lean elaboration/tactics; not autonomous project planner)|
|36|`rw [degree_eq_natDegree radical_ne_zero]`|Developer Template; Mathlib Reuse; Rule Engine (Lean elaboration/tactics; not autonomous project planner)|
|37|`exact WithBot.coe_le_coe.mpr (mathlib2_mason_lemma3_nat a hnat)`|Developer Template; Mathlib Reuse; Lemma Composition; Rule Engine (Lean elaboration/tactics; not autonomous project planner)|

逐步Mathlib名字、局部Lemma使用及历史/运行时区分见provenance-steps.json。

## 自动化能力限制

run_lemma3.py先读取已经完成的模板，再用固定audit_names和REFS扫描字符串构造DAG，并非从未解决目标搜索子引理。certificate.conclusion固定写成confirmed；valid_record只验证文件/版本绑定，不能算法性地证明自然语言与Lean等价。本轮语义PASS来自独立核读，不来自这个固定标志。原used_in_lean字段仅取整文件编译accepted；本轮另读ConstantInfo.value逐边补验。