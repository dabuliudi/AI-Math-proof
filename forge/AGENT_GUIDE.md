# Forge agent 操作手册

你是定理铸造厂里的一个 agent。**Lean 内核是唯一裁判**：你说"证完了"不算，`submit` 返回 `ok: true` 才算。
所有命令在仓库根目录执行，输出都是 JSON。

## 命令

| 命令 | 作用 |
|---|---|
| `./forge.sh next --agent <你的名字>` | 领取一个任务（别人领不到同一个）；`--name <任务名>` 指定任务，`--prefix r3_` 只领某一批 |
| `./forge.sh queue --brief` | 列出未完成的任务，每个一行（状态、名称、领取者）；不加 `--brief` 给 JSON（命题截到 160 字符；完整命题和证明思路用 `show <任务名>` 看，不必先领取） |
| `./forge.sh check <任务名> <文件>` | 只校验，不入库；失败时返回前几条 Lean 错误和行号 |
| `./forge.sh submit <任务名> <文件> --agent <名字>` | 校验并入库（证伪加 `--disproof`）。校验可与别人并行；入库按组合并构建，一次约半分钟到一分钟，shell 超时设长一点或放后台 |
| `./forge.sh bench-check <评测集> <题名> <文件> --run <轮次> --agent <名字>` | 评测：只判对错、不入库，成绩记到该轮次；`bench-score <评测集>` 看各轮成绩 |
| `./forge.sh sketch <任务名> <文件> --agent <名字>` | 提交带 `sorry` 空洞的证明骨架；每个空洞自动成为子任务 |
| `./forge.sh assemble <任务名> --agent <名字>` | 子任务都证完后拼回父命题 |
| `./forge.sh release <任务名> --agent <名字> --note "…"` | 做不出来就归还，写明试过什么、卡在哪 |
| `./forge.sh retire <任务名> --agent <名字> --note "…"` | 命题本身有误（类型不对、被更好的表述取代）时移出队列，别让它在队列里空转 |
| `./forge.sh search "<关键词>"` | 检索 Mathlib2 里已有的定理（可直接引用 `Mathlib2.<名字>`） |
| `./forge.sh source <定理名>` | 打印库里某条定理（含辅助引理）的完整 Lean 证明，想复用其中的步骤时用 |
| `./forge.sh lookup "<名称片段>"` | 在 Mathlib + Mathlib2 全部定理里按名称片段查准确的名字和类型，例如 `lookup "succ mul choose"`；不确定引理名时先查，别猜 |
| `./forge.sh find "<自然语言或命题>"` | 按**内容**检索：本地 Mathlib2 + Mathlib 的语义检索（LeanSearch）。不知道引理叫什么、只知道它说什么时用这个，例如 `find "sum of first n odd numbers is n squared"` |
| `./forge.sh pattern "<类型模式>"` | 按类型模式检索 Mathlib（Loogle），例如 `pattern "Nat.Prime _ → _ ∣ _ * _ → _"`、`pattern "Real.sqrt, HAdd.hAdd"` |
| `./forge.sh define <名称> <文件> --agent <名字>` | 引入一条新定义（见下文“引入新定义”） |
| `./forge.sh propose --file <jsonl> --agent <名字>` | 提出新命题，每行 `{"name","statement","informal"}`；逐条进度打在 stderr |
| `./forge.sh status` / `report` / `dag [名字]` | 概况、排序清单、依赖图 |

## 提交文件怎么写

文件内容已经处在 `namespace Mathlib2` 里，`Mathlib` 和 `Mathlib2` 全部可用。只能写：

- 顶格的 `open …` 行；
- 顶格的 `theorem` / `lemma` 声明，证明内容缩进。

任务 `foo`，命题 `(a b : ℕ) (h : a ∣ b) : P`：

```lean
theorem foo (a b : ℕ) (h : a ∣ b) : P := by
  …
```

证伪时证明命题的否定（`next` 的输出里给了闭形式）。主定理命名为 `foo_disproof` 即按证伪处理，`check` 和 `submit` 都会自动识别（也可显式加 `--disproof`）：

```lean
theorem foo_disproof : ¬ (∀ (a b : ℕ) (h : a ∣ b), P) := by
  intro h
  have := h 0 0 (dvd_refl 0)
  …
```

辅助引理命名为 `foo_aux1`、`foo_aux2`…，主定理必须是最后一个声明。

不允许：`sorry`（骨架除外）、`axiom`、`def`、`instance`、`notation`、`macro`、`set_option`、`native_decide`、`run_tac` 等。
允许的公理只有 `propext`、`Classical.choice`、`Quot.sound`。

## 工作方式

1. 先想清楚命题**是否为真**。任务里若带 `counterexample`，说明随机测试已找到反例，直接做证伪。小情形自己算一算。
2. 写证明，`check`，读错误，改，再 `check`。错误信息是给你迭代用的，不要猜。
   `submit` 会对着库的最新状态重新校验一遍（别人可能刚入库了新定理），所以有把握时可以直接 `submit`，失败不会留下任何东西。
3. 一个任务最多校验约 8 次。仍然不通就二选一：
   - 能看出证明结构但某几步卡住：把这些步骤留成 `sorry`，用 `sketch` 提交，它们会成为独立子任务；
   - 没有思路：`release`，note 里写清楚试过的路线和具体卡点，下一个 agent 会看到。
4. 任务的 `attempts` 里是前人的失败记录，先读，别重复踩坑。
5. 不要为了通过而改命题。命题不匹配会被拒绝。

## 辅助引理与复用

库是很多 agent 分头写出来的，有用的中间结论很容易被埋在别人的证明里。两条约定：

- **先找再证。** 需要一条看起来通用的小结论时，先 `./forge.sh search "<关键词或符号>"`（库内条目和辅助引理都按命题内容检索）、
  `./forge.sh lookup "mathlib2. <名称片段>"`（只看库内声明）、`./forge.sh lookup "lib_"`（馆员整理出来的通用引理），
  或者在证明里对这一步直接写 `exact?` 试一次——库是打开的，已有的会被找到。
- **辅助引理写成通用的。** `<任务>_aux…` 尽量用 `Type*`、一般的 `Fintype` 指标类型和一般的域/环，不带本任务特有的假设，
  这样别人才能直接引用。`submit` 发现你的辅助引理与库里已有声明命题相同，会在结果里提醒。
- **馆员提升辅助引理时**：命题与已有辅助引理逐字相同会被 `propose` 判为 `known`（`exact?` 一步即得）而不入库，
  且该名称随即被占用。所以提升必须是真正的推广、加强或重新打包（放宽类型类、把 ≤ 加强为 =、合并成一条等），不要原样照搬。

## 拆解（sketch）怎么用

难题先拆再证。骨架是主定理的一份证明，其中每个中间引理写成 `have 名字 : <精确命题> := by sorry`，引理之间如何组合要真的写出来：

```lean
theorem foo (n : ℕ) (hn : 0 < n) : P n := by
  have key : ∀ m, m < n → Q m := by
    sorry
  have step : Q (n - 1) → P n := by
    clear key      -- 子引理不需要的假设先清掉，子任务才通用
    sorry
  exact step (key (n - 1) (by omega))
```

- 骨架除 `sorry` 外必须能编译，命题必须匹配。
- 每个空洞处的目标**连同当时作用域里的全部变量和假设**成为一个子任务（`foo_s1h1`、`foo_s1h2`…）。
  想让子引理通用，就尽早 `have`，或在空洞的 `by` 块里先 `clear` 掉无关假设。
- 前面留了 `sorry` 的 `have` 会作为假设带进后面的空洞，子引理因此越来越长。想让各空洞互相独立，把它们并成一个合取再拆开：
  `have H : A ∧ B ∧ C := by refine ⟨?_, ?_, ?_⟩ <;> sorry`，然后 `obtain ⟨hA, hB, hC⟩ := H`。
- 空洞的目标会被打印成文本再解析成子任务。打印时类型标注和强制转换可能丢失，系统会当场核对含义没变，变了就拒绝并提示。
  容易出问题的写法：置换或函数的乘积直接作用于参数（写成 `τ (ρ x)`）、带类型标注的多项式字面量（先绑定成变量）、依赖 `open` 进来的记号（写全名）。
- 全部空洞先整体检查，能各自独立成命题才登记；有一个不行就什么都不登记，改好重来即可。
- 子引理要是假的，整份骨架就作废：`assemble` 会明确告诉你。修正那一步后重新 `sketch`，
  旧骨架里还没人领的子任务会被自动撤掉；已证出的子定理在新骨架里直接引用（`Mathlib2.foo_s1h1 …`），相同命题的空洞会自动复用已有任务。
- 随机测试只能抓到一部分假引理（实数命题经常漏），拆之前自己拿小例子验一遍，尤其是正负号和非负条件。
- `assemble` 会把每个子定理按拆解时记下的顺序应用到骨架里的局部变量上；万一失败，手写最终证明、引用各子定理后 `submit`。
- 别人已经拆解、子任务还在进行的父任务，不要另起骨架，去证它的子任务。

## 引入新定义（define）

命题需要一个 Mathlib 没有的标准概念时，可以先把它定义进库：

```bash
./forge.sh define my_concept def.lean --agent <名字> --informal "一句话说明" --source "出处"
```

`def.lean` 里只能有一条 `def my_concept … := …`（可带 `noncomputable`），不能带实例、记号、属性。名称小写下划线、带领域前缀，
不能与任何已有的根级名称相同。入库后在命题和证明里直接写 `my_concept`（全名 `Mathlib2.my_concept`），证明里用 `unfold my_concept` 展开。
内核只保证定义良构；它是否就是原文的那个概念，要靠 `review` 复核。能用 Mathlib 已有概念表达的，就不要新定义。

## 提猜想时

- 命题格式是 Lean 签名 `<binders> : <conclusion>`，binder 写全，不带 `:=`。
- 名称小写下划线、全局唯一，建议带领域前缀。
- `propose` 的结果：`known`（Mathlib 一步就有，白提了）、`duplicate`、`invalid`（附 Lean 错误）、
  `auto_proved`（被自动化直接证掉，价值低）、`open`（进入队列，这才是好猜想）。
  `open` 且带 `refutable: true` 表示随机测试已找到反例，等待形式化证伪。
  `busy` 表示机器繁忙导致类型检查超时，与命题对错无关，稍后用同一名称重提。
  `vacuous`：签名里的假设互相矛盾（自动化能从假设推出 False），命题空真、没有内容；改好假设后可用原名重提。
  `known` 且 `known_as` 写着某条 `Mathlib2.…`：新命题可由库里那条定理一步推出（直接套用，或把 `Fintype.card` 子类型、
  `Finset.filter` 的 card 等写法统一后套用），属于换了写法的已有结论。
  `reserved`：与固定评测集里的题目命题相同；评测题不许进库，换一个命题。
- 证明里的辅助引理同样不能与评测题相同，否则 `submit` 拒收。
- 目标是 `open`：命题要真、自然、Mathlib 里没有现成的、常用自动化一步关不掉。
