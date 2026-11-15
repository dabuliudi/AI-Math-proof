/-
Forge：定理铸造厂的内核侧校验命令。

Python 侧不解析 `#print axioms` 之类的文本，而是调用这里的命令，
直接从环境里读取常量的类型、公理依赖和证明项引用的常量。
每条输出带调用方给的随机 nonce，防止提交内容伪造输出。
-/
import Lean
open Lean Elab Command Meta Term

namespace Forge

/-- 证明项与类型中引用的常量；自动生成的辅助声明会被展开，不计为依赖。 -/
def directDeps (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut out : NameSet := {}
  let mut stack : Array Name := #[root]
  let mut fuel := 100000
  while !stack.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let fromValue := match ci.value? (allowOpaque := true) with
      | some v => v.getUsedConstants
      | none => #[]
    for c in ci.type.getUsedConstants ++ fromValue do
      if c == root then continue
      if c.isInternalDetail || root.isPrefixOf c then stack := stack.push c
      else out := out.insert c
  return out

private def emit (tag : String) (fields : List (String × Json)) : CommandElabM Unit :=
  logInfo m!"{tag} {(Json.mkObj fields).compress}"

/-- `#forge_info "nonce" name`：输出常量的种类、类型、结构哈希、公理和直接依赖。 -/
syntax (name := forgeInfo) "#forge_info " str ident : command

@[command_elab forgeInfo] def elabForgeInfo : CommandElab := fun stx => do
  let nonce := stx[1].isStrLit?.getD ""
  let n ← liftCoreM <| realizeGlobalConstNoOverload stx[2]
  let env ← getEnv
  let some ci := env.find? n | throwError "unknown constant {n}"
  let axs ← liftCoreM <| collectAxioms n
  let ty ← liftTermElabM do return (← ppExpr ci.type).pretty 1000000
  let kind := match ci with
    | .thmInfo _ => "theorem"
    | .defnInfo _ => "def"
    | .axiomInfo _ => "axiom"
    | _ => "other"
  emit "FORGE_INFO" [
    ("nonce", nonce), ("name", toString n), ("kind", kind),
    ("hash", toString ci.type.hash), ("type", ty),
    ("axioms", toJson (axs.map toString)),
    ("deps", toJson ((directDeps env n).toList.map toString)),
    -- 去掉命名空间后的短名是否已被根级常量占用（新定义不许遮蔽已有概念）
    ("rootClash", toJson (match n with
      | .str _ last => env.contains (Name.mkSimple last)
      | _ => false))]

/--
`#forge_match "nonce" name "proved" (P)`：常量的类型是否与命题 `P` 定义等价；
`"disproved"` 时比较的是 `¬ P`。全称宇宙参数用新的宇宙元变量实例化后再比较。
-/
syntax (name := forgeMatch) "#forge_match " str ident str term : command

@[command_elab forgeMatch] def elabForgeMatch : CommandElab := fun stx => do
  let nonce := stx[1].isStrLit?.getD ""
  let mode := stx[3].isStrLit?.getD ""
  let n ← liftCoreM <| realizeGlobalConstNoOverload stx[2]
  let env ← getEnv
  let some ci := env.find? n | throwError "unknown constant {n}"
  let ok ← liftTermElabM do
    let p ← Term.elabType stx[4]
    Term.synthesizeSyntheticMVarsNoPostponing
    let p ← instantiateMVars p
    unless (← isProp p) do throwError "statement is not a proposition"
    let lvls ← mkFreshLevelMVars ci.levelParams.length
    let ty := ci.type.instantiateLevelParams ci.levelParams lvls
    let target := if mode == "disproved" then mkNot p else p
    isDefEq ty target
  emit "FORGE_MATCH" [("nonce", nonce), ("name", toString n), ("mode", mode), ("ok", ok)]

/--
`forge_hole "nonce"`：证明骨架里的空洞。把当前目标连同全部局部假设收成一个闭命题输出，
然后用 `sorry` 关掉目标。Python 侧据此把每个空洞登记成独立的子任务。
-/
syntax (name := forgeHole) "forge_hole " str : tactic

open Lean.Elab.Tactic in
@[tactic forgeHole] def evalForgeHole : Tactic := fun stx => do
  let nonce := stx[1].isStrLit?.getD ""
  let goal ← getMainGoal
  let (closed, reverted, args) ← goal.withContext do
    let lctx ← getLCtx
    let decls := lctx.foldl (init := #[]) fun acc d => if d.isImplementationDetail then acc else acc.push d
    -- 拼装时要把子定理应用到这些局部变量上。名字可直接引用的写名字；
    -- 被遮蔽或不可访问的，命题类写 `(by assumption)`，其余留给统一去填。
    let mut args : Array String := #[]
    for i in [0:decls.size] do
      let d := decls[i]!
      let shadowed := (decls.extract (i + 1) decls.size).any (·.userName == d.userName)
      if !d.userName.hasMacroScopes && !shadowed then
        args := args.push (d.userName.toString)
      else if (← isProp d.type) then
        args := args.push "(by assumption)"
      else
        args := args.push "_"
    let (_, reverted) ← goal.revert (decls.map (·.fvarId)) (preserveOrder := true)
    let ty ← instantiateMVars (← reverted.getType)
    pure (ty, reverted, args)
  -- 打印时带上绑定变量的类型，保证这段文本能被原样解析回同一个命题。
  let text ← withOptions (fun o => (o.setBool `pp.funBinderTypes true).setBool `pp.coercions.types true) do
    return (← ppExpr closed).pretty 1000000
  -- 打印出来的文本必须能解析回同一个命题：否则子任务证的就不是这个空洞（例如置换乘积被读成逐点乘积）。
  let roundtrip ← withoutModifyingState <| withLCtx {} {} do
    try
      match Parser.runParserCategory (← getEnv) `term text with
      | .error _ => pure false
      | .ok stx =>
        let e ← Term.elabType stx
        Term.synthesizeSyntheticMVarsNoPostponing
        isDefEq (← instantiateMVars e) closed
    catch _ => pure false
  logInfo m!"FORGE_HOLE {(Json.mkObj [("nonce", nonce), ("statement", text), ("hash", toString closed.hash), ("args", toJson args), ("roundtrip", roundtrip)]).compress}"
  reverted.admit
  replaceMainGoal []

/--
`#forge_find "nonce" "frag1 frag2"`：按名称片段在整个环境（Mathlib + Mathlib2）里找定理，
要求名称同时包含所有片段（不分大小写），按名称长度取前 25 个并给出类型。供 agent 查准确的引理名。
-/
syntax (name := forgeFind) "#forge_find " str str : command

@[command_elab forgeFind] def elabForgeFind : CommandElab := fun stx => do
  let nonce := stx[1].isStrLit?.getD ""
  let query := stx[2].isStrLit?.getD ""
  let frags := (query.splitOn " ").filter (· ≠ "") |>.map String.toLower
  let env ← getEnv
  let hits := env.constants.fold (init := (#[] : Array Name)) fun acc n ci =>
    let wanted := match ci with
      | .thmInfo _ => true
      | .defnInfo _ => true   -- 定义也要能查到（例如某个 Equiv 的名字）
      | _ => false
    if !wanted || n.isInternalDetail then acc
    else
      let s := (toString n).toLower
      if frags.all (fun f => (s.splitOn f).length > 1) then acc.push n else acc
  let sorted := hits.qsort (fun a b => (toString a).length < (toString b).length)
  let top := sorted.extract 0 25
  let mut rows : Array Json := #[]
  for n in top do
    let some ci := env.find? n | continue
    let ty ← liftTermElabM do return (← ppExpr ci.type).pretty 1000000
    let shown := if ty.length > 2000 then ty.take 2000 ++ " …（截断）" else ty
    rows := rows.push (Json.mkObj [("name", toString n), ("type", shown)])
  emit "FORGE_FIND" [("nonce", nonce), ("total", hits.size), ("results", Json.arr rows)]

end Forge
