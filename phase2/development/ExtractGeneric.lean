import Mathlib.RingTheory.Polynomial.Radical
import Lean
open Lean Meta Elab Command

-- Generic Nat Horn-fragment decoder; contains no benchmark or target theorem names.
def p2term (vars : Array Expr) (e : Expr) : Option Json := do
  if let some i := vars.findIdx? (· == e) then
    return Json.mkObj [("var", toJson i)]
  if let .lit (.natVal n) := e then return Json.mkObj [("lit", toJson n)]
  if e.isAppOfArity ``OfNat.ofNat 3 then
    if let .lit (.natVal n) := e.getAppArgs[1]! then
      return Json.mkObj [("lit", toJson n)]
  none

def p2atom (vars : Array Expr) (e : Expr) : Option Json := do
  let .const name _ := e.getAppFn | none
  let op ← if name == ``LE.le || name == ``Nat.le then some "≤"
    else if name == ``LT.lt || name == ``Nat.lt then some "<"
    else if name == ``Dvd.dvd then some "∣"
    else if name == ``Eq then some "=" else none
  let args := e.getAppArgs
  if args.size < 2 then none else
    return Json.mkObj [("op", toJson op),
      ("left", ← p2term vars args[args.size-2]!), ("right", ← p2term vars args[args.size-1]!)]

def p2decode (ci : ConstantInfo) : MetaM (Option Json) := do
  try
    let c ← mkConstWithFreshMVarLevels ci.name
    let ty ← inferType c
    let (xs, _, body) ← forallMetaTelescope ty
    if xs.size > 10 then return none
    let mut vars := #[]
    let mut premises := #[]
    let mut binders := #[]
    for x in xs do
      let t ← instantiateMVars (← inferType x)
      if t.isSort then
        if !(← isDefEq t (mkSort (.succ .zero))) then return none
        x.mvarId!.assign (mkConst ``Nat)
        binders := binders.push (Json.mkObj [("type", toJson "Nat")])
      else if (← isClass? t).isSome then
        let inst ← synthInstance t
        x.mvarId!.assign inst
        binders := binders.push (Json.mkObj [("instance", toJson true)])
      else if t.isConstOf ``Nat then
        binders := binders.push (Json.mkObj [("var", toJson vars.size)])
        vars := vars.push x
      else
        let some atom := p2atom vars t | return none
        binders := binders.push (Json.mkObj [("premise", toJson premises.size)])
        premises := premises.push atom
    let some conclusion := p2atom vars (← instantiateMVars body) | return none
    if vars.size > 4 || premises.size > 3 then return none
    let fullType ← ppExpr ci.type
    return some (Json.mkObj [("name",toJson ci.name.toString), ("variables",toJson vars.size),
      ("premises",Json.arr premises), ("conclusion",conclusion),
      ("binders",Json.arr binders), ("type",toJson fullType.pretty)])
  catch _ => return none

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    if let .thmInfo _ := ci then
      -- Nat monomorphic declarations only; unsupported types are not guessed.
      if !name.toString.startsWith "_" && !(name.toString.splitOn ".").any (·.startsWith "_") then
        let rule ← liftTermElabM (p2decode ci)
        if let some rule := rule then
          let modName := match env.getModuleIdxFor? name with
            | some idx => env.header.moduleNames[idx.toNat]!
            | none => env.mainModule
          let ranges ← findDeclarationRanges? name
          let loc := match ranges with | some r => toJson r.selectionRange.pos.line | none => Json.null
          logInfo ("P2_RULE " ++ (Json.mkObj [("rule",rule),("module",toJson modName.toString),("line",loc)]).compress)
