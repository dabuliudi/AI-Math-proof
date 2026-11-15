/-
Forge 独立内核重放（与 lean4checker 同一做法，复用 Lean 核心的 `Lean.Environment.replay`）。

把 Mathlib2 分片里的全部常量从编译产物中取出，放进一个**只导入 Mathlib** 的新环境，逐个交给内核重新检查。
这样不信任构建时留下的任何结论：即使有人用元编程绕过 elaborator 往环境里塞了未经检查的声明，
或篡改了 .olean，重放时内核也会拒绝。另外：
* `replay` 会跳过 unsafe / partial 常量，所以这里先把它们当作违规直接报出来；
* Mathlib2 里不允许出现新公理（axiom 声明）。

用法（在 lean/ 目录）：lake env lean --run scripts/ForgeReplay.lean
输出一行 `FORGE_REPLAY {json}`；退出码 0 表示全部通过。
-/
import Lean

open Lean

def isLibraryModule (m : Name) : Bool :=
  (`Mathlib2).isPrefixOf m

def main (_args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let full ← importModules #[{ module := `Mathlib2 }] {}
  let mut fresh : Std.HashMap Name ConstantInfo := {}
  let mut axioms : Array Name := #[]
  let mut unsafeOrPartial : Array Name := #[]
  for (name, info) in full.constants.map₁.toList do
    let some idx := full.getModuleIdxFor? name | continue
    let some modName := full.header.moduleNames[idx.toNat]? | continue
    unless isLibraryModule modName do continue
    fresh := fresh.insert name info
    if info matches .axiomInfo _ then axioms := axioms.push name
    if info.isUnsafe || info.isPartial then unsafeOrPartial := unsafeOrPartial.push name
  let base ← importModules #[{ module := `Mathlib }] {}
  let mut kernelError : Option String := none
  try
    let _ ← base.replay fresh
  catch e =>
    kernelError := some (toString e)
  let ok := kernelError.isNone && axioms.isEmpty && unsafeOrPartial.isEmpty
  let report := Json.mkObj [
    ("ok", toJson ok),
    ("constants", toJson fresh.size),
    ("axioms", toJson (axioms.map toString)),
    ("unsafe_or_partial", toJson (unsafeOrPartial.map toString)),
    ("kernel_error", toJson kernelError)]
  IO.println s!"FORGE_REPLAY {report.compress}"
  return if ok then 0 else 1
