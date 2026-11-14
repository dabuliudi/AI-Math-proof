import Mathlib.RingTheory.Polynomial.Radical
open Polynomial UniqueFactorizationMonoid EuclideanDomain

theorem mathlib2_unit_of_natDegree_zero {k : Type*} [Field k]
    (a : k[X]) (ha : a ≠ 0) (hz : a.natDegree = 0) : IsUnit a := by
  apply isUnit_iff_degree_eq_zero.mpr
  rw [degree_eq_natDegree ha, hz]
  rfl

theorem mathlib2_unit_of_radical_unit {k : Type*} [Field k] [DecidableEq k]
    (a : k[X]) (ha : a ≠ 0) (hu : IsUnit (radical a)) : IsUnit a := by
  have hr : radical a = 1 := by
    calc
      radical a = radical (radical a) := radical_radical.symm
      _ = 1 := radical_of_isUnit hu
  exact (radical_eq_one_iff.mp hr).resolve_left ha

theorem mathlib2_radical_natDegree_ne_zero {k : Type*} [Field k] [DecidableEq k]
    (a : k[X]) (h : 1 ≤ a.natDegree) : (radical a).natDegree ≠ 0 := by
  have hn : a.natDegree ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one h)
  have ha : a ≠ 0 := fun hz => hn (by simp [hz])
  intro hz
  have hu := mathlib2_unit_of_natDegree_zero (radical a) radical_ne_zero hz
  have hau := mathlib2_unit_of_radical_unit a ha hu
  exact hn (natDegree_eq_zero_of_isUnit hau)

theorem mathlib2_mason_lemma3_nat {k : Type*} [Field k] [DecidableEq k]
    (a : k[X]) (h : 1 ≤ a.natDegree) : 1 ≤ (radical a).natDegree := by
  exact Nat.one_le_iff_ne_zero.mpr (mathlib2_radical_natDegree_ne_zero a h)

theorem mathlib2_mason_lemma3 {k : Type*} [Field k] [DecidableEq k]
    (a : k[X]) (h : (1 : WithBot ℕ) ≤ a.degree) :
    (1 : WithBot ℕ) ≤ (radical a).degree := by
  have hnat : 1 ≤ a.natDegree := Nat.succ_le_of_lt
    (natDegree_pos_iff_degree_pos.mpr (lt_of_lt_of_le (by decide) h))
  rw [degree_eq_natDegree radical_ne_zero]
  exact WithBot.coe_le_coe.mpr (mathlib2_mason_lemma3_nat a hnat)

#print axioms mathlib2_unit_of_natDegree_zero
#print axioms mathlib2_unit_of_radical_unit
#print axioms mathlib2_radical_natDegree_ne_zero
#print axioms mathlib2_mason_lemma3_nat
#print axioms mathlib2_mason_lemma3
#print mathlib2_mason_lemma3

set_option pp.fullNames true
set_option pp.universes false
#check @Polynomial.isUnit_iff_degree_eq_zero
#check @Polynomial.degree_eq_natDegree
#check @UniqueFactorizationMonoid.radical_radical
#check @UniqueFactorizationMonoid.radical_of_isUnit
#check @UniqueFactorizationMonoid.radical_eq_one_iff
#check @UniqueFactorizationMonoid.radical_ne_zero
#check @Polynomial.natDegree_eq_zero_of_isUnit
#check @Polynomial.natDegree_pos_iff_degree_pos
#check @WithBot.coe_le_coe

open Lean in
run_cmd do
  let env ← getEnv
  for name in [``mathlib2_unit_of_natDegree_zero, ``mathlib2_unit_of_radical_unit, ``mathlib2_radical_natDegree_ne_zero, ``mathlib2_mason_lemma3_nat, ``mathlib2_mason_lemma3] do
    let some ci := env.find? name | throwError "missing declaration"
    let v := match ci.value? with | some e => e.getUsedConstants | none => #[]
    let entry := Json.mkObj [("name", Json.str name.toString),
      ("type_dependencies", Json.arr (ci.type.getUsedConstants.map fun n => Json.str n.toString)),
      ("proof_dependencies", Json.arr (v.map fun n => Json.str n.toString))]
    logInfo ("AUDIT_JSON " ++ entry.compress)

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut all : NameSet := {}
  for name in [``mathlib2_unit_of_natDegree_zero, ``mathlib2_unit_of_radical_unit, ``mathlib2_radical_natDegree_ne_zero, ``mathlib2_mason_lemma3_nat, ``mathlib2_mason_lemma3] do
    let some ci := env.find? name | throwError "missing declaration"
    all := all.insert name
    for n in ci.getUsedConstantsAsSet.toList do
      all := all.insert n
  for n in all.toList do
    let some ci := env.find? n | throwError "missing dependency"
    let ty ← liftTermElabM (Meta.ppExpr ci.type)
    let modName := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    let loc ← findDeclarationRanges? n
    let line := match loc with | some r => toJson r.selectionRange.pos.line | none => Json.null
    let kind := match ci with | .thmInfo _ => "theorem" | .axiomInfo _ => "axiom" | _ => "definition_or_instance"
    logInfo ("DECL_JSON " ++ (Json.mkObj [("name",toJson n.toString),("type",toJson ty.pretty),
      ("module",toJson modName.toString),("line",line),("kind",toJson kind)]).compress)
