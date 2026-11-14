import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n002 (p2v0 : Nat) : (p2v0 ≤ p2v0) := by
  exact @Lean.Grind.instIsPreorderNat._proof_2 p2v0

theorem p2_target (p2v0 : Nat) : (p2v0 ≤ p2v0) := by
  exact (p2_n002 p2v0)

#print axioms p2_n002
#print axioms p2_target
