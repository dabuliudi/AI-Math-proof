import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) : (p2v0 ≤ p2v0) := by
  exact @Lean.Grind.instIsPreorderNat._proof_2 p2v0

theorem p2_n002 (p2v0 : Nat) (p2v1 : Nat) : (p2v0 ∣ p2v0) := by
  exact @Nat.dvd_refl p2v0

theorem p2_n003 (p2v0 : Nat) (p2v1 : Nat) : (p2v0 ∣ 0) := by
  exact @Nat.dvd_zero p2v0

theorem p2_n004 (p2v0 : Nat) (p2v1 : Nat) : (p2v0 = p2v0) := by
  exact @Lean.Grind.Nat.eq_of_le_of_le p2v0 p2v0 (p2_n001 p2v0 p2v1) (p2_n001 p2v0 p2v1)

theorem p2_n005 (p2v0 : Nat) (p2v1 : Nat) : (p2v1 ≤ p2v1) := by
  exact @Lean.Grind.instIsPreorderNat._proof_2 p2v1

#print axioms p2_n001
#print axioms p2_n002
#print axioms p2_n003
#print axioms p2_n004
#print axioms p2_n005
