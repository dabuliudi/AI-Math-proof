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

theorem p2_n006 (p2v0 : Nat) (p2v1 : Nat) : (0 ≤ p2v1) := by
  exact @Nat.dfold._proof_6 p2v1

theorem p2_n007 (p2v0 : Nat) (p2v1 : Nat) : (p2v1 ∣ p2v1) := by
  exact @Nat.dvd_refl p2v1

theorem p2_n008 (p2v0 : Nat) (p2v1 : Nat) : (1 ∣ p2v1) := by
  exact @Nat.one_dvd p2v1

theorem p2_n009 (p2v0 : Nat) (p2v1 : Nat) : (p2v1 = p2v1) := by
  exact @Lean.Grind.Nat.eq_of_le_of_le p2v1 p2v1 (p2_n005 p2v0 p2v1) (p2_n005 p2v0 p2v1)

theorem p2_n010 (p2v0 : Nat) (p2v1 : Nat) : (0 < 1) := by
  exact @Array.forIn'._proof_1 

theorem p2_n011 (p2v0 : Nat) (p2v1 : Nat) : (0 < 2) := by
  exact @Dyadic.toRat._proof_4 

#print axioms p2_n001
#print axioms p2_n002
#print axioms p2_n003
#print axioms p2_n004
#print axioms p2_n005
#print axioms p2_n006
#print axioms p2_n007
#print axioms p2_n008
#print axioms p2_n009
#print axioms p2_n010
#print axioms p2_n011
