import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (h0 : (p2v1 ≤ p2v0)) : (p2v1 ≤ p2v1) := by
  exact @Preorder.le_refl Nat _ p2v1

theorem p2_n002 (p2v0 : Nat) (p2v1 : Nat) (h0 : (p2v1 ≤ p2v0)) : (p2v1 = p2v1) := by
  exact @LE.le.antisymm Nat _ p2v1 p2v1 (p2_n001 p2v0 p2v1 h0) (p2_n001 p2v0 p2v1 h0)

theorem p2_n003 (p2v0 : Nat) (p2v1 : Nat) (h0 : (p2v1 ≤ p2v0)) : (p2v1 ∣ p2v1) := by
  exact @dvd_refl Nat _ p2v1

theorem p2_n004 (p2v0 : Nat) (p2v1 : Nat) (h0 : (p2v1 ≤ p2v0)) : (p2v1 ∣ 0) := by
  exact @dvd_zero Nat _ p2v1

theorem p2_n005 (p2v0 : Nat) (p2v1 : Nat) (h0 : (p2v1 ≤ p2v0)) : (p2v0 ≤ p2v0) := by
  exact @Preorder.le_refl Nat _ p2v0

theorem p2_n006 (p2v0 : Nat) (p2v1 : Nat) (h0 : (p2v1 ≤ p2v0)) : (p2v0 = p2v0) := by
  exact @LE.le.antisymm Nat _ p2v0 p2v0 (p2_n005 p2v0 p2v1 h0) (p2_n005 p2v0 p2v1 h0)

theorem p2_n007 (p2v0 : Nat) (p2v1 : Nat) (h0 : (p2v1 ≤ p2v0)) : (p2v0 ∣ p2v0) := by
  exact @dvd_refl Nat _ p2v0

theorem p2_n008 (p2v0 : Nat) (p2v1 : Nat) (h0 : (p2v1 ≤ p2v0)) : (1 ∣ p2v0) := by
  exact @one_dvd Nat _ p2v0

theorem p2_n009 (p2v0 : Nat) (p2v1 : Nat) (h0 : (p2v1 ≤ p2v0)) : (0 ≤ p2v0) := by
  exact @zero_le Nat _ _ _ p2v0

theorem p2_n010 (p2v0 : Nat) (p2v1 : Nat) (h0 : (p2v1 ≤ p2v0)) : (0 ≤ 1) := by
  exact @LinearOrderedCommMonoidWithZero.zero_le_one Nat _

theorem p2_n011 (p2v0 : Nat) (p2v1 : Nat) (h0 : (p2v1 ≤ p2v0)) : (0 < 1) := by
  exact @Mathlib.Tactic.Linarith.zero_lt_one Nat _ _ _

theorem p2_n012 (p2v0 : Nat) (p2v1 : Nat) (h0 : (p2v1 ≤ p2v0)) : (0 ≤ 0) := by
  exact @Preorder.le_refl Nat _ 0

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
#print axioms p2_n012
