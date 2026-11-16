import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (h0 : (p2v2 ≤ p2v0)) (h1 : (p2v1 ≤ p2v0)) : (p2v2 ≤ p2v2) := by
  exact @Preorder.le_refl Nat _ p2v2

theorem p2_n002 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (h0 : (p2v2 ≤ p2v0)) (h1 : (p2v1 ≤ p2v0)) : (p2v1 ≤ p2v1) := by
  exact @Preorder.le_refl Nat _ p2v1

theorem p2_n003 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (h0 : (p2v2 ≤ p2v0)) (h1 : (p2v1 ≤ p2v0)) : (p2v2 ∣ p2v2) := by
  exact @dvd_refl Nat _ p2v2

theorem p2_n004 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (h0 : (p2v2 ≤ p2v0)) (h1 : (p2v1 ≤ p2v0)) : (p2v2 ∣ 0) := by
  exact @dvd_zero Nat _ p2v2

theorem p2_n005 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (h0 : (p2v2 ≤ p2v0)) (h1 : (p2v1 ≤ p2v0)) : (0 ≤ p2v1) := by
  exact @zero_le Nat _ _ _ p2v1

theorem p2_n006 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (h0 : (p2v2 ≤ p2v0)) (h1 : (p2v1 ≤ p2v0)) : (p2v2 = p2v2) := by
  exact @Dvd.dvd.antisymm Nat _ p2v2 p2v2 _ (p2_n003 p2v0 p2v1 p2v2 h0 h1) (p2_n003 p2v0 p2v1 p2v2 h0 h1)

theorem p2_n007 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (h0 : (p2v2 ≤ p2v0)) (h1 : (p2v1 ≤ p2v0)) : (p2v1 ∣ p2v1) := by
  exact @dvd_refl Nat _ p2v1

#print axioms p2_n001
#print axioms p2_n002
#print axioms p2_n003
#print axioms p2_n004
#print axioms p2_n005
#print axioms p2_n006
#print axioms p2_n007
