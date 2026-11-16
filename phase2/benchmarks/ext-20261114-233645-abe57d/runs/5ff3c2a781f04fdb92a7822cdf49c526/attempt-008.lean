import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (h0 : (p2v0 ∣ p2v1)) (h1 : (p2v4 ∣ p2v3)) (h2 : (0 < p2v2)) (h3 : (p2v1 ∣ p2v4)) (h4 : (p2v3 ∣ p2v2)) : (0 ≤ p2v0) := by
  exact @zero_le Nat _ _ _ p2v0

theorem p2_n002 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (h0 : (p2v0 ∣ p2v1)) (h1 : (p2v4 ∣ p2v3)) (h2 : (0 < p2v2)) (h3 : (p2v1 ∣ p2v4)) (h4 : (p2v3 ∣ p2v2)) : (0 < 1) := by
  exact @Mathlib.Tactic.Linarith.zero_lt_one Nat _ _ _

theorem p2_n003 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (h0 : (p2v0 ∣ p2v1)) (h1 : (p2v4 ∣ p2v3)) (h2 : (0 < p2v2)) (h3 : (p2v1 ∣ p2v4)) (h4 : (p2v3 ∣ p2v2)) : (p2v0 ≤ p2v0) := by
  exact @Preorder.le_refl Nat _ p2v0

theorem p2_n004 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (h0 : (p2v0 ∣ p2v1)) (h1 : (p2v4 ∣ p2v3)) (h2 : (0 < p2v2)) (h3 : (p2v1 ∣ p2v4)) (h4 : (p2v3 ∣ p2v2)) : (p2v0 ∣ p2v0) := by
  exact @dvd_refl Nat _ p2v0

theorem p2_n005 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (h0 : (p2v0 ∣ p2v1)) (h1 : (p2v4 ∣ p2v3)) (h2 : (0 < p2v2)) (h3 : (p2v1 ∣ p2v4)) (h4 : (p2v3 ∣ p2v2)) : (p2v0 ∣ 0) := by
  exact @dvd_zero Nat _ p2v0

theorem p2_n006 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (h0 : (p2v0 ∣ p2v1)) (h1 : (p2v4 ∣ p2v3)) (h2 : (0 < p2v2)) (h3 : (p2v1 ∣ p2v4)) (h4 : (p2v3 ∣ p2v2)) : (0 < 4) := by
  exact @four_pos Nat _ _ _ _ _

theorem p2_n007 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (h0 : (p2v0 ∣ p2v1)) (h1 : (p2v4 ∣ p2v3)) (h2 : (0 < p2v2)) (h3 : (p2v1 ∣ p2v4)) (h4 : (p2v3 ∣ p2v2)) : (0 < 3) := by
  exact @three_pos Nat _ _ _ _ _

theorem p2_n008 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (h0 : (p2v0 ∣ p2v1)) (h1 : (p2v4 ∣ p2v3)) (h2 : (0 < p2v2)) (h3 : (p2v1 ∣ p2v4)) (h4 : (p2v3 ∣ p2v2)) : (0 < 2) := by
  exact @two_pos Nat _ _ _ _ _

#print axioms p2_n001
#print axioms p2_n002
#print axioms p2_n003
#print axioms p2_n004
#print axioms p2_n005
#print axioms p2_n006
#print axioms p2_n007
#print axioms p2_n008
