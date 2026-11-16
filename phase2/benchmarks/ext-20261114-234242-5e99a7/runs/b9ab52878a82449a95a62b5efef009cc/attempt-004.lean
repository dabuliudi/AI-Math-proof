import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (h0 : (p2v4 ∣ p2v5)) (h1 : (p2v5 ∣ p2v3)) (h2 : (p2v1 ∣ p2v2)) (h3 : (0 < p2v2)) (h4 : (p2v3 ∣ p2v1)) (h5 : (p2v0 ∣ p2v4)) : (p2v0 ≤ p2v0) := by
  exact @Preorder.le_refl Nat _ p2v0

theorem p2_n002 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (h0 : (p2v4 ∣ p2v5)) (h1 : (p2v5 ∣ p2v3)) (h2 : (p2v1 ∣ p2v2)) (h3 : (0 < p2v2)) (h4 : (p2v3 ∣ p2v1)) (h5 : (p2v0 ∣ p2v4)) : (p2v2 ≤ p2v2) := by
  exact @Preorder.le_refl Nat _ p2v2

theorem p2_n003 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (h0 : (p2v4 ∣ p2v5)) (h1 : (p2v5 ∣ p2v3)) (h2 : (p2v1 ∣ p2v2)) (h3 : (0 < p2v2)) (h4 : (p2v3 ∣ p2v1)) (h5 : (p2v0 ∣ p2v4)) : (p2v0 ∣ p2v0) := by
  exact @dvd_refl Nat _ p2v0

theorem p2_n004 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (h0 : (p2v4 ∣ p2v5)) (h1 : (p2v5 ∣ p2v3)) (h2 : (p2v1 ∣ p2v2)) (h3 : (0 < p2v2)) (h4 : (p2v3 ∣ p2v1)) (h5 : (p2v0 ∣ p2v4)) : (p2v0 ∣ 0) := by
  exact @dvd_zero Nat _ p2v0

#print axioms p2_n001
#print axioms p2_n002
#print axioms p2_n003
#print axioms p2_n004
