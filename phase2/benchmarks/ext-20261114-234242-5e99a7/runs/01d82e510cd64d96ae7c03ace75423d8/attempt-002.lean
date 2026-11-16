import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (h0 : (p2v2 ∣ p2v4)) (h1 : (p2v4 ∣ p2v1)) (h2 : (p2v3 ∣ p2v5)) (h3 : (0 < p2v5)) (h4 : (p2v1 ∣ p2v0)) (h5 : (p2v0 ∣ p2v3)) : (0 ≤ p2v2) := by
  exact @zero_le Nat _ _ _ p2v2

theorem p2_n002 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (h0 : (p2v2 ∣ p2v4)) (h1 : (p2v4 ∣ p2v1)) (h2 : (p2v3 ∣ p2v5)) (h3 : (0 < p2v5)) (h4 : (p2v1 ∣ p2v0)) (h5 : (p2v0 ∣ p2v3)) : (0 < 1) := by
  exact @Mathlib.Tactic.Linarith.zero_lt_one Nat _ _ _

#print axioms p2_n001
#print axioms p2_n002
