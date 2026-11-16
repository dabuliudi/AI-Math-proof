import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (h0 : (p2v5 ∣ p2v3)) (h1 : (p2v4 ≤ p2v5)) (h2 : (p2v3 ≤ p2v1)) (h3 : (p2v1 ≤ p2v4)) (h4 : (p2v1 ≤ p2v2)) (h5 : (p2v2 ≤ p2v0)) : (p2v3 ≤ p2v0) := by
  exact @le_imp_le_of_le_of_le Nat _ p2v1 p2v2 p2v3 p2v0 h2 h5 h4

#print axioms p2_n001
