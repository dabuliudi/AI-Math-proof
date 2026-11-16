import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (h0 : (p2v2 ≤ p2v0)) (h1 : (p2v0 ≤ p2v1)) (h2 : (p2v3 ≤ p2v2)) (h3 : (p2v1 ≤ p2v3)) : (p2v2 ≤ p2v3) := by
  exact @le_imp_le_of_le_of_le Nat _ p2v0 p2v1 p2v2 p2v3 h0 h3 h1

#print axioms p2_n001
