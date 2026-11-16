import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (h0 : (p2v3 = p2v1)) (h1 : (p2v5 ≤ p2v2)) (h2 : (p2v0 = p2v5)) (h3 : (p2v2 = p2v3)) (h4 : (p2v4 = p2v0)) : (p2v4 = p2v5) := by
  exact @Eq.trans Nat p2v4 p2v0 p2v5 h4 h2

#print axioms p2_n001
