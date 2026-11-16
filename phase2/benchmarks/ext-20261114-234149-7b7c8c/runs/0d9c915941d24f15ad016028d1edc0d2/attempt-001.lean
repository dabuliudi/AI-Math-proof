import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (h0 : (p2v2 ≤ p2v1)) (h1 : (p2v0 < p2v2)) : (p2v0 < p2v1) := by
  exact @LE.le.trans_lt' Nat _ p2v1 p2v2 p2v0 h0 h1

#print axioms p2_n001
