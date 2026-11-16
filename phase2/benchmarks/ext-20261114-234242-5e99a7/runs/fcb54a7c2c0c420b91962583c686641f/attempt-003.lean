import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (h0 : (p2v4 < p2v5)) (h1 : (p2v5 < p2v2)) (h2 : (p2v3 ≤ p2v0)) (h3 : (p2v2 ≤ p2v3)) (h4 : (p2v0 < p2v1)) : (p2v4 < p2v2) := by
  exact @LT.lt.trans Nat _ p2v4 p2v5 p2v2 h0 h1

theorem p2_n002 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (h0 : (p2v4 < p2v5)) (h1 : (p2v5 < p2v2)) (h2 : (p2v3 ≤ p2v0)) (h3 : (p2v2 ≤ p2v3)) (h4 : (p2v0 < p2v1)) : (p2v4 < p2v3) := by
  exact @LE.le.trans_lt' Nat _ p2v3 p2v2 p2v4 h3 (p2_n001 p2v0 p2v1 p2v2 p2v3 p2v4 p2v5 h0 h1 h2 h3 h4)

theorem p2_n003 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (h0 : (p2v4 < p2v5)) (h1 : (p2v5 < p2v2)) (h2 : (p2v3 ≤ p2v0)) (h3 : (p2v2 ≤ p2v3)) (h4 : (p2v0 < p2v1)) : (p2v4 < p2v0) := by
  exact @LE.le.trans_lt' Nat _ p2v0 p2v3 p2v4 h2 (p2_n002 p2v0 p2v1 p2v2 p2v3 p2v4 p2v5 h0 h1 h2 h3 h4)

#print axioms p2_n001
#print axioms p2_n002
#print axioms p2_n003
