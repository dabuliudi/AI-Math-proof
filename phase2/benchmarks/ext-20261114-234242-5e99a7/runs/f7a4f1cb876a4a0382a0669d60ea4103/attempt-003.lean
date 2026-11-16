import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (h0 : (p2v3 < p2v0)) (h1 : (p2v0 = p2v1)) (h2 : (p2v1 ≤ p2v2)) : (p2v3 < p2v1) := by
  exact @Eq.trans_gt Nat _ p2v3 p2v0 p2v1 h1 h0

theorem p2_n002 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (h0 : (p2v3 < p2v0)) (h1 : (p2v0 = p2v1)) (h2 : (p2v1 ≤ p2v2)) : (p2v3 < p2v2) := by
  exact @LE.le.trans_lt' Nat _ p2v2 p2v1 p2v3 h2 (p2_n001 p2v0 p2v1 p2v2 p2v3 h0 h1 h2)

theorem p2_target (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (h0 : (p2v3 < p2v0)) (h1 : (p2v0 = p2v1)) (h2 : (p2v1 ≤ p2v2)) : (p2v3 < p2v2) := by
  exact (p2_n002 p2v0 p2v1 p2v2 p2v3 h0 h1 h2)

#print axioms p2_n001
#print axioms p2_n002
#print axioms p2_target
