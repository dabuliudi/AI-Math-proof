import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (h0 : (p2v1 ≤ p2v0)) (h1 : (p2v0 ≤ p2v1)) : (p2v1 = p2v0) := by
  exact @LE.le.antisymm Nat _ p2v1 p2v0 h0 h1

theorem p2_target (p2v0 : Nat) (p2v1 : Nat) (h0 : (p2v1 ≤ p2v0)) (h1 : (p2v0 ≤ p2v1)) : (p2v1 = p2v0) := by
  exact (p2_n001 p2v0 p2v1 h0 h1)

#print axioms p2_n001
#print axioms p2_target
