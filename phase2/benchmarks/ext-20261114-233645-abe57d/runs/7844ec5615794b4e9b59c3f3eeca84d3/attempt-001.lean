import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (h0 : (p2v1 ≤ p2v0)) : (p2v1 ≤ p2v1) := by
  exact @Preorder.le_refl Nat _ p2v1

#print axioms p2_n001
