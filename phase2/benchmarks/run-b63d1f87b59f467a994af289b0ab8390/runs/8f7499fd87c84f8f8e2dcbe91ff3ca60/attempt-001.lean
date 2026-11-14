import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (h0 : (p2v4 ≤ p2v2)) (h1 : (p2v2 ≤ p2v0)) (h2 : (p2v1 ≤ p2v4)) (h3 : (p2v3 ≤ p2v1)) : (p2v3 ≤ p2v3) := by
  exact @Preorder.le_refl Nat _ p2v3

#print axioms p2_n001
