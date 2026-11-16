import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (h0 : (p2v2 ∣ p2v3)) (h1 : (p2v0 ∣ p2v2)) (h2 : (0 < p2v1)) (h3 : (p2v3 ∣ p2v1)) : (p2v0 ≤ p2v0) := by
  exact @Preorder.le_refl Nat _ p2v0

#print axioms p2_n001
