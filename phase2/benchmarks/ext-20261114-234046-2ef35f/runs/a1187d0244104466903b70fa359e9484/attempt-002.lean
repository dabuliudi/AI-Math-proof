import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (h0 : (p2v0 ∣ p2v1)) (h1 : (p2v1 ∣ p2v0)) : (p2v0 = p2v1) := by
  exact @Dvd.dvd.antisymm Nat _ p2v0 p2v1 _ h0 h1

theorem p2_target (p2v0 : Nat) (p2v1 : Nat) (h0 : (p2v0 ∣ p2v1)) (h1 : (p2v1 ∣ p2v0)) : (p2v0 = p2v1) := by
  exact (p2_n001 p2v0 p2v1 h0 h1)

#print axioms p2_n001
#print axioms p2_target
