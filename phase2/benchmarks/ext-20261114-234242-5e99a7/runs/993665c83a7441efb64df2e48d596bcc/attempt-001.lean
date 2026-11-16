import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (h0 : (p2v2 ∣ p2v1)) (h1 : (p2v0 ∣ p2v2)) (h2 : (0 < p2v1)) : (p2v0 ∣ p2v1) := by
  exact @Dvd.dvd.trans Nat _ p2v0 p2v2 p2v1 h1 h0

#print axioms p2_n001
