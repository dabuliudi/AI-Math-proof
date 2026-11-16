import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (h0 : (0 < p2v3)) (h1 : (p2v1 ∣ p2v0)) (h2 : (p2v0 ∣ p2v4)) (h3 : (p2v2 ∣ p2v1)) (h4 : (p2v4 ∣ p2v3)) : (p2v2 ∣ p2v0) := by
  exact @Dvd.dvd.trans Nat _ p2v2 p2v1 p2v0 h3 h1

#print axioms p2_n001
