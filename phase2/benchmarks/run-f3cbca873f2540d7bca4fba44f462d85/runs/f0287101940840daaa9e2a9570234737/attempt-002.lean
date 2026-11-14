import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (h0 : (p2v0 ∣ p2v1)) (h1 : (p2v1 ∣ p2v2)) (h2 : (0 < p2v2)) : (p2v0 ∣ p2v2) := by
  exact @Nat.dvd_trans p2v0 p2v1 p2v2 h0 h1

theorem p2_n002 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (h0 : (p2v0 ∣ p2v1)) (h1 : (p2v1 ∣ p2v2)) (h2 : (0 < p2v2)) : (p2v0 ≤ p2v2) := by
  exact @Nat.le_of_dvd p2v0 p2v2 h2 (p2_n001 p2v0 p2v1 p2v2 h0 h1 h2)

#print axioms p2_n001
#print axioms p2_n002
