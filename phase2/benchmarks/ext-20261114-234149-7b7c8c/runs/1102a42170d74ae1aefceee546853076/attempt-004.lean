import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (h0 : (p2v2 < p2v0)) (h1 : (p2v1 ∣ p2v0)) : (1 ≤ p2v0) := by
  exact @Nat.one_le_of_lt p2v2 p2v0 h0

theorem p2_n002 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (h0 : (p2v2 < p2v0)) (h1 : (p2v1 ∣ p2v0)) : (0 < p2v0) := by
  exact @LT.lt.pos Nat _ _ _ p2v2 p2v0 h0

theorem p2_n003 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (h0 : (p2v2 < p2v0)) (h1 : (p2v1 ∣ p2v0)) : (p2v1 ≤ p2v0) := by
  exact @Nat.le_of_dvd p2v1 p2v0 (p2_n002 p2v0 p2v1 p2v2 h0 h1) h1

theorem p2_target (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (h0 : (p2v2 < p2v0)) (h1 : (p2v1 ∣ p2v0)) : (1 ≤ p2v0) ∧ (p2v1 ≤ p2v0) := by
  exact And.intro (p2_n001 p2v0 p2v1 p2v2 h0 h1) ((p2_n003 p2v0 p2v1 p2v2 h0 h1))

#print axioms p2_n001
#print axioms p2_n002
#print axioms p2_n003
#print axioms p2_target
