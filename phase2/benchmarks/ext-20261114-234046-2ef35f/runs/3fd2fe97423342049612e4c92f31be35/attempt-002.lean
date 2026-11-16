import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (p2v6 : Nat) (h0 : (p2v0 ≤ p2v4)) (h1 : (p2v0 ≤ p2v5)) (h2 : (p2v5 ≤ p2v6)) (h3 : (p2v4 ≤ p2v1)) (h4 : (p2v3 ≤ p2v0)) (h5 : (p2v6 ≤ p2v2)) (h6 : (p2v1 ∣ p2v3)) : (p2v3 ≤ p2v5) := by
  exact @LE.le.trans Nat _ p2v3 p2v0 p2v5 h4 h1

theorem p2_n002 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (p2v6 : Nat) (h0 : (p2v0 ≤ p2v4)) (h1 : (p2v0 ≤ p2v5)) (h2 : (p2v5 ≤ p2v6)) (h3 : (p2v4 ≤ p2v1)) (h4 : (p2v3 ≤ p2v0)) (h5 : (p2v6 ≤ p2v2)) (h6 : (p2v1 ∣ p2v3)) : (p2v3 ≤ p2v2) := by
  exact @le_imp_le_of_le_of_le Nat _ p2v5 p2v6 p2v3 p2v2 (p2_n001 p2v0 p2v1 p2v2 p2v3 p2v4 p2v5 p2v6 h0 h1 h2 h3 h4 h5 h6) h5 h2

#print axioms p2_n001
#print axioms p2_n002
