import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (p2v6 : Nat) (p2v7 : Nat) (h0 : (p2v2 ≤ p2v3)) (h1 : (p2v4 ≤ p2v6)) (h2 : (p2v5 ≤ p2v1)) (h3 : (p2v5 ≤ p2v2)) (h4 : (p2v3 ∣ p2v7)) (h5 : (p2v7 ≤ p2v5)) (h6 : (p2v6 ≤ p2v0)) (h7 : (p2v1 ≤ p2v4)) : (p2v7 ≤ p2v7) := by
  exact @Preorder.le_refl Nat _ p2v7

theorem p2_n002 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (p2v6 : Nat) (p2v7 : Nat) (h0 : (p2v2 ≤ p2v3)) (h1 : (p2v4 ≤ p2v6)) (h2 : (p2v5 ≤ p2v1)) (h3 : (p2v5 ≤ p2v2)) (h4 : (p2v3 ∣ p2v7)) (h5 : (p2v7 ≤ p2v5)) (h6 : (p2v6 ≤ p2v0)) (h7 : (p2v1 ≤ p2v4)) : (p2v7 ≤ p2v1) := by
  exact @LE.le.trans Nat _ p2v7 p2v5 p2v1 h5 h2

theorem p2_n003 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (p2v6 : Nat) (p2v7 : Nat) (h0 : (p2v2 ≤ p2v3)) (h1 : (p2v4 ≤ p2v6)) (h2 : (p2v5 ≤ p2v1)) (h3 : (p2v5 ≤ p2v2)) (h4 : (p2v3 ∣ p2v7)) (h5 : (p2v7 ≤ p2v5)) (h6 : (p2v6 ≤ p2v0)) (h7 : (p2v1 ≤ p2v4)) : (p2v7 ≤ p2v2) := by
  exact @LE.le.trans Nat _ p2v7 p2v5 p2v2 h5 h3

#print axioms p2_n001
#print axioms p2_n002
#print axioms p2_n003
