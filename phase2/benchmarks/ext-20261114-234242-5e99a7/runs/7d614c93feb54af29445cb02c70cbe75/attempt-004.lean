import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (p2v6 : Nat) (p2v7 : Nat) (h0 : (p2v7 ≤ p2v0)) (h1 : (p2v3 ≤ p2v6)) (h2 : (p2v4 ∣ p2v2)) (h3 : (p2v5 ≤ p2v1)) (h4 : (p2v3 ≤ p2v7)) (h5 : (p2v6 ≤ p2v4)) (h6 : (p2v2 ≤ p2v3)) (h7 : (p2v0 ≤ p2v5)) : (p2v2 ≤ p2v2) := by
  exact @Preorder.le_refl Nat _ p2v2

theorem p2_n002 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (p2v6 : Nat) (p2v7 : Nat) (h0 : (p2v7 ≤ p2v0)) (h1 : (p2v3 ≤ p2v6)) (h2 : (p2v4 ∣ p2v2)) (h3 : (p2v5 ≤ p2v1)) (h4 : (p2v3 ≤ p2v7)) (h5 : (p2v6 ≤ p2v4)) (h6 : (p2v2 ≤ p2v3)) (h7 : (p2v0 ≤ p2v5)) : (p2v2 ≤ p2v6) := by
  exact @LE.le.trans Nat _ p2v2 p2v3 p2v6 h6 h1

theorem p2_n003 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (p2v6 : Nat) (p2v7 : Nat) (h0 : (p2v7 ≤ p2v0)) (h1 : (p2v3 ≤ p2v6)) (h2 : (p2v4 ∣ p2v2)) (h3 : (p2v5 ≤ p2v1)) (h4 : (p2v3 ≤ p2v7)) (h5 : (p2v6 ≤ p2v4)) (h6 : (p2v2 ≤ p2v3)) (h7 : (p2v0 ≤ p2v5)) : (p2v2 ≤ p2v4) := by
  exact @LE.le.trans Nat _ p2v2 p2v6 p2v4 (p2_n002 p2v0 p2v1 p2v2 p2v3 p2v4 p2v5 p2v6 p2v7 h0 h1 h2 h3 h4 h5 h6 h7) h5

theorem p2_n004 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (p2v6 : Nat) (p2v7 : Nat) (h0 : (p2v7 ≤ p2v0)) (h1 : (p2v3 ≤ p2v6)) (h2 : (p2v4 ∣ p2v2)) (h3 : (p2v5 ≤ p2v1)) (h4 : (p2v3 ≤ p2v7)) (h5 : (p2v6 ≤ p2v4)) (h6 : (p2v2 ≤ p2v3)) (h7 : (p2v0 ≤ p2v5)) : (p2v2 ≤ p2v7) := by
  exact @LE.le.trans Nat _ p2v2 p2v3 p2v7 h6 h4

#print axioms p2_n001
#print axioms p2_n002
#print axioms p2_n003
#print axioms p2_n004
