import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (h0 : (p2v5 ∣ p2v2)) (h1 : (p2v4 ∣ p2v0)) (h2 : (p2v0 ∣ p2v5)) (h3 : (p2v2 ∣ p2v3)) (h4 : (0 < p2v1)) (h5 : (p2v3 ∣ p2v1)) : (p2v4 ∣ p2v5) := by
  exact @Dvd.dvd.trans Nat _ p2v4 p2v0 p2v5 h1 h2

theorem p2_n002 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (h0 : (p2v5 ∣ p2v2)) (h1 : (p2v4 ∣ p2v0)) (h2 : (p2v0 ∣ p2v5)) (h3 : (p2v2 ∣ p2v3)) (h4 : (0 < p2v1)) (h5 : (p2v3 ∣ p2v1)) : (p2v4 ∣ p2v2) := by
  exact @Dvd.dvd.trans Nat _ p2v4 p2v5 p2v2 (p2_n001 p2v0 p2v1 p2v2 p2v3 p2v4 p2v5 h0 h1 h2 h3 h4 h5) h0

theorem p2_n003 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (h0 : (p2v5 ∣ p2v2)) (h1 : (p2v4 ∣ p2v0)) (h2 : (p2v0 ∣ p2v5)) (h3 : (p2v2 ∣ p2v3)) (h4 : (0 < p2v1)) (h5 : (p2v3 ∣ p2v1)) : (p2v4 ∣ p2v3) := by
  exact @Dvd.dvd.trans Nat _ p2v4 p2v2 p2v3 (p2_n002 p2v0 p2v1 p2v2 p2v3 p2v4 p2v5 h0 h1 h2 h3 h4 h5) h3

theorem p2_n004 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (h0 : (p2v5 ∣ p2v2)) (h1 : (p2v4 ∣ p2v0)) (h2 : (p2v0 ∣ p2v5)) (h3 : (p2v2 ∣ p2v3)) (h4 : (0 < p2v1)) (h5 : (p2v3 ∣ p2v1)) : (p2v4 ∣ p2v1) := by
  exact @Dvd.dvd.trans Nat _ p2v4 p2v3 p2v1 (p2_n003 p2v0 p2v1 p2v2 p2v3 p2v4 p2v5 h0 h1 h2 h3 h4 h5) h5

theorem p2_n005 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (h0 : (p2v5 ∣ p2v2)) (h1 : (p2v4 ∣ p2v0)) (h2 : (p2v0 ∣ p2v5)) (h3 : (p2v2 ∣ p2v3)) (h4 : (0 < p2v1)) (h5 : (p2v3 ∣ p2v1)) : (p2v4 ≤ p2v1) := by
  exact @Nat.le_of_dvd p2v4 p2v1 h4 (p2_n004 p2v0 p2v1 p2v2 p2v3 p2v4 p2v5 h0 h1 h2 h3 h4 h5)

theorem p2_target (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (h0 : (p2v5 ∣ p2v2)) (h1 : (p2v4 ∣ p2v0)) (h2 : (p2v0 ∣ p2v5)) (h3 : (p2v2 ∣ p2v3)) (h4 : (0 < p2v1)) (h5 : (p2v3 ∣ p2v1)) : (p2v4 ≤ p2v1) := by
  exact (p2_n005 p2v0 p2v1 p2v2 p2v3 p2v4 p2v5 h0 h1 h2 h3 h4 h5)

#print axioms p2_n001
#print axioms p2_n002
#print axioms p2_n003
#print axioms p2_n004
#print axioms p2_n005
#print axioms p2_target
