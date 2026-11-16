import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (h0 : (0 < p2v4)) (h1 : (p2v1 ∣ p2v4)) (h2 : (p2v3 ∣ p2v2)) (h3 : (p2v2 ∣ p2v0)) (h4 : (p2v0 ∣ p2v1)) : (p2v3 ≤ p2v3) := by
  exact @Preorder.le_refl Nat _ p2v3

theorem p2_n002 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (h0 : (0 < p2v4)) (h1 : (p2v1 ∣ p2v4)) (h2 : (p2v3 ∣ p2v2)) (h3 : (p2v2 ∣ p2v0)) (h4 : (p2v0 ∣ p2v1)) : (p2v4 ≤ p2v4) := by
  exact @Preorder.le_refl Nat _ p2v4

theorem p2_n003 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (h0 : (0 < p2v4)) (h1 : (p2v1 ∣ p2v4)) (h2 : (p2v3 ∣ p2v2)) (h3 : (p2v2 ∣ p2v0)) (h4 : (p2v0 ∣ p2v1)) : (p2v3 ∣ p2v3) := by
  exact @dvd_refl Nat _ p2v3

theorem p2_n004 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (h0 : (0 < p2v4)) (h1 : (p2v1 ∣ p2v4)) (h2 : (p2v3 ∣ p2v2)) (h3 : (p2v2 ∣ p2v0)) (h4 : (p2v0 ∣ p2v1)) : (p2v3 ∣ 0) := by
  exact @dvd_zero Nat _ p2v3

theorem p2_n005 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (h0 : (0 < p2v4)) (h1 : (p2v1 ∣ p2v4)) (h2 : (p2v3 ∣ p2v2)) (h3 : (p2v2 ∣ p2v0)) (h4 : (p2v0 ∣ p2v1)) : (0 ≤ p2v4) := by
  exact @zero_le Nat _ _ _ p2v4

theorem p2_n006 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (h0 : (0 < p2v4)) (h1 : (p2v1 ∣ p2v4)) (h2 : (p2v3 ∣ p2v2)) (h3 : (p2v2 ∣ p2v0)) (h4 : (p2v0 ∣ p2v1)) : (1 ≤ p2v4) := by
  exact @Nat.one_le_of_lt 0 p2v4 h0

theorem p2_n007 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (h0 : (0 < p2v4)) (h1 : (p2v1 ∣ p2v4)) (h2 : (p2v3 ∣ p2v2)) (h3 : (p2v2 ∣ p2v0)) (h4 : (p2v0 ∣ p2v1)) : (p2v3 = p2v3) := by
  exact @Dvd.dvd.antisymm Nat _ p2v3 p2v3 _ (p2_n003 p2v0 p2v1 p2v2 p2v3 p2v4 h0 h1 h2 h3 h4) (p2_n003 p2v0 p2v1 p2v2 p2v3 p2v4 h0 h1 h2 h3 h4)

theorem p2_n008 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (h0 : (0 < p2v4)) (h1 : (p2v1 ∣ p2v4)) (h2 : (p2v3 ∣ p2v2)) (h3 : (p2v2 ∣ p2v0)) (h4 : (p2v0 ∣ p2v1)) : (p2v3 ∣ p2v0) := by
  exact @Dvd.dvd.trans Nat _ p2v3 p2v2 p2v0 h2 h3

theorem p2_n009 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (h0 : (0 < p2v4)) (h1 : (p2v1 ∣ p2v4)) (h2 : (p2v3 ∣ p2v2)) (h3 : (p2v2 ∣ p2v0)) (h4 : (p2v0 ∣ p2v1)) : (p2v3 ∣ p2v1) := by
  exact @Dvd.dvd.trans Nat _ p2v3 p2v0 p2v1 (p2_n008 p2v0 p2v1 p2v2 p2v3 p2v4 h0 h1 h2 h3 h4) h4

theorem p2_n010 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (h0 : (0 < p2v4)) (h1 : (p2v1 ∣ p2v4)) (h2 : (p2v3 ∣ p2v2)) (h3 : (p2v2 ∣ p2v0)) (h4 : (p2v0 ∣ p2v1)) : (p2v3 ∣ p2v4) := by
  exact @Dvd.dvd.trans Nat _ p2v3 p2v1 p2v4 (p2_n009 p2v0 p2v1 p2v2 p2v3 p2v4 h0 h1 h2 h3 h4) h1

theorem p2_n011 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (h0 : (0 < p2v4)) (h1 : (p2v1 ∣ p2v4)) (h2 : (p2v3 ∣ p2v2)) (h3 : (p2v2 ∣ p2v0)) (h4 : (p2v0 ∣ p2v1)) : (p2v3 ≤ p2v4) := by
  exact @Nat.le_of_dvd p2v3 p2v4 h0 (p2_n010 p2v0 p2v1 p2v2 p2v3 p2v4 h0 h1 h2 h3 h4)

#print axioms p2_n001
#print axioms p2_n002
#print axioms p2_n003
#print axioms p2_n004
#print axioms p2_n005
#print axioms p2_n006
#print axioms p2_n007
#print axioms p2_n008
#print axioms p2_n009
#print axioms p2_n010
#print axioms p2_n011
