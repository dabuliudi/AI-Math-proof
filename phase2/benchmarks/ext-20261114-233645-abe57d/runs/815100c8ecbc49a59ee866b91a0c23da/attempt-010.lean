import Mathlib.RingTheory.Polynomial.Radical
theorem p2_n001 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (p2v6 : Nat) (h0 : (p2v2 ≤ p2v1)) (h1 : (p2v3 < p2v5)) (h2 : (p2v5 < p2v2)) (h3 : (p2v1 ≤ p2v4)) (h4 : (p2v0 ≤ p2v6)) (h5 : (p2v6 ≤ p2v3)) : (p2v0 ≤ p2v0) := by
  exact @Preorder.le_refl Nat _ p2v0

theorem p2_n002 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (p2v6 : Nat) (h0 : (p2v2 ≤ p2v1)) (h1 : (p2v3 < p2v5)) (h2 : (p2v5 < p2v2)) (h3 : (p2v1 ≤ p2v4)) (h4 : (p2v0 ≤ p2v6)) (h5 : (p2v6 ≤ p2v3)) : (p2v0 ∣ p2v0) := by
  exact @dvd_refl Nat _ p2v0

theorem p2_n003 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (p2v6 : Nat) (h0 : (p2v2 ≤ p2v1)) (h1 : (p2v3 < p2v5)) (h2 : (p2v5 < p2v2)) (h3 : (p2v1 ≤ p2v4)) (h4 : (p2v0 ≤ p2v6)) (h5 : (p2v6 ≤ p2v3)) : (p2v0 ∣ 0) := by
  exact @dvd_zero Nat _ p2v0

theorem p2_n004 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (p2v6 : Nat) (h0 : (p2v2 ≤ p2v1)) (h1 : (p2v3 < p2v5)) (h2 : (p2v5 < p2v2)) (h3 : (p2v1 ≤ p2v4)) (h4 : (p2v0 ≤ p2v6)) (h5 : (p2v6 ≤ p2v3)) : (p2v0 = p2v0) := by
  exact @Dvd.dvd.antisymm Nat _ p2v0 p2v0 _ (p2_n002 p2v0 p2v1 p2v2 p2v3 p2v4 p2v5 p2v6 h0 h1 h2 h3 h4 h5) (p2_n002 p2v0 p2v1 p2v2 p2v3 p2v4 p2v5 p2v6 h0 h1 h2 h3 h4 h5)

theorem p2_n005 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (p2v6 : Nat) (h0 : (p2v2 ≤ p2v1)) (h1 : (p2v3 < p2v5)) (h2 : (p2v5 < p2v2)) (h3 : (p2v1 ≤ p2v4)) (h4 : (p2v0 ≤ p2v6)) (h5 : (p2v6 ≤ p2v3)) : (p2v0 ≤ p2v3) := by
  exact @LE.le.trans Nat _ p2v0 p2v6 p2v3 h4 h5

theorem p2_n006 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (p2v6 : Nat) (h0 : (p2v2 ≤ p2v1)) (h1 : (p2v3 < p2v5)) (h2 : (p2v5 < p2v2)) (h3 : (p2v1 ≤ p2v4)) (h4 : (p2v0 ≤ p2v6)) (h5 : (p2v6 ≤ p2v3)) : (p2v0 < p2v5) := by
  exact @LE.le.trans_lt Nat _ p2v0 p2v3 p2v5 (p2_n005 p2v0 p2v1 p2v2 p2v3 p2v4 p2v5 p2v6 h0 h1 h2 h3 h4 h5) h1

theorem p2_n007 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (p2v6 : Nat) (h0 : (p2v2 ≤ p2v1)) (h1 : (p2v3 < p2v5)) (h2 : (p2v5 < p2v2)) (h3 : (p2v1 ≤ p2v4)) (h4 : (p2v0 ≤ p2v6)) (h5 : (p2v6 ≤ p2v3)) : (p2v0 < p2v2) := by
  exact @LT.lt.trans Nat _ p2v0 p2v5 p2v2 (p2_n006 p2v0 p2v1 p2v2 p2v3 p2v4 p2v5 p2v6 h0 h1 h2 h3 h4 h5) h2

theorem p2_n008 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (p2v6 : Nat) (h0 : (p2v2 ≤ p2v1)) (h1 : (p2v3 < p2v5)) (h2 : (p2v5 < p2v2)) (h3 : (p2v1 ≤ p2v4)) (h4 : (p2v0 ≤ p2v6)) (h5 : (p2v6 ≤ p2v3)) : (p2v0 < p2v1) := by
  exact @LE.le.trans_lt' Nat _ p2v1 p2v2 p2v0 h0 (p2_n007 p2v0 p2v1 p2v2 p2v3 p2v4 p2v5 p2v6 h0 h1 h2 h3 h4 h5)

theorem p2_n009 (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (p2v6 : Nat) (h0 : (p2v2 ≤ p2v1)) (h1 : (p2v3 < p2v5)) (h2 : (p2v5 < p2v2)) (h3 : (p2v1 ≤ p2v4)) (h4 : (p2v0 ≤ p2v6)) (h5 : (p2v6 ≤ p2v3)) : (p2v0 < p2v4) := by
  exact @LE.le.trans_lt' Nat _ p2v4 p2v1 p2v0 h3 (p2_n008 p2v0 p2v1 p2v2 p2v3 p2v4 p2v5 p2v6 h0 h1 h2 h3 h4 h5)

theorem p2_target (p2v0 : Nat) (p2v1 : Nat) (p2v2 : Nat) (p2v3 : Nat) (p2v4 : Nat) (p2v5 : Nat) (p2v6 : Nat) (h0 : (p2v2 ≤ p2v1)) (h1 : (p2v3 < p2v5)) (h2 : (p2v5 < p2v2)) (h3 : (p2v1 ≤ p2v4)) (h4 : (p2v0 ≤ p2v6)) (h5 : (p2v6 ≤ p2v3)) : (p2v0 < p2v4) := by
  exact (p2_n009 p2v0 p2v1 p2v2 p2v3 p2v4 p2v5 p2v6 h0 h1 h2 h3 h4 h5)

#print axioms p2_n001
#print axioms p2_n002
#print axioms p2_n003
#print axioms p2_n004
#print axioms p2_n005
#print axioms p2_n006
#print axioms p2_n007
#print axioms p2_n008
#print axioms p2_n009
#print axioms p2_target
