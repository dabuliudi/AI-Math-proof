import Mathlib.RingTheory.Polynomial.Radical
open Polynomial UniqueFactorizationMonoid EuclideanDomain
theorem mathlib2_mason_lemma1 {k : Type*} [Field k] [DecidableEq k]
    (a : k[X]) (_ha : a ≠ 0) :
    a / radical a ∣ derivative a := by
  classical
  simpa only [divRadical] using (divRadical_dvd_derivative a)
#print axioms mathlib2_mason_lemma1
