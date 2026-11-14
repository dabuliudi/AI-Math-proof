import Mathlib.RingTheory.Polynomial.Radical
open Polynomial UniqueFactorizationMonoid EuclideanDomain
theorem mathlib2_mason_lemma1 {k : Type*} [Field k] [DecidableEq k]
    (a : k[X]) (_ha : a ≠ 0) :
    a / radical a ∣ derivative a := by
  classical
  simpa only [divRadical] using (divRadical_dvd_derivative a)
#print axioms mathlib2_mason_lemma1

theorem mathlib2_dvd_linear_combination {R : Type*} [Ring R]
    {q x y : R} (hx : q ∣ x) (hy : q ∣ y) (r s : R) :
    q ∣ x * r - y * s := by
  rcases hx with ⟨u, rfl⟩
  rcases hy with ⟨v, rfl⟩
  refine ⟨u * r - v * s, ?_⟩
  rw [mul_sub, mul_assoc, mul_assoc]

theorem mathlib2_quotient_dvd_self {k : Type*} [Field k] [DecidableEq k]
    (a : k[X]) : a / radical a ∣ a := by
  simpa only [divRadical] using (divRadical_dvd_self a)

theorem mathlib2_mason_lemma2 {k : Type*} [Field k] [DecidableEq k]
    (a b : k[X]) (ha : a ≠ 0) : a / radical a ∣ wronskian a b := by
  change a / radical a ∣ a * derivative b - derivative a * b
  exact mathlib2_dvd_linear_combination
    (mathlib2_quotient_dvd_self a) (mathlib2_mason_lemma1 a ha)
    (derivative b) b

#print axioms mathlib2_dvd_linear_combination
#print axioms mathlib2_quotient_dvd_self
#print axioms mathlib2_mason_lemma2
#print mathlib2_mason_lemma2
