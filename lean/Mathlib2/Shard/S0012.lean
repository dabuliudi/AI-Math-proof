/- Mathlib2 分片 12（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0011
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry gen_comb_erdos_szekeres_linear_order kind=proved origin=conjecture
section
/- Generalizes Mathlib2.r3_erdos_szekeres: codomain ℝ → any linear order α; domain Fin (r*s+1) → any finite linear order with more than r*s elements. Proof idea: the original pigeonhole proof on (longest increasing, longest decreasing) labels uses only the order; alternatively transport along the order isomorphism ι ≃o Fin (card ι) and restrict to the first r*s+1 elements. -/
theorem gen_comb_erdos_szekeres_linear_order (α : Type*) [LinearOrder α] (ι : Type*) [LinearOrder ι] [Fintype ι] (r s : ℕ) (hcard : r * s < Fintype.card ι) (f : ι → α) (hf : Function.Injective f) : (∃ t : Finset ι, r < t.card ∧ StrictMonoOn f ↑t) ∨ (∃ t : Finset ι, s < t.card ∧ StrictAntiOn f ↑t) := by
  classical
  let e : Fin (r * s + 1) ↪o ι :=
    (Fin.castLEOrderEmb (Nat.succ_le_of_lt hcard)).trans
      (Fintype.orderIsoFinOfCardEq ι rfl).toOrderEmbedding
  let g : Fin (r * s + 1) → ℝ := fun k => ((Finset.univ.filter (fun j => f j < f (e k))).card : ℝ)
  have hg1 : ∀ k l, f (e k) < f (e l) → g k < g l := by
    intro k l hkl
    have : (Finset.univ.filter (fun j => f j < f (e k))).card < (Finset.univ.filter (fun j => f j < f (e l))).card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨e k, by simp [hkl], by simp⟩
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact hj.trans hkl
    show ((_ : ℕ) : ℝ) < ((_ : ℕ) : ℝ)
    exact_mod_cast this
  have hg2 : ∀ k l, g k < g l → f (e k) < f (e l) := by
    intro k l hkl
    rcases lt_trichotomy (f (e k)) (f (e l)) with h | h | h
    · exact h
    · have : k = l := e.injective (hf h)
      subst this; exact absurd hkl (lt_irrefl _)
    · exact absurd (hg1 l k h) (not_lt.mpr hkl.le)
  have hginj : Function.Injective g := by
    intro k l hkl
    by_contra hne
    have hne' : f (e k) ≠ f (e l) := fun h => hne (e.injective (hf h))
    rcases lt_or_gt_of_ne hne' with h | h
    · exact absurd hkl (ne_of_lt (hg1 k l h))
    · exact absurd hkl (ne_of_gt (hg1 l k h))
  rcases Mathlib2.r3_erdos_szekeres r s g hginj with ⟨t, ht, hm⟩ | ⟨t, ht, hm⟩
  · left
    refine ⟨t.map e.toEmbedding, by simpa using ht, ?_⟩
    intro x hx y hy hxy
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨k, hk, rfl⟩ := hx
    obtain ⟨l, hl, rfl⟩ := hy
    exact hg2 k l (hm hk hl (e.lt_iff_lt.mp hxy))
  · right
    refine ⟨t.map e.toEmbedding, by simpa using ht, ?_⟩
    intro x hx y hy hxy
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨k, hk, rfl⟩ := hx
    obtain ⟨l, hl, rfl⟩ := hy
    exact hg2 l k (hm hk hl (e.lt_iff_lt.mp hxy))
end

-- forge:entry gen_lin_symm_nilpotent_eq_zero_ordered kind=proved origin=conjecture
section
/- Generalizes Mathlib2.lin_symm_nilpotent_eq_zero: ℝ → any linearly ordered commutative ring, Fin n → Fintype. Proof idea: same induction on the exponent; the key step B symmetric, B*B = 0 ⇒ B = 0 holds because the diagonal of Bᵀ*B is a sum of squares, which vanishes only if all terms vanish in an ordered ring. -/
theorem gen_lin_symm_nilpotent_eq_zero_ordered_aux1 (R : Type*) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (ι : Type*) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι R) (h : B.transpose * B = 0) : B = 0 := by
  ext i j
  have hjj : (B.transpose * B) j j = 0 := by rw [h]; rfl
  rw [Matrix.mul_apply] at hjj
  simp only [Matrix.transpose_apply] at hjj
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (B i j))).mp hjj i (Finset.mem_univ i)
  rw [Matrix.zero_apply]
  by_contra hne
  have hpos := mul_self_pos.mpr hne
  rw [this] at hpos
  exact lt_irrefl _ hpos

theorem gen_lin_symm_nilpotent_eq_zero_ordered (R : Type*) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R) (hs : A.IsSymm) (h : IsNilpotent A) : A = 0 := by
  obtain ⟨k, h⟩ := h
  induction k with
  | zero =>
    rw [pow_zero] at h
    rw [← mul_one A, h, mul_zero]
  | succ k ih =>
    cases k with
    | zero => simpa using h
    | succ k =>
      apply ih
      have h2 : (A ^ (k + 1)).transpose * A ^ (k + 1) = 0 := by
        rw [Matrix.transpose_pow, hs.eq, ← pow_add]
        have : k + 1 + (k + 1) = (k + 1 + 1) + k := by ring
        rw [this, pow_add, h, zero_mul]
      exact gen_lin_symm_nilpotent_eq_zero_ordered_aux1 R ι _ h2
end

-- forge:entry gen_lin_commutator_ne_one_card kind=proved origin=conjecture
section
/- Generalizes Mathlib2.lin_commutator_ne_one: ℝ → any commutative ring in which the size of the matrix is nonzero (covers every characteristic-0 field, and char p with p ∤ n; false when char divides n), Fin (n+1) → Fintype. Proof idea: trace(AB − BA) = 0 but trace 1 = card ι. -/
theorem gen_lin_commutator_ne_one_card (R : Type*) [CommRing R] (ι : Type*) [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι R) (hc : (Fintype.card ι : R) ≠ 0) : A * B - B * A ≠ 1 := by
  intro h
  have ht := congrArg Matrix.trace h
  rw [Matrix.trace_sub, Matrix.trace_mul_comm A B, sub_self, Matrix.trace_one] at ht
  exact hc ht.symm
end

-- forge:entry gen_an_schur_nat_pow_ordered_ring kind=proved origin=conjecture
section
/- Generalizes Mathlib2.an_schur_deg_one: ℝ → any linearly ordered commutative ring, and exponent 1 → arbitrary natural exponent t (Schur's inequality; t = 1 is the original). Proof idea: WLOG a ≥ b ≥ c; then a^t(a−b)(a−c) + b^t(b−a)(b−c) = (a−b)(a^t(a−c) − b^t(b−c)) ≥ 0 by monotonicity of x^t on nonnegatives, and the c-term is ≥ 0. -/
theorem gen_an_schur_nat_pow_ordered_ring_aux1 (R : Type*) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (a b c : R) (hc : 0 ≤ c) (hab : b ≤ a) (hbc : c ≤ b) (t : ℕ) : 0 ≤ a ^ t * (a - b) * (a - c) + b ^ t * (b - a) * (b - c) + c ^ t * (c - a) * (c - b) := by
  have hb : 0 ≤ b := hc.trans hbc
  have h1 : 0 ≤ c ^ t * (a - c) * (b - c) :=
    mul_nonneg (mul_nonneg (pow_nonneg hc t) (by linarith)) (by linarith)
  have hpow : b ^ t ≤ a ^ t := pow_le_pow_left₀ hb hab t
  have h3 : b ^ t * (b - c) ≤ a ^ t * (a - c) :=
    mul_le_mul hpow (by linarith) (by linarith) (pow_nonneg (hb.trans hab) t)
  have h2 : 0 ≤ (a - b) * (a ^ t * (a - c) - b ^ t * (b - c)) :=
    mul_nonneg (by linarith) (by linarith)
  have e : a ^ t * (a - b) * (a - c) + b ^ t * (b - a) * (b - c) + c ^ t * (c - a) * (c - b) = (a - b) * (a ^ t * (a - c) - b ^ t * (b - c)) + c ^ t * (a - c) * (b - c) := by ring
  rw [e]; exact add_nonneg h2 h1

theorem gen_an_schur_nat_pow_ordered_ring (R : Type*) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (a b c : R) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (t : ℕ) : 0 ≤ a ^ t * (a - b) * (a - c) + b ^ t * (b - a) * (b - c) + c ^ t * (c - a) * (c - b) := by
  rcases le_total a b with h1 | h1 <;> rcases le_total b c with h2 | h2 <;> rcases le_total a c with h3 | h3
  · linarith [gen_an_schur_nat_pow_ordered_ring_aux1 R c b a ha h2 h1 t]
  · linarith [gen_an_schur_nat_pow_ordered_ring_aux1 R c b a ha h2 h1 t]
  · linarith [gen_an_schur_nat_pow_ordered_ring_aux1 R b c a ha h2 h3 t]
  · linarith [gen_an_schur_nat_pow_ordered_ring_aux1 R b a c hc h1 h3 t]
  · linarith [gen_an_schur_nat_pow_ordered_ring_aux1 R c a b hb h3 h1 t]
  · linarith [gen_an_schur_nat_pow_ordered_ring_aux1 R a c b hb h3 h2 t]
  · linarith [gen_an_schur_nat_pow_ordered_ring_aux1 R a b c hc h1 h2 t]
  · linarith [gen_an_schur_nat_pow_ordered_ring_aux1 R a b c hc h1 h2 t]
end

-- forge:entry gen_lin_skew_odd_two_mul_det kind=proved origin=conjecture
section
/- Generalizes Mathlib2.lin_skew_odd_det_zero: ℝ → any commutative ring, with conclusion 2·det A = 0 (det A = 0 follows whenever 2 is regular; the plain conclusion is false in characteristic 2, e.g. A = 1), Fin (2n+1) → Fintype of odd cardinality. Proof idea: det A = det Aᵀ = det(−A) = (−1)^card det A = −det A. -/
theorem gen_lin_skew_odd_two_mul_det (R : Type*) [CommRing R] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R) (hodd : Odd (Fintype.card ι)) (h : A.transpose = -A) : 2 * A.det = 0 := by
  have h1 := Matrix.det_transpose A
  rw [h, Matrix.det_neg, hodd.neg_one_pow] at h1
  linear_combination -h1
end

-- forge:entry gen_an_chebyshev_index_weighted_ordered_ring kind=proved origin=conjecture
section
/- Generalizes Mathlib2.an2_chebyshev_index_weighted: ℝ → any linearly ordered commutative ring. Proof idea: induction on n, or Chebyshev sum inequality (MonovaryOn.sum_mul_sum_le_card_mul_sum) for the monotone pair (i, a i); no division is used. -/
theorem gen_an_chebyshev_index_weighted_ordered_ring_aux1 (R : Type*) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (a : ℕ → R) (ha : Monotone a) (n : ℕ) : ∑ i ∈ Finset.range n, a i ≤ (n : R) * a n := by
  have h := Finset.sum_le_card_nsmul (Finset.range n) a (a n) (fun i hi => ha (Finset.mem_range.mp hi).le)
  simpa using h

theorem gen_an_chebyshev_index_weighted_ordered_ring (R : Type*) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (a : ℕ → R) (ha : Monotone a) (n : ℕ) : ((n : R) - 1) * ∑ i ∈ Finset.range n, a i ≤ 2 * ∑ i ∈ Finset.range n, (i : R) * a i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h := gen_an_chebyshev_index_weighted_ordered_ring_aux1 R a ha n
    push_cast
    linarith [ih, h]
end

-- forge:entry gen_lin_eigenvalue_root_of_aeval_eq_zero kind=proved origin=conjecture
section
/- Generalizes Mathlib2.lin_involution_eigenvalue: ℝ → any commutative ring R acting without zero-smul-divisors (e.g. any field), and the relation f*f = 1 → an arbitrary polynomial relation p(f) = 0: every eigenvalue is a root of p (the original is p = X²−1). Proof idea: for an eigenvector v, p(f) v = p(μ) • v (Module.End.aeval_apply_of_hasEigenvector), so p(μ) • v = 0 with v ≠ 0. -/
theorem gen_lin_eigenvalue_root_of_aeval_eq_zero (R : Type*) [CommRing R] (V : Type*) [AddCommGroup V] [Module R V] [NoZeroSMulDivisors R V] (f : Module.End R V) (p : Polynomial R) (hp : Polynomial.aeval f p = 0) (μ : R) (hμ : f.HasEigenvalue μ) : p.IsRoot μ := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have h1 := Module.End.aeval_apply_of_hasEigenvector (p := p) hv
  rw [hp, LinearMap.zero_apply] at h1
  rcases smul_eq_zero.mp h1.symm with h | h
  · exact h
  · exact absurd h hv.2
end

-- forge:entry gen_an_nesbitt_finset_ordered_field kind=proved origin=conjecture
section
/- Generalizes Mathlib2.an2_nesbitt_general: ℝ → any linearly ordered field, range (n+2) → arbitrary Finset with at least 2 elements. Also implies an_nesbitt. Proof idea: with S = ∑ a, write a i/(S − a i) = S/(S − a i) − 1 and apply Cauchy–Schwarz / Sedrakyan (Finset.sum_div_pow_le or div_add_div_same style lemmas valid in ordered fields) to ∑ 1/(S − a i) with ∑ (S − a i) = (card − 1) S. -/
theorem gen_an_nesbitt_finset_ordered_field (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] (ι : Type*) (s : Finset ι) (a : ι → K) (ha : ∀ i ∈ s, 0 < a i) (hs : 2 ≤ s.card) : (s.card : K) / ((s.card : K) - 1) ≤ ∑ i ∈ s, a i / (∑ j ∈ s, a j - a i) := by
  classical
  set S := ∑ j ∈ s, a j with hSdef
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  have hS : 0 < S := Finset.sum_pos ha hne
  have hN2 : (2 : K) ≤ (s.card : K) := by exact_mod_cast hs
  set N := (s.card : K) with hN
  have hn : (0:K) < N - 1 := by linarith
  have hn2 : (0:K) < N := by linarith
  have key : ∀ i ∈ s,
      1 / (N - 1) + N^2 / (N - 1)^2 * (a i / S - 1 / N) ≤ a i / (S - a i) := by
    intro i hi
    have hd : 0 < S - a i := by
      obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne (by omega : 1 < s.card) i
      have hlt : a i < S :=
        Finset.single_lt_sum (i := i) (j := j) hji hi hj (ha j hj) (fun k hk _ => (ha k hk).le)
      linarith
    rw [← sub_nonneg]
    have e : a i / (S - a i) - (1 / (N - 1) + N^2 / (N - 1)^2 * (a i / S - 1 / N))
        = (N * a i - S)^2 / (S * (S - a i) * (N - 1)^2) := by
      field_simp
      ring
    rw [e]
    exact div_nonneg (sq_nonneg _) (mul_pos (mul_pos hS hd) (by positivity)).le
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum key)
  have h1 : ∑ x ∈ s, a x / S = 1 := by
    rw [← Finset.sum_div, ← hSdef, div_self hS.ne']
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, h1]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← hN]
  field_simp
  ring
end

-- forge:entry gen_an_hardy_finite_ordered_field kind=proved origin=conjecture
section
/- Generalizes Mathlib2.r3_hardy_inequality_finite: ℝ → any linearly ordered field (no sign hypothesis, as in the original). Proof idea: the original proof is purely algebraic (telescoping bound A_k² − 2 a_k A_k ≤ ... then T ≤ 2Q, Q² ≤ T·B ⇒ T ≤ 4B, which is square-root free); redo the sub-lemmas with K in place of ℝ, using Finset.sum_mul_sq_le_sq_mul_sq for Cauchy–Schwarz. -/
theorem gen_an_hardy_finite_ordered_field_aux1 (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] (a : ℕ → K) (k : ℕ) : ((∑ i ∈ Finset.range (k + 1), a i) / ((k : K) + 1)) ^ 2 - 2 * ((∑ i ∈ Finset.range (k + 1), a i) / ((k : K) + 1)) * a k ≤ (∑ i ∈ Finset.range k, a i) ^ 2 / (k : K) - (∑ i ∈ Finset.range (k + 1), a i) ^ 2 / ((k : K) + 1) := by
  rcases k with _ | k
  · norm_num [Finset.sum_range_one]
    nlinarith [sq_nonneg (a 0)]
  · rw [Finset.sum_range_succ _ (k + 1)]
    have hK : (0 : K) < ((k + 1 : ℕ) : K) := by positivity
    generalize ((k + 1 : ℕ) : K) = M at *
    generalize ∑ i ∈ Finset.range (k + 1), a i = s
    generalize a (k + 1) = x
    have hK1 : (0 : K) < M + 1 := by linarith
    obtain ⟨A', rfl⟩ : ∃ A', s = M * A' := ⟨s / M, by field_simp⟩
    obtain ⟨A, rfl⟩ : ∃ A, x = (M + 1) * A - M * A' := ⟨(x + M * A') / (M + 1), by field_simp; ring⟩
    have e1 : (M * A' + ((M + 1) * A - M * A')) / (M + 1) = A := by
      rw [div_eq_iff hK1.ne']; ring
    have e2 : (M * A') ^ 2 / M = M * A' ^ 2 := by
      rw [div_eq_iff hK.ne']; ring
    have e3 : (M * A' + ((M + 1) * A - M * A')) ^ 2 / (M + 1) = (M + 1) * A ^ 2 := by
      rw [div_eq_iff hK1.ne']; ring
    rw [e1, e2, e3]
    nlinarith [mul_nonneg hK.le (sq_nonneg (A - A'))]

theorem gen_an_hardy_finite_ordered_field_aux2 (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] (a : ℕ → K) (n : ℕ) : ∑ k ∈ Finset.range n, ((∑ i ∈ Finset.range (k + 1), a i) / ((k : K) + 1)) ^ 2 ≤ 2 * ∑ k ∈ Finset.range n, (∑ i ∈ Finset.range (k + 1), a i) / ((k : K) + 1) * a k := by
  have hpt := gen_an_hardy_finite_ordered_field_aux1 K a
  obtain ⟨f, hf⟩ : ∃ f : ℕ → K, ∀ k, f k = (∑ i ∈ Finset.range k, a i) ^ 2 / (k : K) := ⟨_, fun _ => rfl⟩
  have h1 : ∀ k : ℕ, ((∑ i ∈ Finset.range (k + 1), a i) / ((k : K) + 1)) ^ 2 - 2 * ((∑ i ∈ Finset.range (k + 1), a i) / ((k : K) + 1)) * a k ≤ f k - f (k + 1) := by
    intro k
    rw [hf, hf, Nat.cast_add_one]
    exact hpt k
  have h2 := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range n) => h1 k)
  rw [Finset.sum_range_sub', Finset.sum_sub_distrib] at h2
  have h3 : 0 ≤ f n := by rw [hf]; positivity
  have h4 : f 0 = 0 := by rw [hf]; simp
  have h5 : ∑ k ∈ Finset.range n, 2 * ((∑ i ∈ Finset.range (k + 1), a i) / ((k : K) + 1)) * a k = 2 * ∑ k ∈ Finset.range n, (∑ i ∈ Finset.range (k + 1), a i) / ((k : K) + 1) * a k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  linarith

theorem gen_an_hardy_finite_ordered_field_aux3 (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] (T B Q : K) (hT : 0 ≤ T) (hB : 0 ≤ B) (h1 : T ≤ 2 * Q) (h2 : Q ^ 2 ≤ T * B) : T ≤ 4 * B := by
  by_contra hlt
  push_neg at hlt
  have hQ : 0 ≤ Q := by linarith
  have h3 : T ^ 2 ≤ 4 * Q ^ 2 := by nlinarith
  have hT' : 0 < T := by linarith
  have h4 : 4 * (T * B) < T * T := by nlinarith
  nlinarith

theorem gen_an_hardy_finite_ordered_field (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] (a : ℕ → K) (n : ℕ) : ∑ k ∈ Finset.range n, ((∑ i ∈ Finset.range (k + 1), a i) / ((k : K) + 1)) ^ 2 ≤ 4 * ∑ k ∈ Finset.range n, a k ^ 2 := by
  have htel := gen_an_hardy_finite_ordered_field_aux2 K a n
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n)
    (fun k => (∑ i ∈ Finset.range (k + 1), a i) / ((k : K) + 1)) a
  exact gen_an_hardy_finite_ordered_field_aux3 K _ _ _ (Finset.sum_nonneg (fun k _ => sq_nonneg _)) (Finset.sum_nonneg (fun k _ => sq_nonneg _)) htel hcs
end

-- forge:entry gen_an_amgm_finset_ordered_ring kind=proved origin=conjecture
section
/- Generalizes Mathlib2.an2_amgm_range_pow: ℝ → any linearly ordered commutative ring via a division-free form card^card · ∏ a ≤ (∑ a)^card, range (n+1) → arbitrary Finset. Also implies an_amgm_three_cube. Proof idea: no n-th roots available, so induct on the finset (e.g. Cauchy forward–backward induction, or the smoothing step replacing min and max by mean-preserving pair). -/
theorem gen_an_amgm_finset_ordered_ring_aux1 (R : Type*) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (a b : R) (ha : 0 ≤ a) (hb : 0 ≤ b) (m : ℕ) : a ^ (m + 1) + ((m : R) + 1) * a ^ m * (b - a) ≤ b ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 := mul_le_mul_of_nonneg_left ih hb
    have hm : (0 : R) ≤ (m : R) + 1 := by positivity
    have h2 : 0 ≤ ((m : R) + 1) * a ^ m * (b - a) ^ 2 :=
      mul_nonneg (mul_nonneg hm (pow_nonneg ha m)) (sq_nonneg _)
    push_cast
    calc a ^ (m + 1 + 1) + ((m : R) + 1 + 1) * a ^ (m + 1) * (b - a)
        ≤ a ^ (m + 1 + 1) + ((m : R) + 1 + 1) * a ^ (m + 1) * (b - a) + ((m : R) + 1) * a ^ m * (b - a) ^ 2 := le_add_of_nonneg_right h2
      _ = b * (a ^ (m + 1) + ((m : R) + 1) * a ^ m * (b - a)) := by ring
      _ ≤ b * b ^ (m + 1) := h1
      _ = b ^ (m + 1 + 1) := by ring

theorem gen_an_amgm_finset_ordered_ring (R : Type*) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (ι : Type*) (s : Finset ι) (a : ι → R) (ha : ∀ i ∈ s, 0 ≤ a i) : (s.card : R) ^ s.card * ∏ i ∈ s, a i ≤ (∑ i ∈ s, a i) ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have ih := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
    have hx : 0 ≤ a j := ha j (Finset.mem_insert_self j s)
    have hS : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg (fun i hi => ha i (Finset.mem_insert_of_mem hi))
    rw [Finset.card_insert_of_notMem hj, Finset.prod_insert hj, Finset.sum_insert hj]
    generalize (∑ i ∈ s, a i) = S at ih hS ⊢
    generalize (∏ i ∈ s, a i) = P at ih ⊢
    generalize a j = x at hx ⊢
    generalize s.card = n at ih ⊢
    push_cast
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have hP : P ≤ 1 := by simpa using ih
      have : x * P ≤ x * 1 := mul_le_mul_of_nonneg_left hP hx
      simp only [Nat.cast_zero, zero_add, one_pow, one_mul, pow_one]
      linarith
    · have hn : (0 : R) < (n : R) := by exact_mod_cast hpos
      obtain ⟨c, hc⟩ : ∃ c : R, c = (n : R) + 1 := ⟨_, rfl⟩
      have hc0 : 0 ≤ c := by rw [hc]; positivity
      have hB := gen_an_amgm_finset_ordered_ring_aux1 R (c * S) ((n : R) * (x + S)) (mul_nonneg hc0 hS) (mul_nonneg hn.le (add_nonneg hx hS)) n
      rw [← hc, mul_pow, mul_pow, mul_pow] at hB
      have e : (n : R) * (x + S) - c * S = n * x - S := by rw [hc]; ring
      rw [e] at hB
      have hI := mul_le_mul_of_nonneg_left ih (mul_nonneg (mul_nonneg (pow_nonneg hc0 (n + 1)) hn.le) hx)
      rw [← hc]
      have key : (n : R) ^ (n + 1) * (c ^ (n + 1) * (x * P)) ≤ (n : R) ^ (n + 1) * (x + S) ^ (n + 1) := by
        calc (n : R) ^ (n + 1) * (c ^ (n + 1) * (x * P))
            = c ^ (n + 1) * n * x * ((n : R) ^ n * P) := by ring
          _ ≤ c ^ (n + 1) * n * x * S ^ n := hI
          _ = c ^ (n + 1) * S ^ (n + 1) + c * (c ^ n * S ^ n) * (n * x - S) := by ring
          _ ≤ (n : R) ^ (n + 1) * (x + S) ^ (n + 1) := hB
      exact le_of_mul_le_mul_left key (pow_pos hn _)
end

-- forge:entry gen_an_perm_div_sum_ge_card kind=proved origin=conjecture
section
/- Generalizes Mathlib2.an2_cyclic_div_ge_card: ℝ → any linearly ordered field, cyclic shift on range → an arbitrary permutation σ of an arbitrary Fintype: card ι ≤ ∑ x i / x (σ i). Also implies an_cyclic_div_ge_three. Proof idea: the ratios y i = x i / x (σ i) are positive with product 1 (Equiv.prod_comp); prove ∑ y ≥ card for positive y with ∏ y = 1 by induction (merge a term ≤ 1 with a term ≥ 1 using u + v ≥ 1 + u v), which needs no roots. -/
theorem gen_an_perm_div_sum_ge_card (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] (ι : Type*) [Fintype ι] (σ : Equiv.Perm ι) (x : ι → K) (hx : ∀ i, 0 < x i) : (Fintype.card ι : K) ≤ ∑ i, x i / x (σ i) := by
  have hpos : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ x i / x (σ i) := fun i _ => (div_pos (hx i) (hx (σ i))).le
  have hS : 0 ≤ ∑ i, x i / x (σ i) := Finset.sum_nonneg hpos
  have hprod : ∏ i, x i / x (σ i) = 1 := by
    rw [Finset.prod_div_distrib, Equiv.prod_comp σ x]
    exact div_self (Finset.prod_ne_zero_iff.mpr (fun i _ => (hx i).ne'))
  have h := Mathlib2.gen_an_amgm_finset_ordered_ring K ι Finset.univ (fun i => x i / x (σ i)) hpos
  rw [hprod, mul_one, Finset.card_univ] at h
  by_cases hN : Fintype.card ι = 0
  · rw [hN]; simpa using hS
  · exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) hS hN).mp h
end

-- forge:entry alg_artin_schreier_irreducible_zmod_s1h2 kind=proved origin=decomposition
section
/- alg_artin_schreier_irreducible_zmod 的证明骨架中第 2 个空洞 -/
theorem alg_artin_schreier_irreducible_zmod_s1h2 (p : ℕ) [inst : Fact (Nat.Prime p)] (g : Polynomial (ZMod p)) : Irreducible g → AdjoinRoot.root g ^ p ^ g.natDegree = AdjoinRoot.root g := by
  intro hg
  haveI : Fact (Irreducible g) := ⟨hg⟩
  haveI hfin : Module.Finite (ZMod p) (AdjoinRoot g) := (AdjoinRoot.powerBasis hg.ne_zero).finite
  haveI : Finite (AdjoinRoot g) := Module.finite_of_finite (ZMod p)
  haveI := Fintype.ofFinite (AdjoinRoot g)
  have hcard : Fintype.card (AdjoinRoot g) = p ^ g.natDegree := by
    rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card,
      (AdjoinRoot.powerBasis hg.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
  rw [← hcard]
  exact FiniteField.pow_card _
end

-- forge:entry alg_artin_schreier_irreducible_zmod_s1h3 kind=proved origin=decomposition
section
/- alg_artin_schreier_irreducible_zmod 的证明骨架中第 3 个空洞 -/
theorem alg_artin_schreier_irreducible_zmod_s1h3 (p : ℕ) [inst : Fact (Nat.Prime p)] (g : Polynomial (ZMod p)) : Irreducible g → CharP (AdjoinRoot g) p := by
  intro hg
  haveI : Fact (Irreducible g) := ⟨hg⟩
  exact charP_of_injective_algebraMap (algebraMap (ZMod p) (AdjoinRoot g)).injective p
end

-- forge:entry alg_artin_schreier_irreducible_zmod_s1h4 kind=proved origin=decomposition
section
/- alg_artin_schreier_irreducible_zmod 的证明骨架中第 4 个空洞 -/
theorem alg_artin_schreier_irreducible_zmod_s1h4 (p : ℕ) [inst : Fact (Nat.Prime p)] (f : Polynomial (ZMod p)) : f = Polynomial.X ^ p - Polynomial.X - 1 → f.natDegree = p := by
  intro hf
  subst hf
  have hp : p.Prime := Fact.out
  have h0 : (Polynomial.X + 1 : Polynomial (ZMod p)).natDegree ≤ 1 := by compute_degree
  have h1 : (Polynomial.X + 1 : Polynomial (ZMod p)).natDegree
      < (Polynomial.X ^ p : Polynomial (ZMod p)).natDegree := by
    rw [Polynomial.natDegree_X_pow]
    exact lt_of_le_of_lt h0 hp.one_lt
  rw [sub_sub, Polynomial.natDegree_sub_eq_left_of_natDegree_lt h1, Polynomial.natDegree_X_pow]
end

-- forge:entry alg_artin_schreier_irreducible_zmod_s1h1 kind=proved origin=decomposition
section
/- alg_artin_schreier_irreducible_zmod 的证明骨架中第 1 个空洞 -/
theorem alg_artin_schreier_irreducible_zmod_s1h1 (p : ℕ) [Fact (Nat.Prime p)] (K : Type) [inst : CommRing K] [CharP K p] (α : K) : α ^ p = α + 1 → ∀ (k : ℕ), α ^ p ^ k = α + (↑k : K) := by
  intro h k
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : ((k : K)) ^ p = k := by
      have h2 : (frobenius K p) (k : K) = (k : K) := frobenius_natCast K p k
      rw [frobenius_def] at h2
      exact h2
    rw [pow_succ, pow_mul, ih, add_pow_char, h, hk]
    push_cast
    ring
end

-- forge:entry alg_artin_schreier_irreducible_zmod kind=proved origin=conjecture
section
/- The Artin–Schreier polynomial X^p - X - 1 is irreducible over ZMod p — if α is a root in an extension then the roots are α + i (i ∈ F_p), so all irreducible factors have the same degree d with d ∣ p; d = 1 is impossible since a^p - a - 1 = -1 ≠ 0 for a ∈ F_p. -/
theorem alg_artin_schreier_irreducible_zmod (p : ℕ) [Fact p.Prime] : Irreducible (Polynomial.X ^ p - Polynomial.X - 1 : Polynomial (ZMod p)) := by
  have H : (∀ (K : Type) [CommRing K] [CharP K p] (α : K), α ^ p = α + 1 →
        ∀ k : ℕ, α ^ (p ^ k) = α + (k : K)) ∧
      (∀ g : Polynomial (ZMod p), Irreducible g →
        (AdjoinRoot.root g) ^ (p ^ g.natDegree) = AdjoinRoot.root g) ∧
      (∀ g : Polynomial (ZMod p), Irreducible g → CharP (AdjoinRoot g) p) ∧
      (∀ f : Polynomial (ZMod p), f = Polynomial.X ^ p - Polynomial.X - 1 → f.natDegree = p) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (first | exact @Mathlib2.alg_artin_schreier_irreducible_zmod_s1h1 p (by assumption) | exact Mathlib2.alg_artin_schreier_irreducible_zmod_s1h1 | apply Mathlib2.alg_artin_schreier_irreducible_zmod_s1h1 <;> assumption | simpa using Mathlib2.alg_artin_schreier_irreducible_zmod_s1h1 | exact @Mathlib2.alg_artin_schreier_irreducible_zmod_s1h2 p (by assumption) | exact Mathlib2.alg_artin_schreier_irreducible_zmod_s1h2 | apply Mathlib2.alg_artin_schreier_irreducible_zmod_s1h2 <;> assumption | simpa using Mathlib2.alg_artin_schreier_irreducible_zmod_s1h2 | exact @Mathlib2.alg_artin_schreier_irreducible_zmod_s1h3 p (by assumption) | exact Mathlib2.alg_artin_schreier_irreducible_zmod_s1h3 | apply Mathlib2.alg_artin_schreier_irreducible_zmod_s1h3 <;> assumption | simpa using Mathlib2.alg_artin_schreier_irreducible_zmod_s1h3 | exact @Mathlib2.alg_artin_schreier_irreducible_zmod_s1h4 p (by assumption) | exact Mathlib2.alg_artin_schreier_irreducible_zmod_s1h4 | apply Mathlib2.alg_artin_schreier_irreducible_zmod_s1h4 <;> assumption | simpa using Mathlib2.alg_artin_schreier_irreducible_zmod_s1h4)
  obtain ⟨hA, hB, hC, hD'⟩ := H
  have hD := hD' _ rfl
  have hp : p.Prime := Fact.out
  have L1 : ∀ g : Polynomial (ZMod p), Irreducible g →
      g ∣ (Polynomial.X ^ p - Polynomial.X - 1 : Polynomial (ZMod p)) → p ∣ g.natDegree := by
    intro g hg hdvd
    haveI := hC g hg
    have h0 : AdjoinRoot.mk g (Polynomial.X ^ p - Polynomial.X - 1 : Polynomial (ZMod p)) = 0 :=
      AdjoinRoot.mk_eq_zero.2 hdvd
    simp only [map_sub, map_pow, map_one, AdjoinRoot.mk_X] at h0
    have hα : (AdjoinRoot.root g) ^ p = AdjoinRoot.root g + 1 := by
      linear_combination h0
    have h1 := hA (AdjoinRoot g) (AdjoinRoot.root g) hα g.natDegree
    rw [hB g hg] at h1
    have h2 : ((g.natDegree : ℕ) : AdjoinRoot g) = 0 := by
      linear_combination -h1
    exact (CharP.cast_eq_zero_iff (AdjoinRoot g) p g.natDegree).1 h2
  have hf_ne : (Polynomial.X ^ p - Polynomial.X - 1 : Polynomial (ZMod p)) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hD
    exact hp.ne_zero hD.symm
  obtain ⟨g, hg, hgf⟩ := Polynomial.exists_irreducible_of_natDegree_pos
    (f := (Polynomial.X ^ p - Polynomial.X - 1 : Polynomial (ZMod p))) (by rw [hD]; exact hp.pos)
  have hle := Polynomial.natDegree_le_of_dvd hgf hf_ne
  rw [hD] at hle
  have hgd : g.natDegree = p :=
    Nat.le_antisymm hle (Nat.le_of_dvd hg.natDegree_pos (L1 g hg hgf))
  obtain ⟨q, hq⟩ := hgf
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    exact hf_ne hq
  have hqd : q.natDegree = 0 := by
    have h3 := congrArg Polynomial.natDegree hq
    rw [hD, Polynomial.natDegree_mul hg.ne_zero hq0, hgd] at h3
    omega
  have hu : IsUnit q := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hq0, hqd]
    rfl
  rw [hq]
  exact (irreducible_mul_isUnit hu).2 hg
end

-- forge:entry p3_fibsum kind=definition origin=definition
section
/- S_n = F_1 + ... + F_n, the sum of the first n nonzero Fibonacci numbers (F_1 = F_2 = 1) -/
def p3_fibsum (n : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 n, Nat.fib i
end

-- forge:entry p3_pisano kind=definition origin=definition
section
/- Pisano period pi(n): the least positive period of the Fibonacci sequence modulo n -/
noncomputable def p3_pisano (n : ℕ) : ℕ := sInf {k : ℕ | 0 < k ∧ ∀ i : ℕ, Nat.fib (i + k) ≡ Nat.fib i [MOD n]}
end

-- forge:entry p3_lucas kind=definition origin=definition
section
/- Lucas number L_n (L_0 = 2, L_1 = 1), written as 2 F_{n+1} - F_n -/
def p3_lucas (n : ℕ) : ℕ := 2 * Nat.fib (n + 1) - Nat.fib n
end

-- forge:entry p3_self_summable kind=definition origin=definition
section
/- k is a self-summable Fibonacci number if F_k divides F_1 + ... + F_{F_k} -/
def p3_self_summable (k : ℕ) : Prop := Nat.fib k ∣ ∑ i ∈ Finset.Icc 1 (Nat.fib k), Nat.fib i
end

end Mathlib2
