/- Mathlib2 分片 15（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0014
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry top_expanding_compact_isometry kind=proved origin=conjecture
section
/- A distance non-decreasing self-map of a compact metric space is an isometry — for x, y use compactness of X × X to find iterates n with (f^[n] x, f^[n] y) arbitrarily close to (x, y) (recurrence of the orbit of the expanding map f × f); then dist (f x) (f y) ≤ dist (f^[n] x) (f^[n] y) ≤ dist x y + 2ε. -/
theorem top_expanding_compact_isometry_aux1 {X : Type*} [MetricSpace X] (f : X → X)
    (hf : ∀ x y : X, dist x y ≤ dist (f x) (f y)) (k : ℕ) :
    ∀ x y : X, dist x y ≤ dist (f^[k] x) (f^[k] y) := by
  induction k with
  | zero => intro x y; simp
  | succ k ih =>
    intro x y
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact (hf x y).trans (ih (f x) (f y))

theorem top_expanding_compact_isometry_aux2 {Y : Type*} [MetricSpace Y] [CompactSpace Y] (u : ℕ → Y)
    (ε : ℝ) (hε : 0 < ε) : ∃ m n : ℕ, m < n ∧ dist (u m) (u n) < ε := by
  obtain ⟨a, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq u
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) (half_pos hε)
  refine ⟨φ N, φ (N + 1), hφ (Nat.lt_succ_self N), ?_⟩
  have h1 := hN N le_rfl
  have h2 := hN (N + 1) (Nat.le_succ N)
  simp only [Function.comp_apply] at h1 h2
  calc dist (u (φ N)) (u (φ (N + 1))) ≤ dist (u (φ N)) a + dist a (u (φ (N + 1))) := dist_triangle _ _ _
    _ = dist (u (φ N)) a + dist (u (φ (N + 1))) a := by rw [dist_comm a]
    _ < ε := by linarith

theorem top_expanding_compact_isometry {X : Type*} [MetricSpace X] [CompactSpace X] (f : X → X) (hf : ∀ x y : X, dist x y ≤ dist (f x) (f y)) : Isometry f := by
  apply Isometry.of_dist_eq
  intro x y
  apply le_antisymm _ (hf x y)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨m, n, hmn, hd⟩ := top_expanding_compact_isometry_aux2
    (fun n : ℕ => ((f^[n] x, f^[n] y) : X × X)) (ε / 2) (half_pos hε)
  simp only [Prod.dist_eq] at hd
  obtain ⟨hx, hy⟩ := max_lt_iff.mp hd
  obtain ⟨k, rfl⟩ : ∃ k, n = m + (k + 1) := ⟨n - m - 1, by omega⟩
  rw [Function.iterate_add_apply] at hx hy
  have hx' := top_expanding_compact_isometry_aux1 f hf m x (f^[k + 1] x)
  have hy' := top_expanding_compact_isometry_aux1 f hf m y (f^[k + 1] y)
  have h1 := top_expanding_compact_isometry_aux1 f hf k (f x) (f y)
  rw [← Function.iterate_succ_apply, ← Function.iterate_succ_apply] at h1
  have h2 := dist_triangle4 (f^[k + 1] x) x y (f^[k + 1] y)
  rw [dist_comm (f^[k + 1] x) x] at h2
  linarith
end

-- forge:entry p3_thm1_not_dvd kind=proved origin=paper
section
/- for a prime p > 5, p does not divide S_p -/
theorem p3_thm1_not_dvd (p : ℕ) (hp : p.Prime) (h5 : 5 < p) : ¬ p ∣ p3_fibsum p := by
  intro hd
  obtain ⟨hA, hB⟩ := p3_thm1_corrected p hp h5
  have hd' : (p : ℤ) ∣ (p3_fibsum p : ℤ) := Int.natCast_dvd_natCast.mpr hd
  have h50 : p % 5 ≠ 0 := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  have hcases : (p % 5 = 1 ∨ p % 5 = 4) ∨ (p % 5 = 2 ∨ p % 5 = 3) := by omega
  rcases hcases with h | h
  · have := (Int.modEq_iff_dvd).mp (hA h)
    have h1 : (p : ℤ) ∣ 1 := by
      have := dvd_add this hd'
      simpa using this
    have := Int.natCast_dvd.mp h1
    simp at this
    omega
  · have := (Int.modEq_iff_dvd).mp (hB h)
    have h1 : (p : ℤ) ∣ -2 := by
      have := dvd_add this hd'
      simpa using this
    have := Int.natCast_dvd.mp h1
    have := Nat.le_of_dvd (by norm_num) this
    simp at this
    omega
end

-- forge:entry p3_prop2 kind=proved origin=paper
section
/- for even n > 1 the Pisano period of F_n divides 2n -/
theorem p3_prop2 (n : ℕ) (h1 : 1 < n) (h2 : 2 ∣ n) : p3_pisano (Nat.fib n) ∣ 2 * n := by
  have hmem : 2 * n ∈ {k : ℕ | 0 < k ∧ ∀ i : ℕ, Nat.fib (i + k) ≡ Nat.fib i [MOD Nat.fib n]} :=
    ⟨by omega, fun i => by simpa using p3_aux_period n 1 i h2⟩
  have hpi : p3_pisano (Nat.fib n) ∈ {k : ℕ | 0 < k ∧ ∀ i : ℕ, Nat.fib (i + k) ≡ Nat.fib i [MOD Nat.fib n]} := by
    unfold p3_pisano
    exact Nat.sInf_mem ⟨_, hmem⟩
  obtain ⟨hpos, hper⟩ := hpi
  have hmul : ∀ q i : ℕ, Nat.fib (i + p3_pisano (Nat.fib n) * q) ≡ Nat.fib i [MOD Nat.fib n] := by
    intro q
    induction q with
    | zero => intro i; simp [Nat.ModEq]
    | succ q ih =>
      intro i
      rw [show i + p3_pisano (Nat.fib n) * (q + 1) = (i + p3_pisano (Nat.fib n) * q) + p3_pisano (Nat.fib n) by ring]
      exact (hper _).trans (ih i)
  rw [Nat.dvd_iff_mod_eq_zero]
  by_contra hr
  have hrS : 2 * n % p3_pisano (Nat.fib n) ∈ {k : ℕ | 0 < k ∧ ∀ i : ℕ, Nat.fib (i + k) ≡ Nat.fib i [MOD Nat.fib n]} := by
    refine ⟨Nat.pos_of_ne_zero hr, fun i => ?_⟩
    have a := hmul (2 * n / p3_pisano (Nat.fib n)) (i + 2 * n % p3_pisano (Nat.fib n))
    have b := hmem.2 i
    rw [add_assoc, Nat.mod_add_div] at a
    exact a.symm.trans b
  have hle : p3_pisano (Nat.fib n) ≤ 2 * n % p3_pisano (Nat.fib n) := by
    unfold p3_pisano at hrS ⊢
    exact Nat.sInf_le hrS
  have := Nat.mod_lt (2 * n) hpos
  omega
end

-- forge:entry geo_unit_sum_zero_sum_sq kind=proved origin=conjecture
section
/- For unit complex numbers with a+b+c = 0, also a²+b²+c² = 0 — conj a = a⁻¹ etc., so ab+bc+ca = abc·conj(a+b+c) = 0, and a²+b²+c² = (a+b+c)² − 2(ab+bc+ca). -/
open ComplexConjugate

theorem geo_unit_sum_zero_sum_sq_aux1 (a : ℂ) (ha : ‖a‖ = 1) : a * conj a = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]
  norm_num

theorem geo_unit_sum_zero_sum_sq (a b c : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (h : a + b + c = 0) : a ^ 2 + b ^ 2 + c ^ 2 = 0 := by
  have ha' := geo_unit_sum_zero_sum_sq_aux1 a ha
  have hb' := geo_unit_sum_zero_sum_sq_aux1 b hb
  have hc' := geo_unit_sum_zero_sum_sq_aux1 c hc
  have hconj : conj a + conj b + conj c = 0 := by
    have := congrArg conj h
    simpa using this
  linear_combination (a + b + c) * h - 2 * (a * b * c * hconj - b * c * ha' - a * c * hb' - a * b * hc')
end

-- forge:entry p3_thm2 kind=proved origin=paper
section
/- for n = 2p or 4p with p an odd prime, p = 2 mod 3, p = ±2 mod 5: F_n is odd and F_n divides F_{F_n+2} - 1 -/
theorem p3_thm2_aux1 (m : ℕ) : (Nat.fib (2 * m) : ℤ) = Nat.fib m * (2 * Nat.fib (m + 1) - Nat.fib m) := by
  have := Nat.fib_le_fib_succ (n := m)
  rw [Nat.fib_two_mul, Nat.cast_mul, Nat.cast_sub (by omega)]
  push_cast; ring
theorem p3_thm2_aux2 (p : ℕ) (hp : p.Prime) (hodd : Odd p) (h5 : p % 5 = 2 ∨ p % 5 = 3) :
    p ∣ Nat.fib (2 * p) + 1 ∧ p ∣ Nat.fib (4 * p) + 3 := by
  have h2 : p ≠ 2 := by rintro rfl; exact absurd hodd (by decide)
  obtain ⟨a, b⟩ := (p3_thm1_corrected_aux1 p hp h2).2 h5
  have e1 := congrArg (Int.cast : ℤ → ZMod p) (p3_thm2_aux1 p)
  push_cast at e1
  rw [a, b] at e1
  have e1' : (Nat.fib (2 * p) : ZMod p) = -1 := by rw [e1]; ring
  have e2 := congrArg (Nat.cast : ℕ → ZMod p) (Nat.fib_two_mul_add_one p)
  push_cast at e2
  rw [a, b] at e2
  have e2' : (Nat.fib (2 * p + 1) : ZMod p) = 1 := by rw [e2]; ring
  have e3 := congrArg (Int.cast : ℤ → ZMod p) (p3_thm2_aux1 (2 * p))
  push_cast at e3
  rw [e1', e2'] at e3
  constructor
  · rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [e1']; ring
  · rw [← ZMod.natCast_eq_zero_iff, show 4 * p = 2 * (2 * p) by ring]; push_cast; rw [e3]; ring
theorem p3_thm2_aux3 (j : ℕ) : Nat.fib (2 * (6 * j + 5)) ≡ 1 [MOD 2] ∧ Nat.fib (4 * (6 * j + 5)) ≡ 1 [MOD 2] ∧ 4 ∣ Nat.fib (2 * (6 * j + 5)) + 1 ∧ 8 ∣ Nat.fib (4 * (6 * j + 5)) + 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := p3_aux_period_aux3 2 3 (by decide) (by decide) (4 * j + 3) 1
    rw [show 2 * (6 * j + 5) = 1 + 3 * (4 * j + 3) by ring]; exact this
  · have := p3_aux_period_aux3 2 3 (by decide) (by decide) (8 * j + 6) 2
    rw [show 4 * (6 * j + 5) = 2 + 3 * (8 * j + 6) by ring]; exact this
  · have := p3_aux_period_aux3 4 6 (by decide) (by decide) (2 * j + 1) 4
    rw [show 2 * (6 * j + 5) = 4 + 6 * (2 * j + 1) by ring]
    exact (Nat.modEq_zero_iff_dvd).mp ((this.add_right 1).trans (by decide))
  · have := p3_aux_period_aux3 8 12 (by decide) (by decide) (2 * j + 1) 8
    rw [show 4 * (6 * j + 5) = 8 + 12 * (2 * j + 1) by ring]
    exact (Nat.modEq_zero_iff_dvd).mp ((this.add_right 3).trans (by decide))
theorem p3_thm2 (p n : ℕ) (hp : p.Prime) (hodd : Odd p) (h3 : p % 3 = 2) (h5 : p % 5 = 2 ∨ p % 5 = 3) (hn : n = 2 * p ∨ n = 4 * p) : Nat.fib n ≡ 1 [MOD 2] ∧ (Nat.fib (Nat.fib n + 2) : ℤ) - 1 ≡ 0 [ZMOD Nat.fib n] := by
  have hj : p = 6 * (p / 6) + 5 := by obtain ⟨k, hk⟩ := hodd; omega
  obtain ⟨m2a, m2b, d4, d8⟩ := p3_thm2_aux3 (p / 6)
  rw [← hj] at m2a m2b d4 d8
  obtain ⟨dp2, dp4⟩ := p3_thm2_aux2 p hp hodd h5
  have c2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
  rcases hn with rfl | rfl
  · refine ⟨m2a, ?_⟩
    have cop : Nat.Coprime 4 p := Nat.Coprime.pow_left 2 c2
    obtain ⟨t, ht⟩ := cop.mul_dvd_of_dvd_of_dvd d4 dp2
    have per := p3_aux_period (2 * p) t 1 ⟨p, rfl⟩
    have e : 1 + 2 * (2 * p) * t = Nat.fib (2 * p) + 2 := by
      have : 2 * (2 * p) * t = 4 * p * t := by ring
      omega
    rw [e] at per
    have z := (Int.natCast_modEq_iff).mpr per
    rw [Nat.fib_one] at z
    have z2 := z.sub_right 1
    rw [Nat.cast_one, sub_self] at z2
    exact z2
  · refine ⟨m2b, ?_⟩
    have cop : Nat.Coprime 8 p := Nat.Coprime.pow_left 3 c2
    obtain ⟨t, ht⟩ := cop.mul_dvd_of_dvd_of_dvd d8 dp4
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := Nat.exists_eq_succ_of_ne_zero (by rintro rfl; simp at ht)
    have per0 := p3_aux_period (4 * p) (s + 1) 0 ⟨2 * p, by ring⟩
    have per1 := p3_aux_period (4 * p) (s + 1) 1 ⟨2 * p, by ring⟩
    have hM : 2 * (4 * p) * (s + 1) = 8 * p * (s + 1) := by ring
    have e0 : 0 + 2 * (4 * p) * (s + 1) = (Nat.fib (4 * p) + 2) + 1 := by omega
    have e1 : 1 + 2 * (4 * p) * (s + 1) = (Nat.fib (4 * p) + 2) + 2 := by omega
    rw [e0] at per0
    rw [e1] at per1
    generalize Nat.fib (4 * p) + 2 = q at per0 per1 ⊢
    have z0 := (Int.natCast_modEq_iff).mpr per0
    have z1 := (Int.natCast_modEq_iff).mpr per1
    rw [Nat.fib_zero, Nat.cast_zero] at z0
    rw [Nat.fib_one, Nat.cast_one] at z1
    have z := (z1.sub z0).sub_right 1
    rw [show ((1 : ℤ) - 0 - 1) = 0 by norm_num] at z
    have e : (Nat.fib q : ℤ) - 1 = ((Nat.fib (q + 2) : ℕ) : ℤ) - ((Nat.fib (q + 1) : ℕ) : ℤ) - 1 := by
      rw [Nat.fib_add_two]; push_cast; ring
    rw [e]
    exact z
end

-- forge:entry geo_unit_sum_zero_equilateral kind=proved origin=conjecture
section
/- Three unit complex numbers with sum zero form an equilateral triangle of side √3 — ‖a+b‖² = ‖c‖² = 1 and the parallelogram law give ‖a−b‖² = 2+2−1 = 3; symmetric for the others. -/
theorem geo_unit_sum_zero_equilateral_aux1 (a b c : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (h : a + b + c = 0) : ‖a - b‖ = Real.sqrt 3 := by
  have ha2 : a.re * a.re + a.im * a.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, ha]; norm_num
  have hb2 : b.re * b.re + b.im * b.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hb]; norm_num
  have hc2 : c.re * c.re + c.im * c.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hc]; norm_num
  have hre : a.re + b.re + c.re = 0 := by
    have := congrArg Complex.re h
    simpa using this
  have him : a.im + b.im + c.im = 0 := by
    have := congrArg Complex.im h
    simpa using this
  have h3 : ‖a - b‖ ^ 2 = 3 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    linear_combination 2 * ha2 + 2 * hb2 - hc2 + (c.re - a.re - b.re) * hre + (c.im - a.im - b.im) * him
  rw [← h3, Real.sqrt_sq (norm_nonneg _)]

theorem geo_unit_sum_zero_equilateral (a b c : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (h : a + b + c = 0) : ‖a - b‖ = Real.sqrt 3 ∧ ‖b - c‖ = Real.sqrt 3 ∧ ‖c - a‖ = Real.sqrt 3 := by
  refine ⟨geo_unit_sum_zero_equilateral_aux1 a b c ha hb hc h, geo_unit_sum_zero_equilateral_aux1 b c a hb hc ha ?_, geo_unit_sum_zero_equilateral_aux1 c a b hc ha hb ?_⟩
  · linear_combination h
  · linear_combination h
end

-- forge:entry geo_leibniz_centroid kind=proved origin=conjecture
section
/- Leibniz (moment of inertia / parallel axis) identity: for the centroid g of points x_i, Σ|p − x_i|² = n|p − g|² + Σ|g − x_i|² — write p − x_i = (p − g) + (g − x_i), expand, and the cross term vanishes because Σ(g − x_i) = 0 (empty s is trivial). -/
theorem geo_leibniz_centroid {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type*} (s : Finset ι) (x : ι → V) (p : V) : ∑ i ∈ s, ‖p - x i‖ ^ 2 = (s.card : ℝ) * ‖p - (s.card : ℝ)⁻¹ • ∑ j ∈ s, x j‖ ^ 2 + ∑ i ∈ s, ‖(s.card : ℝ)⁻¹ • ∑ j ∈ s, x j - x i‖ ^ 2 := by
  rcases Finset.eq_empty_or_nonempty s with rfl | hs
  · simp
  have hn : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hs).ne'
  simp only [norm_sub_sq_real, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    ← Finset.mul_sum, ← inner_sum, norm_smul, inner_smul_left, inner_smul_right, nsmul_eq_mul,
    mul_pow, Real.norm_eq_abs, sq_abs, RCLike.conj_to_real, real_inner_self_eq_norm_sq]
  field_simp
  ring
end

-- forge:entry p3_cor2 kind=proved origin=paper
section
/- infinitely many odd k divide F_1+...+F_k (also Conjecture 1 of the paper) -/
theorem p3_cor2 : {k : ℕ | Odd k ∧ k ∣ p3_fibsum k}.Infinite := by
  have hu : IsUnit (2 : ZMod 15) := IsUnit.of_mul_eq_one 8 (by decide)
  have hinf := (Nat.infinite_setOfPred_prime_and_eq_mod hu).diff (Set.finite_singleton 2)
  have hinj : Set.InjOn (fun p : ℕ => Nat.fib (2 * p)) ({p : ℕ | Nat.Prime p ∧ (p : ZMod 15) = 2} \ {2}) := by
    rintro p ⟨⟨hp, -⟩, -⟩ q ⟨⟨hq, -⟩, -⟩ h
    have h' : Nat.fib ((2 * p - 2) + 2) = Nat.fib ((2 * q - 2) + 2) := by
      have := hp.two_le
      have := hq.two_le
      rw [show 2 * p - 2 + 2 = 2 * p by omega, show 2 * q - 2 + 2 = 2 * q by omega]
      exact h
    have := Nat.fib_add_two_strictMono.injective h'
    have := hp.two_le
    have := hq.two_le
    omega
  refine (hinf.image hinj).mono ?_
  rintro k ⟨p, ⟨⟨hp, hmod⟩, hne⟩, rfl⟩
  have hne2 : p ≠ 2 := hne
  have h15 : p ≡ 2 [MOD 15] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    exact_mod_cast hmod
  unfold Nat.ModEq at h15
  have hodd : Odd p := hp.odd_of_ne_two hne2
  obtain ⟨hpar, hdiv⟩ := p3_thm2 p (2 * p) hp hodd (by omega) (by omega) (Or.inl rfl)
  refine ⟨Nat.odd_iff.mpr hpar, ?_⟩
  have hs : (p3_fibsum (Nat.fib (2 * p)) : ℤ) = (Nat.fib (Nat.fib (2 * p) + 2) : ℤ) - 1 := by
    have := p3_prop1_aux1 (Nat.fib (2 * p))
    have : (p3_fibsum (Nat.fib (2 * p)) : ℤ) + 1 = Nat.fib (Nat.fib (2 * p) + 2) := by exact_mod_cast this
    linarith
  have := (Int.modEq_zero_iff_dvd).mp hdiv
  rw [← hs] at this
  exact Int.natCast_dvd_natCast.mp this
end

-- forge:entry p3_cor1 kind=proved origin=paper
section
/- lim_{N→∞} min{π(n)/n : 0 < n < N} = 0 -/
theorem p3_cor1_aux1 (n : ℕ) : (((Nat.fib n : ℤ) + Nat.fib (n + 1)) * Nat.fib n - (Nat.fib (n + 1) : ℤ) ^ 2) ^ 2 = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : ((Nat.fib (n + 1 + 1) : ℕ) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by
      exact_mod_cast Nat.fib_add_two
    rw [h2]
    linear_combination ih

theorem p3_cor1_aux2 (n : ℕ) : Nat.fib n ^ 4 ≡ 1 [MOD Nat.fib (n + 1)] := by
  rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd]
  push_cast
  refine ⟨((Nat.fib n : ℤ) - Nat.fib (n + 1)) * (2 * (Nat.fib n : ℤ) ^ 2 + Nat.fib (n + 1) * ((Nat.fib n : ℤ) - Nat.fib (n + 1))), ?_⟩
  linear_combination (-1 : ℤ) * p3_cor1_aux1 n

theorem p3_cor1_aux3 (n i : ℕ) : Nat.fib (i + (n + 1)) ≡ Nat.fib i * Nat.fib n [MOD Nat.fib (n + 1)] := by
  rw [show i + (n + 1) = i + n + 1 from rfl, Nat.fib_add]
  exact Nat.add_mul_mod_self_right _ _ _

theorem p3_cor1_aux4 (n i : ℕ) : Nat.fib (i + 4 * (n + 1)) ≡ Nat.fib i [MOD Nat.fib (n + 1)] := by
  have e : i + 4 * (n + 1) = i + (n + 1) + (n + 1) + (n + 1) + (n + 1) := by ring
  rw [e]
  have s := p3_cor1_aux3 n
  have h1 := s (i + (n + 1) + (n + 1) + (n + 1))
  have h2 := (s (i + (n + 1) + (n + 1))).mul_right (Nat.fib n)
  have h3 := ((s (i + (n + 1))).mul_right (Nat.fib n)).mul_right (Nat.fib n)
  have h4 := (((s i).mul_right (Nat.fib n)).mul_right (Nat.fib n)).mul_right (Nat.fib n)
  have h5 := (p3_cor1_aux2 n).mul_left (Nat.fib i)
  have h6 := h1.trans (h2.trans (h3.trans h4))
  have e2 : Nat.fib i * Nat.fib n * Nat.fib n * Nat.fib n * Nat.fib n = Nat.fib i * Nat.fib n ^ 4 := by ring
  rw [e2] at h6
  have h7 := h6.trans h5
  rwa [mul_one] at h7

theorem p3_cor1_aux5 (m : ℕ) (hm : 0 < m) : p3_pisano (Nat.fib m) ≤ 4 * m := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  unfold p3_pisano
  exact Nat.sInf_le ⟨by omega, fun i => p3_cor1_aux4 n i⟩

theorem p3_cor1 : Filter.Tendsto (fun N : ℕ => sInf ((fun n : ℕ => (p3_pisano n : ℝ) / n) '' Set.Ioo 0 N)) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (8 / ε)
  have hK5 : 5 ≤ k + 5 := by omega
  have hfK : k + 5 ≤ Nat.fib (k + 5) := Nat.le_fib_self hK5
  have hmono : Nat.fib (k + 5) ≤ Nat.fib (k + 5 + 1) := Nat.fib_le_fib_succ
  have hM : (k + 5) * (k + 5) ≤ Nat.fib (2 * (k + 5)) := by
    rw [Nat.fib_two_mul]
    exact (Nat.mul_le_mul hfK hfK).trans (Nat.mul_le_mul_left _ (by omega))
  have hp := p3_cor1_aux5 (2 * (k + 5)) (by omega)
  have hMpos : 0 < Nat.fib (2 * (k + 5)) := by nlinarith
  refine ⟨Nat.fib (2 * (k + 5)) + 1, fun N hN => ?_⟩
  rw [Real.dist_eq, sub_zero]
  have hnn : ∀ x ∈ (fun n : ℕ => (p3_pisano n : ℝ) / n) '' Set.Ioo 0 N, 0 ≤ x := by
    rintro _ ⟨n, -, rfl⟩
    positivity
  rw [abs_of_nonneg (Real.sInf_nonneg hnn)]
  have hle : sInf ((fun n : ℕ => (p3_pisano n : ℝ) / n) '' Set.Ioo 0 N) ≤ (p3_pisano (Nat.fib (2 * (k + 5))) : ℝ) / (Nat.fib (2 * (k + 5)) : ℕ) :=
    csInf_le ⟨0, fun x hx => hnn x hx⟩ ⟨Nat.fib (2 * (k + 5)), ⟨hMpos, by omega⟩, rfl⟩
  refine lt_of_le_of_lt hle ?_
  have hMpos' : (0 : ℝ) < (Nat.fib (2 * (k + 5)) : ℕ) := by exact_mod_cast hMpos
  rw [div_lt_iff₀ hMpos']
  have hM' : ((k : ℝ) + 5) * (k + 5) ≤ (Nat.fib (2 * (k + 5)) : ℕ) := by exact_mod_cast hM
  have hp' : (p3_pisano (Nat.fib (2 * (k + 5))) : ℝ) ≤ 4 * (2 * ((k : ℝ) + 5)) := by exact_mod_cast hp
  have h8 : 8 < ε * k := by
    rw [div_lt_iff₀ hε] at hk
    linarith
  have a1 : ε * (((k : ℝ) + 5) * (k + 5)) ≤ ε * (Nat.fib (2 * (k + 5)) : ℕ) := mul_le_mul_of_nonneg_left hM' hε.le
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have a2 : 8 * ((k : ℝ) + 5) < ε * ((k + 5) * (k + 5)) := by
    nlinarith [mul_pos hε (by linarith : (0 : ℝ) < k + 5), mul_nonneg hε.le hk0]
  linarith
end

-- forge:entry bld_idempotent_sum_rank kind=proved origin=conjecture
section
/- Uses Mathlib2.gen_lin_idempotent_trace_eq_rank_field three times: rank(A+B) = tr(A+B) = tr A + tr B = rank A + rank B in K, then Nat.cast injectivity in characteristic zero. -/
theorem bld_idempotent_sum_rank (K : Type*) [Field K] [CharZero K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι K) (hA : A * A = A) (hB : B * B = B) (hAB : (A + B) * (A + B) = A + B) : Matrix.rank (A + B) = Matrix.rank A + Matrix.rank B := by
  have h1 := Mathlib2.gen_lin_idempotent_trace_eq_rank_field K ι A hA
  have h2 := Mathlib2.gen_lin_idempotent_trace_eq_rank_field K ι B hB
  have h3 := Mathlib2.gen_lin_idempotent_trace_eq_rank_field K ι (A + B) hAB
  rw [Matrix.trace_add, h1, h2] at h3
  exact_mod_cast h3.symm
end

-- forge:entry bld_iterate_shrinking_unique_fixed_point kind=proved origin=conjecture
section
/- Uses Mathlib2.top_edelstein_unique_fixed_point applied to f^[n]: its unique fixed point p satisfies f^[n] (f p) = f p, so f p = p by uniqueness; any fixed point of f is fixed by f^[n]. (Shrinking analogue of Mathlib2.top_fixed_of_iterate_contraction.) -/
theorem bld_iterate_shrinking_unique_fixed_point {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X] (f : X → X) (n : ℕ) (h : ∀ x y : X, x ≠ y → dist (f^[n] x) (f^[n] y) < dist x y) : ∃! p : X, f p = p := by
  obtain ⟨p, hp, huniq⟩ := Mathlib2.top_edelstein_unique_fixed_point (f^[n]) h
  refine ⟨p, ?_, ?_⟩
  · apply huniq
    show f^[n] (f p) = f p
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hp]
  · intro q hq
    exact huniq q (Function.iterate_fixed hq n)
end

-- forge:entry bld_sqrt_two_rec_rate kind=proved origin=conjecture
section
/- Uses Mathlib2.ana_sqrt_two_rec_closed_form: a n = 2 cos(π/2^(n+1)), so 2 - a n = 4 sin^2(π/2^(n+2)) ≤ 4 (π/2^(n+2))^2 = π^2/4^(n+1). Quantitative rate for Mathlib2.ana_sqrt_two_rec_tendsto. -/
theorem bld_sqrt_two_rec_rate (a : ℕ → ℝ) (h0 : a 0 = 0) (hrec : ∀ n : ℕ, a (n + 1) = Real.sqrt (2 + a n)) (n : ℕ) : 2 - a n ≤ Real.pi ^ 2 / 4 ^ (n + 1) := by
  rw [Mathlib2.ana_sqrt_two_rec_closed_form a h0 hrec n]
  have h := Real.one_sub_sq_div_two_le_cos (x := Real.pi / 2 ^ (n + 1))
  have e : Real.pi ^ 2 / 4 ^ (n + 1) = (Real.pi / 2 ^ (n + 1)) ^ 2 := by
    rw [div_pow, ← pow_mul, mul_comm, pow_mul]; norm_num
  rw [e]
  linarith
end

-- forge:entry bld_surjective_nonexpanding_compact_isometry kind=proved origin=conjecture
section
/- Uses Mathlib2.top_expanding_compact_isometry and Mathlib2.top_isometry_compact_surjective: a right inverse g of f is expanding, hence an isometry by the first theorem and surjective by the second; so g is a bijective isometry and f = g⁻¹ is an isometry. -/
theorem bld_surjective_nonexpanding_compact_isometry {X : Type*} [MetricSpace X] [CompactSpace X] (f : X → X) (hs : Function.Surjective f) (hf : ∀ x y : X, dist (f x) (f y) ≤ dist x y) : Isometry f := by
  have hfg : ∀ x, f (Function.surjInv hs x) = x := Function.surjInv_eq hs
  have hg : Isometry (Function.surjInv hs) := by
    apply Mathlib2.top_expanding_compact_isometry
    intro x y
    calc dist x y = dist (f (Function.surjInv hs x)) (f (Function.surjInv hs y)) := by
          rw [hfg, hfg]
      _ ≤ _ := hf _ _
  have hgs := Mathlib2.top_isometry_compact_surjective _ hg
  refine Isometry.of_dist_eq (fun x y => ?_)
  obtain ⟨a, rfl⟩ := hgs x
  obtain ⟨b, rfl⟩ := hgs y
  rw [hfg, hfg, hg.dist_eq]
end

-- forge:entry bld_involution_trace_rank kind=proved origin=conjecture
section
/- Uses Mathlib2.gen_lin_idempotent_trace_eq_rank_field: P = (1/2) • (1 + A) is idempotent, so tr P = rank P = rank (1 + A) (scaling by a unit preserves rank), and tr P = (n + tr A)/2. -/
theorem bld_involution_trace_rank_aux1 (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K) (c : K) (hc : c ≠ 0) : Matrix.rank (c • M) = Matrix.rank M := by
  apply le_antisymm
  · have : c • M = (c • (1 : Matrix ι ι K)) * M := by rw [Matrix.smul_mul, Matrix.one_mul]
    rw [this]; exact Matrix.rank_mul_le_right _ _
  · have : M = (c⁻¹ • (1 : Matrix ι ι K)) * (c • M) := by
      rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hc, one_smul]
    conv_lhs => rw [this]
    exact Matrix.rank_mul_le_right _ _

theorem bld_involution_trace_rank_aux2 (K : Type*) [Field K] [CharZero K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (h : A * A = 1) : ((2:K)⁻¹ • (1 + A)) * ((2:K)⁻¹ • (1 + A)) = (2:K)⁻¹ • (1 + A) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have : (1 + A) * (1 + A) = (2:K) • (1 + A) := by
    rw [mul_add, add_mul, add_mul, h, one_mul, one_mul, mul_one, two_smul]; abel
  rw [this, smul_smul]
  congr 1
  field_simp

theorem bld_involution_trace_rank (K : Type*) [Field K] [CharZero K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (h : A * A = 1) : Matrix.trace A + (Fintype.card ι : K) = 2 * (Matrix.rank (1 + A) : K) := by
  have h1 := Mathlib2.gen_lin_idempotent_trace_eq_rank_field K ι _ (bld_involution_trace_rank_aux2 K ι A h)
  rw [bld_involution_trace_rank_aux1 K ι _ _ (by norm_num), Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one] at h1
  rw [← h1, smul_eq_mul]
  field_simp
  ring
end

-- forge:entry bld_sqrt_two_rec_viete_prod kind=proved origin=conjecture
section
/- Uses Mathlib2.ana_sqrt_two_rec_closed_form: a (i+1)/2 = cos(π/2^(i+2)); induct on n with sin(2θ) = 2 sin θ cos θ (finite Viète product). -/
theorem bld_sqrt_two_rec_viete_prod (a : ℕ → ℝ) (h0 : a 0 = 0) (hrec : ∀ n : ℕ, a (n + 1) = Real.sqrt (2 + a n)) (n : ℕ) : (∏ i ∈ Finset.range n, a (i + 1) / 2) * (2 ^ n * Real.sin (Real.pi / 2 ^ (n + 1))) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Mathlib2.ana_sqrt_two_rec_closed_form a h0 hrec (n + 1)]
    have h2 : Real.pi / 2 ^ (n + 1) = 2 * (Real.pi / 2 ^ (n + 1 + 1)) := by
      rw [pow_succ 2 (n + 1)]; field_simp
    rw [h2, Real.sin_two_mul] at ih
    rw [← ih, pow_succ]
    ring
end

-- forge:entry bld_edelstein_iterates_tendsto kind=proved origin=conjecture
section
/- Uses Mathlib2.top_tendsto_of_subseq_limits_unique (and complements Mathlib2.top_edelstein_unique_fixed_point): dist (f^[n] x) p is antitone with limit c; any subsequential limit b satisfies dist b p = c = dist (f b) p by continuity, forcing b = p by strict contraction; conclude by the subsequence criterion on the compact space. -/
theorem bld_edelstein_iterates_tendsto {X : Type*} [MetricSpace X] [CompactSpace X] (f : X → X) (hf : ∀ x y : X, x ≠ y → dist (f x) (f y) < dist x y) (p : X) (hp : f p = p) (x : X) : Filter.Tendsto (fun n : ℕ => f^[n] x) Filter.atTop (nhds p) := by
  have hf' : ∀ x y : X, dist (f x) (f y) ≤ dist x y := by
    intro x y
    by_cases hxy : x = y
    · subst hxy; simp
    · exact (hf x y hxy).le
  have hcont : Continuous f :=
    (LipschitzWith.of_dist_le_mul (K := 1) (by simpa using hf')).continuous
  have hanti : Antitone (fun n : ℕ => dist (f^[n] x) p) := by
    apply antitone_nat_of_succ_le
    intro n
    show dist (f^[n+1] x) p ≤ dist (f^[n] x) p
    rw [Function.iterate_succ_apply']
    calc dist (f (f^[n] x)) p = dist (f (f^[n] x)) (f p) := by rw [hp]
      _ ≤ _ := hf' _ _
  have hbdd : BddBelow (Set.range (fun n : ℕ => dist (f^[n] x) p)) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact dist_nonneg⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  apply Mathlib2.top_tendsto_of_subseq_limits_unique
  intro φ hφ b hb
  by_contra hne
  have h1 : Filter.Tendsto (fun n => dist (f^[φ n] x) p) Filter.atTop (nhds (dist b p)) :=
    (hb.dist tendsto_const_nhds)
  have h1' : Filter.Tendsto (fun n => dist (f^[φ n] x) p) Filter.atTop
      (nhds (⨅ n, dist (f^[n] x) p)) := hlim.comp hφ.tendsto_atTop
  have e1 := tendsto_nhds_unique h1 h1'
  have h2 : Filter.Tendsto (fun n => dist (f^[φ n + 1] x) p) Filter.atTop (nhds (dist (f b) p)) := by
    have : Filter.Tendsto (fun n => dist (f (f^[φ n] x)) p) Filter.atTop (nhds (dist (f b) p)) :=
      ((hcont.tendsto b).comp hb).dist tendsto_const_nhds
    refine this.congr (fun n => ?_)
    rw [Function.iterate_succ_apply']
  have h2' : Filter.Tendsto (fun n => dist (f^[φ n + 1] x) p) Filter.atTop
      (nhds (⨅ n, dist (f^[n] x) p)) :=
    hlim.comp ((Filter.tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop)
  have e2 := tendsto_nhds_unique h2 h2'
  have := hf b p hne
  rw [hp] at this
  linarith
end

-- forge:entry bld_involution_rank_add_rank kind=proved origin=conjecture
section
/- Uses Mathlib2.gen_lin_idempotent_rank_complement_field: P = (1/2) • (1 + A) is idempotent with 1 - P = (1/2) • (1 - A); rank is invariant under scaling by the unit 1/2. -/
theorem bld_involution_rank_add_rank (K : Type*) [Field K] [CharZero K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (h : A * A = 1) : Matrix.rank (1 + A) + Matrix.rank (1 - A) = Fintype.card ι := by
  have h1 := Mathlib2.gen_lin_idempotent_rank_complement_field K ι _ (Mathlib2.bld_involution_trace_rank_aux2 K ι A h)
  have h2 : (1 : Matrix ι ι K) - (2:K)⁻¹ • (1 + A) = (2:K)⁻¹ • (1 - A) := by
    module
  rw [h2, Mathlib2.bld_involution_trace_rank_aux1 K ι _ _ (by norm_num), Mathlib2.bld_involution_trace_rank_aux1 K ι _ _ (by norm_num)] at h1
  exact h1
end

-- forge:entry bld_nilpotent_rank_bound kind=proved origin=conjecture
section
/- Uses Mathlib2.gen_lin_sylvester_rank_rect: by induction on j, j * rank A ≤ (j-1) * n + rank (A^j) (Sylvester applied to A^j and A); at j = k the last term vanishes. Special case k = 2: A^2 = 0 implies 2 rank A ≤ n. -/
theorem bld_nilpotent_rank_bound_aux1 (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (j : ℕ) : (j + 1) * Matrix.rank A ≤ j * Fintype.card ι + Matrix.rank (A ^ (j + 1)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hs := Mathlib2.gen_lin_sylvester_rank_rect K ι ι ι (A ^ (j + 1)) A
    rw [← pow_succ] at hs
    nlinarith [ih, hs]

theorem bld_nilpotent_rank_bound (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (k : ℕ) (h : A ^ k = 0) : k * Matrix.rank A ≤ (k - 1) * Fintype.card ι := by
  cases k with
  | zero => simp
  | succ j =>
    have := bld_nilpotent_rank_bound_aux1 K ι A j
    rw [h, Matrix.rank_zero] at this
    simpa using this
end

-- forge:entry bld_sqrt_two_rec_viete_tendsto kind=proved origin=conjecture
section
/- Uses Mathlib2.ana_sqrt_two_rec_closed_form (and the finite product identity derived from it): the partial products equal 1/(2^n sin(π/2^(n+1))), and 2^n sin(π/2^(n+1)) → π/2 since sin t / t → 1. This is Viète's formula 2/π = (√2/2)(√(2+√2)/2)⋯. -/
open Filter Topology

theorem bld_sqrt_two_rec_viete_tendsto (a : ℕ → ℝ) (h0 : a 0 = 0) (hrec : ∀ n : ℕ, a (n + 1) = Real.sqrt (2 + a n)) : Filter.Tendsto (fun n : ℕ => ∏ i ∈ Finset.range n, a (i + 1) / 2) Filter.atTop (nhds (2 / Real.pi)) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hd := (hasDerivAt_iff_tendsto_slope_zero.1 (Real.hasDerivAt_sin 0))
  simp only [zero_add, Real.sin_zero, sub_zero, Real.cos_zero, smul_eq_mul] at hd
  have ht0 : Tendsto (fun n : ℕ => Real.pi / 2 ^ (n + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((1:ℝ) / 2) ^ (n + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp (tendsto_add_atTop_nat 1)
    have h2 := h1.const_mul Real.pi
    simp only [mul_zero] at h2
    refine h2.congr (fun n => ?_)
    rw [one_div_pow]; ring
  have ht : Tendsto (fun n : ℕ => Real.pi / 2 ^ (n + 1)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨ht0, Eventually.of_forall (fun n => ?_)⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    positivity
  have hs := ((hd.comp ht).const_mul (Real.pi / 2)).inv₀ (by positivity)
  have e : (Real.pi / 2 * 1)⁻¹ = 2 / Real.pi := by rw [mul_one, inv_div]
  rw [e] at hs
  refine hs.congr (fun n => ?_)
  have hp := Mathlib2.bld_sqrt_two_rec_viete_prod a h0 hrec n
  simp only [Function.comp]
  have e2 : Real.pi / 2 * ((Real.pi / 2 ^ (n + 1))⁻¹ * Real.sin (Real.pi / 2 ^ (n + 1))) = 2 ^ n * Real.sin (Real.pi / 2 ^ (n + 1)) := by
    rw [pow_succ]; field_simp
  rw [e2]
  exact inv_eq_of_mul_eq_one_right (by rw [mul_comm]; exact hp)
end

-- forge:entry bld_mantel_triangle_free kind=proved origin=conjecture
section
/- Uses Mathlib2.comb_degree_add_degree_le_of_triangle_free: summing deg u + deg v ≤ |V| over edges gives ∑_v deg(v)^2 ≤ |E| |V|; Cauchy–Schwarz and the handshake lemma give (2|E|)^2 ≤ |V| ∑ deg^2 ≤ |V|^2 |E|. Extends Mathlib2.comb_card_edgeFinset_le_of_coloring_bool from bipartite to triangle-free graphs (Mantel). -/
theorem bld_mantel_triangle_free (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.CliqueFree 3) : 4 * G.edgeFinset.card ≤ Fintype.card V ^ 2 := by
  have key : ∑ u, ∑ v ∈ G.neighborFinset u, G.degree v = ∑ v, G.degree v ^ 2 := by
    simp_rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, sq]
    congr 1
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext u
    simp [SimpleGraph.adj_comm]
  have h1 : ∑ u, ∑ v ∈ G.neighborFinset u, (G.degree u + G.degree v)
      ≤ ∑ u, G.degree u * Fintype.card V := by
    refine Finset.sum_le_sum (fun u _ => ?_)
    calc ∑ v ∈ G.neighborFinset u, (G.degree u + G.degree v)
        ≤ ∑ v ∈ G.neighborFinset u, Fintype.card V := by
          refine Finset.sum_le_sum (fun v hv => ?_)
          exact Mathlib2.comb_degree_add_degree_le_of_triangle_free V G h u v
            ((SimpleGraph.mem_neighborFinset _ _ _).1 hv)
      _ = G.degree u * Fintype.card V := by
          rw [Finset.sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree]
  have h2 : ∑ u, ∑ v ∈ G.neighborFinset u, (G.degree u + G.degree v)
      = ∑ v, G.degree v ^ 2 + ∑ v, G.degree v ^ 2 := by
    simp_rw [Finset.sum_add_distrib]
    rw [key]
    congr 1
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree, sq]
  have hs := G.sum_degrees_eq_twice_card_edges
  have hc : (∑ v, G.degree v) ^ 2 ≤ Fintype.card V * ∑ v, G.degree v ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset V)) (f := fun v => G.degree v)
    simpa using this
  rw [← Finset.sum_mul, hs] at h1
  rw [h2] at h1
  rw [hs] at hc
  set E := G.edgeFinset.card
  set n := Fintype.card V
  set D := ∑ v, G.degree v ^ 2
  rcases Nat.eq_zero_or_pos E with h0 | hpos
  · rw [h0]; positivity
  · have h3 : (4 * E) * E ≤ n ^ 2 * E := by nlinarith
    exact Nat.le_of_mul_le_mul_right h3 hpos
end

end Mathlib2
