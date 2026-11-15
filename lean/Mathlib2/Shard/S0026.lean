/- Mathlib2 分片 26（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0025
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry poly_x4_x_1_irreducible_zmod2 kind=proved origin=conjecture
section
/- X^4 + X + 1 is irreducible over F_2 — no roots in F_2, and the only irreducible quadratic is X^2+X+1 whose square is X^4+X^2+1 ≠ X^4+X+1. -/
open Polynomial in
theorem poly_x4_x_1_irreducible_zmod2 : Irreducible (Polynomial.X ^ 4 + Polynomial.X + 1 : Polynomial (ZMod 2)) := by
  have hm : (X ^ 4 + X + 1 : (ZMod 2)[X]).Monic := by monicity!
  have hd : (X ^ 4 + X + 1 : (ZMod 2)[X]).natDegree = 4 := by compute_degree!
  rw [hm.irreducible_iff_natDegree']
  refine ⟨?_, ?_⟩
  · intro h; rw [h] at hd; simp at hd
  intro f g hf hg hfg hmem
  rw [hd] at hmem
  have hsum : f.natDegree + g.natDegree = 4 := by
    rw [← hf.natDegree_mul hg, hfg, hd]
  simp only [Finset.mem_Ioc] at hmem
  have hcase : g.natDegree = 1 ∨ g.natDegree = 2 := by omega
  rcases hcase with h1 | h2
  · have key : ∀ r : ZMod 2, r ^ 4 + r + 1 ≠ 0 := by decide
    have hg1 := eq_X_add_C_of_natDegree_le_one (p := g) (by omega)
    have hc : g.coeff 1 = 1 := by have := hg.coeff_natDegree; rwa [h1] at this
    rw [hc] at hg1
    generalize g.coeff 0 = t at hg1
    have hev := congrArg (eval (-t)) hfg
    have hge : eval (-t) g = 0 := by
      rw [hg1]; simp; exact (by decide : ∀ t : ZMod 2, t + t = 0) t
    rw [eval_mul, hge, mul_zero] at hev
    simp only [eval_add, eval_pow, eval_X, eval_one] at hev
    exact key _ hev.symm
  · have hf2 : f.natDegree = 2 := by omega
    have hfq := eq_quadratic_of_degree_le_two (p := f) (by rw [degree_eq_natDegree hf.ne_zero, hf2]; rfl)
    have hgq := eq_quadratic_of_degree_le_two (p := g) (by rw [degree_eq_natDegree hg.ne_zero, h2]; rfl)
    have hfc : f.coeff 2 = 1 := by have := hf.coeff_natDegree; rwa [hf2] at this
    have hgc : g.coeff 2 = 1 := by have := hg.coeff_natDegree; rwa [h2] at this
    rw [hfc] at hfq
    rw [hgc] at hgq
    generalize f.coeff 1 = a at hfq
    generalize f.coeff 0 = b at hfq
    generalize g.coeff 1 = c at hgq
    generalize g.coeff 0 = d at hgq
    have e : f * g = X ^ 4 + C (a + c) * X ^ 3 + C (b + d + a * c) * X ^ 2 + C (a * d + b * c) * X + C (b * d) := by
      rw [hfq, hgq]
      simp only [map_add, map_mul, map_one]
      ring
    rw [e] at hfg
    have c0 := congrArg (fun q => coeff q 0) hfg
    have c1 := congrArg (fun q => coeff q 1) hfg
    have c2 := congrArg (fun q => coeff q 2) hfg
    have c3 := congrArg (fun q => coeff q 3) hfg
    simp only [coeff_add, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X, coeff_one] at c0 c1 c2 c3
    norm_num at c0 c1 c2 c3
    clear hfg e hfq hgq
    revert a b c d
    decide
end

-- forge:entry poly_x4_sub_10x2_add_1_irreducible_int kind=proved origin=conjecture
section
/- The minimal polynomial X^4 - 10X^2 + 1 of √2+√3 is irreducible over ℤ — no integer roots (±1 fail); a factorisation into monic quadratics (X^2+aX+b)(X^2-aX+d) with bd = 1 forces a(d-b) = 0 and b+d-a^2 = -10, i.e. a^2 = 12 or a^2 = 8 or (a = 0, b + d = -10 with bd = 1), all impossible. -/
open Polynomial in
theorem poly_x4_sub_10x2_add_1_irreducible_int : Irreducible (Polynomial.X ^ 4 - 10 * Polynomial.X ^ 2 + 1 : Polynomial ℤ) := by
  have e10 : (X ^ 4 - 10 * X ^ 2 + 1 : ℤ[X]) = X ^ 4 + C (-10) * X ^ 2 + C 1 := by
    simp only [C_neg, map_ofNat, map_one]; ring
  rw [e10]
  have hm : (X ^ 4 + C (-10) * X ^ 2 + C 1 : ℤ[X]).Monic := by monicity!
  have hd : (X ^ 4 + C (-10) * X ^ 2 + C 1 : ℤ[X]).natDegree = 4 := by compute_degree!
  rw [hm.irreducible_iff_natDegree']
  refine ⟨?_, ?_⟩
  · intro h; rw [h] at hd; simp at hd
  intro f g hf hg hfg hmem
  rw [hd] at hmem
  have hsum : f.natDegree + g.natDegree = 4 := by
    rw [← hf.natDegree_mul hg, hfg, hd]
  simp only [Finset.mem_Ioc] at hmem
  have hcase : g.natDegree = 1 ∨ g.natDegree = 2 := by omega
  rcases hcase with h1 | h2
  · have hg1 := eq_X_add_C_of_natDegree_le_one (p := g) (by omega)
    have hc : g.coeff 1 = 1 := by have := hg.coeff_natDegree; rwa [h1] at this
    rw [hc] at hg1
    generalize g.coeff 0 = t at hg1
    have hev := congrArg (eval (-t)) hfg
    have hge : eval (-t) g = 0 := by
      rw [hg1]; simp
    rw [eval_mul, hge, mul_zero] at hev
    simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C] at hev
    have hdvd : t ∣ 1 := ⟨-(t ^ 3 - 10 * t), by linarith⟩
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h <;> subst h <;> norm_num at hev
  · have hf2 : f.natDegree = 2 := by omega
    have hfq := eq_quadratic_of_degree_le_two (p := f) (by rw [degree_eq_natDegree hf.ne_zero, hf2]; rfl)
    have hgq := eq_quadratic_of_degree_le_two (p := g) (by rw [degree_eq_natDegree hg.ne_zero, h2]; rfl)
    have hfc : f.coeff 2 = 1 := by have := hf.coeff_natDegree; rwa [hf2] at this
    have hgc : g.coeff 2 = 1 := by have := hg.coeff_natDegree; rwa [h2] at this
    rw [hfc] at hfq
    rw [hgc] at hgq
    generalize f.coeff 1 = a at hfq
    generalize f.coeff 0 = b at hfq
    generalize g.coeff 1 = c at hgq
    generalize g.coeff 0 = d at hgq
    have e : f * g = X ^ 4 + C (a + c) * X ^ 3 + C (b + d + a * c) * X ^ 2 + C (a * d + b * c) * X + C (b * d) := by
      rw [hfq, hgq]
      simp only [map_add, map_mul, map_one]
      ring
    rw [e] at hfg
    have c0 := congrArg (fun q => coeff q 0) hfg
    have c1 := congrArg (fun q => coeff q 1) hfg
    have c2 := congrArg (fun q => coeff q 2) hfg
    have c3 := congrArg (fun q => coeff q 3) hfg
    simp only [coeff_add, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X] at c0 c1 c2 c3
    norm_num at c0 c1 c2 c3
    have hca : c = -a := by linarith
    subst hca
    rcases Int.isUnit_iff.mp (isUnit_of_mul_eq_one b d c0) with hb | hb <;> subst hb
    · have hd1 : d = 1 := by linarith
      subst hd1
      have h12 : a * a = 12 := by linarith
      have : a ≤ 3 := by nlinarith
      have : -3 ≤ a := by nlinarith
      interval_cases a <;> omega
    · have hd1 : d = -1 := by linarith
      subst hd1
      have h8 : a * a = 8 := by linarith
      have : a ≤ 2 := by nlinarith
      have : -2 ≤ a := by nlinarith
      interval_cases a <;> omega
end

-- forge:entry poly_x4_sub_10x2_add_1_reducible_zmod kind=proved origin=conjecture
section
/- X^4 - 10X^2 + 1 is reducible modulo every prime — one of 2, 3, 6 is a square mod p (Legendre symbol multiplicativity; p = 2, 3 by hand), and X^4-10X^2+1 = (X^2-1)^2 - 8X^2 = (X^2+1)^2 - 12X^2 = (X^2-5)^2 - 24, each a difference of squares when 2, 3, 6 respectively is a square. -/
open Polynomial in
theorem poly_x4_sub_10x2_add_1_reducible_zmod (p : ℕ) [Fact p.Prime] : ¬ Irreducible (Polynomial.X ^ 4 - 10 * Polynomial.X ^ 2 + 1 : Polynomial (ZMod p)) := by
  have c2 : (C (2 : ZMod p) : (ZMod p)[X]) = 2 := map_ofNat C 2
  have c5 : (C (5 : ZMod p) : (ZMod p)[X]) = 5 := map_ofNat C 5
  by_cases h2 : IsSquare (2 : ZMod p)
  · obtain ⟨r, hr⟩ := h2
    have e : (X ^ 4 - 10 * X ^ 2 + 1 : (ZMod p)[X]) = (X ^ 2 + C (2 * r) * X + C (-1)) * (X ^ 2 + C (-(2 * r)) * X + C (-1)) := by
      have : (X ^ 4 - 10 * X ^ 2 + 1 : (ZMod p)[X]) = X ^ 4 - (2 + 4 * C (r * r)) * X ^ 2 + 1 := by rw [← hr]; simp only [c2]; ring
      rw [this]; simp only [C_mul, C_neg, C_1, c2]; ring
    rw [e]; exact alg_x_pow_four_add_one_not_irreducible_zmod_aux1 _ _ _ _ _
  by_cases h3 : IsSquare (3 : ZMod p)
  · obtain ⟨r, hr⟩ := h3
    have c3 : (C (3 : ZMod p) : (ZMod p)[X]) = 3 := map_ofNat C 3
    have e : (X ^ 4 - 10 * X ^ 2 + 1 : (ZMod p)[X]) = (X ^ 2 + C (2 * r) * X + C 1) * (X ^ 2 + C (-(2 * r)) * X + C 1) := by
      have : (X ^ 4 - 10 * X ^ 2 + 1 : (ZMod p)[X]) = X ^ 4 - (4 * C (r * r) - 2) * X ^ 2 + 1 := by rw [← hr]; simp only [c3]; ring
      rw [this]; simp only [C_mul, C_neg, C_1, c2]; ring
    rw [e]; exact alg_x_pow_four_add_one_not_irreducible_zmod_aux1 _ _ _ _ _
  have q2 := quadraticChar_neg_one_iff_not_isSquare.mpr h2
  have q3 := quadraticChar_neg_one_iff_not_isSquare.mpr h3
  have q6 : quadraticChar (ZMod p) 6 = 1 := by
    have : (6 : ZMod p) = 2 * 3 := by norm_num
    rw [this, map_mul, q2, q3]; norm_num
  have hne : (6 : ZMod p) ≠ 0 := by
    intro h0; rw [h0] at q6; simp at q6
  obtain ⟨r, hr⟩ := (quadraticChar_one_iff_isSquare hne).mp q6
  have c6 : (C (6 : ZMod p) : (ZMod p)[X]) = 6 := map_ofNat C 6
  have e : (X ^ 4 - 10 * X ^ 2 + 1 : (ZMod p)[X]) = (X ^ 2 + C 0 * X + C (-5 + 2 * r)) * (X ^ 2 + C 0 * X + C (-5 - 2 * r)) := by
    have : (X ^ 4 - 10 * X ^ 2 + 1 : (ZMod p)[X]) = X ^ 4 - 10 * X ^ 2 + (25 - 4 * C (r * r)) := by rw [← hr]; simp only [c6]; ring
    rw [this]; simp only [C_mul, C_neg, C_0, C_add, C_sub, c2, c5]; ring
  rw [e]; exact alg_x_pow_four_add_one_not_irreducible_zmod_aux1 _ _ _ _ _
end

-- forge:entry bld5_permMatrix_involution_rank_one_sub kind=proved origin=conjecture
section
/- Uses Mathlib2.bld4_permMatrix_involution_rank_fixed_points and Mathlib2.bld_involution_rank_add_rank: P = permMatrix σ satisfies P*P = 1 (permMatrix is multiplicative up to order and σ*σ = 1), so bld_involution_rank_add_rank gives rank(1+P) + rank(1−P) = n, and bld4 gives 2·rank(1+P) = n + fix. Subtracting: 2·rank(1−P) = n − fix, i.e. rank(1 − P) is the number of 2-cycles of σ. -/
theorem bld5_permMatrix_involution_rank_one_sub (K : Type*) [Field K] [CharZero K] (ι : Type*) [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) (hσ : σ * σ = 1) : 2 * (1 - Equiv.Perm.permMatrix K σ).rank + (Finset.univ.filter (fun i => σ i = i)).card = Fintype.card ι := by
  have hPP : σ.permMatrix K * σ.permMatrix K = 1 := by
    have h2 : σ.trans σ = Equiv.refl ι := by
      ext i
      have := congrArg (fun τ : Equiv.Perm ι => τ i) hσ
      simpa using this
    unfold Equiv.Perm.permMatrix
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, h2, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  have h1 := bld_involution_rank_add_rank K ι (σ.permMatrix K) hPP
  have h2 := bld4_permMatrix_involution_rank_fixed_points K ι σ hσ
  omega
end

-- forge:entry poly_trinomial_3k2_not_irreducible_int kind=proved origin=conjecture
section
/- X^n + X + 1 is reducible over ℤ for n ≡ 2 mod 3, n ≥ 5 (e.g. X^5+X+1 = (X^2+X+1)(X^3-X^2+1)) — X^2+X+1 divides it since X^3 ≡ 1; the monic cofactor has degree 3k ≥ 3 so neither factor is a unit. -/
open Polynomial in
theorem poly_trinomial_3k2_not_irreducible_int (k : ℕ) (hk : 1 ≤ k) : ¬ Irreducible (Polynomial.X ^ (3 * k + 2) + Polynomial.X + 1 : Polynomial ℤ) := by
  intro h
  have hdvd := poly_x2_x_1_dvd_trinomial k 0
  simp only [mul_zero, zero_add, pow_one] at hdvd
  obtain ⟨q, hq⟩ := hdvd
  rcases h.isUnit_or_isUnit hq with hu | hu
  · obtain ⟨r, -, hr⟩ := Polynomial.isUnit_iff.mp hu
    have := congrArg (fun q => Polynomial.coeff q 2) hr
    simp only [coeff_add, coeff_X_pow, coeff_C, coeff_X, coeff_one] at this
    norm_num at this
  · obtain ⟨r, -, hr⟩ := Polynomial.isUnit_iff.mp hu
    rw [← hr] at hq
    have := congrArg (fun q => Polynomial.coeff q (3 * k + 2)) hq
    simp only [coeff_mul_C, coeff_add, coeff_X_pow, coeff_X, coeff_one] at this
    have h1 : 3 * k + 2 ≠ 2 := by omega
    have h2 : 1 ≠ 3 * k + 2 := by omega
    have h3 : 3 * k + 2 ≠ 0 := by omega
    have h4 : k ≠ 0 := by omega
    simp [h1, h2, h3, h4] at this
end

-- forge:entry poly_no_consecutive_powerful kind=proved origin=conjecture
section
/- In char 0 there are no non-constant 'consecutive powerful polynomials': if every irreducible factor of f and of f+1 occurs at least squared then f is constant — a powerful polynomial g satisfies 2·deg rad g ≤ deg g; Uses Mathlib2.ms_mason_stothers_v2 with (f, 1, -(f+1)): deg f < deg rad(f(f+1)) = deg rad f + deg rad(f+1) ≤ deg f/2 + deg f/2, contradiction. -/
open UniqueFactorizationMonoid

theorem poly_no_consecutive_powerful_aux1 {k : Type*} [Field k] [DecidableEq k] (g : Polynomial k) (hg : ∀ p : Polynomial k, Irreducible p → p ∣ g → p ^ 2 ∣ g) : (radical g) ^ 2 ∣ g := by
  unfold radical
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_isRelPrime
  · intro x hx y hy hne
    exact (pairwise_primeFactors_isRelPrime hx hy hne).pow
  · intro p hp
    rw [mem_primeFactors] at hp
    exact hg p (irreducible_of_normalized_factor p hp) (dvd_of_mem_normalizedFactors hp)

theorem poly_no_consecutive_powerful {k : Type*} [Field k] [DecidableEq k] [CharZero k] (f : Polynomial k) (hf : ∀ p : Polynomial k, Irreducible p → p ∣ f → p ^ 2 ∣ f) (hf1 : ∀ p : Polynomial k, Irreducible p → p ∣ f + 1 → p ^ 2 ∣ f + 1) : f.natDegree = 0 := by
  by_contra hdeg
  have hpos : 0 < f.natDegree := Nat.pos_of_ne_zero hdeg
  have hf0 : f ≠ 0 := by rintro rfl; simp at hdeg
  have hd1 : (f + 1).natDegree = f.natDegree :=
    Polynomial.natDegree_add_eq_left_of_natDegree_lt (by simpa using hpos)
  have hf10 : f + 1 ≠ 0 := by
    intro h; rw [h] at hd1; simp at hd1; omega
  have key := Mathlib2.poly_abc_radical_bound_of_coprime f 1 isCoprime_one_right hpos
  rw [mul_one] at key
  have h1 := Polynomial.natDegree_le_of_dvd (poly_no_consecutive_powerful_aux1 f hf) hf0
  have h2 := Polynomial.natDegree_le_of_dvd (poly_no_consecutive_powerful_aux1 (f + 1) hf1) hf10
  rw [Polynomial.natDegree_pow] at h1 h2
  have h3 := Polynomial.natDegree_le_of_dvd (radical_mul_dvd (a := f) (b := f + 1)) (mul_ne_zero radical_ne_zero radical_ne_zero)
  rw [Polynomial.natDegree_mul radical_ne_zero radical_ne_zero] at h3
  have : f.natDegree ≤ max f.natDegree (1 : Polynomial k).natDegree := le_max_left _ _
  omega
end

-- forge:entry bld5_gcd_fib_lucas_dvd_two kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_lucas_sq_sub_five_fib_sq: with g = gcd(F_n, L_n), g² divides L_n² − 5F_n² = 4·(−1)^n (the bld2 identity, in ℤ), so g² ∣ 4 and hence g ∣ 2 (g ≤ 2 by size, then case check, or Nat.pow_dvd_pow_iff with 4 = 2²). -/
theorem bld5_gcd_fib_lucas_dvd_two (n : ℕ) : Nat.gcd (Nat.fib n) (p3_lucas n) ∣ 2 := by
  have h := bld2_lucas_sq_sub_five_fib_sq n
  set g := Nat.gcd (Nat.fib n) (p3_lucas n) with hg
  have h1 : (g:ℤ) ∣ (Nat.fib n : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
  have h2 : (g:ℤ) ∣ (p3_lucas n : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)
  have h3 : (g:ℤ)^2 ∣ 4 * (-1)^n := by
    rw [← h]; exact dvd_sub (pow_dvd_pow_of_dvd h2 2) (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd h1 2) 5)
  have h4 : (g:ℤ)^2 ∣ 4 := by
    rcases neg_one_pow_eq_or ℤ n with h' | h' <;> rw [h'] at h3
    · simpa using h3
    · have := (dvd_neg (a := (g:ℤ)^2) (b := 4 * (-1))).mpr h3
      simpa using this
  have h5 : g^2 ∣ 2^2 := by exact_mod_cast h4
  exact (Nat.pow_dvd_pow_iff (n:=2) two_ne_zero).mp h5
end

-- forge:entry bld5_sqrt_two_rec_partial_sum_lower kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_sqrt_two_rec_defect_summable, Mathlib2.bld3_sqrt_two_rec_defect_tsum_bounds and Mathlib2.ana_sqrt_two_rec_lt_two: ∑_{i<n} (2 − a_i) ≤ ∑' (2 − a_i) by sum_le_tsum (terms non-negative by ana_sqrt_two_rec_lt_two, summable by bld2), and the series is ≤ π²/3 by bld3; rearrange using Finset.sum_sub_distrib and Finset.sum_const. -/
theorem bld5_sqrt_two_rec_partial_sum_lower (a : ℕ → ℝ) (h0 : a 0 = 0) (h : ∀ n : ℕ, a (n + 1) = Real.sqrt (2 + a n)) (n : ℕ) : 2 * (n : ℝ) - Real.pi ^ 2 / 3 ≤ ∑ i ∈ Finset.range n, a i := by
  have hs := bld2_sqrt_two_rec_defect_summable a h0 h
  have hb := (bld3_sqrt_two_rec_defect_tsum_bounds a h0 h).2
  have hle : ∑ i ∈ Finset.range n, (2 - a i) ≤ ∑' i, (2 - a i) :=
    hs.sum_le_tsum _ (fun i _ => by linarith [(ana_sqrt_two_rec_lt_two a h0 h i).2])
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
  linarith
end

-- forge:entry bld5_pell_five_neg_four_pisano_mod_eight kind=proved origin=conjecture
section
/- Uses Mathlib2.bld3_pell_five_neg_four_solutions_lucas and Mathlib2.bld2_pisano_fib_odd_eq: the Pell classification gives y = F_{2n+1}; y ≥ 5 forces 2n+1 ≥ 5 (F_1 = 1, F_3 = 2), so bld2_pisano_fib_odd_eq gives pisano y = 4(2n+1) = 8n + 4. -/
theorem bld5_pell_five_neg_four_pisano_mod_eight (x y : ℕ) (h : x ^ 2 + 4 = 5 * y ^ 2) (hy : 5 ≤ y) : p3_pisano y % 8 = 4 := by
  obtain ⟨n, hn, -⟩ := bld3_pell_five_neg_four_solutions_lucas x y h
  have h2 : 2 ≤ n := by
    by_contra hc
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> norm_num at hn <;> omega
  rw [hn, bld2_pisano_fib_odd_eq (2*n+1) (by omega) ⟨n, rfl⟩]; omega
end

-- forge:entry bld5_carleman_sqrt_two_rec_defect kind=proved origin=conjecture
section
/- Uses Mathlib2.bld4_carleman_finite_three, Mathlib2.bld3_sqrt_two_rec_defect_tsum_bounds, Mathlib2.bld2_sqrt_two_rec_defect_summable and Mathlib2.ana_sqrt_two_rec_lt_two: the defects 2 − a_i are non-negative (ana_sqrt_two_rec_lt_two), so Carleman's inequality with constant 3 (bld4) bounds the sum of geometric means by 3·∑_{k<n}(2 − a_k) ≤ 3·∑'(2 − a_k) (sum_le_tsum with bld2 summability) ≤ 3·π²/3 = π² (bld3). -/
theorem bld5_carleman_sqrt_two_rec_defect (a : ℕ → ℝ) (h0 : a 0 = 0) (h : ∀ n : ℕ, a (n + 1) = Real.sqrt (2 + a n)) (n : ℕ) : ∑ k ∈ Finset.range n, (∏ i ∈ Finset.range (k + 1), (2 - a i)) ^ (1 / ((k : ℝ) + 1)) ≤ Real.pi ^ 2 := by
  have hs := bld2_sqrt_two_rec_defect_summable a h0 h
  have hb := (bld3_sqrt_two_rec_defect_tsum_bounds a h0 h).2
  have hnn : ∀ i, 0 ≤ 2 - a i := fun i => by linarith [(ana_sqrt_two_rec_lt_two a h0 h i).2]
  have hle : ∑ i ∈ Finset.range n, (2 - a i) ≤ ∑' i, (2 - a i) :=
    hs.sum_le_tsum _ (fun i _ => hnn i)
  have hc := bld4_carleman_finite_three (fun i => 2 - a i) hnn n
  linarith
end

-- forge:entry bld5_pisano_prime_le_four_mul kind=proved origin=conjecture
section
/- Uses Mathlib2.bld4_pisano_prime_dvd_pred_of_isSquare_five, Mathlib2.bld4_pisano_prime_dvd_two_mul_succ_of_not_isSquare_five, Mathlib2.lib_fib_period_iff and Mathlib2.bld3_pisano_dvd_of_period: for p = 2 and p = 5 check F_3 ≡ 0, F_4 ≡ 1 mod 2 and F_20 ≡ 0, F_21 ≡ 1 mod 5, so (lib_fib_period_iff, bld3_pisano_dvd_of_period) pisano ∣ 3 resp. 20 = 4·5 (equality case). Otherwise split on IsSquare (5 : ZMod p): the first bld4 theorem gives pisano ∣ p − 1, the second pisano ∣ 2(p+1) ≤ 4p; conclude with Nat.le_of_dvd. -/
theorem bld5_pisano_prime_le_four_mul (p : ℕ) (hp : p.Prime) : p3_pisano p ≤ 4 * p := by
  haveI := Fact.mk hp
  have h2le := hp.two_le
  by_cases h2 : p = 2
  · subst h2
    have h : p3_pisano 2 ∣ 3 := bld3_pisano_dvd_of_period 2 3 ((lib_fib_period_iff 2 3).mpr ⟨by norm_num [Nat.ModEq], by norm_num [Nat.ModEq]⟩)
    have := Nat.le_of_dvd (by norm_num) h; omega
  by_cases h5 : p = 5
  · subst h5
    have h : p3_pisano 5 ∣ 20 := bld3_pisano_dvd_of_period 5 20 ((lib_fib_period_iff 5 20).mpr ⟨by norm_num [Nat.ModEq], by norm_num [Nat.ModEq]⟩)
    have := Nat.le_of_dvd (by norm_num) h; omega
  by_cases hs : IsSquare (5 : ZMod p)
  · have := Nat.le_of_dvd (by omega) (bld4_pisano_prime_dvd_pred_of_isSquare_five p h2 h5 hs); omega
  · have := Nat.le_of_dvd (by omega) (bld4_pisano_prime_dvd_two_mul_succ_of_not_isSquare_five p hs); omega
end

-- forge:entry bld5_hardy_sqrt_two_rec_defect_means kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_hardy_inequality_tsum, Mathlib2.bld_sqrt_two_rec_rate and Mathlib2.ana_sqrt_two_rec_lt_two: by ana_sqrt_two_rec_lt_two and bld_sqrt_two_rec_rate, 0 ≤ 2 − a_k ≤ π²/4^(k+1), so (2 − a_k)² ≤ π⁴/16^(k+1), which is summable (geometric) with sum π⁴/15 (tsum_geometric_of_lt_one, tsum_le_tsum). Hardy's inequality bld2_hardy_inequality_tsum applied to the defect sequence bounds the left side by 4·∑'(2 − a_k)² ≤ 4π⁴/15. -/
theorem bld5_hardy_sqrt_two_rec_defect_means (a : ℕ → ℝ) (h0 : a 0 = 0) (h : ∀ n : ℕ, a (n + 1) = Real.sqrt (2 + a n)) : ∑' k : ℕ, ((∑ i ∈ Finset.range (k + 1), (2 - a i)) / ((k : ℝ) + 1)) ^ 2 ≤ 4 * Real.pi ^ 4 / 15 := by
  have hnn : ∀ i, 0 ≤ 2 - a i := fun i => by linarith [(ana_sqrt_two_rec_lt_two a h0 h i).2]
  have hg : HasSum (fun k : ℕ => Real.pi ^ 4 / 16 * (1 / 16 : ℝ) ^ k) (Real.pi ^ 4 / 16 * (1 - 1 / 16)⁻¹) :=
    (hasSum_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hb : ∀ k : ℕ, (2 - a k) ^ 2 ≤ Real.pi ^ 4 / 16 * (1 / 16 : ℝ) ^ k := by
    intro k
    have h1 := bld_sqrt_two_rec_rate a h0 h k
    have h2 : (2 - a k) ^ 2 ≤ (Real.pi ^ 2 / 4 ^ (k + 1)) ^ 2 :=
      pow_le_pow_left₀ (hnn k) h1 2
    have h3 : (Real.pi ^ 2 / 4 ^ (k + 1)) ^ 2 = Real.pi ^ 4 / 16 * (1 / 16 : ℝ) ^ k := by
      have : (16 : ℝ) ^ k = (4 ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [one_div, inv_pow, this, pow_succ]
      field_simp
      ring
    linarith
  have hsum : Summable (fun k : ℕ => (2 - a k) ^ 2) :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) hb hg.summable
  have hH := (bld2_hardy_inequality_tsum (fun i => 2 - a i) hsum).2
  have hle : ∑' k : ℕ, (2 - a k) ^ 2 ≤ Real.pi ^ 4 / 16 * (1 - 1 / 16)⁻¹ := by
    rw [← hg.tsum_eq]
    exact hsum.tsum_le_tsum hb hg.summable
  have : Real.pi ^ 4 / 16 * (1 - 1 / 16 : ℝ)⁻¹ = Real.pi ^ 4 / 15 := by norm_num; ring
  linarith
end

-- forge:entry poly_abc_distinct_roots_complex kind=proved origin=conjecture
section
/- Stothers' form over ℂ: for coprime a, b with a non-constant, the product ab(a+b) has at least deg a + 1 distinct complex roots — Uses Mathlib2.ms_mason_stothers_v2 (c = -(a+b)) to get deg a < deg rad(ab(a+b)), then show over an algebraically closed field that natDegree (radical p) equals the number of distinct roots of p (radical is the product of the distinct monic linear factors). -/
open UniqueFactorizationMonoid Polynomial

theorem poly_abc_distinct_roots_complex_aux1 {k : Type*} [Field k] [DecidableEq k] [IsAlgClosed k] (p : Polynomial k) (hp : p ≠ 0) : (radical p).natDegree ≤ p.roots.toFinset.card := by
  have hfac : ∀ q ∈ primeFactors p, q.Monic ∧ q.natDegree = 1 ∧ q ∣ p := by
    intro q hq
    rw [mem_primeFactors] at hq
    have hirr := irreducible_of_normalized_factor q hq
    have hmon : q.Monic := by
      rw [← normalize_normalized_factor q hq]
      exact Polynomial.monic_normalize hirr.ne_zero
    exact ⟨hmon, Polynomial.natDegree_eq_of_degree_eq_some (IsAlgClosed.degree_eq_one_of_irreducible k hirr), dvd_of_mem_normalizedFactors hq⟩
  have h1 : (radical p).natDegree = (primeFactors p).card := by
    unfold radical
    rw [Polynomial.natDegree_prod_of_monic _ id (fun q hq => (hfac q hq).1)]
    rw [Finset.sum_congr rfl (fun q hq => show (id q).natDegree = 1 from (hfac q hq).2.1)]
    simp
  rw [h1]
  apply Finset.card_le_card_of_injOn (fun q => -q.coeff 0)
  · intro q hq
    obtain ⟨hm, hd, hdvd⟩ := hfac q hq
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def]
    apply Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdvd
    rw [hm.eq_X_add_C hd]
    simp
  · intro q hq q' hq' h
    obtain ⟨hm, hd, -⟩ := hfac q hq
    obtain ⟨hm', hd', -⟩ := hfac q' hq'
    rw [hm.eq_X_add_C hd, hm'.eq_X_add_C hd']
    simp only [neg_inj] at h
    rw [h]

theorem poly_abc_distinct_roots_complex (a b : Polynomial ℂ) (hab : IsCoprime a b) (ha : 0 < a.natDegree) : a.natDegree + 1 ≤ (a * b * (a + b)).roots.toFinset.card := by
  have key := Mathlib2.poly_abc_radical_bound_of_coprime a b hab ha
  have hp : a * b * (a + b) ≠ 0 := by
    intro h
    rw [h, radical_zero] at key
    simp at key
  have h2 := poly_abc_distinct_roots_complex_aux1 _ hp
  have : a.natDegree ≤ max a.natDegree b.natDegree := le_max_left _ _
  omega
end

-- forge:entry bld5_nonexpanding_denseRange_compact_recurrence kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_surjective_nonexpanding_compact_isometry and Mathlib2.bld4_isometry_compact_uniform_recurrence: f is 1-Lipschitz hence continuous, so range f is compact, hence closed, and dense, hence everything (DenseRange.closure_range): f is surjective. bld_surjective_nonexpanding_compact_isometry makes f an isometry and bld4_isometry_compact_uniform_recurrence gives the uniform return time. -/
theorem bld5_nonexpanding_denseRange_compact_recurrence {X : Type*} [MetricSpace X] [CompactSpace X] (f : X → X) (hd : DenseRange f) (hf : ∀ x y : X, dist (f x) (f y) ≤ dist x y) (ε : ℝ) (hε : 0 < ε) : Isometry f ∧ ∃ n : ℕ, 0 < n ∧ ∀ x : X, dist (f^[n] x) x < ε := by
  have hc : Continuous f := (LipschitzWith.mk_one hf).continuous
  have hs : Function.Surjective f := by
    rw [← Set.range_eq_univ, ← hd.closure_range]
    exact ((isCompact_range hc).isClosed.closure_eq).symm
  have hi := bld_surjective_nonexpanding_compact_isometry f hs hf
  exact ⟨hi, bld4_isometry_compact_uniform_recurrence f hi ε hε⟩
end

-- forge:entry poly_derivative_dvd_self_char_zero kind=proved origin=conjecture
section
/- In char 0, a non-constant f with f' ∣ f is c·(X-a)^n — f = f'·q with q linear, q = (X-a)/n by comparing leading coefficients; then n·f = (X-a)f', and induction on n (or comparing root multiplicities at a: f = (X-a)^m g with g(a) ≠ 0 forces m = n) gives the claim. -/
open Polynomial in
theorem poly_derivative_dvd_self_char_zero {k : Type*} [Field k] [CharZero k] (f : Polynomial k) (hf : 0 < f.natDegree) (h : Polynomial.derivative f ∣ f) : ∃ c a : k, f = Polynomial.C c * (Polynomial.X - Polynomial.C a) ^ f.natDegree := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  obtain ⟨m, hm⟩ : ∃ m, f.natDegree = m + 1 := ⟨f.natDegree - 1, by omega⟩
  have hlc : f.coeff (m + 1) ≠ 0 := by
    rw [← hm, coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hf0
  have hm1 : ((m : k) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
  have hdc : (derivative f).coeff m = f.coeff (m + 1) * ((m : k) + 1) := coeff_derivative f m
  have hdc0 : (derivative f).coeff m ≠ 0 := by rw [hdc]; exact mul_ne_zero hlc hm1
  have hdd : (derivative f).natDegree = m :=
    le_antisymm (by have := natDegree_derivative_le f; omega) (le_natDegree_of_ne_zero hdc0)
  have hd0 : derivative f ≠ 0 := by intro h0; rw [h0] at hdc0; simp at hdc0
  obtain ⟨q, hq⟩ := h
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    exact hf0 hq
  have hqd : q.natDegree = 1 := by
    have := natDegree_mul hd0 hq0
    rw [← hq, hm, hdd] at this; omega
  have hq1 := eq_X_add_C_of_natDegree_le_one (p := q) hqd.le
  have hs : q.coeff 1 ≠ 0 := by
    have := leadingCoeff_ne_zero.mpr hq0
    rwa [leadingCoeff, hqd] at this
  have hL : f.leadingCoeff = (derivative f).leadingCoeff * q.leadingCoeff := by
    rw [← leadingCoeff_mul, ← hq]
  simp only [leadingCoeff, hm, hdd, hqd] at hL
  rw [hdc] at hL
  generalize q.coeff 1 = s at *
  generalize q.coeff 0 = t at *
  have hns : ((m : k) + 1) * s = 1 := by
    apply mul_left_cancel₀ hlc
    linear_combination -hL
  obtain ⟨a, ha⟩ : ∃ a, s * a = -t := ⟨-t / s, by field_simp⟩
  have hqa : q = C s * (X - C a) := by
    rw [hq1, mul_sub, ← C_mul, ha, C_neg, sub_neg_eq_add]
  have hroot : f.IsRoot a := by
    have : eval a f = eval a (derivative f * q) := congrArg (eval a) hq
    rw [IsRoot, this, eval_mul, hqa]; simp
  have hμ : 0 < rootMultiplicity a f := (rootMultiplicity_pos hf0).mpr hroot
  obtain ⟨g, hg, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf0 a
  obtain ⟨μ, hμ'⟩ : ∃ μ, rootMultiplicity a f = μ + 1 := ⟨rootMultiplicity a f - 1, by omega⟩
  rw [hμ'] at hg
  have hga : eval a g ≠ 0 := fun h0 => hnd (dvd_iff_isRoot.mpr h0)
  have hg0 : g ≠ 0 := by rintro rfl; simp at hga
  have hder : derivative f = (X - C a) ^ μ * (C ((μ : k) + 1) * g + (X - C a) * derivative g) := by
    have : derivative f = derivative ((X - C a) ^ (μ + 1) * g) := congrArg derivative hg
    rw [this, derivative_mul, derivative_X_sub_C_pow]
    simp only [add_tsub_cancel_right, Nat.cast_add, Nat.cast_one]
    ring
  have hkey : (X - C a) ^ (μ + 1) * g = (X - C a) ^ (μ + 1) * (C s * (C ((μ : k) + 1) * g + (X - C a) * derivative g)) := by
    calc (X - C a) ^ (μ + 1) * g = f := hg.symm
      _ = derivative f * q := hq
      _ = _ := by rw [hder, hqa]; ring
  have hk2 := mul_left_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero a)) hkey
  have hev := congrArg (eval a) hk2
  simp only [eval_mul, eval_add, eval_C, eval_sub, eval_X, sub_self, zero_mul, add_zero] at hev
  have hμs : s * ((μ : k) + 1) = 1 := by
    apply mul_right_cancel₀ hga
    linear_combination -hev
  have hmm : (μ : k) = m := by
    have h2 : s * ((μ : k) + 1) = s * ((m : k) + 1) := by rw [hμs, mul_comm, hns]
    exact add_right_cancel (mul_left_cancel₀ hs h2)
  have hmμ : μ = m := by exact_mod_cast hmm
  subst hmμ
  have hgd : g.natDegree = 0 := by
    have := natDegree_mul (pow_ne_zero (μ + 1) (X_sub_C_ne_zero a)) hg0
    rw [← hg, hm, natDegree_pow, natDegree_X_sub_C] at this
    omega
  refine ⟨g.coeff 0, a, ?_⟩
  rw [hm, ← eq_C_of_natDegree_eq_zero hgd, mul_comm]
  exact hg
end

-- forge:entry bld5_prime_dvd_fib_succ_of_not_isSquare_five kind=proved origin=conjecture
section
/- Uses Mathlib2.bld4_prime_dvd_fib_pred_mul_fib_mul_fib_succ, Mathlib2.bld4_pisano_prime_dvd_two_mul_succ_of_not_isSquare_five and Mathlib2.lib_pisano_dvd_iff_period: p is odd (5 = 1 is a square in ZMod 2). The second bld4 theorem with lib_pisano_dvd_iff_period (i = 0) gives p ∣ F_{2(p+1)}. By the first, p divides F_{p-1}, F_p or F_{p+1}. If p ∣ F_p then Nat.fib_gcd gives p ∣ F_{gcd(p, 2p+2)} = F_1 = 1; if p ∣ F_{p-1} then p ∣ F_{gcd(p-1, 2p+2)} with gcd(p-1, 2p+2) ∣ 4, so p ∣ F_4 = 3, p = 3, but then F_{p-1} = F_2 = 1. Both impossible, so p ∣ F_{p+1}. -/
theorem bld5_prime_dvd_fib_succ_of_not_isSquare_five (p : ℕ) [Fact p.Prime] (h : ¬ IsSquare (5 : ZMod p)) : p ∣ Nat.fib (p + 1) := by
  have hp : p.Prime := Fact.out
  have h2 : p ≠ 2 := by
    intro h2
    have : ∀ q : ℕ, q = 2 → IsSquare (5 : ZMod q) := by
      rintro q rfl
      exact ⟨1, by decide⟩
    exact h (this p h2)
  have hper := (lib_pisano_dvd_iff_period p (2*(p+1)) (by omega)).mp (bld4_pisano_prime_dvd_two_mul_succ_of_not_isSquare_five p h)
  have h0 : p ∣ Nat.fib (2*(p+1)) := by
    have := hper 0
    rw [zero_add, Nat.fib_zero] at this
    exact (Nat.modEq_zero_iff_dvd).mp this
  have hd := bld4_prime_dvd_fib_pred_mul_fib_mul_fib_succ p hp
  rcases (hp.dvd_mul).mp hd with hd | hd
  · rcases (hp.dvd_mul).mp hd with hd | hd
    · exfalso
      have hg : p ∣ Nat.fib (Nat.gcd (p-1) (2*(p+1))) := by rw [Nat.fib_gcd]; exact Nat.dvd_gcd hd h0
      have h4 : Nat.gcd (p-1) (2*(p+1)) ∣ 4 := by
        have a : Nat.gcd (p-1) (2*(p+1)) ∣ 2*(p+1) := Nat.gcd_dvd_right _ _
        have b : Nat.gcd (p-1) (2*(p+1)) ∣ 2*(p-1) := Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) 2
        have := Nat.dvd_sub' a b
        have e : 2*(p+1) - 2*(p-1) = 4 := by have := hp.two_le; omega
        rwa [e] at this
      have h3 : p ∣ 3 := by
        have := hg.trans (Nat.fib_dvd _ _ h4)
        have e : Nat.fib 4 = 3 := by norm_num
        rwa [e] at this
      have : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
      subst this
      norm_num at hd
    · exfalso
      have hg : p ∣ Nat.fib (Nat.gcd p (2*(p+1))) := by rw [Nat.fib_gcd]; exact Nat.dvd_gcd hd h0
      have hc : Nat.Coprime p (2*(p+1)) := Nat.Coprime.mul_right ((Nat.coprime_primes hp Nat.prime_two).mpr h2) (by simp)
      rw [hc.gcd_eq_one] at hg
      simp at hg; exact hp.one_lt.ne' hg
  · exact hd
end

-- forge:entry bld5_prime_dvd_pred_of_card_prime_mul_prime kind=proved origin=conjecture
section
/- Uses Mathlib2.bld3_card_sylow_of_card_prime_mul_prime: a non-abelian group of order pq (p < q) has exactly q Sylow p-subgroups by the bld3 theorem; Sylow's third theorem (card_sylow_modEq_one) gives q ≡ 1 mod p, i.e. p ∣ q − 1 ((Nat.modEq_iff_dvd' hq.one_le).mp after symmetry). -/
theorem bld5_prime_dvd_pred_of_card_prime_mul_prime (p q : ℕ) [Fact p.Prime] (hq : q.Prime) (hpq : p < q) (G : Type*) [Group G] (hG : Nat.card G = p * q) (hna : ∃ a b : G, a * b ≠ b * a) : p ∣ q - 1 := by
  have hp : p.Prime := Fact.out
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact mul_ne_zero hp.ne_zero hq.ne_zero)
  have h1 := bld3_card_sylow_of_card_prime_mul_prime p q hq hpq G hG hna
  have h2 := card_sylow_modEq_one p G
  rw [h1] at h2
  exact (Nat.modEq_iff_dvd' hq.one_le).mp h2.symm
end

-- forge:entry bld5_pell_five_four_prime_y kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_pell_five_solutions_lucas: it gives n with y = F_{2n}, x = L_{2n}. By Nat.fib_two_mul, y = F_n·L_n (p3_lucas n unfolds to 2F_{n+1} − F_n). For n ≥ 3 both factors exceed 1 (F_n ≥ 2, L_n ≥ 4), contradicting primality; n ≤ 1 gives y ≤ 1; so n = 2, y = F_4 = 3 and x = L_4 = 7. -/
theorem bld5_pell_five_four_prime_y (x y : ℕ) (h : x ^ 2 = 5 * y ^ 2 + 4) (hy : y.Prime) : y = 3 ∧ x = 7 := by
  obtain ⟨n, hn, hx⟩ := bld2_pell_five_solutions_lucas x y h
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · interval_cases n
    · exfalso; rw [hn] at hy; norm_num at hy
    · exfalso; rw [hn] at hy; norm_num at hy
    · norm_num [p3_lucas] at hn hx; exact ⟨hn, hx⟩
  · exfalso
    rw [Nat.fib_two_mul] at hn
    have a : 2 ≤ Nat.fib n := by
      have := Nat.fib_mono hge
      have e : Nat.fib 3 = 2 := by norm_num
      omega
    have b : Nat.fib n ≤ Nat.fib (n+1) := Nat.fib_le_fib_succ
    rw [hn] at hy
    exact Nat.not_prime_mul (by omega) (by omega) hy
end

-- forge:entry bld5_fitting_isCompl_pow_card kind=proved origin=conjecture
section
/- Uses Mathlib2.bld4_fitting_range_inter_ker_pow_card: that theorem says exactly that range(A^n) ⊓ ker(A^n) = ⊥ (a vector A^n v killed by A^n is 0), giving Disjoint. For Codisjoint, rank–nullity (LinearMap.finrank_range_add_finrank_ker) gives finrank range + finrank ker = card ι, so by Submodule.finrank_sup_add_finrank_inf_eq the sup has full finrank and equals ⊤ (Submodule.eq_top_of_finrank_eq). Mathlib only has the 'eventually' version (LinearMap.eventually_isCompl_ker_pow_range_pow); this pins the exponent to card ι. -/
theorem bld5_fitting_isCompl_pow_card (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) : IsCompl (LinearMap.range (A ^ Fintype.card ι).mulVecLin) (LinearMap.ker (A ^ Fintype.card ι).mulVecLin) := by
  have hd : Disjoint (LinearMap.range (A ^ Fintype.card ι).mulVecLin) (LinearMap.ker (A ^ Fintype.card ι).mulVecLin) := by
    rw [Submodule.disjoint_def]
    rintro x ⟨v, rfl⟩ hx
    rw [LinearMap.mem_ker] at hx
    exact bld4_fitting_range_inter_ker_pow_card K ι A v (by simpa using hx)
  refine ⟨hd, ?_⟩
  rw [codisjoint_iff]
  apply Submodule.eq_top_of_finrank_eq
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (A ^ Fintype.card ι).mulVecLin) (LinearMap.ker (A ^ Fintype.card ι).mulVecLin)
  rw [hd.eq_bot, finrank_bot, add_zero] at h1
  rw [h1, LinearMap.finrank_range_add_finrank_ker]
end

-- forge:entry bld5_prime_three_mod_four_dvd_lucas kind=proved origin=conjecture
section
/- Uses Mathlib2.bld3_pisano_pos_and_period and Mathlib2.nt2_fib_odd_index_no_prime_factor_three_mod_four: bld3_pisano_pos_and_period at i = 0 gives some k > 0 with p ∣ F_k; take the least such a (Nat.find). The nt2 theorem (no prime ≡ 3 mod 4 divides an odd-indexed Fibonacci number) forces a even, a = 2n with 0 < n < a. Nat.fib_two_mul gives F_{2n} = F_n·L_n (the factor 2F_{n+1} − F_n is p3_lucas n by definition); p ∤ F_n by minimality, so p ∣ L_n. -/
theorem bld5_prime_three_mod_four_dvd_lucas (p : ℕ) (hp : p.Prime) (h : p % 4 = 3) : ∃ n : ℕ, p ∣ p3_lucas n := by
  classical
  obtain ⟨hpos, hper⟩ := bld3_pisano_pos_and_period p hp.pos
  have hex : ∃ k, 0 < k ∧ p ∣ Nat.fib k := ⟨p3_pisano p, hpos, by
    have := hper 0; rw [zero_add, Nat.fib_zero] at this; exact (Nat.modEq_zero_iff_dvd).mp this⟩
  obtain ⟨a, ⟨ha0, had⟩, hmin⟩ : ∃ a, (0 < a ∧ p ∣ Nat.fib a) ∧ ∀ m < a, ¬ (0 < m ∧ p ∣ Nat.fib m) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  rcases Nat.even_or_odd' a with ⟨n, hn | hn⟩
  · refine ⟨n, ?_⟩
    rw [hn, Nat.fib_two_mul] at had
    rcases (hp.dvd_mul).mp had with h1 | h1
    · exact absurd ⟨by omega, h1⟩ (hmin n (by omega))
    · unfold p3_lucas; exact h1
  · rw [hn] at had; exact absurd had (nt2_fib_odd_index_no_prime_factor_three_mod_four n p hp h)
end

end Mathlib2
