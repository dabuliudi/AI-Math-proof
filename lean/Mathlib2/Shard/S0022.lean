/- Mathlib2 分片 22（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0001
import Mathlib2.Shard.S0011
import Mathlib2.Shard.S0016
import Mathlib2.Shard.S0017
import Mathlib2.Shard.S0018
import Mathlib2.Shard.S0019
import Mathlib2.Shard.S0021
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry bld3_card_centralizer_of_card_prime_cube kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_center_card_of_card_prime_cube: the centralizer strictly contains the centre (order p, and it contains g) and is a proper subgroup (g not central), so by Lagrange its order is p^2. -/
theorem bld3_card_centralizer_of_card_prime_cube (p : ℕ) (hp : p.Prime) (G : Type*) [Group G] (hG : Nat.card G = p ^ 3) (hna : ∃ a b : G, a * b ≠ b * a) (g : G) (hg : g ∉ Subgroup.center G) : Nat.card (Subgroup.centralizer ({g} : Set G)) = p ^ 2 := by
  classical
  have h := Mathlib2.bld2_card_conjClasses_of_card_prime_cube_aux1 p hp G hG hna g
  rw [if_neg hg] at h
  rw [← h]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro b
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.eq.symm⟩
end

-- forge:entry bld3_edelstein_iInter_range_iterate kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_edelstein_iterates_tendsto and Mathlib2.bld2_edelstein_no_periodic_points: p is in every range since f^[n] p = p; conversely if y = f^[n] (x_n) for all n, uniform convergence of the iterates to p (Dini applied to the monotone pointwise convergence from the library) gives dist y p < ε for every ε. -/
theorem bld3_edelstein_iInter_range_iterate {X : Type*} [MetricSpace X] [CompactSpace X] (f : X → X) (hf : ∀ x y : X, x ≠ y → dist (f x) (f y) < dist x y) (p : X) (hp : f p = p) : ⋂ n : ℕ, Set.range (f^[n]) = {p} := by
  ext y
  simp only [Set.mem_iInter, Set.mem_range, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hne
    have hpos : 0 < dist y p := dist_pos.2 hne
    obtain ⟨N, hN⟩ := Mathlib2.bld3_edelstein_iterates_tendsto_uniformly f hf p hp (dist y p) hpos
    obtain ⟨x, hx⟩ := h N
    have := hN N le_rfl x
    rw [hx] at this
    exact lt_irrefl _ this
  · rintro rfl n
    exact ⟨y, Function.iterate_fixed hp n⟩
end

-- forge:entry bld3_card_abelianization_of_card_prime_cube kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_commutator_eq_center_of_card_prime_cube and Mathlib2.bld_center_card_of_card_prime_cube: Abelianization G = G ⧸ commutator G, the commutator subgroup equals the centre, which has order p; Lagrange gives index p^2. -/
theorem bld3_card_abelianization_of_card_prime_cube (p : ℕ) (hp : p.Prime) (G : Type*) [Group G] (hG : Nat.card G = p ^ 3) (hna : ∃ a b : G, a * b ≠ b * a) : Nat.card (Abelianization G) = p ^ 2 := by
  have hc := Mathlib2.bld2_commutator_eq_center_of_card_prime_cube p hp G hG hna
  have hZ := Mathlib2.bld_center_card_of_card_prime_cube p hp G hG hna
  have hidx : Nat.card (Abelianization G) = (commutator G).index := rfl
  have h := Subgroup.index_mul_card (commutator G)
  rw [hc] at hidx h
  rw [hZ, hG] at h
  rw [hidx]
  have : (Subgroup.center G).index * p = p ^ 2 * p := by rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_right hp.pos this
end

-- forge:entry bld3_hardy_means_tendsto_zero kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_hardy_inequality_tsum: by Hardy the squares of the Cesàro means are summable, so they tend to 0, hence so do the means (continuity of sqrt / abs). -/
theorem bld3_hardy_means_tendsto_zero (a : ℕ → ℝ) (ha : Summable (fun k : ℕ => a k ^ 2)) : Filter.Tendsto (fun k : ℕ => (∑ i ∈ Finset.range (k + 1), a i) / ((k : ℝ) + 1)) Filter.atTop (nhds 0) := by
  have h := (Mathlib2.bld2_hardy_inequality_tsum a ha).1.tendsto_atTop_zero
  have h2 := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at h2
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine h2.congr fun k => ?_
  simp only [Function.comp_apply]
  exact Real.sqrt_sq_eq_abs _
end

-- forge:entry p5_dedekind_psi kind=definition origin=definition
section
/- Dedekind psi function: psi(n) = prod over primes p | n of p^(a_p - 1) (p+1), where a_p is the exponent of p in n; psi(1) = 1 (and psi(0) = 1 by the empty-product convention). -/
def p5_dedekind_psi (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p + 1)
end

-- forge:entry p5_psi_prime_pow kind=proved origin=paper
section
/- Spec for the Dedekind psi definition: psi(p^(k+1)) = p^k (p+1). -/
theorem p5_psi_prime_pow (p k : ℕ) (hp : p.Prime) : p5_dedekind_psi (p ^ (k + 1)) = p ^ k * (p + 1) := by
  unfold p5_dedekind_psi
  rw [Nat.primeFactors_prime_pow (Nat.succ_ne_zero k) hp, Finset.prod_singleton, hp.factorization_pow]
  simp
end

-- forge:entry p5_sigma_ge_succ kind=proved origin=paper
section
/- Equation (8): sigma(n) >= n+1 for n >= 2. -/
theorem p5_sigma_ge_succ (n : ℕ) (hn : 2 ≤ n) : n + 1 ≤ ArithmeticFunction.sigma 1 n := by
  rw [ArithmeticFunction.sigma_one_apply]
  have hsub : ({n, 1} : Finset ℕ) ⊆ n.divisors := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl <;> simp [Nat.mem_divisors] <;> omega
  calc n + 1 = ∑ d ∈ ({n, 1} : Finset ℕ), d := by
        rw [Finset.sum_pair (by omega)]
    _ ≤ ∑ d ∈ n.divisors, d := Finset.sum_le_sum_of_subset hsub
end

-- forge:entry p5_sigma_prime_mul_of_dvd kind=proved origin=paper
section
/- Equation (7), sigma part: if p | n then sigma(np) > p sigma(n). -/
theorem p5_sigma_prime_mul_of_dvd (p n : ℕ) (hp : p.Prime) (h : p ∣ n) (hn : n ≠ 0) : p * ArithmeticFunction.sigma 1 n < ArithmeticFunction.sigma 1 (p * n) := by
  rw [ArithmeticFunction.sigma_one_apply, ArithmeticFunction.sigma_one_apply]
  have hp2 := hp.two_le
  have hsub : insert 1 (n.divisors.image (fun d => p * d)) ⊆ (p * n).divisors := by
    intro d hd
    rw [Finset.mem_insert, Finset.mem_image] at hd
    rw [Nat.mem_divisors]
    refine ⟨?_, mul_ne_zero hp.ne_zero hn⟩
    rcases hd with rfl | ⟨e, he, rfl⟩
    · exact one_dvd _
    · exact Nat.mul_dvd_mul_left p (Nat.dvd_of_mem_divisors he)
  have hnot : (1 : ℕ) ∉ n.divisors.image (fun d => p * d) := by
    intro h1
    rw [Finset.mem_image] at h1
    obtain ⟨e, _, he⟩ := h1
    have : p ∣ 1 := ⟨e, he.symm⟩
    have := Nat.le_of_dvd one_pos this
    omega
  have hinj : Set.InjOn (fun d => p * d) (n.divisors : Set ℕ) := by
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hp.pos hab
  calc p * ∑ d ∈ n.divisors, d < 1 + ∑ d ∈ n.divisors, p * d := by
        rw [Finset.mul_sum]; omega
    _ = ∑ d ∈ insert 1 (n.divisors.image (fun d => p * d)), d := by
        rw [Finset.sum_insert hnot, Finset.sum_image hinj]
    _ ≤ ∑ d ∈ (p * n).divisors, d := Finset.sum_le_sum_of_subset hsub
end

-- forge:entry lib_convexOn_univ_eq_of_bddAbove kind=proved origin=conjecture
section
/- A convex function on a real vector space that is bounded above is constant (Liouville-type property of convex functions). Promoted and generalised from Mathlib2.ana_convex_bddAbove_const_aux1 (the case E = ℝ). -/
theorem lib_convexOn_univ_eq_of_bddAbove {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f) (M : ℝ) (hM : ∀ x, f x ≤ M) (x y : E) : f x = f y := by
  have hg : ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • (y - x))) := by
    refine ⟨convex_univ, ?_⟩
    intro s _ t _ a b ha hb hab
    have := hf.2 (Set.mem_univ (x + s • (y - x))) (Set.mem_univ (x + t • (y - x))) ha hb hab
    have e : x + (a • s + b • t) • (y - x) = a • (x + s • (y - x)) + b • (x + t • (y - x)) := by
      have hb' : b = 1 - a := by linarith
      subst hb'
      simp only [smul_eq_mul, add_smul, smul_add, sub_smul, one_smul, mul_smul]
      abel
    show f (x + (a • s + b • t) • (y - x)) ≤ _
    rw [e]
    exact this
  have := Mathlib2.ana_convex_bddAbove_const _ hg M (fun t => hM _) 0 1
  simpa using this
end

-- forge:entry lib_convex_nat_seq_add_mul_sub_le kind=proved origin=conjecture
section
/- For a convex ℕ-valued sequence, a drop d = f m - f (m+1) ≥ 0 at step m propagates backwards, so f 0 ≥ f (m+1) + (m+1)·d (quantitative form; d ≥ 1 gives f (m+1) + (m+1) ≤ f 0). Promoted and generalised from Mathlib2.bld3_rank_pow_card_stabilizes_aux2 (and _aux1; used for rank stabilisation of matrix powers). -/
theorem lib_convex_nat_seq_add_mul_sub_le (f : ℕ → ℕ) (h : ∀ k, 2 * f (k + 1) ≤ f k + f (k + 2)) (m : ℕ) (hm : f (m + 1) ≤ f m) : f (m + 1) + (m + 1) * (f m - f (m + 1)) ≤ f 0 := by
  have hmono : Monotone (fun k => (f (k + 1) : ℤ) - (f k : ℤ)) := by
    apply monotone_nat_of_le_succ
    intro k
    show (f (k + 1) : ℤ) - f k ≤ (f (k + 1 + 1) : ℤ) - f (k + 1)
    have := h k
    have h2 : k + 1 + 1 = k + 2 := rfl
    rw [h2]
    omega
  have key : ∀ n : ℕ, n ≤ m + 1 → (f n : ℤ) + (n : ℤ) * ((f m : ℤ) - (f (m + 1) : ℤ)) ≤ (f 0 : ℤ) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      have h2 : (f (n + 1) : ℤ) - (f n : ℤ) ≤ (f (m + 1) : ℤ) - (f m : ℤ) := hmono (by omega : n ≤ m)
      have h3 : ((n + 1 : ℕ) : ℤ) * ((f m : ℤ) - (f (m + 1) : ℤ)) = (n : ℤ) * ((f m : ℤ) - (f (m + 1) : ℤ)) + ((f m : ℤ) - (f (m + 1) : ℤ)) := by
        push_cast; ring
      rw [h3]
      linarith
  have hk := key (m + 1) le_rfl
  have hc : ((f m - f (m + 1) : ℕ) : ℤ) = (f m : ℤ) - (f (m + 1) : ℤ) := Nat.cast_sub hm
  have : ((f (m + 1) + (m + 1) * (f m - f (m + 1)) : ℕ) : ℤ) ≤ ((f 0 : ℕ) : ℤ) := by
    push_cast [hc]
    push_cast at hk
    linarith
  exact_mod_cast this
end

-- forge:entry p5_psi_mul_coprime kind=proved origin=paper
section
/- Spec: Dedekind psi is multiplicative on coprime arguments. -/
theorem p5_psi_mul_coprime (m n : ℕ) (h : m.Coprime n) : p5_dedekind_psi (m * n) = p5_dedekind_psi m * p5_dedekind_psi n := by
  unfold p5_dedekind_psi
  rw [h.primeFactors_mul, Finset.prod_union h.disjoint_primeFactors]
  congr 1
  · refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.factorization_eq_of_coprime_left h (List.mem_toFinset.mp hp)]
  · refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.factorization_eq_of_coprime_right h (List.mem_toFinset.mp hp)]
end

-- forge:entry lib_fib_cassini_cast kind=proved origin=conjecture
section
/- Cassini's identity F_(n+2) F_n - F_(n+1)^2 = (-1)^(n+1) in an arbitrary commutative ring (e.g. ZMod p). Promoted and generalised from Mathlib2.p3_aux_period_aux1 (same identity over ℤ as Mathlib2.an_cassini_int, r3_fib_iff_five_sq_pm_four_is_square_s1h1, p3_cor1_aux1). -/
theorem lib_fib_cassini_cast (R : Type*) [CommRing R] (n : ℕ) : (Nat.fib (n + 2) : R) * (Nat.fib n : R) - (Nat.fib (n + 1) : R) ^ 2 = (-1) ^ (n + 1) := by
  have h := congrArg (Int.cast : ℤ → R) (Mathlib2.an_cassini_int n)
  push_cast at h
  exact h
end

-- forge:entry p5_psi_prime_mul_of_dvd kind=proved origin=paper
section
/- Equation (7), psi part: if p | n then psi(np) = p psi(n). -/
theorem p5_psi_prime_mul_of_dvd (p n : ℕ) (hp : p.Prime) (h : p ∣ n) (hn : n ≠ 0) : p5_dedekind_psi (p * n) = p * p5_dedekind_psi n := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have he : e ≠ 0 := by
    rintro rfl
    simp at h
    exact hm h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
  have hc : ∀ j, (p ^ j).Coprime m := fun j =>
    Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  have e1 : p * (p ^ (k + 1) * m) = p ^ (k + 1 + 1) * m := by ring
  rw [e1, Mathlib2.p5_psi_mul_coprime _ _ (hc _), Mathlib2.p5_psi_mul_coprime _ _ (hc _),
    Mathlib2.p5_psi_prime_pow p (k + 1) hp, Mathlib2.p5_psi_prime_pow p k hp]
  ring
end

-- forge:entry lib_fib_dvd_fib_iff kind=proved origin=conjecture
section
/- Fibonacci divisibility criterion: for m ≠ 2, F_m ∣ F_n iff m ∣ n (converse of Nat.fib_dvd, via Nat.fib_gcd). Promoted and generalised from Mathlib2.bld2_pisano_fib_odd_eq_aux2 (also used in bld2_pisano_fib_odd_eq / bld2_pisano_fib_even_eq). -/
theorem lib_fib_dvd_fib_iff (m n : ℕ) (hm : m ≠ 2) : Nat.fib m ∣ Nat.fib n ↔ m ∣ n := by
  refine ⟨fun h => ?_, Nat.fib_dvd m n⟩
  rcases Nat.lt_or_ge m 3 with h3 | h3
  · interval_cases m
    · have h0 : Nat.fib n = 0 := by simpa using h
      have : n = 0 := by simpa [Nat.fib_eq_zero] using h0
      simp [this]
    · exact one_dvd n
    · exact absurd rfl hm
  · have hg : Nat.fib (Nat.gcd m n) = Nat.fib m := by
      rw [Nat.fib_gcd]; exact Nat.gcd_eq_left h
    have hdvd : Nat.gcd m n ∣ m := Nat.gcd_dvd_left m n
    have hle : Nat.gcd m n ≤ m := Nat.le_of_dvd (by omega) hdvd
    rcases Nat.eq_or_lt_of_le hle with he | hlt
    · rw [← he]; exact Nat.gcd_dvd_right m n
    · exfalso
      have h1 : Nat.fib (Nat.gcd m n) ≤ Nat.fib (m - 1) := Nat.fib_mono (by omega)
      have h2 : Nat.fib (m - 1) < Nat.fib (m - 1 + 1) := Nat.fib_lt_fib_succ (by omega)
      have h4 : m - 1 + 1 = m := by omega
      rw [h4] at h2
      omega
end

-- forge:entry lib_isIdempotentElem_of_mul_self_eq_one kind=proved origin=conjecture
section
/- Spectral projections of an involution: if a^2 = 1 and 2 is invertible then (1 + a)/2 and (1 - a)/2 are idempotent, in any ring. Promoted and generalised from Mathlib2.bld_involution_trace_rank_aux2 (the case of matrices over a char-0 field; used in bld_involution_rank_add_rank, bld2_involution_iff_rank_add_rank, bld3_rank_involution_defect). -/
theorem lib_isIdempotentElem_of_mul_self_eq_one (R : Type*) [Ring R] [Invertible (2 : R)] (a : R) (h : a * a = 1) : IsIdempotentElem (⅟(2 : R) * (1 + a)) ∧ IsIdempotentElem (⅟(2 : R) * (1 - a)) := by
  have hc : ∀ x : R, x * ⅟(2 : R) = ⅟(2 : R) * x := fun x =>
    ((Commute.ofNat_right x 2).invOf_right).eq
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self _
  have hp : (1 + a) * (1 + a) = 2 * (1 + a) := by
    have : (1 + a) * (1 + a) = 1 + a + a + a * a := by noncomm_ring
    rw [this, h]; noncomm_ring
  have hq : (1 - a) * (1 - a) = 2 * (1 - a) := by
    have : (1 - a) * (1 - a) = 1 - a - a + a * a := by noncomm_ring
    rw [this, h]; noncomm_ring
  constructor
  · show ⅟(2 : R) * (1 + a) * (⅟(2 : R) * (1 + a)) = ⅟(2 : R) * (1 + a)
    calc ⅟(2 : R) * (1 + a) * (⅟(2 : R) * (1 + a)) = ⅟(2 : R) * ((1 + a) * ⅟(2 : R)) * (1 + a) := by simp only [mul_assoc]
      _ = ⅟(2 : R) * (⅟(2 : R) * (1 + a)) * (1 + a) := by rw [hc]
      _ = ⅟(2 : R) * (⅟(2 : R) * ((1 + a) * (1 + a))) := by simp only [mul_assoc]
      _ = ⅟(2 : R) * ((⅟(2 : R) * 2) * (1 + a)) := by rw [hp]; simp only [mul_assoc]
      _ = ⅟(2 : R) * (1 + a) := by rw [h2, one_mul]
  · show ⅟(2 : R) * (1 - a) * (⅟(2 : R) * (1 - a)) = ⅟(2 : R) * (1 - a)
    calc ⅟(2 : R) * (1 - a) * (⅟(2 : R) * (1 - a)) = ⅟(2 : R) * ((1 - a) * ⅟(2 : R)) * (1 - a) := by simp only [mul_assoc]
      _ = ⅟(2 : R) * (⅟(2 : R) * (1 - a)) * (1 - a) := by rw [hc]
      _ = ⅟(2 : R) * (⅟(2 : R) * ((1 - a) * (1 - a))) := by simp only [mul_assoc]
      _ = ⅟(2 : R) * ((⅟(2 : R) * 2) * (1 - a)) := by rw [hq]; simp only [mul_assoc]
      _ = ⅟(2 : R) * (1 - a) := by rw [h2, one_mul]
end

-- forge:entry lib_matrix_det_add_of_isNilpotent_of_commute kind=proved origin=conjecture
section
/- A nilpotent perturbation commuting with an invertible matrix does not change the determinant: det (B + A) = det B, over any reduced commutative ring and any finite index type. Promoted and generalised from Mathlib2.bld_nilpotent_commute_det_add_aux1 (which is the case Fin n, ℝ; builds on gen_lin_nilpotent_det_one_add_reduced). -/
theorem lib_matrix_det_add_of_isNilpotent_of_commute (R : Type*) [CommRing R] [IsReduced R] (ι : Type*) [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι R) (hA : IsNilpotent A) (hAB : Commute A B) (hB : IsUnit B.det) : (B + A).det = B.det := by
  have hAB' : A * B = B * A := hAB.eq
  have hc : B⁻¹ * A = A * B⁻¹ := by
    calc B⁻¹ * A = B⁻¹ * A * (B * B⁻¹) := by rw [Matrix.mul_nonsing_inv B hB, mul_one]
      _ = B⁻¹ * (A * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (B⁻¹ * B) * A * B⁻¹ := by rw [hAB']; simp only [Matrix.mul_assoc]
      _ = A * B⁻¹ := by rw [Matrix.nonsing_inv_mul B hB, one_mul]
  have hn : IsNilpotent (B⁻¹ * A) := by
    obtain ⟨k, hk⟩ := hA
    refine ⟨k, ?_⟩
    have hcomm : Commute B⁻¹ A := hc
    rw [hcomm.mul_pow, hk, mul_zero]
  have hd := Mathlib2.gen_lin_nilpotent_det_one_add_reduced R ι (B⁻¹ * A) hn
  have e : B + A = B * (1 + B⁻¹ * A) := by
    rw [Matrix.mul_add, mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv B hB, one_mul]
  rw [e, Matrix.det_mul, hd, mul_one]
end

-- forge:entry lib_matrix_ker_mulVecLin_le_ker_mul kind=proved origin=conjecture
section
/- Null space of a product: ker N ≤ ker (M * N), over any commutative semiring (dual companion of range (M * N) ≤ range M). Promoted and generalised from Mathlib2.bld3_rank_tripotent_defect_aux1 (kernel companion; used inline in rank-defect proofs). -/
theorem lib_matrix_ker_mulVecLin_le_ker_mul (R : Type*) [CommSemiring R] (m n p : Type*) [Fintype n] [Fintype p] (M : Matrix m n R) (N : Matrix n p R) : LinearMap.ker N.mulVecLin ≤ LinearMap.ker (M * N).mulVecLin := by
  rw [Matrix.mulVecLin_mul]
  exact LinearMap.ker_le_ker_comp _ _
end

-- forge:entry p5_psi_ge_succ kind=proved origin=paper
section
/- Equation (8): psi(n) >= n+1 for n >= 2. -/
theorem p5_psi_ge_succ_aux1 (p n : ℕ) (hp : p.Prime) (h : ¬ p ∣ n) : p5_dedekind_psi (p * n) = (p + 1) * p5_dedekind_psi n := by
  rw [Mathlib2.p5_psi_mul_coprime _ _ ((Nat.Prime.coprime_iff_not_dvd hp).2 h)]
  have := Mathlib2.p5_psi_prime_pow p 0 hp
  simp only [zero_add, pow_one, pow_zero, one_mul] at this
  rw [this]

theorem p5_psi_ge_succ_aux2 : p5_dedekind_psi 1 = 1 := by
  simp [p5_dedekind_psi]

theorem p5_psi_ge_succ (n : ℕ) (hn : 2 ≤ n) : n + 1 ≤ p5_dedekind_psi n := by
  induction n using induction_on_primes with
  | zero => omega
  | one => omega
  | prime_mul p a hp ih =>
    have hp2 := hp.two_le
    rcases Nat.lt_or_ge a 2 with ha | ha
    · interval_cases a
      · omega
      · rw [p5_psi_ge_succ_aux1 p 1 hp (by intro h; have := Nat.le_of_dvd one_pos h; omega), p5_psi_ge_succ_aux2]
        omega
    · have ih' := ih ha
      by_cases hd : p ∣ a
      · rw [Mathlib2.p5_psi_prime_mul_of_dvd p a hp hd (by omega)]
        nlinarith
      · rw [p5_psi_ge_succ_aux1 p a hp hd]
        nlinarith
end

-- forge:entry lib_matrix_range_mulVecLin_mul_le kind=proved origin=conjecture
section
/- Column space of a product: range (M * N) ≤ range M, over any commutative semiring and rectangular index types. Promoted and generalised from Mathlib2.bld3_rank_tripotent_defect_aux1 (same step inline in bld3_rank_involution_defect, bld_frobenius_rank_inequality). -/
theorem lib_matrix_range_mulVecLin_mul_le (R : Type*) [CommSemiring R] (m n p : Type*) [Fintype n] [Fintype p] (M : Matrix m n R) (N : Matrix n p R) : LinearMap.range (M * N).mulVecLin ≤ LinearMap.range M.mulVecLin := by
  rw [Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _
end

-- forge:entry p5_lemma1 kind=proved origin=paper
section
/- Lemma 1 (Atanassov): phi(n)+psi(n) >= 2n for n >= 2. -/
theorem p5_lemma1_aux1 (n : ℕ) : 2 * n ≤ n.totient + p5_dedekind_psi n := by
  induction n using induction_on_primes with
  | zero => omega
  | one => simp [Mathlib2.p5_psi_ge_succ_aux2]
  | prime_mul p a hp ih =>
    have hp2 := hp.two_le
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    have hge : a ≤ p5_dedekind_psi a := by
      rcases Nat.lt_or_ge a 2 with h2 | h2
      · have : a = 1 := by omega
        subst this
        rw [Mathlib2.p5_psi_ge_succ_aux2]
      · have := Mathlib2.p5_psi_ge_succ a h2
        omega
    have hle : a.totient ≤ a := Nat.totient_le a
    by_cases hd : p ∣ a
    · rw [Mathlib2.p5_psi_prime_mul_of_dvd p a hp hd (by omega), Nat.totient_mul_of_prime_of_dvd hp hd]
      nlinarith
    · rw [Mathlib2.p5_psi_ge_succ_aux1 p a hp hd, Nat.totient_mul_of_prime_of_not_dvd hp hd]
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      nlinarith

theorem p5_lemma1 (n : ℕ) (hn : 2 ≤ n) : 2 * n ≤ n.totient + p5_dedekind_psi n :=
  p5_lemma1_aux1 n
end

end Mathlib2
