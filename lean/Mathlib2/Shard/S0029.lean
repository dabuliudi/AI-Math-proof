/- Mathlib2 分片 29（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0028
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry lib_polynomial_fermat_quotients_eq_C kind=proved origin=conjecture
section
/- promoted from Mathlib2.poly_ratfunc_fermat_curve_const_aux1 (DecidableEq dropped, both quotients): polynomial FLT without coprimality in quotient form — if A^n + B^n = E^n with n ≥ 3, E ≠ 0 in char 0 then A/E and B/E are constant rational functions. -/
theorem lib_polynomial_fermat_quotients_eq_C {k : Type*} [Field k] [CharZero k] (n : ℕ) (hn : 3 ≤ n) (A B E : Polynomial k) (hE : E ≠ 0) (heq : A ^ n + B ^ n = E ^ n) : ∃ c d : k, algebraMap (Polynomial k) (RatFunc k) A / algebraMap (Polynomial k) (RatFunc k) E = RatFunc.C c ∧ algebraMap (Polynomial k) (RatFunc k) B / algebraMap (Polynomial k) (RatFunc k) E = RatFunc.C d := by
  classical
  obtain ⟨c, hc⟩ := Mathlib2.poly_ratfunc_fermat_curve_const_aux1 n hn A B E hE heq
  obtain ⟨d, hd⟩ := Mathlib2.poly_ratfunc_fermat_curve_const_aux1 n hn B A E hE (by rw [add_comm]; exact heq)
  exact ⟨c, d, hc, hd⟩
end

-- forge:entry arith_dvd_sum_coprime kind=proved origin=conjecture
section
/- For n ≥ 3 the sum of the totatives of n is divisible by n — Uses Mathlib2.nt2_two_mul_sum_coprime_eq_mul_totient at step 1: 2·S = n·φ(n); φ(n) is even for n > 2 (Nat.totient_even), so S = n·(φ(n)/2). -/
theorem arith_dvd_sum_coprime (n : ℕ) (hn : 3 ≤ n) : n ∣ ∑ k ∈ Finset.range n with k.Coprime n, k := by
  have h := Mathlib2.nt2_two_mul_sum_coprime_eq_mul_totient n (by omega)
  obtain ⟨c, hc⟩ := Nat.totient_even (show 2 < n by omega)
  refine ⟨c, ?_⟩
  have : 2 * ∑ k ∈ Finset.range n with k.Coprime n, k = 2 * (n * c) := by
    rw [h, hc]; ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
end

-- forge:entry calc_tsum_inv_mul_two_pow kind=proved origin=conjecture
section
/- ∑_{n≥1} 1/(n 2ⁿ) = log 2 — Real.hasSum_pow_div_log_of_abs_lt_one at x = 1/2 gives −log(1/2). -/
theorem calc_tsum_inv_mul_two_pow : ∑' n : ℕ, 1 / (((n : ℝ) + 1) * 2 ^ (n + 1)) = Real.log 2 := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := (1/2 : ℝ)) (by rw [abs_of_pos] <;> norm_num)
  have e : -Real.log (1 - 1/2 : ℝ) = Real.log 2 := by
    rw [show (1 - 1/2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]; ring
  rw [e] at h
  rw [← h.tsum_eq]
  congr 1
  funext n
  rw [one_div_pow]
  field_simp
end

-- forge:entry lib_lucas_two_mul_ring_cast kind=proved origin=conjecture
section
/- promoted from Mathlib2.bld5_prime_dvd_lucas_four_mul_mod_eight_aux1 (generalised from commutative rings to any ring): Lucas doubling L_{2m} = L_m^2 - 2(-1)^m. -/
theorem lib_lucas_two_mul_ring_cast (R : Type*) [Ring R] (m : ℕ) : ((Mathlib2.p3_lucas (2 * m) : ℕ) : R) = ((Mathlib2.p3_lucas m : ℕ) : R) ^ 2 - 2 * (-1) ^ m := by
  have h := congrArg (Int.cast : ℤ → R) (Mathlib2.bld5_prime_dvd_lucas_four_mul_mod_eight_aux1 ℤ m)
  push_cast at h
  exact h
end

-- forge:entry arith_prod_divisors_sq kind=proved origin=conjecture
section
/- The product of the divisors of m² is m^τ(m²) — Uses Mathlib2.nt2_prod_divisors_sq at step 1 with n = m²: (∏ d)² = (m²)^τ = (m^τ)², then take square roots in ℕ. -/
theorem arith_prod_divisors_sq (m : ℕ) (hm : 0 < m) : ∏ d ∈ (m ^ 2).divisors, d = m ^ (m ^ 2).divisors.card := by
  have h := Mathlib2.nt2_prod_divisors_sq (m ^ 2)
  rw [← pow_mul, mul_comm, pow_mul] at h
  exact Nat.pow_left_injective (by norm_num) h
end

-- forge:entry calc_integral_arctan_zero_one kind=proved origin=conjecture
section
/- ∫₀¹ arctan x dx = π/4 − (log 2)/2 — antiderivative x arctan x − log(1+x²)/2; FTC, arctan 1 = π/4. -/
theorem calc_integral_arctan_zero_one : ∫ x in (0:ℝ)..1, Real.arctan x = Real.pi / 4 - Real.log 2 / 2 := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun x : ℝ => x * Real.arctan x - Real.log (1 + x ^ 2) / 2) (Real.arctan x) x := by
    intro x _
    have hx0 : (1 + x ^ 2) ≠ 0 := by positivity
    have h1 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * x) x := by
      simpa using ((hasDerivAt_id x).pow 2).const_add 1
    have h := ((hasDerivAt_id x).mul (Real.hasDerivAt_arctan x)).sub ((h1.log hx0).div_const 2)
    convert h using 1
    simp only [id]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (Real.continuous_arctan.intervalIntegrable _ _)]
  norm_num
end

-- forge:entry lib_fib_add_ring_cast kind=proved origin=conjecture
section
/- promoted from Mathlib2.bld5_pisano_mul_dvd_mul_aux1 (generalised from commutative rings to any ring; same identity as Mathlib2.bld5_pisano_five_pow_aux1 over ℤ): subtraction form of the Fibonacci addition law F_{a+b} = F_a F_{b+1} + F_{a+1} F_b - F_a F_b, with no index shift. -/
theorem lib_fib_add_ring_cast (R : Type*) [Ring R] (a b : ℕ) : ((Nat.fib (a + b) : ℕ) : R) = ((Nat.fib a : ℕ) : R) * ((Nat.fib (b + 1) : ℕ) : R) + ((Nat.fib (a + 1) : ℕ) : R) * ((Nat.fib b : ℕ) : R) - ((Nat.fib a : ℕ) : R) * ((Nat.fib b : ℕ) : R) := by
  have h := congrArg (Int.cast : ℤ → R) (Mathlib2.bld5_pisano_mul_dvd_mul_aux1 ℤ a b)
  push_cast at h
  exact h
end

-- forge:entry arith_totient_add_sigma_eq_two_mul_iff_prime kind=proved origin=conjecture
section
/- Equality case of the Sandor–Atanassov inequality φ(n)+σ(n) ≥ 2n (Mathlib2.p5_lemma2): equality iff n is prime — for composite n with least prime factor p, σ(n) ≥ n + n/p + 1 and φ(n) ≥ n - n/p (count of multiples of p is not all non-coprime... use φ(n) ≥ n - Σ_{q|n} n/q carefully, or induct with Mathlib2.p5_sigma_prime_mul_of_dvd), giving strict inequality. -/
theorem arith_totient_add_sigma_eq_two_mul_iff_prime (n : ℕ) (hn : 2 ≤ n) : n.totient + ArithmeticFunction.sigma 1 n = 2 * n ↔ n.Prime := by
  have h1 := Nat.sum_totient n
  rw [← Nat.cons_self_properDivisors (by omega : n ≠ 0), Finset.sum_cons] at h1
  have h2 : ArithmeticFunction.sigma 1 n = ∑ d ∈ n.properDivisors, d + n := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  have h3 : ∀ d ∈ n.properDivisors, d.totient ≤ d := fun d _ => Nat.totient_le d
  have h4 := Finset.sum_le_sum h3
  constructor
  · intro h
    have hsum : ∑ d ∈ n.properDivisors, d.totient = ∑ d ∈ n.properDivisors, d := by omega
    rw [Finset.sum_eq_sum_iff_of_le h3] at hsum
    rw [Nat.prime_def]
    refine ⟨hn, fun m hm => ?_⟩
    by_cases hmn : m = n
    · exact Or.inr hmn
    · left
      have hmem : m ∈ n.properDivisors := by
        rw [Nat.mem_properDivisors]
        exact ⟨hm, lt_of_le_of_ne (Nat.le_of_dvd (by omega) hm) hmn⟩
      have hm0 : m ≠ 0 := by
        rintro rfl
        simp at hm
        omega
      by_contra hm1
      have := Nat.totient_lt m (by omega)
      have := hsum m hmem
      omega
  · intro hp
    rw [hp.properDivisors] at h1 h2
    simp at h1 h2
    omega
end

-- forge:entry arith_abundant_mul kind=proved origin=conjecture
section
/- Every positive multiple of an abundant number is abundant — Uses Mathlib2.ab_abundant_def at the first and last step to pass to full divisor sums, and Mathlib2.ab_t2_mul_mem_divisors to inject d ↦ k·d from divisors of n into divisors of k·n, so σ(kn) ≥ kσ(n) > 2kn. -/
theorem arith_abundant_mul (n k : ℕ) (hn : n.Abundant) (hk : 0 < k) : (k * n).Abundant := by
  rw [Mathlib2.ab_abundant_def] at hn ⊢
  have hsub : n.divisors.image (fun d => k * d) ⊆ (k * n).divisors := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    exact Mathlib2.ab_t2_mul_mem_divisors n k d hk hd
  have h1 : ∑ d ∈ n.divisors.image (fun d => k * d), d ≤ ∑ d ∈ (k * n).divisors, d :=
    Finset.sum_le_sum_of_subset hsub
  rw [Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hk hab), ← Finset.mul_sum] at h1
  have h2 : k * (2 * n) < k * ∑ d ∈ n.divisors, d := Nat.mul_lt_mul_of_pos_left hn hk
  calc 2 * (k * n) = k * (2 * n) := by ring
    _ < _ := h2
    _ ≤ _ := h1
end

-- forge:entry calc_card_no_adjacent_subsets kind=proved origin=conjecture
section
/- Subsets of {0,…,n−1} with no two consecutive elements number F_{n+2} — two-step induction: split by whether the last element is in the set, giving a(n+2) = a(n+1) + a(n); bijections via Fin.castSucc / Finset.map. -/
theorem calc_card_no_adjacent_subsets_aux1 (n : ℕ) :
    ((Finset.range (n + 2)).powerset.filter (fun t : Finset ℕ => ∀ i ∈ t, i + 1 ∉ t)).card
      = ((Finset.range (n + 1)).powerset.filter (fun t : Finset ℕ => ∀ i ∈ t, i + 1 ∉ t)).card
        + ((Finset.range n).powerset.filter (fun t : Finset ℕ => ∀ i ∈ t, i + 1 ∉ t)).card := by
  have hr : Finset.range (n + 2) = insert (n + 1) (Finset.range (n + 1)) := Finset.range_succ
  rw [hr, Finset.powerset_insert, Finset.filter_union, Finset.card_union_of_disjoint]
  · congr 1
    have himg : ((Finset.range (n + 1)).powerset.image (insert (n + 1))).filter (fun t : Finset ℕ => ∀ i ∈ t, i + 1 ∉ t)
        = (((Finset.range n).powerset.filter (fun t : Finset ℕ => ∀ i ∈ t, i + 1 ∉ t))).image (insert (n + 1)) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_powerset]
      constructor
      · rintro ⟨⟨s, hs, rfl⟩, hP⟩
        have hn : n ∉ s := by
          intro hns
          exact hP n (Finset.mem_insert_of_mem hns) (Finset.mem_insert_self _ _)
        refine ⟨s, ⟨?_, ?_⟩, rfl⟩
        · intro x hx
          have h1 := Finset.mem_range.mp (hs hx)
          have h2 : x ≠ n := fun h => hn (h ▸ hx)
          exact Finset.mem_range.mpr (by omega)
        · intro i hi hi1
          exact hP i (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hi1)
      · rintro ⟨s, ⟨hs, hP⟩, rfl⟩
        refine ⟨⟨s, ?_, rfl⟩, ?_⟩
        · exact hs.trans (Finset.range_subset_range.mpr (Nat.le_succ n))
        · intro i hi hi1
          rcases Finset.mem_insert.mp hi with h | h
          · rcases Finset.mem_insert.mp hi1 with h' | h'
            · omega
            · have := Finset.mem_range.mp (hs h')
              omega
          · rcases Finset.mem_insert.mp hi1 with h' | h'
            · have := Finset.mem_range.mp (hs h)
              omega
            · exact hP i h h'
    rw [himg]
    apply Finset.card_image_of_injOn
    intro s hs s' hs' hss
    have h1 : n + 1 ∉ s := by
      intro h
      have := Finset.mem_range.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1) h)
      omega
    have h2 : n + 1 ∉ s' := by
      intro h
      have := Finset.mem_range.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hs').1) h)
      omega
    have h3 : insert (n + 1) s = insert (n + 1) s' := hss
    rw [← Finset.erase_insert h1, ← Finset.erase_insert h2, h3]
  · rw [Finset.disjoint_left]
    intro t ht ht'
    have h1 := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ht').1
    have := Finset.mem_range.mp (h1 (Finset.mem_insert_self _ _))
    omega

theorem calc_card_no_adjacent_subsets_aux2 (n : ℕ) :
    ((Finset.range n).powerset.filter (fun t : Finset ℕ => ∀ i ∈ t, i + 1 ∉ t)).card = Nat.fib (n + 2)
    ∧ ((Finset.range (n + 1)).powerset.filter (fun t : Finset ℕ => ∀ i ∈ t, i + 1 ∉ t)).card = Nat.fib (n + 3) := by
  induction n with
  | zero => constructor <;> decide
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [calc_card_no_adjacent_subsets_aux1 k, ih.1, ih.2]
    have h : Nat.fib (k + 1 + 3) = Nat.fib (k + 2) + Nat.fib (k + 3) := Nat.fib_add_two (n := k + 2)
    omega

theorem calc_card_no_adjacent_subsets (n : ℕ) : ((Finset.univ : Finset (Finset (Fin n))).filter (fun s => ∀ i : Fin n, ∀ j : Fin n, i ∈ s → j ∈ s → (i : ℕ) + 1 ≠ (j : ℕ))).card = Nat.fib (n + 2) := by
  rw [← (calc_card_no_adjacent_subsets_aux2 n).1]
  apply Finset.card_bij (fun s _ => s.map Fin.valEmbedding)
  · intro s hs
    have hP := (Finset.mem_filter.mp hs).2
    rw [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro x hx
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
      exact Finset.mem_range.mpr a.2
    · intro i hi hi1
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hi
      obtain ⟨b, hb, hab⟩ := Finset.mem_map.mp hi1
      exact hP a b ha hb hab.symm
  · intro s _ s' _ h
    exact Finset.map_injective _ h
  · intro t ht
    have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
    have hP := (Finset.mem_filter.mp ht).2
    refine ⟨Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ t), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro i j hi hj hij
      have hi' := (Finset.mem_filter.mp hi).2
      have hj' := (Finset.mem_filter.mp hj).2
      rw [← hij] at hj'
      exact hP _ hi' hj'
    · ext x
      rw [Finset.mem_map]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact (Finset.mem_filter.mp ha).2
      · intro hx
        exact ⟨⟨x, Finset.mem_range.mp (hsub hx)⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
end

-- forge:entry lib_fib_two_mul_ring_cast kind=proved origin=conjecture
section
/- promoted from Mathlib2.bld4_pisano_lucas_dvd_four_mul_aux1 (generalised from commutative rings to any ring): cast form of Nat.fib_two_mul without truncated subtraction, F_{2m} = F_m (2 F_{m+1} - F_m). -/
theorem lib_fib_two_mul_ring_cast (R : Type*) [Ring R] (m : ℕ) : ((Nat.fib (2 * m) : ℕ) : R) = ((Nat.fib m : ℕ) : R) * (2 * ((Nat.fib (m + 1) : ℕ) : R) - ((Nat.fib m : ℕ) : R)) := by
  have h := congrArg (Int.cast : ℤ → R) (Mathlib2.bld4_pisano_lucas_dvd_four_mul_aux1 ℤ m)
  push_cast at h
  exact h
end

-- forge:entry arith_sum_moebius_mul_card_divisors kind=proved origin=conjecture
section
/- Σ_{d|n} μ(d)τ(n/d) = 1 — Dirichlet convolution μ * (ζ * ζ) = ζ, then unfold the convolution over divisorsAntidiagonal. -/
theorem arith_sum_moebius_mul_card_divisors (n : ℕ) (hn : 0 < n) : ∑ d ∈ n.divisors, ArithmeticFunction.moebius d * ((n / d).divisors.card : ℤ) = 1 := by
  have key : (ArithmeticFunction.moebius * ((ArithmeticFunction.sigma 0 : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)) = (ArithmeticFunction.zeta : ArithmeticFunction ℤ) := by
    rw [← ArithmeticFunction.zeta_mul_pow_eq_sigma, ArithmeticFunction.pow_zero_eq_zeta, ArithmeticFunction.natCoe_mul, ← mul_assoc, ArithmeticFunction.moebius_mul_coe_zeta, one_mul]
  have h := congrArg (fun f => f n) key
  simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, ArithmeticFunction.sigma_zero_apply] at h
  rw [Nat.sum_divisorsAntidiagonal (fun a b => ArithmeticFunction.moebius a * ((b.divisors.card : ℕ) : ℤ))] at h
  rw [h]; simp [hn.ne']
end

-- forge:entry lib_matrix_rank_pow_succ_lt_of_isNilpotent_of_ne_zero kind=proved origin=conjecture
section
/- promoted from Mathlib2.bld5_nilpotent_pow_rank_succ_eq_zero_aux2 (hypothesis restated as A^k ≠ 0 instead of rank ≠ 0): for a nilpotent matrix the ranks of the powers strictly decrease as long as the power is nonzero. -/
theorem lib_matrix_rank_pow_succ_lt_of_isNilpotent_of_ne_zero (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (hA : IsNilpotent A) (k : ℕ) (hk : A ^ k ≠ 0) : (A ^ (k + 1)).rank < (A ^ k).rank := by
  apply Mathlib2.bld5_nilpotent_pow_rank_succ_eq_zero_aux2 K ι A hA k
  intro h
  exact hk ((Mathlib2.lib_matrix_rank_eq_zero_iff K ι ι (A ^ k)).mp h)
end

-- forge:entry calc_integral_dalzell kind=proved origin=conjecture
section
/- Dalzell's integral ∫₀¹ x⁴(1−x)⁴/(1+x²) dx = 22/7 − π — polynomial division: integrand = x⁶ − 4x⁵ + 5x⁴ − 4x² + 4 − 4/(1+x²); integrate termwise, integral_inv_one_add_sq / arctan 1 = π/4. -/
theorem calc_integral_dalzell : ∫ x in (0:ℝ)..1, x ^ 4 * (1 - x) ^ 4 / (1 + x ^ 2) = 22 / 7 - Real.pi := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun x : ℝ => x ^ 7 / 7 - 2 * x ^ 6 / 3 + x ^ 5 - 4 * x ^ 3 / 3 + 4 * x - 4 * Real.arctan x) (x ^ 4 * (1 - x) ^ 4 / (1 + x ^ 2)) x := by
    intro x _
    have hx0 : (1 + x ^ 2) ≠ 0 := by positivity
    have hid := hasDerivAt_id x
    have h := (((((hid.pow 7).div_const 7).sub (((hid.pow 6).const_mul 2).div_const 3)).add (hid.pow 5)).sub (((hid.pow 3).const_mul 4).div_const 3)).add (hid.const_mul 4) |>.sub ((Real.hasDerivAt_arctan x).const_mul 4)
    convert h using 1
    simp only [id]
    field_simp
    ring
  have hc : Continuous (fun x : ℝ => x ^ 4 * (1 - x) ^ 4 / (1 + x ^ 2)) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro x; positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
  simp
  ring
end

-- forge:entry arith_sum_sigma_divisors kind=proved origin=conjecture
section
/- Σ_{d|n} σ(d) = Σ_{d|n} (n/d)τ(d) — both are the Dirichlet convolution id * ζ * ζ evaluated at n (associativity/commutativity of convolution). -/
theorem arith_sum_sigma_divisors (n : ℕ) : ∑ d ∈ n.divisors, ArithmeticFunction.sigma 1 d = ∑ d ∈ n.divisors, n / d * d.divisors.card := by
  have key : (ArithmeticFunction.zeta * ArithmeticFunction.sigma 1 : ArithmeticFunction ℕ) = ArithmeticFunction.pow 1 * ArithmeticFunction.sigma 0 := by
    rw [← ArithmeticFunction.zeta_mul_pow_eq_sigma, ← ArithmeticFunction.zeta_mul_pow_eq_sigma, ArithmeticFunction.pow_zero_eq_zeta]
    ring
  have h := congrArg (fun f => f n) key
  simp only [ArithmeticFunction.mul_apply] at h
  rw [Nat.sum_divisorsAntidiagonal' (fun a b => ArithmeticFunction.zeta a * ArithmeticFunction.sigma 1 b), Nat.sum_divisorsAntidiagonal' (fun a b => ArithmeticFunction.pow 1 a * ArithmeticFunction.sigma 0 b)] at h
  have hd : ∀ d ∈ n.divisors, n / d ≠ 0 := fun d hd =>
    (Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)).ne'
  calc ∑ d ∈ n.divisors, ArithmeticFunction.sigma 1 d
      = ∑ d ∈ n.divisors, ArithmeticFunction.zeta (n / d) * ArithmeticFunction.sigma 1 d :=
        Finset.sum_congr rfl (fun d h' => by simp [ArithmeticFunction.zeta_apply, hd d h'])
    _ = _ := h
    _ = _ := Finset.sum_congr rfl (fun d h' => by simp [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.pow_apply])
end

-- forge:entry calc_integral_x_mul_sin_sq kind=proved origin=conjecture
section
/- ∫₀^π x sin²x dx = π²/4 — sin² = (1−cos 2x)/2, antiderivative x²/4 − x sin(2x)/4 − cos(2x)/8; or symmetry x ↦ π−x with integral_sin_sq. -/
theorem calc_integral_x_mul_sin_sq : ∫ x in (0:ℝ)..Real.pi, x * Real.sin x ^ 2 = Real.pi ^ 2 / 4 := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) Real.pi, HasDerivAt (fun x : ℝ => x ^ 2 / 4 - x * Real.sin (2 * x) / 4 - Real.cos (2 * x) / 8) (x * Real.sin x ^ 2) x := by
    intro x _
    have hid := hasDerivAt_id x
    have h2 : HasDerivAt (fun x : ℝ => 2 * x) 2 x := by simpa using hid.const_mul 2
    have hs : HasDerivAt (fun x : ℝ => Real.sin (2 * x)) (Real.cos (2 * x) * 2) x := h2.sin
    have hcs : HasDerivAt (fun x : ℝ => Real.cos (2 * x)) (-Real.sin (2 * x) * 2) x := h2.cos
    have h := (((hid.pow 2).div_const 4).sub ((hid.mul hs).div_const 4)).sub (hcs.div_const 8)
    convert h using 1
    simp only [id]
    rw [Real.cos_two_mul]
    linear_combination x * (Real.sin_sq_add_cos_sq x)
  have hc : Continuous (fun x : ℝ => x * Real.sin x ^ 2) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
  have : Real.cos (2 * Real.pi) = 1 := Real.cos_two_pi
  have h3 : Real.sin (2 * Real.pi) = 0 := Real.sin_two_pi
  simp [this, h3]
end

-- forge:entry arith_sigma_mul_totient_lt_sq kind=proved origin=conjecture
section
/- σ(n)φ(n) < n² for n ≥ 2 — both sides multiplicative; on a prime power σ(p^a)φ(p^a) = p^(a-1)(p^(a+1)-1) < p^(2a); multiply over the factorization (strong induction splitting off ordCompl). -/
lemma arith_sigma_mul_totient_lt_sq_aux1 (q k : ℕ) : q * ∑ i ∈ Finset.range (k + 1), (q + 1) ^ i + 1 = (q + 1) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, add_right_comm, ih]
    ring

theorem arith_sigma_mul_totient_lt_sq (n : ℕ) (hn : 2 ≤ n) : ArithmeticFunction.sigma 1 n * n.totient < n ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => omega
  | prime_pow p k hp hk =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.pos.ne'
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp, Nat.totient_prime_pow_succ hp]
    have h := arith_sigma_mul_totient_lt_sq_aux1 q (k + 1)
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at *
    have hpos : 0 < (q + 1) ^ k := by positivity
    have hle : (q + 1) ^ k ≤ (q + 1) ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    calc (∑ i ∈ Finset.range (k + 1 + 1), (q + 1) ^ i) * ((q + 1) ^ k * q)
        = (q + 1) ^ k * (q * ∑ i ∈ Finset.range (k + 1 + 1), (q + 1) ^ i) := by ring
      _ < (q + 1) ^ k * (q + 1) ^ (k + 1 + 1) := by
          apply Nat.mul_lt_mul_of_pos_left _ hpos
          omega
      _ = ((q + 1) ^ (k + 1)) ^ 2 := by ring
  | coprime a b ha hb hab iha ihb =>
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hab, Nat.totient_mul hab]
    have h1 := iha (by omega)
    have h2 := ihb (by omega)
    calc ArithmeticFunction.sigma 1 a * ArithmeticFunction.sigma 1 b * (a.totient * b.totient)
        = (ArithmeticFunction.sigma 1 a * a.totient) * (ArithmeticFunction.sigma 1 b * b.totient) := by ring
      _ < a ^ 2 * b ^ 2 := Nat.mul_lt_mul'' h1 h2
      _ = (a * b) ^ 2 := by ring
end

-- forge:entry calc_integral_log_sq_one_e kind=proved origin=conjecture
section
/- ∫₁^e log² x dx = e − 2 — antiderivative x log²x − 2x log x + 2x on [1,e]; FTC. -/
theorem calc_integral_log_sq_one_e : ∫ x in (1:ℝ)..Real.exp 1, Real.log x ^ 2 = Real.exp 1 - 2 := by
  have he : (1:ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hd : ∀ x ∈ Set.uIcc (1:ℝ) (Real.exp 1), HasDerivAt (fun x : ℝ => x * Real.log x ^ 2 - 2 * x * Real.log x + 2 * x) (Real.log x ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le he] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have hid := hasDerivAt_id x
    have hl := Real.hasDerivAt_log hx0
    have h := ((hid.mul (hl.pow 2)).sub ((hid.const_mul 2).mul hl)).add (hid.const_mul 2)
    convert h using 1
    simp only [id, Pi.pow_apply]
    field_simp
    ring
  have hc : ContinuousOn (fun x : ℝ => Real.log x ^ 2) (Set.uIcc 1 (Real.exp 1)) := by
    rw [Set.uIcc_of_le he]
    apply ContinuousOn.pow
    apply Real.continuousOn_log.mono
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith [hx.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  simp
end

-- forge:entry calc_card_surjective_fin_three kind=proved origin=conjecture
section
/- Number of surjections from an n-set (n ≥ 1) onto a 3-set is 3ⁿ − 3·2ⁿ + 3 — inclusion–exclusion over the missed values; count functions avoiding a given value (2ⁿ) and avoiding two values (1). -/
theorem calc_card_surjective_fin_three (n : ℕ) (hn : 0 < n) : (((Finset.univ : Finset (Fin n → Fin 3)).filter (fun f => Function.Surjective f)).card : ℤ) = 3 ^ n - 3 * 2 ^ n + 3 := by
  have hc : ∀ S : Finset (Fin 3), (Fintype.piFinset (fun _ : Fin n => S)).card = S.card ^ n := by
    intro S
    rw [Fintype.card_piFinset]
    simp
  have hI : ∀ S T : Finset (Fin 3), Fintype.piFinset (fun _ : Fin n => S) ∩ Fintype.piFinset (fun _ : Fin n => T)
      = Fintype.piFinset (fun _ : Fin n => S ∩ T) := by
    intro S T
    ext f
    simp only [Finset.mem_inter, Fintype.mem_piFinset]
    exact forall_and.symm
  have key : ∀ x : Fin 3, (x ∈ ({1, 2} : Finset (Fin 3)) ↔ x ≠ 0) ∧ (x ∈ ({0, 2} : Finset (Fin 3)) ↔ x ≠ 1)
      ∧ (x ∈ ({0, 1} : Finset (Fin 3)) ↔ x ≠ 2) := by decide
  have hset : (Finset.univ : Finset (Fin n → Fin 3)).filter (fun f => Function.Surjective f)
      = (Fintype.piFinset (fun _ : Fin n => ({1, 2} : Finset (Fin 3))) ∪ Fintype.piFinset (fun _ : Fin n => ({0, 2} : Finset (Fin 3)))
          ∪ Fintype.piFinset (fun _ : Fin n => ({0, 1} : Finset (Fin 3))))ᶜ := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, Finset.mem_union, Fintype.mem_piFinset,
      (key _).1, (key _).2.1, (key _).2.2]
    constructor
    · intro h
      rintro ((h0 | h1) | h2)
      · obtain ⟨i, hi⟩ := h 0
        exact h0 i hi
      · obtain ⟨i, hi⟩ := h 1
        exact h1 i hi
      · obtain ⟨i, hi⟩ := h 2
        exact h2 i hi
    · intro h c
      push_neg at h
      obtain ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, ⟨k, hk⟩⟩ := h
      fin_cases c
      · exact ⟨i, hi⟩
      · exact ⟨j, hj⟩
      · exact ⟨k, hk⟩
  rw [hset]
  have h1 := Finset.card_union_add_card_inter
    (Fintype.piFinset (fun _ : Fin n => ({1, 2} : Finset (Fin 3))) ∪ Fintype.piFinset (fun _ : Fin n => ({0, 2} : Finset (Fin 3))))
    (Fintype.piFinset (fun _ : Fin n => ({0, 1} : Finset (Fin 3))))
  have h2 := Finset.card_union_add_card_inter
    (Fintype.piFinset (fun _ : Fin n => ({1, 2} : Finset (Fin 3)))) (Fintype.piFinset (fun _ : Fin n => ({0, 2} : Finset (Fin 3))))
  rw [Finset.union_inter_distrib_right, hI, hI] at h1
  have h3 := Finset.card_union_add_card_inter
    (Fintype.piFinset (fun _ : Fin n => ({1, 2} ∩ {0, 1} : Finset (Fin 3))))
    (Fintype.piFinset (fun _ : Fin n => ({0, 2} ∩ {0, 1} : Finset (Fin 3))))
  rw [hI] at h2 h3
  rw [hc] at h1
  rw [hc, hc] at h2 h3
  rw [hc] at h2 h3
  have e1 : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
  have e2 : ({0, 2} : Finset (Fin 3)).card = 2 := by decide
  have e3 : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  have e4 : ({1, 2} ∩ {0, 2} : Finset (Fin 3)).card = 1 := by decide
  have e5 : ({1, 2} ∩ {0, 1} : Finset (Fin 3)).card = 1 := by decide
  have e6 : ({0, 2} ∩ {0, 1} : Finset (Fin 3)).card = 1 := by decide
  have e7 : (({1, 2} ∩ {0, 1}) ∩ ({0, 2} ∩ {0, 1}) : Finset (Fin 3)).card = 0 := by decide
  rw [e1, e2, e4] at h2
  rw [e5, e6, e7, zero_pow hn.ne', one_pow] at h3
  rw [e3] at h1
  rw [one_pow] at h2
  have h4 := Finset.card_compl_add_card
    (Fintype.piFinset (fun _ : Fin n => ({1, 2} : Finset (Fin 3))) ∪ Fintype.piFinset (fun _ : Fin n => ({0, 2} : Finset (Fin 3)))
          ∪ Fintype.piFinset (fun _ : Fin n => ({0, 1} : Finset (Fin 3))))
  have h5 : Fintype.card (Fin n → Fin 3) = 3 ^ n := by simp
  rw [h5] at h4
  zify at h1 h2 h3 h4
  linarith
end

-- forge:entry arith_even_gt_46_sum_two_abundant kind=proved origin=conjecture
section
/- Every even integer greater than 46 is a sum of two abundant numbers — Uses Mathlib2.ab_perfect_mul_abundant with Mathlib2.ab_perfect_six at the key step: every multiple 6k with k > 1 is abundant; split n mod 6: n = 12 + (n-12), n = 20 + (n-20), or n = 40 + (n-40) with 20, 40 abundant and the other summand a multiple of 6 that is ≥ 12. -/
theorem arith_even_gt_46_sum_two_abundant (n : ℕ) (he : Even n) (hn : 46 < n) : ∃ a b : ℕ, a.Abundant ∧ b.Abundant ∧ a + b = n := by
  have h20 : Nat.Abundant 20 := by
    rw [Mathlib2.ab_abundant_def]; decide
  have h40 : Nat.Abundant 40 := Mathlib2.arith_abundant_mul 20 2 h20 (by norm_num)
  have h6 : ∀ k, 1 < k → Nat.Abundant (k * 6) := fun k hk =>
    Mathlib2.ab_perfect_mul_abundant 6 k Mathlib2.ab_perfect_six hk
  obtain ⟨c, hc⟩ := he
  have hmod : n % 6 = 0 ∨ n % 6 = 2 ∨ n % 6 = 4 := by omega
  rcases hmod with h | h | h
  · refine ⟨2 * 6, (n / 6 - 2) * 6, h6 2 (by norm_num), h6 _ (by omega), by omega⟩
  · refine ⟨20, ((n - 20) / 6) * 6, h20, h6 _ (by omega), by omega⟩
  · refine ⟨40, ((n - 40) / 6) * 6, h40, h6 _ (by omega), by omega⟩
end

end Mathlib2
