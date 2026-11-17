/- Mathlib2 分片 28（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0003
import Mathlib2.Shard.S0005
import Mathlib2.Shard.S0012
import Mathlib2.Shard.S0020
import Mathlib2.Shard.S0021
import Mathlib2.Shard.S0024
import Mathlib2.Shard.S0026
import Mathlib2.Shard.S0027
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry bld5_pisano_five_pow kind=proved origin=conjecture
section
/- Uses Mathlib2.lib_fib_period_iff, Mathlib2.bld3_pisano_dvd_of_period, Mathlib2.bld3_pisano_dvd_pisano_of_dvd and Mathlib2.lib_pisano_dvd_iff_period: key identity F_{5n} = 25F_n^5 + 25(-1)^n F_n^3 + 5F_n (over ℤ), whence by induction 5^j ∣ F_{5^j} but 5^(j+1) ∤ F_{5^j}. Upper bound: induct with the matrix/binomial argument (Q^{4·5^k} = 1 + 5^k•M ⇒ Q^{4·5^(k+1)} ≡ 1 mod 5^(k+1)), base F_20 = 6765, F_21 = 10946; then lib_fib_period_iff + bld3_pisano_dvd_of_period give pisano ∣ 4·5^(k+1). Lower bound by induction: bld3_pisano_dvd_pisano_of_dvd gives 4·5^k ∣ pisano(5^(k+1)) ∣ 4·5^(k+1), so the quotient is 1 or 5; if pisano = 4·5^k then (lib_pisano_dvd_iff_period, i = 0) 5^(k+1) ∣ F_{4·5^k}, and with 5^(k+1) ∣ F_{5^(k+1)} and Nat.fib_gcd this gives 5^(k+1) ∣ F_{5^k}, contradiction. Base pisano 5 = 20 by direct check of the divisors of 20. -/
theorem bld5_pisano_five_pow_aux1 (m n : ℕ) : ((Nat.fib (m + n) : ℕ) : ℤ) = Nat.fib m * ((Nat.fib (n + 1) : ℤ) - Nat.fib n) + Nat.fib (m + 1) * Nat.fib n := by
  have h1 : Nat.fib (m + n + 2) = Nat.fib m * Nat.fib (n + 1) + Nat.fib (m + 1) * Nat.fib (n + 2) := Nat.fib_add m (n + 1)
  have h2 := Nat.fib_add m n
  have h3 : Nat.fib (m + n + 2) = Nat.fib (m + n) + Nat.fib (m + n + 1) := Nat.fib_add_two
  have h4 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
  have h1' : ((Nat.fib (m + n + 2) : ℕ) : ℤ) = Nat.fib m * Nat.fib (n + 1) + Nat.fib (m + 1) * Nat.fib (n + 2) := by exact_mod_cast h1
  have h2' : ((Nat.fib (m + n + 1) : ℕ) : ℤ) = Nat.fib m * Nat.fib n + Nat.fib (m + 1) * Nat.fib (n + 1) := by exact_mod_cast h2
  have h3' : ((Nat.fib (m + n + 2) : ℕ) : ℤ) = Nat.fib (m + n) + Nat.fib (m + n + 1) := by exact_mod_cast h3
  have h4' : ((Nat.fib (n + 2) : ℕ) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by exact_mod_cast h4
  linear_combination h1' - h2' - h3' + (Nat.fib (m + 1) : ℤ) * h4'

theorem bld5_pisano_five_pow_aux2 (n : ℕ) (a b : ℤ) (ha : (Nat.fib n : ℤ) = a) (hb : (Nat.fib (n + 1) : ℤ) = b) : ((Nat.fib (5 * n) : ℕ) : ℤ) = 5 * a * (b ^ 4 + a * (-4 * b ^ 3 + 6 * a * b ^ 2 - 4 * a ^ 2 * b + a ^ 3 + 2 * (b - a) ^ 3 + 4 * a * (b - a) ^ 2 + 3 * a ^ 2 * (b - a) + a ^ 3)) := by
  have hB : ∀ m : ℕ, ((Nat.fib (m + n + 1) : ℕ) : ℤ) = Nat.fib m * a + Nat.fib (m + 1) * b := by
    intro m
    rw [← ha, ← hb]
    exact_mod_cast Nat.fib_add m n
  have hA : ∀ m : ℕ, ((Nat.fib (m + n) : ℕ) : ℤ) = Nat.fib m * (b - a) + Nat.fib (m + 1) * a := by
    intro m
    rw [← ha, ← hb]
    exact bld5_pisano_five_pow_aux1 m n
  have x2 := hA n
  have y2 := hB n
  have x3 := hA (n + n)
  have y3 := hB (n + n)
  have x4 := hA (n + n + n)
  have y4 := hB (n + n + n)
  have x5 := hA (n + n + n + n)
  rw [show 5 * n = n + n + n + n + n by ring, x5, y4, x4, y3, x3, y2, x2, ha, hb]
  ring

theorem bld5_pisano_five_pow_aux3 (k : ℕ) : ∃ t : ℤ, ¬ (5 : ℤ) ∣ t ∧ ((Nat.fib (4 * 5 ^ (k + 1)) : ℕ) : ℤ) = 5 ^ (k + 1) * t := by
  induction k with
  | zero => exact ⟨1353, by norm_num, by norm_num⟩
  | succ k ih =>
    obtain ⟨t, ht, hF⟩ := ih
    have h5 : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
    have hid := bld5_pisano_five_pow_aux2 (4 * 5 ^ (k + 1)) _ _ hF rfl
    have hda : (5 : ℤ) ∣ 5 ^ (k + 1) * t := ⟨5 ^ k * t, by ring⟩
    have hnb : ¬ (5 : ℤ) ∣ (Nat.fib (4 * 5 ^ (k + 1) + 1) : ℤ) := by
      intro hb
      have h1 : (5 : ℕ) ∣ Nat.fib (4 * 5 ^ (k + 1) + 1) := by exact_mod_cast hb
      have h2 : (5 : ℕ) ∣ Nat.fib (4 * 5 ^ (k + 1)) := by
        have : (5 : ℤ) ∣ ((Nat.fib (4 * 5 ^ (k + 1)) : ℕ) : ℤ) := by rw [hF]; exact hda
        exact_mod_cast this
      have h3 := Nat.dvd_gcd h2 h1
      rw [Nat.Coprime.gcd_eq_one (Nat.fib_coprime_fib_succ _)] at h3
      omega
    refine ⟨t * ((Nat.fib (4 * 5 ^ (k + 1) + 1) : ℤ) ^ 4 + 5 ^ (k + 1) * t * (-4 * (Nat.fib (4 * 5 ^ (k + 1) + 1) : ℤ) ^ 3 + 6 * (5 ^ (k + 1) * t) * (Nat.fib (4 * 5 ^ (k + 1) + 1) : ℤ) ^ 2 - 4 * (5 ^ (k + 1) * t) ^ 2 * (Nat.fib (4 * 5 ^ (k + 1) + 1) : ℤ) + (5 ^ (k + 1) * t) ^ 3 + 2 * ((Nat.fib (4 * 5 ^ (k + 1) + 1) : ℤ) - 5 ^ (k + 1) * t) ^ 3 + 4 * (5 ^ (k + 1) * t) * ((Nat.fib (4 * 5 ^ (k + 1) + 1) : ℤ) - 5 ^ (k + 1) * t) ^ 2 + 3 * (5 ^ (k + 1) * t) ^ 2 * ((Nat.fib (4 * 5 ^ (k + 1) + 1) : ℤ) - 5 ^ (k + 1) * t) + (5 ^ (k + 1) * t) ^ 3)), ?_, ?_⟩
    · intro hd
      rcases h5.dvd_or_dvd hd with h | h
      · exact ht h
      · have h' := (dvd_add_left (Dvd.dvd.mul_right hda _)).mp h
        exact hnb (h5.dvd_of_dvd_pow h')
    · rw [show 4 * 5 ^ (k + 1 + 1) = 5 * (4 * 5 ^ (k + 1)) by ring, hid]
      ring

theorem bld5_pisano_five_pow_aux4 (k : ℕ) : p3_pisano (5 ^ (k + 1)) ∣ 4 * 5 ^ (k + 1) := by
  induction k with
  | zero =>
    apply bld3_pisano_dvd_of_period
    rw [lib_fib_period_iff]
    constructor <;> norm_num [Nat.ModEq]
  | succ k ih =>
    have h1 := bld5_pisano_mul_dvd_mul 5 (5 ^ (k + 1)) (dvd_pow_self 5 (by omega))
    have h2 := h1.trans (mul_dvd_mul_left 5 ih)
    rw [show 5 ^ (k + 1 + 1) = 5 * 5 ^ (k + 1) by ring, show 4 * (5 * 5 ^ (k + 1)) = 5 * (4 * 5 ^ (k + 1)) by ring]
    exact h2

theorem bld5_pisano_five_pow (k : ℕ) : p3_pisano (5 ^ (k + 1)) = 4 * 5 ^ (k + 1) := by
  induction k with
  | zero =>
    have h1 := bld5_pisano_five_pow_aux4 0
    have e : 4 * 5 ^ (0 + 1) = 20 := by norm_num
    have e5 : 5 ^ (0 + 1) = 5 := by norm_num
    rw [e] at h1 ⊢
    rw [e5] at h1 ⊢
    have h4 : ¬ p3_pisano 5 ∣ 4 := by
      intro h
      have := (lib_pisano_dvd_iff_period 5 4 (by norm_num)).mp h 0
      revert this
      norm_num [Nat.ModEq]
    have h10 : ¬ p3_pisano 5 ∣ 10 := by
      intro h
      have := (lib_pisano_dvd_iff_period 5 10 (by norm_num)).mp h 1
      revert this
      norm_num [Nat.ModEq]
    have key : ∀ P : ℕ, P ∣ 20 → ¬ P ∣ 4 → ¬ P ∣ 10 → P = 20 := by
      intro P h a b
      have := Nat.le_of_dvd (by norm_num) h
      interval_cases P <;> omega
    exact key _ h1 h4 h10
  | succ k ih =>
    have h1 := bld5_pisano_five_pow_aux4 (k + 1)
    have h2 := bld3_pisano_dvd_pisano_of_dvd (5 ^ (k + 1)) (5 ^ (k + 1 + 1)) (pow_dvd_pow 5 (by omega))
    rw [ih] at h2
    obtain ⟨c, hc⟩ := h2
    have e : 4 * 5 ^ (k + 1 + 1) = 4 * 5 ^ (k + 1) * 5 := by ring
    rw [hc, e] at h1
    rw [hc, e]
    have hc2 : c ∣ 5 := Nat.dvd_of_mul_dvd_mul_left (by positivity) h1
    rcases (Nat.dvd_prime Nat.prime_five).mp hc2 with rfl | rfl
    · exfalso
      rw [mul_one] at hc
      have hper := (lib_pisano_dvd_iff_period (5 ^ (k + 1 + 1)) (4 * 5 ^ (k + 1)) (by positivity)).mp (by rw [hc])
      have h3 := hper 0
      rw [zero_add, Nat.fib_zero, Nat.modEq_zero_iff_dvd] at h3
      obtain ⟨t, ht, hF⟩ := bld5_pisano_five_pow_aux3 k
      have h4 : ((5 ^ (k + 1 + 1) : ℕ) : ℤ) ∣ ((Nat.fib (4 * 5 ^ (k + 1)) : ℕ) : ℤ) := by exact_mod_cast h3
      rw [hF] at h4
      push_cast at h4
      rw [pow_succ] at h4
      exact ht ((mul_dvd_mul_iff_left (by positivity)).mp h4)
    · rfl
end

-- forge:entry lib_radical_pow_dvd_of_irreducible_pow_dvd kind=proved origin=conjecture
section
/- promoted from Mathlib2.poly_no_consecutive_powerful_aux1 (generalised from k[X], n = 2 to any normalised UFM and any exponent): if every irreducible factor of g occurs to the n-th power then (radical g)^n divides g. -/
theorem lib_radical_pow_dvd_of_irreducible_pow_dvd {M : Type*} [CommMonoidWithZero M] [IsCancelMulZero M] [NormalizationMonoid M] [UniqueFactorizationMonoid M] (n : ℕ) (g : M) (hg : ∀ p : M, Irreducible p → p ∣ g → p ^ n ∣ g) : (UniqueFactorizationMonoid.radical g) ^ n ∣ g := by
  classical
  unfold UniqueFactorizationMonoid.radical
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_isRelPrime
  · intro x hx y hy hne
    exact (UniqueFactorizationMonoid.pairwise_primeFactors_isRelPrime hx hy hne).pow
  · intro p hp
    rw [UniqueFactorizationMonoid.mem_primeFactors] at hp
    exact hg p (UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp) (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp)
end

-- forge:entry lib_polynomial_natDegree_radical_eq_card_roots_toFinset kind=proved origin=conjecture
section
/- promoted from Mathlib2.poly_abc_distinct_roots_complex_aux1 (strengthened from ≤ to =): over an algebraically closed field the degree of the radical of a nonzero polynomial is its number of distinct roots. -/
open UniqueFactorizationMonoid Polynomial
theorem lib_polynomial_natDegree_radical_eq_card_roots_toFinset {k : Type*} [Field k] [DecidableEq k] [IsAlgClosed k] (p : Polynomial k) (hp : p ≠ 0) : (UniqueFactorizationMonoid.radical p).natDegree = p.roots.toFinset.card := by
  apply le_antisymm (Mathlib2.poly_abc_distinct_roots_complex_aux1 p hp)
  have hfac : ∀ q ∈ primeFactors p, q.Monic ∧ q.natDegree = 1 := by
    intro q hq
    rw [mem_primeFactors] at hq
    have hirr := irreducible_of_normalized_factor q hq
    have hmon : q.Monic := by
      rw [← normalize_normalized_factor q hq]
      exact Polynomial.monic_normalize hirr.ne_zero
    exact ⟨hmon, Polynomial.natDegree_eq_of_degree_eq_some (IsAlgClosed.degree_eq_one_of_irreducible k hirr)⟩
  have h1 : (radical p).natDegree = (primeFactors p).card := by
    unfold radical
    rw [Polynomial.natDegree_prod_of_monic _ id (fun q hq => (hfac q hq).1)]
    rw [Finset.sum_congr rfl (fun q hq => show (id q).natDegree = 1 from (hfac q hq).2)]
    simp
  rw [h1]
  apply Finset.card_le_card_of_injOn (fun a => X - C a)
  · intro a ha
    simp only [Finset.mem_coe, Multiset.mem_toFinset] at ha
    simp only [Finset.mem_coe, mem_primeFactors]
    rw [UniqueFactorizationMonoid.mem_normalizedFactors_iff' hp]
    exact ⟨Polynomial.irreducible_X_sub_C a, (Polynomial.monic_X_sub_C a).normalize_eq_self, Polynomial.dvd_iff_isRoot.mpr (Polynomial.isRoot_of_mem_roots ha)⟩
  · intro a _ b _ h
    simpa using h
end

-- forge:entry lib_chebyshev_T_natDegree_le kind=proved origin=conjecture
section
/- promoted from Mathlib2.poly_chebyshev_T_card_distinct_real_roots_aux1 (generalised from natural to integer index): the Chebyshev polynomial T_n has degree at most |n| over any commutative ring. -/
theorem lib_chebyshev_T_natDegree_le (R : Type*) [CommRing R] (n : ℤ) : (Polynomial.Chebyshev.T R n).natDegree ≤ n.natAbs := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using (Mathlib2.poly_chebyshev_T_card_distinct_real_roots_aux1 R m).1
  · rw [Polynomial.Chebyshev.T_neg]
    simpa using (Mathlib2.poly_chebyshev_T_card_distinct_real_roots_aux1 R m).1
end

-- forge:entry lib_fib_two_mul_add_one_cast_eq_fib_succ_mul_lucas kind=proved origin=conjecture
section
/- promoted from Mathlib2.bld5_pisano_lucas_odd_eq_aux1 (generalised from ℤ to any commutative ring): F_{2n+1} = F_{n+1} L_n - (-1)^n. -/
theorem lib_fib_two_mul_add_one_cast_eq_fib_succ_mul_lucas (R : Type*) [CommRing R] (n : ℕ) : ((Nat.fib (2 * n + 1) : ℕ) : R) = ((Nat.fib (n + 1) : ℕ) : R) * ((Mathlib2.p3_lucas n : ℕ) : R) - (-1) ^ n := by
  have h := congrArg (Int.cast : ℤ → R) (Mathlib2.bld5_pisano_lucas_odd_eq_aux1 n)
  push_cast at h
  exact h
end

-- forge:entry lib_matrix_mulVec_eq_zero_of_rank_mul_self_eq kind=proved origin=conjecture
section
/- promoted from Mathlib2.bld4_fitting_range_inter_ker_pow_card_aux2: if rank(N^2) = rank N then range N meets ker N trivially, i.e. N(Nv) = 0 implies Nv = 0. -/
theorem lib_matrix_mulVec_eq_zero_of_rank_mul_self_eq (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (N : Matrix ι ι K) (hN : (N * N).rank = N.rank) (v : ι → K) (hv : N.mulVec (N.mulVec v) = 0) : N.mulVec v = 0 := by
  exact Mathlib2.bld4_fitting_range_inter_ker_pow_card_aux2 K ι N hN v hv
end

-- forge:entry lib_antitone_convex_nat_seq_eq_of_succ_eq kind=proved origin=conjecture
section
/- promoted from Mathlib2.bld5_nilpotent_pow_rank_succ_eq_zero_aux1 (conclusion simplified): a non-increasing convex sequence of naturals that stalls once is constant from then on. -/
theorem lib_antitone_convex_nat_seq_eq_of_succ_eq (r : ℕ → ℕ) (hanti : ∀ k, r (k + 1) ≤ r k) (hconv : ∀ k, 2 * r (k + 1) ≤ r k + r (k + 2)) (k : ℕ) (hk : r (k + 1) = r k) (j : ℕ) : r (k + j) = r k := by
  exact (Mathlib2.bld5_nilpotent_pow_rank_succ_eq_zero_aux1 r hanti hconv k hk j).1
end

-- forge:entry arith_padicValNat_two_centralBinom kind=proved origin=conjecture
section
/- v_2(C(2n,n)) equals the number of ones in the binary expansion of n — Kummer/Legendre: v_2 = s_2(n) + s_2(n) - s_2(2n) and s_2(2n) = s_2(n). -/
theorem arith_padicValNat_two_centralBinom (n : ℕ) : padicValNat 2 n.centralBinom = (Nat.digits 2 n).sum := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h := @sub_one_mul_padicValNat_choose_eq_sub_sum_digits' 2 n n ⟨Nat.prime_two⟩
    have h2 : Nat.digits 2 (n + n) = 0 :: Nat.digits 2 n := by
      rw [← two_mul]; exact Nat.digits_base_mul (by norm_num) hn
    rw [h2] at h
    simp only [List.sum_cons, zero_add] at h
    rw [Nat.centralBinom_eq_two_mul_choose, two_mul]
    omega
end

-- forge:entry arith_card_divisors_sq_le kind=proved origin=conjecture
section
/- τ(n) ≤ 2√n — the map d ↦ min(d, n/d) is at most 2-to-1 from divisors into {1..⌊√n⌋}. -/
theorem arith_card_divisors_sq_le (n : ℕ) : n.divisors.card ^ 2 ≤ 4 * n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hs : n.sqrt * n.sqrt ≤ n := Nat.sqrt_le n
  have hs' : n < (n.sqrt + 1) * (n.sqrt + 1) := Nat.lt_succ_sqrt n
  have h1 : (n.divisors.filter (fun d => d ≤ n.sqrt)).card ≤ n.sqrt := by
    calc _ ≤ (Finset.Icc 1 n.sqrt).card := by
          apply Finset.card_le_card
          intro d hd
          rw [Finset.mem_filter, Nat.mem_divisors] at hd
          rw [Finset.mem_Icc]
          exact ⟨Nat.pos_of_dvd_of_pos hd.1.1 hn, hd.2⟩
      _ = n.sqrt := by simp
  have h2 : (n.divisors.filter (fun d => ¬ d ≤ n.sqrt)).card ≤ n.sqrt := by
    calc _ ≤ (Finset.Icc 1 n.sqrt).card := by
          apply Finset.card_le_card_of_injOn (fun d => n / d)
          · intro d hd
            simp only [Finset.coe_filter, Set.mem_setOf_eq, Nat.mem_divisors] at hd
            obtain ⟨⟨⟨k, hk⟩, _⟩, hd2⟩ := hd
            have hd0 : 0 < d := by omega
            have hq : n / d = k := by rw [hk, Nat.mul_div_cancel_left _ hd0]
            simp only [Finset.coe_Icc, Set.mem_Icc]
            rw [hq]
            constructor
            · rcases Nat.eq_zero_or_pos k with rfl | hk0
              · simp at hk; omega
              · exact hk0
            · by_contra hlt
              have : (n.sqrt+1)*(n.sqrt+1) ≤ d * k := Nat.mul_le_mul (by omega) (by omega)
              omega
          · intro d1 hd1 d2 hd2 h
            simp only [Finset.coe_filter, Set.mem_setOf_eq, Nat.mem_divisors] at hd1 hd2
            simp only at h
            have e1 := Nat.div_mul_cancel hd1.1.1
            have e2 := Nat.div_mul_cancel hd2.1.1
            rw [h] at e1
            have hq : 0 < n / d2 := Nat.div_pos (Nat.le_of_dvd hn hd2.1.1) (Nat.pos_of_dvd_of_pos hd2.1.1 hn)
            exact Nat.eq_of_mul_eq_mul_left hq (e1.trans e2.symm)
      _ = n.sqrt := by simp
  have h3 := Finset.card_filter_add_card_filter_not (s := n.divisors) (fun d => d ≤ n.sqrt)
  have h4 : n.divisors.card ≤ 2 * n.sqrt := by omega
  nlinarith
end

-- forge:entry arith_two_mul_totient_eq_self_iff kind=proved origin=conjecture
section
/- φ(n) = n/2 iff n is a power of 2 with n ≥ 2 — n must be even; write n = 2^a m with m odd, then φ(n) = 2^(a-1) φ(m) so φ(m) = m forcing m = 1. -/
theorem arith_two_mul_totient_eq_self_iff (n : ℕ) (hn : 0 < n) : 2 * n.totient = n ↔ ∃ k : ℕ, n = 2 ^ (k + 1) := by
  constructor
  · intro h
    obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
    have hcop : Nat.Coprime (2^a) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
    rw [Nat.totient_mul hcop] at h
    cases a with
    | zero =>
      exfalso
      simp at h
      obtain ⟨k, rfl⟩ := hm
      omega
    | succ a =>
      rw [Nat.totient_prime_pow_succ Nat.prime_two] at h
      simp only [Nat.reduceSub, mul_one] at h
      have h2 : 2 ^ (a+1) * m.totient = 2 ^ (a+1) * m := by rw [← h]; ring
      have h3 : m.totient = m := Nat.eq_of_mul_eq_mul_left (by positivity) h2
      have hm1 : m = 1 := by
        by_contra hne
        have : m.totient < m := Nat.totient_lt m (by rcases hm with ⟨k, rfl⟩; omega)
        omega
      exact ⟨a, by rw [hm1, mul_one]⟩
  · rintro ⟨k, rfl⟩
    rw [Nat.totient_prime_pow_succ Nat.prime_two]; ring
end

-- forge:entry lib_fib_mul_modEq_sq_of_dvd kind=proved origin=conjecture
section
/- promoted from Mathlib2.bld5_pisano_mul_dvd_mul_aux2 (the square-zero lifting lemma specialised to ZMod (m^2), stated as congruences): if F_N = m·u and F_{N+1} = 1 + m·v then modulo m^2, F_{jN} ≡ j·m·u and F_{jN+1} ≡ 1 + j·m·v. For the general ring form (μ^2 = 0) use the aux lemma directly. -/
theorem lib_fib_mul_modEq_sq_of_dvd (m N : ℕ) (u v : ℤ) (h0 : (Nat.fib N : ℤ) = (m : ℤ) * u) (h1 : (Nat.fib (N + 1) : ℤ) = 1 + (m : ℤ) * v) (j : ℕ) : (Nat.fib (j * N) : ℤ) ≡ (j : ℤ) * (m : ℤ) * u [ZMOD ((m ^ 2 : ℕ) : ℤ)] ∧ (Nat.fib (j * N + 1) : ℤ) ≡ 1 + (j : ℤ) * (m : ℤ) * v [ZMOD ((m ^ 2 : ℕ) : ℤ)] := by
  have hμ : ((m : ℕ) : ZMod (m ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  have e0 : ((Nat.fib N : ℕ) : ZMod (m ^ 2)) = (m : ZMod (m ^ 2)) * (u : ZMod (m ^ 2)) := by
    have := congrArg (Int.cast : ℤ → ZMod (m ^ 2)) h0
    push_cast at this
    exact this
  have e1 : ((Nat.fib (N + 1) : ℕ) : ZMod (m ^ 2)) = 1 + (m : ZMod (m ^ 2)) * (v : ZMod (m ^ 2)) := by
    have := congrArg (Int.cast : ℤ → ZMod (m ^ 2)) h1
    push_cast at this
    exact this
  have H := Mathlib2.bld5_pisano_mul_dvd_mul_aux2 (ZMod (m ^ 2)) N _ _ _ hμ e0 e1 j
  constructor
  · rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    exact H.1
  · rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    exact H.2
end

-- forge:entry lib_pisano_lucas_two_mul_dvd_and_dvd_four_mul kind=proved origin=conjecture
section
/- promoted from Mathlib2.bld5_pisano_lucas_odd_eq_aux3 (combined with Mathlib2.bld4_pisano_lucas_dvd_four_mul): for n ≥ 2 the Pisano period of the Lucas number L_n is 2n or 4n — it is a multiple of 2n and a divisor of 4n. -/
theorem lib_pisano_lucas_two_mul_dvd_and_dvd_four_mul (n : ℕ) (hn : 2 ≤ n) : 2 * n ∣ Mathlib2.p3_pisano (Mathlib2.p3_lucas n) ∧ Mathlib2.p3_pisano (Mathlib2.p3_lucas n) ∣ 4 * n := by
  exact ⟨Mathlib2.bld5_pisano_lucas_odd_eq_aux3 n hn, Mathlib2.bld4_pisano_lucas_dvd_four_mul n⟩
end

-- forge:entry lib_orderOf_eq_prime_of_card_prime_mul_prime_of_not_isCyclic kind=proved origin=conjecture
section
/- promoted from Mathlib2.bld3_card_conjClasses_of_card_prime_mul_prime_aux1 (order part, hypothesis weakened from non-abelian to non-cyclic): in a non-cyclic group of order pq every non-identity element has order p or q. (The aux lemma also gives |C(a)| = orderOf a in the non-abelian case.) -/
theorem lib_orderOf_eq_prime_of_card_prime_mul_prime_of_not_isCyclic (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (G : Type*) [Group G] (hG : Nat.card G = p * q) (hnc : ¬ IsCyclic G) (a : G) (ha : a ≠ 1) : orderOf a = p ∨ orderOf a = q := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact (Nat.mul_pos hp.pos hq.pos).ne')
  have hd : orderOf a ∣ p * q := hG ▸ orderOf_dvd_natCard a
  have h1 : orderOf a ≠ 1 := by
    intro h; exact ha (orderOf_eq_one_iff.mp h)
  have hpq : orderOf a ≠ p * q := fun h => hnc (isCyclic_of_orderOf_eq_card a (by rw [h, hG]))
  obtain ⟨d1, d2, h1', h2', he⟩ := (Nat.dvd_mul).mp hd
  rw [← he] at h1 hpq ⊢
  rcases (Nat.dvd_prime hp).mp h1' with rfl | rfl <;> rcases (Nat.dvd_prime hq).mp h2' with rfl | rfl
  · exact absurd (one_mul 1) h1
  · right; exact one_mul _
  · left; exact mul_one _
  · exact absurd rfl hpq
end

-- forge:entry arith_perfect_dvd_perfect_eq kind=proved origin=conjecture
section
/- A perfect number never properly divides another perfect number — write n = k·m; k = 0 is impossible, k = 1 gives equality, and for k > 1 Uses Mathlib2.ab_perfect_mul_abundant at the key step: k·m is abundant, contradicting perfection of n (Nat.Perfect excludes Abundant). -/
theorem arith_perfect_dvd_perfect_eq (m n : ℕ) (hm : m.Perfect) (hn : n.Perfect) (h : m ∣ n) : m = n := by
  obtain ⟨k, rfl⟩ := h
  rcases Nat.lt_or_ge 1 k with hk | hk
  · have := Mathlib2.ab_perfect_mul_abundant m k hm hk
    rw [mul_comm] at this
    exact absurd hn.1 (ne_of_gt this)
  · interval_cases k
    · exact absurd hn.2 (by simp)
    · simp
end

-- forge:entry arith_two_pow_mod_self_ne_one kind=proved origin=conjecture
section
/- For n ≥ 2, 2^n is never ≡ 1 (mod n) — if 2^n % n = 1 then n | 2^n - 1 and Uses Mathlib2.nt2_dvd_two_pow_sub_one_eq_one at this step to get n = 1, contradiction. -/
theorem arith_two_pow_mod_self_ne_one (n : ℕ) (hn : 2 ≤ n) : 2 ^ n % n ≠ 1 := by
  intro h
  have h1 : n ∣ 2 ^ n - 1 := by
    have : 2 ^ n % n = 1 % n := by rw [h, Nat.mod_eq_of_lt (by omega)]
    exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp this.symm
  have := Mathlib2.nt2_dvd_two_pow_sub_one_eq_one n (by omega) h1
  omega
end

-- forge:entry calc_sum_mul_choose_sq kind=proved origin=conjecture
section
/- ∑ₖ k·C(n+1,k)² = (n+1)·C(2n+1,n) — absorb k·C(n+1,k) = (n+1)·C(n,k−1), then Vandermonde ∑ C(n,k−1)C(n+1,n+1−k) = C(2n+1,n) (Nat.add_choose_eq). -/
theorem calc_sum_mul_choose_sq (n : ℕ) : ∑ k ∈ Finset.range (n + 2), k * (n + 1).choose k ^ 2 = (n + 1) * (2 * n + 1).choose n := by
  rw [Finset.sum_range_succ']
  have hv : (2 * n + 1).choose n = ∑ i ∈ Finset.range (n + 1), n.choose i * (n + 1).choose (n - i) := by
    have := Nat.add_choose_eq n (n + 1) n
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at this
    rw [← this]
    congr 1
    omega
  rw [hv, Finset.mul_sum]
  simp only [Nat.zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h1 : (n + 1) * n.choose k = (n + 1).choose (k + 1) * (k + 1) := Nat.add_one_mul_choose_eq n k
  have h2 : (n + 1).choose (n - k) = (n + 1).choose (k + 1) := by
    have := Nat.choose_symm (n := n + 1) (k := k + 1) (by omega)
    rw [← this]
    congr 1
    omega
  rw [h2, ← mul_assoc, h1]
  ring
end

-- forge:entry arith_prime_mul_prime_deficient kind=proved origin=conjecture
section
/- A product of two primes other than 6 is deficient — Uses Mathlib2.ab_prime_mul_prime_not_abundant at step 1 (not abundant); step 2: not perfect since (p+1)(q+1) = 2pq forces (p-1)(q-1) = 2, i.e. {p,q} = {2,3}, and p² is a prime power; conclude by Nat.deficient_iff_not_abundant_and_not_perfect. -/
theorem arith_prime_mul_prime_deficient (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h : p * q ≠ 6) : (p * q).Deficient := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hpos : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  rw [Nat.deficient_iff_not_abundant_and_not_perfect hpos.ne']
  refine ⟨Mathlib2.ab_prime_mul_prime_not_abundant p q hp hq, ?_⟩
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos]
  intro hs
  by_cases hpq : p = q
  · subst hpq
    rw [← pow_two, Nat.sum_divisors_prime_pow hp] at hs
    simp [Finset.sum_range_succ] at hs
    nlinarith
  · have hc : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq
    rw [hc.sum_divisors_mul, hp.sum_divisors, hq.sum_divisors] at hs
    have h3 : p ≤ 3 := by
      by_contra hc'
      push_neg at hc'
      nlinarith
    have h4 : q ≤ 3 := by
      by_contra hc'
      push_neg at hc'
      nlinarith
    interval_cases p <;> interval_cases q <;> omega
end

-- forge:entry calc_integral_log_one_add kind=proved origin=conjecture
section
/- ∫₀¹ log(1+x) dx = 2 log 2 − 1 — antiderivative (1+x)log(1+x) − x on [0,1]; FTC. -/
theorem calc_integral_log_one_add : ∫ x in (0:ℝ)..1, Real.log (1 + x) = 2 * Real.log 2 - 1 := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun x : ℝ => (1 + x) * Real.log (1 + x) - x) (Real.log (1 + x)) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    have hx0 : (1 + x) ≠ 0 := by linarith [hx.1]
    have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 x := by simpa using (hasDerivAt_id x).const_add 1
    have h := (h1.mul (h1.log hx0)).sub (hasDerivAt_id x)
    apply h.congr_deriv
    field_simp [hx0]
    ring
  have hc : ContinuousOn (fun x : ℝ => Real.log (1 + x)) (Set.uIcc 0 1) := by
    rw [Set.uIcc_of_le (by norm_num)]
    apply ContinuousOn.log (by fun_prop)
    intro x hx
    linarith [hx.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  norm_num
end

-- forge:entry calc_card_even_card_subsets kind=proved origin=conjecture
section
/- Exactly half (2ⁿ) of the subsets of an (n+1)-set have even cardinality — involution s ↦ s ∆ {0} flips parity; or ∑ (−1)^|s| = 0 (Finset.sum_powerset_neg_one_pow_card) with total 2^(n+1). -/
theorem calc_card_even_card_subsets (n : ℕ) : ((Finset.univ : Finset (Finset (Fin (n + 1)))).filter (fun s => Even s.card)).card = 2 ^ n := by
  have h1 : ∑ s : Finset (Fin (n+1)), ((-1:ℤ))^s.card = 0 := by
    have := Finset.sum_powerset_neg_one_pow_card (x := (Finset.univ : Finset (Fin (n+1))))
    rw [if_neg Finset.univ_nonempty.ne_empty] at this
    simpa using this
  have h2 : ∑ s : Finset (Fin (n+1)), ((-1:ℤ))^s.card
      = ((Finset.univ.filter (fun s : Finset (Fin (n+1)) => Even s.card)).card : ℤ)
        - ((Finset.univ.filter (fun s : Finset (Fin (n+1)) => ¬ Even s.card)).card : ℤ) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s : Finset (Fin (n+1)) => Even s.card)]
    rw [Finset.sum_congr rfl (g := fun _ => (1:ℤ)) (fun s hs => Even.neg_one_pow (Finset.mem_filter.mp hs).2)]
    rw [Finset.sum_congr rfl (g := fun _ => (-1:ℤ)) (fun s hs => Odd.neg_one_pow (Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hs).2))]
    simp
    ring
  have h3 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Finset (Fin (n+1))))) (fun s => Even s.card)
  rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin, pow_succ] at h3
  omega
end

-- forge:entry calc_integral_sq_div_one_add_sq kind=proved origin=conjecture
section
/- ∫₀¹ x²/(1+x²) dx = 1 − π/4 — rewrite integrand as 1 − 1/(1+x²); arctan. -/
theorem calc_integral_sq_div_one_add_sq : ∫ x in (0:ℝ)..1, x ^ 2 / (1 + x ^ 2) = 1 - Real.pi / 4 := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun x : ℝ => x - Real.arctan x) (x ^ 2 / (1 + x ^ 2)) x := by
    intro x _
    have hx0 : (1 + x ^ 2) ≠ 0 := by positivity
    have h := (hasDerivAt_id x).sub (Real.hasDerivAt_arctan x)
    apply h.congr_deriv
    field_simp
    ring
  have hc : Continuous (fun x : ℝ => x ^ 2 / (1 + x ^ 2)) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro x; positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
  simp
end

end Mathlib2
