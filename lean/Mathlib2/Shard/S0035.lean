/- Mathlib2 分片 35（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0005
import Mathlib2.Shard.S0016
import Mathlib2.Shard.S0020
import Mathlib2.Shard.S0021
import Mathlib2.Shard.S0023
import Mathlib2.Shard.S0024
import Mathlib2.Shard.S0026
import Mathlib2.Shard.S0027
import Mathlib2.Shard.S0028
import Mathlib2.Shard.S0029
import Mathlib2.Shard.S0030
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry fld_irrational_cos_pi_div_nine kind=proved origin=conjecture
section
/- cos(π/9) = cos 20° is irrational — by the triple angle formula c = cos(π/9) satisfies 8c^3 - 6c - 1 = 0 (cos(π/3) = 1/2); 2c is a root of the monic integer polynomial y^3 - 3y - 1, so if rational it is an integer dividing 1, but ±1 are not roots. -/
theorem fld_irrational_cos_pi_div_nine : Irrational (Real.cos (Real.pi / 9)) := by
  rintro ⟨q, hq⟩
  have h3 : Real.cos (3 * (Real.pi / 9)) = 4 * Real.cos (Real.pi / 9) ^ 3 - 3 * Real.cos (Real.pi / 9) := Real.cos_three_mul _
  have e : 3 * (Real.pi / 9) = Real.pi / 3 := by ring
  rw [e, Real.cos_pi_div_three, ← hq] at h3
  have hQ : (2 * q) ^ 3 - 3 * (2 * q) - 1 = 0 := by
    have : (((2 * q) ^ 3 - 3 * (2 * q) - 1 : ℚ) : ℝ) = 0 := by push_cast; linear_combination (-2) * h3
    exact_mod_cast this
  have hmon : (Polynomial.X ^ 3 - (3 * Polynomial.X + 1) : Polynomial ℤ).Monic := by
    apply Polynomial.monic_X_pow_sub
    have : (3 * Polynomial.X + 1 : Polynomial ℤ).degree ≤ 1 := by compute_degree
    exact lt_of_le_of_lt this (by norm_num)
  have hroot : Polynomial.aeval (2 * q) (Polynomial.X ^ 3 - (3 * Polynomial.X + 1) : Polynomial ℤ) = 0 := by
    simp only [map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X, map_one, map_ofNat]
    linear_combination hQ
  obtain ⟨m, hm⟩ := isInteger_of_is_root_of_monic hmon hroot
  simp only [eq_intCast] at hm
  rw [← hm] at hQ
  have hZ : m ^ 3 - 3 * m - 1 = 0 := by exact_mod_cast hQ
  have hdiv : m ∣ 1 := ⟨m ^ 2 - 3, by linear_combination -hZ⟩
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdiv) with rfl | rfl <;> norm_num at hZ
end

-- forge:entry fld_irrational_exp_one kind=proved origin=conjecture
section
/- e is irrational (Fourier's proof) — if e = a/b then b!·(e - Σ_{k≤b} 1/k!) is an integer, but it equals Σ_{k>b} b!/k!, which lies strictly between 0 and 1/b ≤ 1 (bound the tail by a geometric series; Real.exp_bound / the series expansion of exp). -/
theorem fld_irrational_exp_one : Irrational (Real.exp 1) := by
  rintro ⟨q, hq⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = q.den + 2 := ⟨_, rfl⟩
  have hNpos : 0 < N := by omega
  have hub := Real.exp_bound (x := 1) (by norm_num) hNpos
  have hlb := Real.sum_le_exp_of_nonneg (x := 1) (by norm_num) (N + 2)
  simp only [one_pow, abs_one, one_mul] at hub
  simp only [one_pow] at hlb
  rw [Finset.sum_range_succ, Finset.sum_range_succ] at hlb
  have hS : ∃ s : ℤ, (N.factorial : ℝ) * ∑ m ∈ Finset.range N, 1 / (m.factorial : ℝ) = s := by
    refine ⟨∑ m ∈ Finset.range N, ((N.factorial / m.factorial : ℕ) : ℤ), ?_⟩
    rw [Finset.mul_sum, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hdvd : m.factorial ∣ N.factorial := Nat.factorial_dvd_factorial (Finset.mem_range.mp hm).le
    rw [Int.cast_natCast, Nat.cast_div hdvd (by positivity)]; ring
  have hE : ∃ t : ℤ, (N.factorial : ℝ) * Real.exp 1 = t := by
    have hdvd : q.den ∣ N.factorial := Nat.dvd_factorial q.den_pos (by omega)
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨q.num * c, ?_⟩
    rw [← hq, hc, Rat.cast_def q]
    have hd : (q.den:ℝ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
    push_cast
    rw [mul_div_assoc', div_eq_iff hd]; ring
  obtain ⟨s, hs⟩ := hS
  obtain ⟨t, ht⟩ := hE
  have hFpos : (0:ℝ) < (N.factorial : ℝ) := by positivity
  have hGpos : (0:ℝ) < ((N + 1).factorial : ℝ) := by positivity
  generalize hSdef : ∑ m ∈ Finset.range N, 1 / (m.factorial : ℝ) = S at *
  generalize hFdef : (N.factorial : ℝ) = F at *
  have h1 : 1 < F * (Real.exp 1 - S) := by
    have h0 : F * (1 / F + 1 / ((N + 1).factorial : ℝ)) ≤ F * (Real.exp 1 - S) := by
      apply mul_le_mul_of_nonneg_left _ hFpos.le; linarith
    have h' : F * (1 / F + 1 / ((N + 1).factorial : ℝ)) = 1 + F / ((N + 1).factorial : ℝ) := by
      rw [mul_add, mul_one_div_cancel hFpos.ne', mul_one_div]
    have : 0 < F / ((N + 1).factorial : ℝ) := by positivity
    linarith
  have h2 : F * (Real.exp 1 - S) < 2 := by
    have hu := (abs_le.mp hub).2
    have hNr : (2:ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
    have hN0 : (N:ℝ) ≠ 0 := by linarith
    have hF0 : F ≠ 0 := hFpos.ne'
    calc F * (Real.exp 1 - S) ≤ F * ((N.succ : ℝ) / (F * N)) := mul_le_mul_of_nonneg_left hu hFpos.le
      _ = (N + 1) / N := by push_cast; field_simp
      _ < 2 := by rw [div_lt_iff₀ (by linarith)]; linarith
  have h3 : F * (Real.exp 1 - S) = ((t - s : ℤ) : ℝ) := by push_cast; rw [← ht, ← hs]; ring
  rw [h3] at h1 h2
  have h1' : (1:ℤ) < t - s := by exact_mod_cast h1
  have h2' : t - s < (2:ℤ) := by exact_mod_cast h2
  omega
end

-- forge:entry bld6_chebyshev_T_separable kind=proved origin=conjecture
section
/- Uses Mathlib2.poly_chebyshev_T_card_distinct_real_roots and Mathlib2.lib_chebyshev_T_natDegree_le: n = #distinct roots ≤ card roots ≤ natDegree ≤ n (the first equality from the poly theorem, the last bound from the lib lemma), so T_n has natDegree n, splits over ℝ with all roots simple; a polynomial with natDegree-many distinct roots is squarefree, hence separable in characteristic 0. -/
theorem bld6_chebyshev_T_separable (n : ℕ) : (Polynomial.Chebyshev.T ℝ (n : ℤ)).Separable := by
  have h1 := Mathlib2.poly_chebyshev_T_card_distinct_real_roots n
  have h2 := Mathlib2.lib_chebyshev_T_natDegree_le ℝ (n:ℤ)
  simp only [Int.natAbs_natCast] at h2
  have h3 := Multiset.toFinset_card_le (Polynomial.Chebyshev.T ℝ (n : ℤ)).roots
  have h4 := Polynomial.card_roots' (Polynomial.Chebyshev.T ℝ (n : ℤ))
  have hp0 : Polynomial.Chebyshev.T ℝ (n : ℤ) ≠ 0 := by
    intro h0
    rw [h0] at h1
    have hn : n = 0 := by
      simp at h1
      omega
    rw [hn] at h0
    simp at h0
  rw [← Polynomial.nodup_roots_iff_of_splits hp0 (Polynomial.splits_iff_card_roots.2 (by omega))]
  exact Multiset.toFinset_card_eq_card_iff_nodup.1 (by omega)
end

-- forge:entry bld6_chebyshev_T_derivative_card_distinct_real_roots kind=proved origin=conjecture
section
/- Uses Mathlib2.poly_chebyshev_T_card_distinct_real_roots and Mathlib2.lib_chebyshev_T_natDegree_le: Rolle (Polynomial.card_roots_toFinset_le_derivative) gives n = #roots(T_n) ≤ #roots(T_n') + 1 using the poly theorem; conversely #roots(T_n') ≤ natDegree T_n' ≤ natDegree T_n - 1 ≤ n - 1 by the lib degree bound (the cases n = 0, 1 give the zero / constant derivative). -/
theorem bld6_chebyshev_T_derivative_card_distinct_real_roots (n : ℕ) : (Polynomial.derivative (Polynomial.Chebyshev.T ℝ (n : ℤ))).roots.toFinset.card = n - 1 := by
  have h1 := Mathlib2.poly_chebyshev_T_card_distinct_real_roots n
  have h2 := Mathlib2.lib_chebyshev_T_natDegree_le ℝ (n:ℤ)
  simp only [Int.natAbs_natCast] at h2
  have h5 := Polynomial.card_roots_toFinset_le_derivative (Polynomial.Chebyshev.T ℝ (n : ℤ))
  have h6 := Multiset.toFinset_card_le (Polynomial.derivative (Polynomial.Chebyshev.T ℝ (n : ℤ))).roots
  have h7 := Polynomial.card_roots' (Polynomial.derivative (Polynomial.Chebyshev.T ℝ (n : ℤ)))
  have h8 := Polynomial.natDegree_derivative_le (Polynomial.Chebyshev.T ℝ (n : ℤ))
  omega
end

-- forge:entry bld6_poly_mul_add_one_eq_pow_const kind=proved origin=conjecture
section
/- Uses Mathlib2.poly_no_consecutive_powerful: f and f+1 are coprime, so in the UFD k[X] any irreducible p dividing f has p-adic multiplicity in f equal to its multiplicity in h^n, a multiple of n ≥ 2, hence p^2 ∣ f; same for f+1. Both powerfulness hypotheses of poly_no_consecutive_powerful hold, giving natDegree f = 0 (last step). -/
theorem bld6_poly_mul_add_one_eq_pow_const {k : Type*} [Field k] [DecidableEq k] [CharZero k] (n : ℕ) (hn : 2 ≤ n) (f h : Polynomial k) (heq : f * (f + 1) = h ^ n) : f.natDegree = 0 := by
  have hco : IsCoprime f (f + 1) := ⟨-1, 1, by ring⟩
  have key : ∀ a : Polynomial k, (∃ d, Associated (d ^ n) a) → ∀ p : Polynomial k, Irreducible p → p ∣ a → p ^ 2 ∣ a := by
    rintro a ⟨d, hd⟩ p hp hpa
    have h1 : p ∣ d ^ n := hpa.trans hd.symm.dvd
    have h2 : p ∣ d := hp.prime.dvd_of_dvd_pow h1
    exact ((pow_dvd_pow_of_dvd h2 2).trans (pow_dvd_pow d hn)).trans hd.dvd
  exact Mathlib2.poly_no_consecutive_powerful f (key f (exists_associated_pow_of_mul_eq_pow' hco heq)) (key (f+1) (exists_associated_pow_of_mul_eq_pow' hco.symm (by rw [mul_comm]; exact heq)))
end

-- forge:entry bld6_card_circular_no_adjacent_subsets kind=proved origin=conjecture
section
/- Uses Mathlib2.calc_card_no_adjacent_subsets: split cyclically non-adjacent subsets of Z/(n+1) by whether the last point n belongs to s. If not, s is a linear non-adjacent subset of Fin n: fib(n+2) of them by calc_card_no_adjacent_subsets n; if yes (n ≥ 2), then 0 and n-1 are excluded and the rest is a linear non-adjacent subset of the n-2 middle points: fib n by calc_card_no_adjacent_subsets (n-2); small n by decide. The total is the Lucas number L_(n+1). -/
lemma bld6_card_circular_no_adjacent_subsets_aux1 (n : ℕ) (hn : 1 ≤ n) :
    ((Finset.range (n + 1)).powerset.filter
      (fun t : Finset ℕ => ∀ i ∈ t, (i + 1) % (n + 1) ∉ t)).card = Nat.fib n + Nat.fib (n + 2) := by
  have hr : Finset.range (n + 1) = insert n (Finset.range n) := Finset.range_add_one
  rw [hr, Finset.powerset_insert, Finset.filter_union, Finset.card_union_of_disjoint]
  · have h1 : (Finset.range n).powerset.filter (fun t : Finset ℕ => ∀ i ∈ t, (i + 1) % (n + 1) ∉ t)
        = (Finset.range n).powerset.filter (fun t : Finset ℕ => ∀ i ∈ t, i + 1 ∉ t) := by
      apply Finset.filter_congr
      intro t ht
      have hsub := Finset.mem_powerset.mp ht
      constructor
      · intro h i hi
        have hi' := Finset.mem_range.mp (hsub hi)
        have := h i hi
        rwa [Nat.mod_eq_of_lt (by omega)] at this
      · intro h i hi
        have hi' := Finset.mem_range.mp (hsub hi)
        rw [Nat.mod_eq_of_lt (by omega)]
        exact h i hi
    have h2 : ((Finset.range n).powerset.image (insert n)).filter
          (fun t : Finset ℕ => ∀ i ∈ t, (i + 1) % (n + 1) ∉ t)
        = ((Finset.range (n - 2)).powerset.filter (fun t : Finset ℕ => ∀ i ∈ t, i + 1 ∉ t)).image
            (fun u => insert n (u.image (fun x => x + 1))) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_powerset]
      constructor
      · rintro ⟨⟨s, hs, rfl⟩, hP⟩
        have hlt : ∀ x ∈ s, x < n := fun x hx => Finset.mem_range.mp (hs hx)
        have h0 : 0 ∉ s := by
          intro h0
          have := hP n (Finset.mem_insert_self _ _)
          rw [Nat.mod_self] at this
          exact this (Finset.mem_insert_of_mem h0)
        have hn1 : n - 1 ∉ s := by
          intro h'
          have := hP (n - 1) (Finset.mem_insert_of_mem h')
          have e : (n - 1 + 1) % (n + 1) = n := by
            rw [Nat.mod_eq_of_lt (by omega)]; omega
          rw [e] at this
          exact this (Finset.mem_insert_self _ _)
        have hQ : ∀ i ∈ s, i + 1 ∉ s := by
          intro i hi hi1
          have := hP i (Finset.mem_insert_of_mem hi)
          rw [Nat.mod_eq_of_lt (by have := hlt i hi; omega)] at this
          exact this (Finset.mem_insert_of_mem hi1)
        have hrange : ∀ x ∈ s, 1 ≤ x ∧ x + 2 ≤ n := by
          intro x hx
          have a1 := hlt x hx
          have a2 : x ≠ 0 := fun h => h0 (h ▸ hx)
          have a3 : x ≠ n - 1 := fun h => hn1 (h ▸ hx)
          omega
        refine ⟨s.image (fun x => x - 1), ⟨?_, ?_⟩, ?_⟩
        · intro y hy
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
          have := hrange x hx
          exact Finset.mem_range.mpr (by omega)
        · intro i hi hi1
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
          obtain ⟨x', hx', he⟩ := Finset.mem_image.mp hi1
          have a := hrange x hx
          have b := hrange x' hx'
          have : x' = x + 1 := by omega
          exact hQ x hx (this ▸ hx')
        · congr 1
          ext y
          simp only [Finset.mem_image]
          constructor
          · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
            have a := hrange x hx
            have : x - 1 + 1 = x := by omega
            rw [this]; exact hx
          · intro hy
            have a := hrange y hy
            exact ⟨y - 1, ⟨y, hy, rfl⟩, by omega⟩
      · rintro ⟨u, ⟨hu, hQ⟩, rfl⟩
        have hlt : ∀ x ∈ u, x + 2 < n := fun x hx => by
          have := Finset.mem_range.mp (hu hx); omega
        refine ⟨⟨u.image (fun x => x + 1), ?_, rfl⟩, ?_⟩
        · intro y hy
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
          have := hlt x hx
          exact Finset.mem_range.mpr (by omega)
        · intro i hi hmem
          rcases Finset.mem_insert.mp hi with rfl | hi
          · rw [Nat.mod_self] at hmem
            rcases Finset.mem_insert.mp hmem with h | h
            · omega
            · obtain ⟨x, _, hx⟩ := Finset.mem_image.mp h
              omega
          · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
            have a := hlt x hx
            rw [Nat.mod_eq_of_lt (by omega)] at hmem
            rcases Finset.mem_insert.mp hmem with h | h
            · omega
            · obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp h
              have : y = x + 1 := by omega
              exact hQ x hx (this ▸ hy)
    rw [h1, h2, (calc_card_no_adjacent_subsets_aux2 n).1, Finset.card_image_of_injOn,
      (calc_card_no_adjacent_subsets_aux2 (n - 2)).1]
    · rcases Nat.lt_or_ge n 2 with h | h
      · have : n = 1 := by omega
        subst this
        rfl
      · have : n - 2 + 2 = n := by omega
        rw [this]; ring
    · intro u hu u' hu' huu
      have hlt : ∀ v : Finset ℕ, v ∈ ((Finset.range (n - 2)).powerset.filter
          (fun t : Finset ℕ => ∀ i ∈ t, i + 1 ∉ t) : Finset (Finset ℕ)) →
          n ∉ v.image (fun x => x + 1) := by
        intro v hv hmem
        obtain ⟨x, hx, hxn⟩ := Finset.mem_image.mp hmem
        have := Finset.mem_range.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hv).1) hx)
        omega
      have h3 : insert n (u.image (fun x => x + 1)) = insert n (u'.image (fun x => x + 1)) := huu
      have h4 : u.image (fun x => x + 1) = u'.image (fun x => x + 1) := by
        rw [← Finset.erase_insert (hlt u hu), ← Finset.erase_insert (hlt u' hu'), h3]
      exact Finset.image_injective (fun a b hab => by simpa using hab) h4
  · rw [Finset.disjoint_left]
    intro t ht ht'
    have h1 := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ht').1
    have := Finset.mem_range.mp (h1 (Finset.mem_insert_self _ _))
    omega

theorem bld6_card_circular_no_adjacent_subsets (n : ℕ) : ((Finset.univ : Finset (Finset (Fin (n + 1)))).filter (fun s => ∀ i : Fin (n + 1), ∀ j : Fin (n + 1), i ∈ s → j ∈ s → ((i : ℕ) + 1) % (n + 1) ≠ (j : ℕ))).card = Nat.fib n + Nat.fib (n + 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · decide
  rw [← bld6_card_circular_no_adjacent_subsets_aux1 n hn]
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
    refine ⟨Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) ∈ t), ?_, ?_⟩
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

-- forge:entry bld6_abundant_two_mul_totient_lt kind=proved origin=conjecture
section
/- Uses Mathlib2.arith_sigma_mul_totient_lt_sq: 2n·φ(n) ≤ σ(n)·φ(n) < n^2 by the hypothesis and arith_sigma_mul_totient_lt_sq; cancel n > 0. So perfect and abundant numbers have φ(n) < n/2. -/
theorem bld6_abundant_two_mul_totient_lt (n : ℕ) (hn : 2 ≤ n) (h : 2 * n ≤ ArithmeticFunction.sigma 1 n) : 2 * n.totient < n := by
  have h1 := Mathlib2.arith_sigma_mul_totient_lt_sq n hn
  by_contra hc
  push_neg at hc
  have a : n * n ≤ n * (2 * n.totient) := Nat.mul_le_mul_left n hc
  have b : (2 * n) * n.totient ≤ ArithmeticFunction.sigma 1 n * n.totient := Nat.mul_le_mul_right _ h
  have c : n * (2 * n.totient) = (2 * n) * n.totient := by ring
  rw [sq] at h1
  omega
end

-- forge:entry bld6_card_involutions_even kind=proved origin=conjecture
section
/- Uses Mathlib2.calc_card_involutions_rec: two-step induction with I(m+2) = I(m+1) + (m+1)·I(m) from calc_card_involutions_rec; base cases I(2) = 2 and I(3) = I(2) + 2·I(1) = 4 (again from the recurrence, I(0) = I(1) = 1 by decide), and for m ≥ 2 both I(m+1) and I(m) are even. -/
theorem bld6_card_involutions_even (n : ℕ) : Even ((Finset.univ : Finset (Equiv.Perm (Fin (n + 2)))).filter (fun σ => σ * σ = 1)).card := by
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℕ, ∀ m, g m = ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter (fun σ => σ * σ = 1)).card := ⟨fun m => _, fun m => rfl⟩
  have rec' : ∀ m, g (m+2) = g (m+1) + (m+1) * g m := by
    intro m
    rw [hg, hg, hg]
    exact Mathlib2.calc_card_involutions_rec m
  have h0 : g 0 = 1 := by rw [hg]; decide
  have h1 : g 1 = 1 := by rw [hg]; decide
  have h2 : g 2 = 2 := by
    have := rec' 0
    simp only [zero_add] at this
    omega
  have h3 : g 3 = 4 := by
    have := rec' 1
    norm_num at this
    omega
  have key : ∀ m : ℕ, Even (g (m+2)) ∧ Even (g (m+2+1)) := by
    intro m
    induction m with
    | zero => exact ⟨by rw [h2]; decide, by rw [h3]; decide⟩
    | succ m ih =>
      refine ⟨by rw [show m+1+2 = m+2+1 by omega]; exact ih.2, ?_⟩
      rw [show m+1+2+1 = m+2+2 by omega, rec' (m+2)]
      exact ih.2.add (ih.1.mul_left _)
  rw [← hg]
  exact (key n).1
end

-- forge:entry bld6_nilpotent_max_index_iff_rank kind=proved origin=conjecture
section
/- Uses Mathlib2.bld5_nilpotent_max_index_rank and Mathlib2.bld4_nilpotent_corank_one_rank_pow: the forward direction is bld5_nilpotent_max_index_rank; conversely, if rank A + 1 = n then n ≥ 1 and bld4_nilpotent_corank_one_rank_pow with k = n - 1 gives rank(A^(n-1)) = 1, so A^(n-1) ≠ 0. -/
theorem bld6_nilpotent_max_index_iff_rank (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (hA : IsNilpotent A) : A ^ (Fintype.card ι - 1) ≠ 0 ↔ A.rank + 1 = Fintype.card ι := by
  constructor
  · exact Mathlib2.bld5_nilpotent_max_index_rank K ι A hA
  · intro hr h0
    have := Mathlib2.bld4_nilpotent_corank_one_rank_pow K ι A hA hr (Fintype.card ι - 1) (by omega)
    rw [h0, Matrix.rank_zero] at this
    omega
end

-- forge:entry bld6_nilpotent_rank_pow_succ_le_rank_sub kind=proved origin=conjecture
section
/- Uses Mathlib2.lib_matrix_rank_pow_succ_lt_of_isNilpotent_of_ne_zero: induction on k; if A^(k+1) = 0 then A^(k+2) = 0 has rank 0, otherwise the lib lemma gives rank(A^(k+2)) < rank(A^(k+1)) ≤ rank A - k with rank(A^(k+1)) > 0, so rank(A^(k+2)) ≤ rank A - (k+1). Sharpens Mathlib2.bld3_nilpotent_rank_pow_le (card ι - k) and reproves Mathlib2.bld5_nilpotent_pow_rank_succ_eq_zero at k = rank A. -/
theorem bld6_nilpotent_rank_pow_succ_le_rank_sub (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (hA : IsNilpotent A) (k : ℕ) : (A ^ (k + 1)).rank ≤ A.rank - k := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases h : A ^ (k+1) = 0
    · rw [pow_succ, h, zero_mul, Matrix.rank_zero]; exact Nat.zero_le _
    · have := Mathlib2.lib_matrix_rank_pow_succ_lt_of_isNilpotent_of_ne_zero K ι A hA (k+1) h
      omega
end

-- forge:entry bld6_rank_cube_sub_self_defect kind=proved origin=conjecture
section
/- Uses Mathlib2.bld3_rank_tripotent_defect and Mathlib2.bld2_rank_add_rank_one_sub: the idempotent-defect identity bld2_rank_add_rank_one_sub applied to A and to -A gives rank(A*A - A) = rank A + rank(A - 1) - n and rank(A*A + A) = rank A + rank(A + 1) - n (ranks invariant under negation); substitute both into bld3_rank_tripotent_defect: rank(A*A+A) + rank(A*A-A) = rank A + rank(A^3 - A). Corollary: A^3 = A iff rank A + rank(A-1) + rank(A+1) = 2n. -/
theorem bld6_rank_cube_sub_self_defect_aux1 {K : Type*} [Field K] {m n : Type*} [Fintype n] [DecidableEq n] (A : Matrix m n K) : (-A).rank = A.rank := by
  apply le_antisymm
  · have := Matrix.rank_mul_le_left A (-1 : Matrix n n K)
    simpa using this
  · have := Matrix.rank_mul_le_left (-A) (-1 : Matrix n n K)
    simpa using this

theorem bld6_rank_cube_sub_self_defect (K : Type*) [Field K] [CharZero K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) : A.rank + (A - 1).rank + (A + 1).rank = 2 * Fintype.card ι + (A * A * A - A).rank := by
  have h1 := Mathlib2.bld2_rank_add_rank_one_sub K ι A
  have h2 := Mathlib2.bld2_rank_add_rank_one_sub K ι (-A)
  have h3 := Mathlib2.bld3_rank_tripotent_defect K ι A
  have e1 : (1 - A).rank = (A - 1).rank := by rw [← bld6_rank_cube_sub_self_defect_aux1, neg_sub]
  have e2 : (A - A * A).rank = (A * A - A).rank := by rw [← bld6_rank_cube_sub_self_defect_aux1, neg_sub]
  have e3 : (1 - -A) = A + 1 := by rw [sub_neg_eq_add, add_comm]
  have e4 : (-A - -A * -A) = -(A * A + A) := by rw [neg_mul_neg]; abel
  rw [e1, e2] at h1
  rw [e3, e4, bld6_rank_cube_sub_self_defect_aux1, bld6_rank_cube_sub_self_defect_aux1] at h2
  omega
end

-- forge:entry bld6_real_nonneg_poly_root_sq_dvd kind=proved origin=conjecture
section
/- Uses Mathlib2.poly_real_nonneg_eq_sum_two_squares: write p = f^2 + g^2; evaluating at a gives f(a)^2 + g(a)^2 = 0, so f(a) = g(a) = 0, hence X - a divides both f and g (Polynomial.dvd_iff_isRoot) and (X - a)^2 divides f^2 + g^2. -/
theorem bld6_real_nonneg_poly_root_sq_dvd (p : Polynomial ℝ) (h : ∀ x : ℝ, 0 ≤ Polynomial.eval x p) (a : ℝ) (ha : Polynomial.eval a p = 0) : (Polynomial.X - Polynomial.C a) ^ 2 ∣ p := by
  obtain ⟨f, g, rfl⟩ := Mathlib2.poly_real_nonneg_eq_sum_two_squares p h
  simp only [Polynomial.eval_add, Polynomial.eval_pow] at ha
  have hf2 : Polynomial.eval a f ^ 2 = 0 := by
    nlinarith [sq_nonneg (Polynomial.eval a f), sq_nonneg (Polynomial.eval a g)]
  have hg2 : Polynomial.eval a g ^ 2 = 0 := by
    nlinarith [sq_nonneg (Polynomial.eval a f), sq_nonneg (Polynomial.eval a g)]
  have hf : Polynomial.eval a f = 0 := by simpa using hf2
  have hg : Polynomial.eval a g = 0 := by simpa using hg2
  have df : (Polynomial.X - Polynomial.C a) ∣ f := Polynomial.dvd_iff_isRoot.2 hf
  have dg : (Polynomial.X - Polynomial.C a) ∣ g := Polynomial.dvd_iff_isRoot.2 hg
  exact dvd_add (pow_dvd_pow_of_dvd df 2) (pow_dvd_pow_of_dvd dg 2)
end

-- forge:entry bld6_sum_fixed_points_sub_one_sq_perm kind=proved origin=conjecture
section
/- Uses Mathlib2.calc_sum_sq_card_fixed_points_perm and Mathlib2.calc_sum_card_fixed_points_perm: expand (X - 1)^2 = X^2 - 2X + 1 and sum over the n! permutations: 2·n! (second moment, calc_sum_sq_card_fixed_points_perm) - 2·n! (first moment, calc_sum_card_fixed_points_perm) + n! (Fintype.card_perm) — the number of fixed points of a random permutation has variance 1. -/
theorem bld6_sum_fixed_points_sub_one_sq_perm (n : ℕ) (hn : 2 ≤ n) : ∑ σ : Equiv.Perm (Fin n), (((Finset.univ.filter (fun i => σ i = i)).card : ℤ) - 1) ^ 2 = (n.factorial : ℤ) := by
  have h2 := Mathlib2.calc_sum_sq_card_fixed_points_perm n hn
  have h1 := Mathlib2.calc_sum_card_fixed_points_perm n (by omega)
  have e : ∀ σ : Equiv.Perm (Fin n), (((Finset.univ.filter (fun i => σ i = i)).card : ℤ) - 1) ^ 2 = (((Finset.univ.filter (fun i => σ i = i)).card ^ 2 : ℕ) : ℤ) - 2 * (((Finset.univ.filter (fun i => σ i = i)).card : ℕ) : ℤ) + 1 := by
    intro σ; push_cast; ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Nat.cast_sum, ← Finset.mul_sum, ← Nat.cast_sum, h2, h1]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast; ring
end

-- forge:entry bld6_card_image_two_fin_three kind=proved origin=conjecture
section
/- Uses Mathlib2.calc_card_surjective_fin_three: for n > 0 the image of f : Fin n → Fin 3 has 1, 2 or 3 elements; size 3 means surjective (3^n - 3·2^n + 3 functions by calc_card_surjective_fin_three), size 1 means constant (3 functions), and all functions number 3^n, so size 2 occurs 3^n - (3^n - 3·2^n + 3) - 3 = 3·2^n - 6 times. -/
theorem bld6_card_image_two_fin_three (n : ℕ) (hn : 0 < n) : ((Finset.univ : Finset (Fin n → Fin 3)).filter (fun f => (Finset.univ.image f).card = 2)).card = 3 * (2 ^ n - 2) := by
  haveI : NeZero n := ⟨by omega⟩
  have hS := Mathlib2.calc_card_surjective_fin_three n hn
  have hle : ∀ f : Fin n → Fin 3, (Finset.univ.image f).card ≤ 3 := fun f => by
    have := Finset.card_le_univ (Finset.univ.image f)
    simpa using this
  have hfib := Finset.card_eq_sum_card_fiberwise (f := fun f : Fin n → Fin 3 => (Finset.univ.image f).card) (s := Finset.univ) (t := Finset.range 4) (fun f _ => by
    simp only [Finset.coe_range, Set.mem_Iio]
    have := hle f
    omega)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at hfib
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hfib
  have h0 : (Finset.univ.filter (fun f : Fin n → Fin 3 => (Finset.univ.image f).card = 0)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro f _ h
    rw [Finset.card_eq_zero, Finset.image_eq_empty] at h
    exact Finset.univ_nonempty.ne_empty h
  have h1 : (Finset.univ.filter (fun f : Fin n → Fin 3 => (Finset.univ.image f).card = 1)).card = 3 := by
    have : Finset.univ.filter (fun f : Fin n → Fin 3 => (Finset.univ.image f).card = 1) = Finset.univ.image (fun c : Fin 3 => (fun _ : Fin n => c)) := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h
        obtain ⟨c, hc⟩ := Finset.card_eq_one.1 h
        refine ⟨c, ?_⟩
        funext i
        have : f i ∈ Finset.univ.image f := Finset.mem_image_of_mem f (Finset.mem_univ i)
        rw [hc, Finset.mem_singleton] at this
        exact this.symm
      · rintro ⟨c, rfl⟩
        rw [Finset.image_const Finset.univ_nonempty, Finset.card_singleton]
    rw [this, Finset.card_image_of_injective]
    · simp
    · intro c c' h
      exact congrFun h ⟨0, hn⟩
  have h3 : (Finset.univ.filter (fun f : Fin n → Fin 3 => (Finset.univ.image f).card = 3)) = Finset.univ.filter (fun f : Fin n → Fin 3 => Function.Surjective f) := by
    apply Finset.filter_congr
    intro f _
    constructor
    · intro h b
      have hu : Finset.univ.image f = Finset.univ := Finset.eq_univ_of_card _ (by simpa using h)
      have : b ∈ Finset.univ.image f := by rw [hu]; exact Finset.mem_univ b
      obtain ⟨a, -, ha⟩ := Finset.mem_image.1 this
      exact ⟨a, ha⟩
    · intro h
      rw [Finset.image_univ_of_surjective h]; simp
  rw [h0, h1, h3] at hfib
  have key := congrArg (Nat.cast : ℕ → ℤ) hfib
  push_cast at key
  rw [hS] at key
  have h2n : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  zify [h2n]
  linarith
end

-- forge:entry p6_kfib kind=definition origin=definition
section
/- k-Fibonacci number f_n for all integer n (f_0=0, f_1=1, f_{n+1}=k f_n+f_{n-1}), defined as the (0,1) entry of M^n, M=[[k,1],[1,0]], as in the paper's matrix formula -/
noncomputable def p6_kfib (k : ℤ) (n : ℤ) : ℤ := ((!![k, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) ^ n) 0 1
end

-- forge:entry gr_mantel_equality_compl_not_connected kind=proved origin=conjecture
section
/- The complement of an extremal triangle-free graph is disconnected — Uses Mathlib2.bld4_mantel_equality_complete_bipartite at step 1 to get s with 2|s| = n and Adj x y ↔ (x ∈ s ↔ y ∉ s); then Gᶜ has no edge between s and sᶜ; if n = 0 Connected fails by emptiness, otherwise both sides are nonempty and a Gᶜ-walk from s to sᶜ would need a crossing edge. -/
theorem gr_mantel_equality_compl_not_connected
    (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : G.CliqueFree 3)
    (he : 4 * G.edgeFinset.card = Fintype.card V ^ 2) : ¬ Gᶜ.Connected := by
  intro hc
  letI : Nonempty V := hc.nonempty
  obtain ⟨s, hs, hadj⟩ := bld4_mantel_equality_complete_bipartite V G h he
  have hn : 0 < Fintype.card V := Fintype.card_pos
  have hspos : 0 < s.card := by omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hspos
  have hex : ∃ w : V, w ∉ s := by
    by_contra hc'
    push_neg at hc'
    have hsu : s = Finset.univ := Finset.eq_univ_iff_forall.mpr hc'
    rw [hsu, Finset.card_univ] at hs
    omega
  obtain ⟨w, hw⟩ := hex
  have hstep : ∀ {x y : V}, Gᶜ.Adj x y → (x ∈ s ↔ y ∈ s) := by
    intro x y hxy
    have hnxy := ((SimpleGraph.compl_adj G x y).mp hxy).2
    have hiff := hadj x y
    tauto
  have hwalk : ∀ {x y : V}, Gᶜ.Walk x y → (x ∈ s ↔ y ∈ s) := by
    intro x y p
    induction p with
    | nil => rfl
    | cons hxy p ih => exact (hstep hxy).trans ih
  obtain ⟨p⟩ := hc.preconnected u w
  exact hw ((hwalk p).mp hu)
end

-- forge:entry gr_ramsey_three_four_le_ten kind=proved origin=conjecture
section
/- R(3,4) ≤ 10: every graph on at least 10 vertices has a triangle or an independent 4-set — pick v; if v has ≥ 4 neighbours, either two are adjacent (triangle with v) or 4 of them form an independent set; otherwise v has ≥ 6 non-neighbours, and Uses Mathlib2.r3_ramsey_three_three at this step on the induced graph on the non-neighbours: a triangle there is a triangle of G, an independent triple plus v is an independent 4-set. -/
theorem gr_ramsey_three_four_le_ten (V : Type) [Fintype V]
    (h : 10 ≤ Fintype.card V) (G : SimpleGraph V) :
    ¬ G.CliqueFree 3 ∨ ¬ Gᶜ.CliqueFree 4 := by
  classical
  by_contra! hbad
  obtain ⟨hG, hGc⟩ := hbad
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card V by omega)
  have hd : G.degree v ≤ 3 := by
    by_contra hn
    obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq
      (show 4 ≤ (G.neighborFinset v).card by
        rw [G.card_neighborFinset_eq_degree]
        omega)
    have hi : Gᶜ.IsClique (G.neighborSet v) :=
      (SimpleGraph.isClique_compl G).mpr (G.isIndepSet_neighborSet_of_triangleFree hG v)
    apply hGc s
    refine ⟨hi.subset ?_, hcard⟩
    intro x hx
    exact (G.mem_neighborFinset v x).mp (hs hx)
  let N : Set V := Gᶜ.neighborSet v
  let H : SimpleGraph N := G.induce N
  have hN : 6 ≤ Fintype.card N := by
    change 6 ≤ Fintype.card (Gᶜ.neighborSet v)
    rw [SimpleGraph.card_neighborSet_eq_degree, G.degree_compl]
    omega
  rcases Mathlib2.r3_ramsey_three_three N hN H with htri | hind
  · exact htri (hG.comap (SimpleGraph.Embedding.induce N).isContained)
  · obtain ⟨s, hs⟩ : ∃ s, Hᶜ.IsNClique 3 s := by
      simpa only [SimpleGraph.CliqueFree, not_forall, Classical.not_not] using hind
    let e : Hᶜ ↪g Gᶜ :=
      SimpleGraph.Embedding.complEquiv (SimpleGraph.Embedding.induce N)
    have hc : Gᶜ.IsNClique 3 (s.map e.toEmbedding) := by
      refine ⟨?_, by simpa only [Finset.card_map] using hs.card_eq⟩
      intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
      exact e.map_adj_iff.mpr (hs.isClique ha hb (fun hab => hxy (congrArg e hab)))
    apply hGc (insert v (s.map e.toEmbedding))
    apply hc.insert
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    exact a.property
end

-- forge:entry gr_triangle_free_regular_half_colorable_two kind=proved origin=conjecture
section
/- A triangle-free n/2-regular graph is bipartite — the handshake lemma gives 2e = n·d so 4e = n²; then Uses Mathlib2.bld3_mantel_equality_colorable_two at the final step. -/
theorem gr_triangle_free_regular_half_colorable_two (V : Type) [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (h : G.CliqueFree 3) (hr : G.IsRegularOfDegree d)
    (hd : 2 * d = Fintype.card V) : G.Colorable 2 := by
  apply bld3_mantel_equality_colorable_two V G h
  have hs : Fintype.card V * d = 2 * G.edgeFinset.card := by
    simpa only [hr.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul]
      using G.sum_degrees_eq_twice_card_edges
  rw [← hd] at hs ⊢
  nlinarith
end

-- forge:entry gr_bipartite_extremal_complete kind=proved origin=conjecture
section
/- A properly 2-coloured graph with n²/4 edges is complete between its colour classes — a Bool-coloured graph is triangle-free, so Uses Mathlib2.bld4_mantel_equality_complete_bipartite at step 2 to get G = complete bipartite on (s, sᶜ) with both sides nonempty; this graph is connected, so the colouring C must be constant on s and on sᶜ with different values, whence C x ≠ C y forces x,y on opposite sides (alternatively count: e ≤ a·b ≤ n²/4 with equality only if all cross pairs are edges, cf. Mathlib2.comb_card_edgeFinset_le_of_coloring_bool). -/
theorem gr_bipartite_extremal_complete (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : G.Coloring Bool)
    (he : 4 * G.edgeFinset.card = Fintype.card V ^ 2)
    (x y : V) (hxy : C x ≠ C y) : G.Adj x y := by
  have hc : G.Colorable 2 := by
    simpa using C.colorable
  have hG : G.CliqueFree 3 := hc.cliqueFree (by norm_num)
  by_contra hnot
  have hreg := bld2_mantel_equality_regular V G hG he x
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨x⟩
  have hdeg : 0 < (G.neighborFinset x).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hdeg
  have hxz : G.Adj x z := (SimpleGraph.mem_neighborFinset _ _ _).mp hz
  have hyz : G.Adj y z :=
    (bld3_mantel_equality_same_neighbors V G hG he x y hnot z).mp hxz
  have hcxz := C.valid hxz
  have hcyz := C.valid hyz
  cases hcx : C x <;> cases hcy : C y <;> cases hcz : C z <;> simp_all
end

-- forge:entry gr_mantel_equality_dist_le_two kind=proved origin=conjecture
section
/- An extremal triangle-free graph has diameter at most 2 — Uses Mathlib2.bld4_mantel_equality_complete_bipartite at step 1 to get the balanced bipartition s; x,y on opposite sides are adjacent (dist ≤ 1); on the same side pick z on the other side (nonempty since 2|s| = n ≥ 1) and use the walk x-z-y with SimpleGraph.dist_le. -/
theorem gr_mantel_equality_dist_le_two (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.CliqueFree 3)
    (he : 4 * G.edgeFinset.card = Fintype.card V ^ 2) (x y : V) : G.dist x y ≤ 2 := by
  obtain ⟨s, hs, hadj⟩ := bld4_mantel_equality_complete_bipartite V G h he
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨x⟩
  have hspos : 0 < s.card := by omega
  have hscpos : 0 < (sᶜ).card := by
    rw [Finset.card_compl]
    omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hspos
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hscpos
  have hv' : v ∉ s := Finset.mem_compl.mp hv
  by_cases hxy : G.Adj x y
  · rw [SimpleGraph.dist_eq_one_iff_adj.mpr hxy]
    decide
  · have hsame : x ∈ s ↔ y ∈ s := by
      have := hadj x y
      tauto
    by_cases hx : x ∈ s
    · have hy : y ∈ s := hsame.mp hx
      have hxv : G.Adj x v := (hadj x v).mpr (by tauto)
      have hvy : G.Adj v y := (hadj v y).mpr (by tauto)
      simpa using SimpleGraph.dist_le
        (SimpleGraph.Walk.cons hxv (SimpleGraph.Walk.cons hvy SimpleGraph.Walk.nil))
    · have hy : y ∉ s := by tauto
      have hxu : G.Adj x u := (hadj x u).mpr (by tauto)
      have huy : G.Adj u y := (hadj u y).mpr (by tauto)
      simpa using SimpleGraph.dist_le
        (SimpleGraph.Walk.cons hxu (SimpleGraph.Walk.cons huy SimpleGraph.Walk.nil))
end

end Mathlib2
