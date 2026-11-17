/- Mathlib2 分片 24（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0001
import Mathlib2.Shard.S0008
import Mathlib2.Shard.S0010
import Mathlib2.Shard.S0012
import Mathlib2.Shard.S0013
import Mathlib2.Shard.S0015
import Mathlib2.Shard.S0016
import Mathlib2.Shard.S0017
import Mathlib2.Shard.S0020
import Mathlib2.Shard.S0021
import Mathlib2.Shard.S0022
import Mathlib2.Shard.S0023
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry p5_cited_squares kind=proved origin=paper
section
/- Cited result (Dimitrov 2023): phi^2+psi^2+sigma^2 >= 3n^2+2n+3 for n >= 2. -/
theorem p5_cited_squares_aux1 (n x y z : ℕ) (hn : 2 ≤ n) (hy : n + 1 ≤ y) (hz : n + 1 ≤ z) (hxy : 2 * n ≤ x + y) (hxz : 2 * n ≤ x + z) : 3 * n ^ 2 + 2 * n + 3 ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
  wlog hyz : y ≤ z generalizing y z
  · have h := this z y hz hy hxz hxy (by omega)
    calc 3 * n ^ 2 + 2 * n + 3 ≤ x ^ 2 + z ^ 2 + y ^ 2 := h
      _ = x ^ 2 + y ^ 2 + z ^ 2 := by ring
  have h1 : x ^ 2 + y ^ 2 + y ^ 2 ≤ x ^ 2 + y ^ 2 + z ^ 2 := by gcongr
  refine le_trans ?_ h1
  rcases le_or_gt (2 * n) y with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, y = 2 * (k + 2) + s := ⟨y - 2 * (k + 2), by omega⟩
    calc 3 * (k + 2) ^ 2 + 2 * (k + 2) + 3 ≤ 3 * (k + 2) ^ 2 + 2 * (k + 2) + 3 + (5 * k^2 + 8 * k * s + 18 * k + 2 * s^2 + 16 * s + 1 * x^2 + 13) := Nat.le_add_right _ _
      _ = x ^ 2 + (2 * (k + 2) + s) ^ 2 + (2 * (k + 2) + s) ^ 2 := by ring
  · obtain ⟨s, rfl⟩ : ∃ s, y = n + 1 + s := ⟨y - (n + 1), by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = s + 2 + k := ⟨n - (s + 2), by omega⟩
    obtain ⟨r, rfl⟩ : ∃ r, x = k + 1 + r := ⟨x - (k + 1), by omega⟩
    calc 3 * (s + 2 + k) ^ 2 + 2 * (s + 2 + k) + 3 ≤ 3 * (s + 2 + k) ^ 2 + 2 * (s + 2 + k) + 3 + (2 * k * s + 2 * k * r + 5 * s^2 + 10 * s + 1 * r^2 + 2 * r) := Nat.le_add_right _ _
      _ = (k + 1 + r) ^ 2 + (s + 2 + k + 1 + s) ^ 2 + (s + 2 + k + 1 + s) ^ 2 := by ring

theorem p5_cited_squares (n : ℕ) (hn : 2 ≤ n) : 3 * n ^ 2 + 2 * n + 3 ≤ n.totient ^ 2 + p5_dedekind_psi n ^ 2 + ArithmeticFunction.sigma 1 n ^ 2 :=
  p5_cited_squares_aux1 n _ _ _ hn (Mathlib2.p5_psi_ge_succ n hn) (Mathlib2.p5_sigma_ge_succ n hn) (Mathlib2.p5_lemma1 n hn) (Mathlib2.p5_lemma2 n hn)
end

-- forge:entry p5_cited_products kind=proved origin=paper
section
/- Cited result (Dimitrov 2023): phi psi + phi sigma + sigma psi >= 3n^2+2n-1 for n >= 2 (the -1 moved across). -/
theorem p5_cited_products_aux1 (n x y z : ℕ) (hn : 2 ≤ n) (hy : n + 1 ≤ y) (hz : n + 1 ≤ z) (hxy : 2 * n ≤ x + y) (hxz : 2 * n ≤ x + z) : 3 * n ^ 2 + 2 * n ≤ x * y + x * z + z * y + 1 := by
  wlog hyz : y ≤ z generalizing y z
  · have h := this z y hz hy hxz hxy (by omega)
    calc 3 * n ^ 2 + 2 * n ≤ x * z + x * y + y * z + 1 := h
      _ = x * y + x * z + z * y + 1 := by ring
  have h1 : x * y + x * y + y * y + 1 ≤ x * y + x * z + z * y + 1 := by gcongr
  refine le_trans ?_ h1
  rcases le_or_gt (2 * n) y with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, y = 2 * (k + 2) + s := ⟨y - 2 * (k + 2), by omega⟩
    calc 3 * (k + 2) ^ 2 + 2 * (k + 2) ≤ 3 * (k + 2) ^ 2 + 2 * (k + 2) + (1 * k^2 + 4 * k * s + 4 * k * x + 2 * k + 1 * s^2 + 2 * s * x + 8 * s + 8 * x + 1) := Nat.le_add_right _ _
      _ = x * (2 * (k + 2) + s) + x * (2 * (k + 2) + s) + (2 * (k + 2) + s) * (2 * (k + 2) + s) + 1 := by ring
  · obtain ⟨s, rfl⟩ : ∃ s, y = n + 1 + s := ⟨y - (n + 1), by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = s + 2 + k := ⟨n - (s + 2), by omega⟩
    obtain ⟨r, rfl⟩ : ∃ r, x = k + 1 + r := ⟨x - (k + 1), by omega⟩
    calc 3 * (s + 2 + k) ^ 2 + 2 * (s + 2 + k) ≤ 3 * (s + 2 + k) ^ 2 + 2 * (s + 2 + k) + (2 * k * s + 2 * k * r + 1 * s^2 + 4 * s * r + 2 * s + 6 * r) := Nat.le_add_right _ _
      _ = (k + 1 + r) * (s + 2 + k + 1 + s) + (k + 1 + r) * (s + 2 + k + 1 + s) + (s + 2 + k + 1 + s) * (s + 2 + k + 1 + s) + 1 := by ring

theorem p5_cited_products (n : ℕ) (hn : 2 ≤ n) : 3 * n ^ 2 + 2 * n ≤ n.totient * p5_dedekind_psi n + n.totient * ArithmeticFunction.sigma 1 n + ArithmeticFunction.sigma 1 n * p5_dedekind_psi n + 1 :=
  p5_cited_products_aux1 n _ _ _ hn (Mathlib2.p5_psi_ge_succ n hn) (Mathlib2.p5_sigma_ge_succ n hn) (Mathlib2.p5_lemma1 n hn) (Mathlib2.p5_lemma2 n hn)
end

-- forge:entry bld4_sqrt_two_rec_defect_tsum_lower kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_sqrt_two_rec_defect_summable, Mathlib2.ana_sqrt_two_rec_closed_form and Mathlib2.ana_sin_ge_cubic_of_nonneg: termwise 2 − a_n ≥ π^2/4^(n+1) − π^4/(192·16^n) (closed form + cubic sine bound, as in the pointwise estimate). The right side is a difference of geometric series with sum π^2/3 − π^4/180; bld2_sqrt_two_rec_defect_summable supplies summability of the left side so tsum comparison (hasSum_le / tsum_le_tsum) applies. Improves the bound 8/3 of bld3_sqrt_two_rec_defect_tsum_bounds. -/
theorem bld4_sqrt_two_rec_defect_tsum_lower_aux1 (n : ℕ) : Real.pi ^ 2 / 4 ^ (n + 1) - Real.pi ^ 4 / (192 * 16 ^ n) ≤ 2 - 2 * Real.cos (Real.pi / 2 ^ (n + 1)) := by
  have hp : (0:ℝ) < 2 ^ n := by positivity
  have hp1 : (1:ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have h4 : (4:ℝ) ^ n = (2 ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h16 : (16:ℝ) ^ n = (2 ^ n) ^ 4 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  set p : ℝ := 2 ^ n with hpdef
  set x : ℝ := Real.pi / (4 * p) with hxdef
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_le_four
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    rw [hxdef, div_le_one (by positivity)]; nlinarith
  have harg : Real.pi / 2 ^ (n + 1) = 2 * x := by
    rw [hxdef, pow_succ]; field_simp; ring
  have hsin := ana_sin_ge_cubic_of_nonneg x hx0
  have hy0 : 0 ≤ x - x ^ 3 / 6 := by nlinarith [mul_nonneg hx0 (sq_nonneg x)]
  have hsq : (x - x ^ 3 / 6) ^ 2 ≤ Real.sin x ^ 2 := pow_le_pow_left₀ hy0 hsin 2
  have hcs := Real.sin_sq_add_cos_sq x
  have e1 : Real.pi ^ 2 / 4 ^ (n + 1) = 4 * x ^ 2 := by
    rw [pow_succ (4:ℝ) n, h4, hxdef]; field_simp
  have e2 : Real.pi ^ 4 / (192 * 16 ^ n) = 4 * x ^ 4 / 3 := by
    rw [h16, hxdef]; field_simp; ring
  rw [harg, Real.cos_two_mul, e1, e2]
  nlinarith [pow_nonneg hx0 6]

theorem bld4_sqrt_two_rec_defect_tsum_lower (a : ℕ → ℝ) (h0 : a 0 = 0) (h : ∀ n : ℕ, a (n + 1) = Real.sqrt (2 + a n)) : Real.pi ^ 2 / 3 - Real.pi ^ 4 / 180 ≤ ∑' n : ℕ, (2 - a n) := by
  have hsum := bld2_sqrt_two_rec_defect_summable a h0 h
  have hg4 : HasSum (fun n : ℕ => ((1:ℝ) / 4) ^ n) (1 - 1 / 4)⁻¹ :=
    hasSum_geometric_of_lt_one (by norm_num) (by norm_num)
  have hg16 : HasSum (fun n : ℕ => ((1:ℝ) / 16) ^ n) (1 - 1 / 16)⁻¹ :=
    hasSum_geometric_of_lt_one (by norm_num) (by norm_num)
  have hs := (hg4.mul_left (Real.pi ^ 2 / 4)).sub (hg16.mul_left (Real.pi ^ 4 / 192))
  have hlow : ∀ n : ℕ, Real.pi ^ 2 / 4 * ((1:ℝ) / 4) ^ n - Real.pi ^ 4 / 192 * ((1:ℝ) / 16) ^ n ≤ 2 - a n := by
    intro n
    rw [ana_sqrt_two_rec_closed_form a h0 h n]
    refine le_trans (le_of_eq ?_) (bld4_sqrt_two_rec_defect_tsum_lower_aux1 n)
    rw [one_div, one_div, inv_pow, inv_pow, pow_succ (4:ℝ) n]; field_simp
  have := hasSum_le hlow hs hsum.hasSum
  refine le_trans (le_of_eq ?_) this
  norm_num; ring
end

-- forge:entry bld4_sqrt_two_rec_defect_lower kind=proved origin=conjecture
section
/- Uses Mathlib2.ana_sqrt_two_rec_closed_form and Mathlib2.ana_sin_ge_cubic_of_nonneg: the closed form gives 2 − a_n = 2 − 2cos(2θ) = 4 sin^2 θ with θ = π/2^(n+2). ana_sin_ge_cubic_of_nonneg gives sin θ ≥ θ − θ^3/6 ≥ 0, so 4 sin^2 θ ≥ 4θ^2(1 − θ^2/6)^2 ≥ 4θ^2 − 4θ^4/3, which is the stated bound (matching upper bound: bld_sqrt_two_rec_rate). -/
theorem bld4_sqrt_two_rec_defect_lower (a : ℕ → ℝ) (h0 : a 0 = 0) (h : ∀ n : ℕ, a (n + 1) = Real.sqrt (2 + a n)) (n : ℕ) : Real.pi ^ 2 / 4 ^ (n + 1) - Real.pi ^ 4 / (192 * 16 ^ n) ≤ 2 - a n := by
  rw [ana_sqrt_two_rec_closed_form a h0 h n]
  exact bld4_sqrt_two_rec_defect_tsum_lower_aux1 n
end

-- forge:entry bld4_pisano_prime_dvd_two_mul_succ_of_not_isSquare_five kind=proved origin=conjecture
section
/- Uses Mathlib2.p3_aux_fib_prime, Mathlib2.lib_fib_period_iff and Mathlib2.bld3_pisano_dvd_of_period: p ≠ 2, 5 since 5 is a square there; Euler's criterion gives 5^(p/2) = −1, so p3_aux_fib_prime yields F_p ≡ −1, F_{p+1} ≡ 0, hence F_{p+2} ≡ −1 mod p. By Nat.fib_add, F_{2p+2} ≡ 0 and F_{2p+3} ≡ F_{p+2}^2 ≡ 1, so lib_fib_period_iff makes 2(p+1) a period and bld3_pisano_dvd_of_period concludes. -/
theorem bld4_pisano_prime_dvd_two_mul_succ_of_not_isSquare_five (p : ℕ) [Fact p.Prime] (h : ¬ IsSquare (5 : ZMod p)) : p3_pisano p ∣ 2 * (p + 1) := by
  have hp : p.Prime := Fact.out
  have h5 : (5 : ZMod p) ≠ 0 := by
    intro h0
    exact h ⟨0, by simp [h0]⟩
  have hp2 : p ≠ 2 := by
    have key : (5 : ZMod 2) = 1 * 1 := by decide
    rintro rfl
    exact h ⟨1, key⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp this)
  have he : (5 : ZMod p) ^ (p / 2) = -1 := by
    rcases ZMod.pow_div_two_eq_neg_one_or_one p h5 with h1 | h1
    · exact absurd ((ZMod.euler_criterion p h5).mpr h1) h
    · exact h1
  obtain ⟨hA, hB⟩ := p3_aux_fib_prime p hp hp2
  have hA' := (ZMod.intCast_eq_intCast_iff _ _ p).mpr hA
  have hB' := (ZMod.intCast_eq_intCast_iff _ _ p).mpr hB
  push_cast at hA' hB'
  rw [he] at hB'
  rw [hB'] at hA'
  have hb : ((Nat.fib (p + 1) : ℕ) : ZMod p) = 0 := by
    have : (2 : ZMod p) * ((Nat.fib (p + 1) : ℕ) : ZMod p) = 2 * 0 := by
      linear_combination hA'
    exact mul_left_cancel₀ h2 this
  have hc : ((Nat.fib (p + 2) : ℕ) : ZMod p) = -1 := by
    rw [Nat.fib_add_two]; push_cast; rw [hb, hB']; ring
  apply bld3_pisano_dvd_of_period
  rw [lib_fib_period_iff]
  refine ⟨?_, ?_⟩
  · rw [← ZMod.natCast_eq_natCast_iff]
    rw [show 2 * (p + 1) = (p + 1) + p + 1 by ring, Nat.fib_add]
    push_cast
    rw [hb]; ring
  · rw [← ZMod.natCast_eq_natCast_iff]
    rw [show 2 * (p + 1) + 1 = (p + 1) + (p + 1) + 1 by ring, Nat.fib_add]
    push_cast
    rw [hb, hc]; ring
end

-- forge:entry bld4_rat_sum_two_squares_iff_nat kind=proved origin=conjecture
section
/- Uses Mathlib2.bld3_rat_sq_add_sq_ne_of_odd_padicValNat: (⇐) is a cast. (⇒) by Mathlib's Nat.eq_sq_add_sq_iff it suffices that padicValNat q n is even for every prime q ≡ 3 mod 4; if it were odd, bld3_rat_sq_add_sq_ne_of_odd_padicValNat would contradict the rational representation. -/
theorem bld4_rat_sum_two_squares_iff_nat (n : ℕ) : (∃ x y : ℚ, x ^ 2 + y ^ 2 = (n : ℚ)) ↔ ∃ a b : ℕ, n = a ^ 2 + b ^ 2 := by
  constructor
  · rintro ⟨x, y, hxy⟩
    rw [Nat.eq_sq_add_sq_iff]
    intro q hq hq4
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    exact bld3_rat_sq_add_sq_ne_of_odd_padicValNat q n (Nat.prime_of_mem_primeFactors hq) hq4 hodd x y hxy
  · rintro ⟨a, b, hab⟩
    exact ⟨a, b, by rw [hab]; push_cast; ring⟩
end

-- forge:entry bld4_rat_sq_add_sq_eq_mul_sq_trivial kind=proved origin=conjecture
section
/- Uses Mathlib2.bld3_rat_sq_add_sq_ne_of_odd_padicValNat: if z ≠ 0 then (x/z)^2 + (y/z)^2 = n, contradicting bld3_rat_sq_add_sq_ne_of_odd_padicValNat; so z = 0, and then x^2 + y^2 = 0 in ℚ forces x = y = 0. -/
theorem bld4_rat_sq_add_sq_eq_mul_sq_trivial (p n : ℕ) (hp : p.Prime) (hp3 : p % 4 = 3) (hodd : Odd (padicValNat p n)) (x y z : ℚ) (h : x ^ 2 + y ^ 2 = (n : ℚ) * z ^ 2) : x = 0 ∧ y = 0 ∧ z = 0 := by
  have hz : z = 0 := by
    by_contra hz
    refine bld3_rat_sq_add_sq_ne_of_odd_padicValNat p n hp hp3 hodd (x / z) (y / z) ?_
    rw [div_pow, div_pow, ← add_div, h]
    field_simp
  subst hz
  have h' : x ^ 2 + y ^ 2 = 0 := by rw [h]; ring
  refine ⟨?_, ?_, rfl⟩ <;> nlinarith [sq_nonneg x, sq_nonneg y]
end

-- forge:entry bld4_permMatrix_involution_rank_fixed_points kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_involution_trace_rank: the permutation matrix P of an involution satisfies P * P = 1 (Matrix.permMatrix_mul), so bld_involution_trace_rank gives tr P + n = 2 rank(1 + P) in K; tr P is the number of fixed points of σ (diagonal entries are 1 or 0), and Nat.cast injectivity in characteristic 0 gives the identity in ℕ. -/
theorem bld4_permMatrix_involution_rank_fixed_points (K : Type*) [Field K] [CharZero K] (ι : Type*) [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) (hσ : σ * σ = 1) : 2 * (1 + σ.permMatrix K).rank = Fintype.card ι + (Finset.univ.filter (fun i : ι => σ i = i)).card := by
  have hPP : σ.permMatrix K * σ.permMatrix K = 1 := by
    have h2 : σ.trans σ = Equiv.refl ι := by
      ext i
      have := congrArg (fun τ : Equiv.Perm ι => τ i) hσ
      simpa using this
    unfold Equiv.Perm.permMatrix
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, h2, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  have h := bld_involution_trace_rank K ι (σ.permMatrix K) hPP
  have htr : Matrix.trace (σ.permMatrix K) = ((Finset.univ.filter (fun i : ι => σ i = i)).card : K) := by
    rw [Matrix.trace, ← Finset.sum_boole]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, eq_comm]
  rw [htr] at h
  have : ((2 * (1 + σ.permMatrix K).rank : ℕ) : K) = ((Fintype.card ι + (Finset.univ.filter (fun i : ι => σ i = i)).card : ℕ) : K) := by
    push_cast
    rw [← h]; ring
  exact_mod_cast this
end

-- forge:entry bld4_prime_dvd_fib_pred_mul_fib_mul_fib_succ kind=proved origin=conjecture
section
/- Uses Mathlib2.p3_aux_fib_prime and Mathlib2.an_cassini_int: p = 2 and p = 5 by computation (F_3 = 2, F_5 = 5). Otherwise p3_aux_fib_prime gives F_p ≡ 5^(p/2), so F_p^2 ≡ 5^(p−1) ≡ 1 mod p by Fermat; an_cassini_int at n = p − 1 gives F_{p+1} F_{p−1} = F_p^2 + (−1)^p = F_p^2 − 1 ≡ 0 mod p. -/
theorem bld4_prime_dvd_fib_pred_mul_fib_mul_fib_succ (p : ℕ) (hp : p.Prime) : p ∣ Nat.fib (p - 1) * Nat.fib p * Nat.fib (p + 1) := by
  by_cases hp2 : p = 2
  · subst hp2; decide
  by_cases hp5 : p = 5
  · subst hp5; decide
  haveI : Fact p.Prime := ⟨hp⟩
  have h5 : (5 : ZMod p) ≠ 0 := by
    intro h0
    have : ((5 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp this)
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  obtain ⟨_, hB⟩ := p3_aux_fib_prime p hp hp2
  have hB' := (ZMod.intCast_eq_intCast_iff _ _ p).mpr hB
  push_cast at hB'
  have hsq : ((Nat.fib p : ℕ) : ZMod p) ^ 2 = 1 := by
    rw [hB', ← pow_mul]
    have : p / 2 * 2 = p - 1 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    rw [this]
    exact ZMod.pow_card_sub_one_eq_one h5
  have hC := an_cassini_int (p - 1)
  have e1 : p - 1 + 2 = p + 1 := by have := hp.two_le; omega
  have e2 : p - 1 + 1 = p := by have := hp.two_le; omega
  rw [e1, e2, hodd.neg_one_pow] at hC
  have hC' := congrArg (fun x : ℤ => (x : ZMod p)) hC
  push_cast at hC'
  rw [hsq] at hC'
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  linear_combination ((Nat.fib p : ℕ) : ZMod p) * hC'
end

-- forge:entry bld4_rank_pow_eq_of_card_le kind=proved origin=conjecture
section
/- Uses Mathlib2.bld3_rank_pow_card_stabilizes and Mathlib2.bld2_rank_pow_convex: induct on j showing rank A^(j+1) = rank A^j for j ≥ n. Base case is bld3_rank_pow_card_stabilizes; for the step, bld2_rank_pow_convex gives 2 r_{j+1} ≤ r_j + r_{j+2} = r_{j+1} + r_{j+2}, so r_{j+2} ≥ r_{j+1}, and r_{j+2} ≤ r_{j+1} by Matrix.rank_mul_le_left. -/
theorem bld4_rank_pow_eq_of_card_le (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (j : ℕ) (hj : Fintype.card ι ≤ j) : (A ^ j).rank = (A ^ Fintype.card ι).rank := by
  have key : ∀ d : ℕ, (A ^ (Fintype.card ι + d + 1)).rank = (A ^ (Fintype.card ι + d)).rank := by
    intro d
    induction d with
    | zero => exact bld3_rank_pow_card_stabilizes K ι A
    | succ d ih =>
      have h1 := bld2_rank_pow_convex K ι A (Fintype.card ι + d)
      have h2 : (A ^ (Fintype.card ι + d + 2)).rank ≤ (A ^ (Fintype.card ι + d + 1)).rank := by
        rw [pow_succ]; exact Matrix.rank_mul_le_left _ _
      have e : Fintype.card ι + (d + 1) + 1 = Fintype.card ι + d + 2 := by ring
      have e' : Fintype.card ι + (d + 1) = Fintype.card ι + d + 1 := by ring
      rw [e, e']
      omega
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  induction d with
  | zero => rfl
  | succ d ih => rw [← add_assoc, key d]; exact ih (Nat.le_add_right _ _)
end

-- forge:entry p5_cited_atanassov kind=proved origin=paper
section
/- Cited result (Atanassov 2013): phi psi sigma >= n^3+n^2-n-1 for n >= 2 (subtractions moved across). -/
theorem p5_cited_atanassov (n : ℕ) (hn : 2 ≤ n) : n ^ 3 + n ^ 2 ≤ n.totient * p5_dedekind_psi n * ArithmeticFunction.sigma 1 n + n + 1 := by
  induction n using induction_on_primes with
  | zero => omega
  | one => omega
  | prime_mul p a hp ih =>
    have hp2 := hp.two_le
    have hsp : ArithmeticFunction.sigma 1 p = p + 1 := by
      rw [ArithmeticFunction.sigma_one_apply, hp.divisors, Finset.sum_pair hp.ne_one.symm]
      omega
    have hpsp : p5_dedekind_psi p = p + 1 := by
      have := Mathlib2.p5_psi_prime_pow p 0 hp
      simpa using this
    rcases Nat.lt_or_ge a 2 with ha | ha
    · interval_cases a
      · omega
      · rw [mul_one, hsp, hpsp, Nat.totient_prime hp]
        obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        exact le_of_eq (by ring)
    · have ih' := ih ha
      by_cases hd : p ∣ a
      · have hs := Mathlib2.p5_sigma_prime_mul_of_dvd p a hp hd (by omega)
        rw [Mathlib2.p5_psi_prime_mul_of_dvd p a hp hd (by omega), Nat.totient_mul_of_prime_of_dvd hp hd]
        have hx : 1 ≤ a.totient := Nat.totient_pos.2 (by omega)
        have hy := Mathlib2.p5_psi_ge_succ a ha
        have hpa : p ≤ a := Nat.le_of_dvd (by omega) hd
        generalize a.totient = x at *
        generalize p5_dedekind_psi a = y at *
        generalize ArithmeticFunction.sigma 1 (p * a) = z' at *
        generalize ArithmeticFunction.sigma 1 a = z at *
        obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
        obtain ⟨c, rfl⟩ : ∃ c, a = q + 2 + c := ⟨a - (q + 2), by omega⟩
        have e : (q + 2 + c) ^ 3 + (q + 2 + c) ^ 2 = (q + c + 1) * (q + c + 3) ^ 2 + (q + 2 + c) + 1 := by ring
        have hw : (q + c + 1) * (q + c + 3) ^ 2 ≤ x * y * z := by linarith
        have hxy : 1 ≤ x * y := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
        have hz' : (q + 2) * z + 1 ≤ z' := hs
        calc ((q + 2) * (q + 2 + c)) ^ 3 + ((q + 2) * (q + 2 + c)) ^ 2
            ≤ ((q + 2) * (q + 2 + c)) ^ 3 + ((q + 2) * (q + 2 + c)) ^ 2 + (1 * q^5 + 2 * q^4 * c + 8 * q^4 + 1 * q^3 * c^2 + 13 * q^3 * c + 23 * q^3 + 5 * q^2 * c^2 + 30 * q^2 * c + 28 * q^2 + 8 * q * c^2 + 29 * q * c + 12 * q + 4 * c^2 + 10 * c + 1) := Nat.le_add_right _ _
          _ = (q + 2) ^ 3 * ((q + c + 1) * (q + c + 3) ^ 2) + (q + 2) ^ 2 * 1 + (q + 2) * (q + 2 + c) + 1 := by ring
          _ ≤ (q + 2) ^ 3 * (x * y * z) + (q + 2) ^ 2 * (x * y) + (q + 2) * (q + 2 + c) + 1 := by gcongr
          _ = (q + 2) * x * ((q + 2) * y) * ((q + 2) * z + 1) + (q + 2) * (q + 2 + c) + 1 := by ring
          _ ≤ (q + 2) * x * ((q + 2) * y) * z' + (q + 2) * (q + 2 + c) + 1 := by gcongr
      · rw [Mathlib2.p5_psi_ge_succ_aux1 p a hp hd, Nat.totient_mul_of_prime_of_not_dvd hp hd,
          ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime ((Nat.Prime.coprime_iff_not_dvd hp).2 hd), hsp]
        generalize a.totient = x at *
        generalize p5_dedekind_psi a = y at *
        generalize ArithmeticFunction.sigma 1 a = z at *
        obtain ⟨q, hq⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
        have hq1 : p - 1 = q + 1 := by omega
        rw [hq1]
        subst hq
        obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
        have e : (b + 2) ^ 3 + (b + 2) ^ 2 = (b + 1) * (b + 3) ^ 2 + (b + 2) + 1 := by ring
        have hw : (b + 1) * (b + 3) ^ 2 ≤ x * y * z := by linarith
        calc ((q + 2) * (b + 2)) ^ 3 + ((q + 2) * (b + 2)) ^ 2
            ≤ ((q + 2) * (b + 2)) ^ 3 + ((q + 2) * (b + 2)) ^ 2 + (1 * q^3 * b^2 + 3 * q^3 * b + 1 * q^3 + 1 * q^2 * b^3 + 12 * q^2 * b^2 + 29 * q^2 * b + 11 * q^2 + 3 * q * b^3 + 29 * q * b^2 + 66 * q * b + 25 * q + 1 * b^3 + 11 * b^2 + 25 * b + 6) := Nat.le_add_right _ _
          _ = (q + 1) * (q + 3) ^ 2 * ((b + 1) * (b + 3) ^ 2) + (q + 2) * (b + 2) + 1 := by ring
          _ ≤ (q + 1) * (q + 3) ^ 2 * (x * y * z) + (q + 2) * (b + 2) + 1 := by gcongr
          _ = (q + 1) * x * ((q + 2 + 1) * y) * ((q + 2 + 1) * z) + (q + 2) * (b + 2) + 1 := by ring
end

-- forge:entry bld4_fitting_range_inter_ker_pow_card kind=proved origin=conjecture
section
/- Uses Mathlib2.bld3_rank_pow_card_stabilizes and Mathlib2.bld2_rank_pow_convex: with N = A^n, stabilisation (base case from rank_pow_card_stabilizes, propagated to exponent 2n by rank_pow_convex) gives rank(N * N) = rank N. By rank–nullity ker N ≤ ker (N * N) have equal finrank, hence are equal, which is the claim (Fitting: range N ∩ ker N = 0). -/
lemma bld4_fitting_range_inter_ker_pow_card_aux1 (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (m : ℕ) : Matrix.rank (A ^ (Fintype.card ι + m)) = Matrix.rank (A ^ Fintype.card ι) := by
  have key : ∀ m : ℕ, Matrix.rank (A ^ (Fintype.card ι + m + 1)) = Matrix.rank (A ^ (Fintype.card ι + m)) := by
    intro m
    induction m with
    | zero => exact bld3_rank_pow_card_stabilizes K ι A
    | succ m ih =>
      have hc := bld2_rank_pow_convex K ι A (Fintype.card ι + m)
      have hm : Matrix.rank (A ^ (Fintype.card ι + m + 2)) ≤ Matrix.rank (A ^ (Fintype.card ι + m + 1)) := by
        rw [pow_succ A (Fintype.card ι + m + 1)]
        exact Matrix.rank_mul_le_left _ _
      have e : Fintype.card ι + (m + 1) + 1 = Fintype.card ι + m + 2 := by ring
      have e' : Fintype.card ι + (m + 1) = Fintype.card ι + m + 1 := by ring
      rw [e, e']
      omega
  induction m with
  | zero => rfl
  | succ m ih => rw [← ih, ← add_assoc, key m]

lemma bld4_fitting_range_inter_ker_pow_card_aux2 (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (N : Matrix ι ι K) (hN : (N * N).rank = N.rank) (v : ι → K) (h : N.mulVec (N.mulVec v) = 0) : N.mulVec v = 0 := by
  have hle : LinearMap.ker N.mulVecLin ≤ LinearMap.ker (N * N).mulVecLin := by
    intro w hw
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw ⊢
    rw [← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
  have h1 := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker (N * N).mulVecLin
  have hr1 : Module.finrank K (LinearMap.range N.mulVecLin) = N.rank := rfl
  have hr2 : Module.finrank K (LinearMap.range (N * N).mulVecLin) = (N * N).rank := rfl
  have heq : LinearMap.ker N.mulVecLin = LinearMap.ker (N * N).mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  have hv : v ∈ LinearMap.ker (N * N).mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, h]
  rw [← heq, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
  exact hv

theorem bld4_fitting_range_inter_ker_pow_card (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (v : ι → K) (h : (A ^ Fintype.card ι).mulVec ((A ^ Fintype.card ι).mulVec v) = 0) : (A ^ Fintype.card ι).mulVec v = 0 := by
  refine bld4_fitting_range_inter_ker_pow_card_aux2 K ι _ ?_ v h
  rw [← pow_add]
  exact bld4_fitting_range_inter_ker_pow_card_aux1 K ι A _
end

-- forge:entry bld4_pisano_lucas_dvd_four_mul kind=proved origin=conjecture
section
/- Uses Mathlib2.an_cassini_int, Mathlib2.lib_fib_period_iff and Mathlib2.bld3_pisano_dvd_of_period: modulo L_n = F_{n+1} + F_{n−1} one has F_{2n} = F_n L_n ≡ 0 and F_{2n+1} = F_{n+1}^2 + F_n^2 ≡ F_n^2 − F_{n+1}F_{n−1} = ±1 by an_cassini_int. Hence F_{4n} ≡ 0 and F_{4n+1} ≡ F_{2n+1}^2 ≡ 1, so lib_fib_period_iff makes 4n a period mod L_n and bld3_pisano_dvd_of_period concludes (n = 0 trivial). -/
theorem bld4_pisano_lucas_dvd_four_mul_aux1 (R : Type*) [CommRing R] (m : ℕ) :
    ((Nat.fib (2 * m) : ℕ) : R) = (Nat.fib m : R) * (2 * (Nat.fib (m + 1) : R) - (Nat.fib m : R)) := by
  rw [Nat.fib_two_mul]
  have hle : Nat.fib m ≤ 2 * Nat.fib (m + 1) := by
    have := Nat.fib_le_fib_succ (n := m)
    omega
  push_cast [Nat.cast_sub hle]
  ring

theorem bld4_pisano_lucas_dvd_four_mul (n : ℕ) : p3_pisano (p3_lucas n) ∣ 4 * n := by
  have hL : (2 * (Nat.fib (n + 1) : ZMod (p3_lucas n)) - (Nat.fib n : ZMod (p3_lucas n))) = 0 := by
    rw [← lib_p3_lucas_cast]; exact ZMod.natCast_self _
  have hcas := lib_fib_cassini_cast (ZMod (p3_lucas n)) n
  rw [Nat.fib_add_two] at hcas
  push_cast at hcas
  have h2n : ((Nat.fib (2 * n) : ℕ) : ZMod (p3_lucas n)) = 0 := by
    rw [bld4_pisano_lucas_dvd_four_mul_aux1, hL, mul_zero]
  have h2n1 : ((Nat.fib (2 * n + 1) : ℕ) : ZMod (p3_lucas n)) = (-1) ^ (n + 1) := by
    rw [Nat.fib_two_mul_add_one]
    push_cast
    linear_combination hcas + (Nat.fib (n + 1) : ZMod (p3_lucas n)) * hL
  apply bld3_pisano_dvd_of_period
  rw [lib_fib_period_iff, show 4 * n = 2 * (2 * n) by ring]
  refine ⟨?_, ?_⟩
  · rw [← ZMod.natCast_eq_natCast_iff, bld4_pisano_lucas_dvd_four_mul_aux1, h2n]
    simp
  · rw [← ZMod.natCast_eq_natCast_iff, Nat.fib_two_mul_add_one]
    push_cast
    rw [h2n, h2n1, ← pow_mul, mul_comm, pow_mul]
    simp
end

-- forge:entry bld4_pow_prime_monoidHom_center_of_card_prime_cube kind=proved origin=conjecture
section
/- Uses Mathlib2.bld3_pow_prime_mem_center_of_card_prime_cube and Mathlib2.bld3_mul_pow_prime_of_card_prime_cube: define φ g = ⟨g^p, _⟩ using pow_prime_mem_center for membership; map_mul is exactly (ab)^p = a^p b^p from mul_pow_prime (p odd), map_one is one_pow. -/
theorem bld4_pow_prime_monoidHom_center_of_card_prime_cube (p : ℕ) (hp : p.Prime) (G : Type*) [Group G] (hG : Nat.card G = p ^ 3) (hna : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) : ∃ φ : G →* Subgroup.center G, ∀ g : G, ((φ g : Subgroup.center G) : G) = g ^ p := by
  refine ⟨MonoidHom.mk' (fun g => ⟨g ^ p, bld3_pow_prime_mem_center_of_card_prime_cube p hp G hG hna g⟩) ?_, fun g => rfl⟩
  intro a b
  exact Subtype.ext (bld3_mul_pow_prime_of_card_prime_cube p hp G hG hna hp2 a b)
end

-- forge:entry bld4_card_pow_prime_eq_one_ge_of_card_prime_cube kind=proved origin=conjecture
section
/- Uses Mathlib2.bld3_pow_prime_mem_center_of_card_prime_cube, Mathlib2.bld3_mul_pow_prime_of_card_prime_cube and Mathlib2.bld_center_card_of_card_prime_cube: the p-th power map is a homomorphism φ : G →* center G (first two theorems); |ker φ| · |range φ| = p^3 and |range φ| ≤ |center G| = p by bld_center_card_of_card_prime_cube, so |ker φ| ≥ p^2, and ker φ is the set {g | g^p = 1}. -/
theorem bld4_card_pow_prime_eq_one_ge_of_card_prime_cube (p : ℕ) (hp : p.Prime) (G : Type*) [Group G] (hG : Nat.card G = p ^ 3) (hna : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) : p ^ 2 ≤ Nat.card {g : G // g ^ p = 1} := by
  obtain ⟨φ, hφ⟩ := bld4_pow_prime_monoidHom_center_of_card_prime_cube p hp G hG hna hp2
  have hfin : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact pow_ne_zero _ hp.ne_zero)
  have hker : Nat.card φ.ker = Nat.card {g : G // g ^ p = 1} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
    rw [MonoidHom.mem_ker, ← hφ g, OneMemClass.coe_eq_one]
  have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card G := by
    rw [← Subgroup.index_ker]; exact Subgroup.card_mul_index _
  have h2 : Nat.card φ.range ∣ p := by
    rw [← bld_center_card_of_card_prime_cube p hp G hG hna]
    exact Subgroup.card_subgroup_dvd_card _
  have h3 := Nat.le_of_dvd hp.pos h2
  rw [← hker]
  rw [hG] at h1
  have hp0 := hp.pos
  by_contra hlt
  push_neg at hlt
  have : Nat.card φ.ker * Nat.card φ.range < p ^ 2 * p := by
    calc Nat.card φ.ker * Nat.card φ.range ≤ Nat.card φ.ker * p := Nat.mul_le_mul_left _ h3
      _ < p ^ 2 * p := Nat.mul_lt_mul_of_pos_right hlt hp0
  rw [h1] at this
  exact absurd this (by rw [pow_succ]; exact lt_irrefl _)
end

-- forge:entry bld4_pisano_ten kind=proved origin=conjecture
section
/- Uses Mathlib2.lib_pisano_dvd_iff_period, Mathlib2.lib_fib_period_iff and Mathlib2.bld3_pisano_dvd_pisano_of_dvd: lib_pisano_dvd_iff_period + lib_fib_period_iff reduce 'π(m) ∣ N' to the decidable check F_N ≡ 0, F_{N+1} ≡ 1 mod m; this gives π(10) ∣ 60, and identifies π(2) = 3 and π(5) = 20 (20 works, the divisors 4 and 10 fail). bld3_pisano_dvd_pisano_of_dvd then gives 3 ∣ π(10) and 20 ∣ π(10), so 60 ∣ π(10). -/
theorem bld4_pisano_ten : p3_pisano 10 = 60 := by
  have key : ∀ N : ℕ, 0 < N → (p3_pisano 10 ∣ N ↔ Nat.fib N ≡ 0 [MOD 10] ∧ Nat.fib (N + 1) ≡ 1 [MOD 10]) := by
    intro N hN
    rw [lib_pisano_dvd_iff_period 10 N hN, lib_fib_period_iff]
  have h60 : p3_pisano 10 ∣ 60 := by
    rw [key 60 (by norm_num)]; norm_num [Nat.ModEq]
  have h30 : ¬ p3_pisano 10 ∣ 30 := by
    rw [key 30 (by norm_num)]; norm_num [Nat.ModEq]
  have h20 : ¬ p3_pisano 10 ∣ 20 := by
    rw [key 20 (by norm_num)]; norm_num [Nat.ModEq]
  have h12 : ¬ p3_pisano 10 ∣ 12 := by
    rw [key 12 (by norm_num)]; norm_num [Nat.ModEq]
  generalize p3_pisano 10 = d at *
  have hle : d ≤ 60 := Nat.le_of_dvd (by norm_num) h60
  clear key
  interval_cases d <;> omega
end

-- forge:entry bld4_hardy_harmonic_means_tsum_le kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_hardy_inequality_tsum: apply it to a k = 1/(k+1); the hypothesis is summability of 1/(k+1)^2 and the right side is 4 · ∑' 1/(k+1)^2 = 4 · π^2/6 by Mathlib's Basel sum hasSum_zeta_two (reindexed by k ↦ k + 1). -/
theorem bld4_hardy_harmonic_means_tsum_le : ∑' k : ℕ, ((∑ i ∈ Finset.range (k + 1), 1 / ((i : ℝ) + 1)) / ((k : ℝ) + 1)) ^ 2 ≤ 2 * Real.pi ^ 2 / 3 := by
  have hs : HasSum (fun k : ℕ => (1 / ((k : ℝ) + 1)) ^ 2) (Real.pi ^ 2 / 6) := by
    have h := (hasSum_nat_add_iff' (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) (g := Real.pi ^ 2 / 6) 1).mpr hasSum_zeta_two
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero] at h
    norm_num at h
    simpa only [Nat.cast_add, Nat.cast_one, one_div, inv_pow] using h
  have h := (bld2_hardy_inequality_tsum (fun k : ℕ => 1 / ((k : ℝ) + 1)) hs.summable).2
  rw [hs.tsum_eq] at h
  linarith
end

-- forge:entry bld4_mantel_equality_complete_bipartite kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_mantel_equality_regular and Mathlib2.bld3_mantel_equality_same_neighbors: if V is empty take s = ∅; otherwise fix v and let s = G.neighborFinset v, of size n/2 by bld2_mantel_equality_regular. Two vertices of s are non-adjacent (triangle-free); a vertex y ∉ s is non-adjacent to v so by bld3_mantel_equality_same_neighbors it has the same neighbours as v, i.e. it is adjacent exactly to the vertices of s; this gives Adj x y ↔ (x ∈ s ↔ y ∉ s) in all four cases. -/
theorem bld4_mantel_equality_complete_bipartite (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.CliqueFree 3) (he : 4 * G.edgeFinset.card = Fintype.card V ^ 2) : ∃ s : Finset V, 2 * s.card = Fintype.card V ∧ ∀ x y : V, G.Adj x y ↔ (x ∈ s ↔ y ∉ s) := by
  rcases isEmpty_or_nonempty V with hV | ⟨⟨v⟩⟩
  · exact ⟨∅, by simp, fun x => isEmptyElim x⟩
  · refine ⟨G.neighborFinset v, ?_, ?_⟩
    · rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact bld2_mantel_equality_regular V G hG he v
    · intro x y
      simp only [SimpleGraph.mem_neighborFinset]
      have hs := bld3_mantel_equality_same_neighbors V G hG he
      by_cases hx : G.Adj v x <;> by_cases hy : G.Adj v y
      · have : ¬ G.Adj x y := fun hxy =>
          hG {v, x, y} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hx, hy, hxy⟩)
        tauto
      · have := (hs v y hy x).mp hx
        have := this.symm
        tauto
      · have := (hs v x hx y).mp hy
        tauto
      · have := hs v x hx y
        tauto
end

-- forge:entry bld4_compact_mutual_isometric_embeddings_isometryEquiv kind=proved origin=conjecture
section
/- Uses Mathlib2.bld3_compact_mutual_expanding_isometry: isometries are expanding (dist equality), so the cited theorem gives that f is a surjective isometry; an isometry is injective, so Equiv.ofBijective f packaged with hf is the IsometryEquiv. -/
theorem bld4_compact_mutual_isometric_embeddings_isometryEquiv {X : Type*} [MetricSpace X] [CompactSpace X] {Y : Type*} [MetricSpace Y] [CompactSpace Y] (f : X → Y) (g : Y → X) (hf : Isometry f) (hg : Isometry g) : Nonempty (X ≃ᵢ Y) := by
  obtain ⟨-, hs⟩ := bld3_compact_mutual_expanding_isometry f g
    (fun x x' => (hf.dist_eq x x').ge) (fun y y' => (hg.dist_eq y y').ge)
  exact ⟨IsometryEquiv.mk' f (Function.surjInv hs) (Function.surjInv_eq hs) hf⟩
end

-- forge:entry bld4_isometry_compact_uniform_recurrence kind=proved origin=conjecture
section
/- Uses Mathlib2.lib_compactSpace_exists_lt_and_dist_lt: take a finite ε/3-net t of X and apply the lemma in the compact space Y = (t → X) (sup metric) to u k = fun i => f^[k] i, getting m < n' with dist (f^[m] i) (f^[n'] i) < ε/3 for all i ∈ t. With n = n' − m, the isometry property gives dist i (f^[n] i) < ε/3 on the net, and the triangle inequality (f^[n] is an isometry) gives dist (f^[n] x) x < ε for all x. -/
theorem bld4_isometry_compact_uniform_recurrence {X : Type*} [MetricSpace X] [CompactSpace X] (f : X → X) (hf : Isometry f) (ε : ℝ) (hε : 0 < ε) : ∃ n : ℕ, 0 < n ∧ ∀ x : X, dist (f^[n] x) x < ε := by
  have hε3 : 0 < ε / 3 := by positivity
  have hiso : ∀ k : ℕ, Isometry f^[k] := by
    intro k
    induction k with
    | zero => exact isometry_id
    | succ k ih => rw [Function.iterate_succ']; exact hf.comp ih
  obtain ⟨t, -, htfin, htcov⟩ := finite_cover_balls_of_compact (isCompact_univ (X := X)) hε3
  haveI : Fintype ↥t := htfin.fintype
  obtain ⟨m, n, hmn, hd⟩ := lib_compactSpace_exists_lt_and_dist_lt
    (fun k : ℕ => fun i : ↥t => f^[k] (i : X)) (ε / 3) hε3
  rw [dist_pi_lt_iff hε3] at hd
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hmn
  refine ⟨d + 1, Nat.succ_pos d, fun x => ?_⟩
  have hx := htcov (Set.mem_univ x)
  simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at hx
  obtain ⟨i, hit, hxi⟩ := hx
  have h1 := hd ⟨i, hit⟩
  simp only at h1
  rw [show m + d + 1 = m + (d + 1) by ring, Function.iterate_add_apply,
    (hiso m).dist_eq] at h1
  have h2 : dist (f^[d + 1] x) (f^[d + 1] i) = dist x i := (hiso (d + 1)).dist_eq x i
  have h3 := dist_triangle (f^[d + 1] x) (f^[d + 1] i) x
  have h4 := dist_triangle (f^[d + 1] i) i x
  rw [dist_comm i (f^[d + 1] i)] at h1
  rw [dist_comm i x] at h4
  linarith
end

end Mathlib2
