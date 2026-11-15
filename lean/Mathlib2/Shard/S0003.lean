/- Mathlib2 分片 3（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0002
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry an2_chebyshev_index_weighted kind=proved origin=conjecture
section
/- Chebyshev sum inequality against the index sequence: for a monotone real sequence a, (n-1) * sum_{i<n} a_i ≤ 2 * sum_{i<n} i * a_i. -/
theorem an2_chebyshev_index_weighted_aux1 (a : ℕ → ℝ) (ha : Monotone a) (n : ℕ) : ∑ i ∈ Finset.range n, a i ≤ (n : ℝ) * a n := by
  have h := Finset.sum_le_card_nsmul (Finset.range n) a (a n) (fun i hi => ha (Finset.mem_range.mp hi).le)
  simpa using h

theorem an2_chebyshev_index_weighted (a : ℕ → ℝ) (ha : Monotone a) (n : ℕ) : ((n : ℝ) - 1) * ∑ i ∈ Finset.range n, a i ≤ 2 * ∑ i ∈ Finset.range n, (i : ℝ) * a i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h := an2_chebyshev_index_weighted_aux1 a ha n
    push_cast
    nlinarith [ih, h]
end

-- forge:entry an2_cyclic_div_ge_card kind=proved origin=conjecture
section
/- Cyclic ratio inequality for n+1 positive reals: x_0/x_1 + x_1/x_2 + ... + x_{n-1}/x_n + x_n/x_0 ≥ n+1. Generalizes Mathlib2.an_cyclic_div_ge_three (n = 2). -/
theorem an2_cyclic_div_ge_card (n : ℕ) (x : ℕ → ℝ) (hx : ∀ i, 0 < x i) : (n : ℝ) + 1 ≤ ∑ i ∈ Finset.range n, x i / x (i + 1) + x n / x 0 := by
  have key : ∀ a b : ℝ, 0 < a → 0 < b → 1 + (Real.log a - Real.log b) ≤ a / b := by
    intro a b ha hb
    have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
    rw [Real.log_div ha.ne' hb.ne'] at h
    linarith
  have h1 : ∑ i ∈ Finset.range n, (1 + (Real.log (x i) - Real.log (x (i + 1)))) ≤ ∑ i ∈ Finset.range n, x i / x (i + 1) :=
    Finset.sum_le_sum (fun i _ => key _ _ (hx i) (hx (i + 1)))
  rw [Finset.sum_add_distrib, Finset.sum_range_sub' (fun i => Real.log (x i))] at h1
  have h2 := key _ _ (hx n) (hx 0)
  simp at h1
  linarith
end

-- forge:entry an2_succ_pow_lt_three_mul_pow kind=proved origin=conjecture
section
/- (1 + 1/n)^n < 3 for n ≥ 1, stated in naturals as (n+1)^n < 3 n^n. -/
theorem an2_succ_pow_lt_three_mul_pow (n : ℕ) (hn : 0 < n) : (n + 1) ^ n < 3 * n ^ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (1 / (n : ℝ) + 1) ≤ Real.exp (1 / (n : ℝ)) := Real.add_one_le_exp _
  have h2 : (1 / (n : ℝ) + 1) ^ n ≤ Real.exp (1 / (n : ℝ)) ^ n :=
    pow_le_pow_left₀ (by positivity) h1 n
  have h3 : Real.exp (1 / (n : ℝ)) ^ n = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have h4 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h5 : (1 / (n : ℝ) + 1) ^ n = ((n : ℝ) + 1) ^ n / (n : ℝ) ^ n := by
    rw [← div_pow]
    congr 1
    field_simp
    ring
  have h6 : ((n : ℝ) + 1) ^ n / (n : ℝ) ^ n < 3 := by
    rw [← h5]; linarith [h3 ▸ h2]
  have h7 : ((n : ℝ) + 1) ^ n < 3 * (n : ℝ) ^ n := by
    rwa [div_lt_iff₀ (by positivity)] at h6
  exact_mod_cast h7
end

-- forge:entry an2_amgm_range_pow kind=proved origin=conjecture
section
/- AM-GM for n+1 nonnegative reals in power form (no rpow): prod a_i ≤ (mean)^(n+1). Generalizes Mathlib2.an_amgm_three_cube (n = 2). -/
theorem an2_amgm_range_pow (n : ℕ) (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) : ∏ i ∈ Finset.range (n + 1), a i ≤ ((∑ i ∈ Finset.range (n + 1), a i) / ((n : ℝ) + 1)) ^ (n + 1) := by
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h := Real.geom_mean_le_arith_mean_weighted (Finset.range (n + 1)) (fun _ => (((n + 1 : ℕ) : ℝ))⁻¹) a
    (fun i _ => by positivity) (by simp; field_simp) (fun i _ => ha i)
  have h0 : 0 ≤ ∏ i ∈ Finset.range (n + 1), a i ^ (((n + 1 : ℕ) : ℝ))⁻¹ :=
    Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (ha i) _)
  have h2 := pow_le_pow_left₀ h0 h (n + 1)
  rw [← Finset.prod_pow] at h2
  have h3 : ∀ i ∈ Finset.range (n + 1), (a i ^ (((n + 1 : ℕ) : ℝ))⁻¹) ^ (n + 1) = a i :=
    fun i _ => Real.rpow_inv_natCast_pow (ha i) (Nat.succ_ne_zero n)
  rw [Finset.prod_congr rfl h3, ← Finset.mul_sum] at h2
  calc _ ≤ _ := h2
    _ = _ := by congr 1; push_cast; field_simp
end

-- forge:entry an2_nesbitt_general kind=proved origin=conjecture
section
/- Nesbitt's inequality for N = n+2 positive reals with sum S: sum a_i/(S - a_i) ≥ N/(N-1). Generalizes Mathlib2.an_nesbitt (n = 1). -/
theorem an2_nesbitt_general (n : ℕ) (a : ℕ → ℝ) (ha : ∀ i, 0 < a i) : ((n : ℝ) + 2) / ((n : ℝ) + 1) ≤ ∑ i ∈ Finset.range (n + 2), a i / (∑ j ∈ Finset.range (n + 2), a j - a i) := by
  set S := ∑ j ∈ Finset.range (n + 2), a j with hSdef
  have hS : 0 < S := Finset.sum_pos (fun i _ => ha i) (by simp)
  have hn : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have hn2 : (0:ℝ) < (n:ℝ) + 2 := by positivity
  have key : ∀ i ∈ Finset.range (n + 2),
      1 / ((n:ℝ) + 1) + ((n:ℝ) + 2)^2 / ((n:ℝ) + 1)^2 * (a i / S - 1 / ((n:ℝ) + 2)) ≤ a i / (S - a i) := by
    intro i hi
    have hd : 0 < S - a i := by
      have hlt : a i < S := by
        by_cases h0 : i = 0
        · subst h0
          exact Finset.single_lt_sum (i := 0) (j := 1) (by norm_num) hi (by simp) (ha 1)
            (fun k _ _ => (ha k).le)
        · exact Finset.single_lt_sum (i := i) (j := 0) (Ne.symm h0) hi (by simp) (ha 0)
            (fun k _ _ => (ha k).le)
      linarith
    rw [← sub_nonneg]
    have e : a i / (S - a i) - (1 / ((n:ℝ) + 1) + ((n:ℝ) + 2)^2 / ((n:ℝ) + 1)^2 * (a i / S - 1 / ((n:ℝ) + 2)))
        = (((n:ℝ) + 2) * a i - S)^2 / (S * (S - a i) * ((n:ℝ) + 1)^2) := by
      field_simp
      ring
    rw [e]
    exact div_nonneg (sq_nonneg _) (mul_pos (mul_pos hS hd) (by positivity)).le
  have e2 : ((n : ℝ) + 2) / ((n : ℝ) + 1) = ∑ i ∈ Finset.range (n + 2),
      (1 / ((n:ℝ) + 1) + ((n:ℝ) + 2)^2 / ((n:ℝ) + 1)^2 * (a i / S - 1 / ((n:ℝ) + 2))) := by
    have h1 : ∑ x ∈ Finset.range (n + 2), a x / S = 1 := by
      rw [← Finset.sum_div, ← hSdef, div_self hS.ne']
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, h1]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    field_simp
    ring
  rw [e2]
  exact Finset.sum_le_sum key
end

-- forge:entry an2_pow_self_le_three_pow_mul_factorial kind=proved origin=conjecture
section
/- n! ≥ (n/3)^n, stated as n^n ≤ 3^n * n!. Induction using (n+1)^n ≤ 3 n^n. -/
theorem an2_pow_self_le_three_pow_mul_factorial (n : ℕ) : n ^ n ≤ 3 ^ n * n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; norm_num
    · have h1 := (Mathlib2.an2_succ_pow_lt_three_mul_pow n h).le
      calc (n + 1) ^ (n + 1) = (n + 1) ^ n * (n + 1) := pow_succ _ _
        _ ≤ (3 * n ^ n) * (n + 1) := Nat.mul_le_mul_right _ h1
        _ ≤ (3 * (3 ^ n * n.factorial)) * (n + 1) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ih)
        _ = 3 ^ (n + 1) * (n + 1).factorial := by
            rw [Nat.factorial_succ]; ring
end

-- forge:entry nt2_dvd_two_pow_sub_one_eq_one kind=proved origin=conjecture
section
/- If n ≥ 1 divides 2^n - 1 then n = 1 (take the least prime factor p of n; the order of 2 mod p divides gcd(n, p-1) = 1). -/
theorem nt2_dvd_two_pow_sub_one_eq_one (n : ℕ) (hn : 0 < n) (h : n ∣ 2 ^ n - 1) : n = 1 := by
  by_contra hne
  have hp : (n.minFac).Prime := Nat.minFac_prime hne
  haveI : Fact (n.minFac).Prime := ⟨hp⟩
  have hdiv : n.minFac ∣ 2 ^ n - 1 := (Nat.minFac_dvd n).trans h
  have h1 : ((2 ^ n - 1 : ℕ) : ZMod n.minFac) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have hpow : (2 : ZMod n.minFac) ^ n = 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow] at h1
    push_cast at h1
    linear_combination h1
  have h2ne : (2 : ZMod n.minFac) ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn.ne'] at hpow
    exact zero_ne_one hpow
  have hd1 : orderOf (2 : ZMod n.minFac) ∣ n := orderOf_dvd_of_pow_eq_one hpow
  have hd2 : orderOf (2 : ZMod n.minFac) ∣ n.minFac - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h2ne)
  have hlt : orderOf (2 : ZMod n.minFac) < n.minFac := by
    have := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hd2
    have := hp.one_lt
    omega
  have hone : orderOf (2 : ZMod n.minFac) = 1 := by
    by_contra hd
    have ha := Nat.minFac_le_of_dvd (Nat.minFac_prime hd).two_le ((Nat.minFac_dvd _).trans hd1)
    have hb := Nat.minFac_le (orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hpow⟩))
    omega
  rw [orderOf_eq_one_iff] at hone
  have : (1 : ZMod n.minFac) = 0 := by linear_combination hone
  exact one_ne_zero this
end

-- forge:entry nt2_prime_three_mod_four_dvd_sq_add_sq kind=proved origin=conjecture
section
/- Generalization of Mathlib2.nt_seven_dvd_sq_add_sq from 7 to every prime p ≡ 3 (mod 4): if p divides a^2+b^2 then p divides both a and b (-1 is not a square mod p). -/
theorem nt2_prime_three_mod_four_dvd_sq_add_sq (p : ℕ) (hp : Nat.Prime p) (h : p % 4 = 3) (a b : ℤ) (hd : (p : ℤ) ∣ a ^ 2 + b ^ 2) : (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have h0 : ((a : ZMod p)) ^ 2 + (b : ZMod p) ^ 2 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ 2 + b ^ 2) p).mpr hd
    push_cast at this
    exact this
  have h1 : (a : ZMod p) ^ 2 = -(b : ZMod p) ^ 2 := eq_neg_of_add_eq_zero_left h0
  constructor
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    by_contra hne
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq hne h1 h
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    by_contra hne
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hne h1 h
end

-- forge:entry an2_one_add_inv_pow_strict_mono kind=proved origin=conjecture
section
/- The sequence (1 + 1/m)^m is strictly increasing for m ≥ 1. -/
theorem an2_one_add_inv_pow_strict_mono (n : ℕ) : (1 + 1 / ((n : ℝ) + 1)) ^ (n + 1) < (1 + 1 / ((n : ℝ) + 2)) ^ (n + 2) := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hy : 1 + 1 / ((n:ℝ) + 2) = (1 + 1 / ((n:ℝ) + 1)) * (1 + -(1 / ((n:ℝ) + 2)^2)) := by
    field_simp
    ring
  have hsmall : 1 / ((n:ℝ) + 2)^2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hB := one_add_mul_le_pow (a := -(1 / ((n:ℝ) + 2)^2)) (by linarith) (n + 1)
  have h3 : 1 < (1 + 1 / ((n:ℝ) + 2)) * (1 + ((n + 1 : ℕ) : ℝ) * -(1 / ((n:ℝ) + 2)^2)) := by
    push_cast
    rw [← sub_pos]
    have e : (1 + 1 / ((n:ℝ) + 2)) * (1 + ((n:ℝ) + 1) * -(1 / ((n:ℝ) + 2)^2)) - 1 = 1 / ((n:ℝ) + 2)^3 := by
      field_simp
      ring
    rw [e]
    positivity
  have hx : (0:ℝ) < (1 + 1 / ((n : ℝ) + 1)) ^ (n + 1) := by positivity
  have hypos : (0:ℝ) ≤ 1 + 1 / ((n : ℝ) + 2) := by positivity
  calc (1 + 1 / ((n : ℝ) + 1)) ^ (n + 1)
      < (1 + 1 / ((n : ℝ) + 1)) ^ (n + 1) * ((1 + 1 / ((n:ℝ) + 2)) * (1 + ((n + 1 : ℕ) : ℝ) * -(1 / ((n:ℝ) + 2)^2))) :=
        lt_mul_of_one_lt_right hx h3
    _ ≤ (1 + 1 / ((n : ℝ) + 1)) ^ (n + 1) * ((1 + 1 / ((n:ℝ) + 2)) * (1 + -(1 / ((n:ℝ) + 2)^2)) ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB hypos) hx.le
    _ = (1 + 1 / ((n : ℝ) + 2)) ^ (n + 2) := by
        rw [hy]
        generalize (1 + 1 / ((n : ℝ) + 1)) = x
        generalize (1 + -(1 / ((n:ℝ) + 2)^2)) = q
        ring
end

-- forge:entry nt2_sq_add_sq_eq_seven_mul_sq kind=proved origin=conjecture
section
/- x^2 + y^2 = 7 z^2 has only the trivial integer solution. Consequence of Mathlib2.nt_seven_dvd_sq_add_sq by infinite descent (7 | x, y, then 7 | z, divide through by 49). -/
theorem nt2_sq_add_sq_eq_seven_mul_sq_aux1 (n : ℕ) : ∀ x y z : ℤ, z.natAbs < n → x ^ 2 + y ^ 2 = 7 * z ^ 2 → z = 0 := by
  induction n with
  | zero => intro x y z hz; omega
  | succ n ih =>
    intro x y z hz h
    by_contra hz0
    obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := Mathlib2.nt_seven_dvd_sq_add_sq x y ⟨z ^ 2, h⟩
    have h7 : (7 : ℤ) ∣ z ^ 2 := ⟨a ^ 2 + b ^ 2, by linarith⟩
    have hp : Prime (7 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
    obtain ⟨c, rfl⟩ := hp.dvd_of_dvd_pow h7
    have hc : c = 0 := by
      apply ih a b c
      · have : c ≠ 0 := by rintro rfl; simp at hz0
        have : 0 < c.natAbs := Int.natAbs_pos.mpr this
        rw [Int.natAbs_mul] at hz
        norm_num at hz
        omega
      · linarith
    subst hc
    simp at hz0

theorem nt2_sq_add_sq_eq_seven_mul_sq (x y z : ℤ) (h : x ^ 2 + y ^ 2 = 7 * z ^ 2) : x = 0 ∧ y = 0 ∧ z = 0 := by
  have hz := nt2_sq_add_sq_eq_seven_mul_sq_aux1 (z.natAbs + 1) x y z (Nat.lt_succ_self _) h
  subst hz
  have hx : x ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hy : y ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  exact ⟨by simpa using hx, by simpa using hy, rfl⟩
end

-- forge:entry an2_sum_inv_sqrt_bounds kind=proved origin=conjecture
section
/- 2(sqrt(n+1) - 1) ≤ sum_{k=1}^n 1/sqrt k ≤ 2 sqrt n. -/
theorem an2_sum_inv_sqrt_bounds_aux1 (t : ℝ) (ht : 0 ≤ t) :
    2 * (Real.sqrt (t + 1 + 1) - Real.sqrt (t + 1)) ≤ 1 / Real.sqrt (t + 1) ∧
    1 / Real.sqrt (t + 1) ≤ 2 * (Real.sqrt (t + 1) - Real.sqrt t) := by
  have hb : 0 < Real.sqrt (t + 1) := Real.sqrt_pos.mpr (by linarith)
  have ha2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
  have hb2 : Real.sqrt (t + 1) ^ 2 = t + 1 := Real.sq_sqrt (by linarith)
  have hc2 : Real.sqrt (t + 1 + 1) ^ 2 = t + 1 + 1 := Real.sq_sqrt (by linarith)
  constructor
  · rw [le_div_iff₀ hb]
    nlinarith [sq_nonneg (Real.sqrt (t + 1 + 1) - Real.sqrt (t + 1))]
  · rw [div_le_iff₀ hb]
    nlinarith [sq_nonneg (Real.sqrt t - Real.sqrt (t + 1))]

theorem an2_sum_inv_sqrt_bounds (n : ℕ) : 2 * (Real.sqrt ((n : ℝ) + 1) - 1) ≤ ∑ i ∈ Finset.range n, 1 / Real.sqrt ((i : ℝ) + 1) ∧ ∑ i ∈ Finset.range n, 1 / Real.sqrt ((i : ℝ) + 1) ≤ 2 * Real.sqrt (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := an2_sum_inv_sqrt_bounds_aux1 (n : ℝ) (Nat.cast_nonneg n)
    rw [Finset.sum_range_succ]
    push_cast
    constructor <;> linarith [ih.1, ih.2]
end

-- forge:entry nt2_fib_catalan_identity kind=proved origin=conjecture
section
/- Catalan's Fibonacci identity F_{n+r}^2 - F_n F_{n+2r} = (-1)^n F_r^2, generalizing Cassini's identity Mathlib2.an_cassini_int (the case r = 1). -/
theorem nt2_fib_catalan_identity (n r : ℕ) : (Nat.fib (n + r) : ℤ) ^ 2 - (Nat.fib n : ℤ) * (Nat.fib (n + 2 * r) : ℤ) = (-1) ^ n * (Nat.fib r : ℤ) ^ 2 := by
  rcases r with _ | s
  · simp
    ring
  · have h1 : Nat.fib (n + (s + 1)) = Nat.fib n * Nat.fib s + Nat.fib (n + 1) * Nat.fib (s + 1) := by
      rw [← Nat.fib_add]; rfl
    have h2 : Nat.fib (n + 2 * (s + 1)) = Nat.fib n * Nat.fib (2 * s + 1) + Nat.fib (n + 1) * Nat.fib (2 * s + 2) := by
      rw [← Nat.fib_add]; congr 1
    have h3 : Nat.fib (2 * s + 1) = Nat.fib s * Nat.fib s + Nat.fib (s + 1) * Nat.fib (s + 1) := by
      rw [← Nat.fib_add]; congr 1; ring
    have h4 : Nat.fib (2 * s + 2) = Nat.fib s * Nat.fib (s + 1) + Nat.fib (s + 1) * Nat.fib (s + 2) := by
      rw [← Nat.fib_add]; congr 1; ring
    have h5 : Nat.fib (s + 2) = Nat.fib s + Nat.fib (s + 1) := Nat.fib_add_two
    have hc := Mathlib2.an_cassini_int n
    rw [Nat.fib_add_two] at hc
    rw [h1, h2, h3, h4, h5]
    push_cast at hc ⊢
    linear_combination (-(Nat.fib (s + 1) : ℤ) ^ 2) * hc
end

-- forge:entry nt2_fib_odd_index_no_prime_factor_three_mod_four kind=proved origin=conjecture
section
/- No prime p ≡ 3 (mod 4) divides an odd-indexed Fibonacci number: F_{2n+1} = F_n^2 + F_{n+1}^2 is a sum of two coprime squares. -/
theorem nt2_fib_odd_index_no_prime_factor_three_mod_four (n p : ℕ) (hp : Nat.Prime p) (h : p % 4 = 3) : ¬ p ∣ Nat.fib (2 * n + 1) := by
  intro hd
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.fib_two_mul_add_one] at hd
  have h1 : ((Nat.fib (n + 1) ^ 2 + Nat.fib n ^ 2 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  push_cast at h1
  have h2 : ((Nat.fib (n + 1) : ℕ) : ZMod p) ^ 2 = -((Nat.fib n : ℕ) : ZMod p) ^ 2 := by linear_combination h1
  by_cases hx : ((Nat.fib (n + 1) : ℕ) : ZMod p) = 0
  · have hy : ((Nat.fib n : ℕ) : ZMod p) = 0 := by
      rw [hx] at h2
      have : ((Nat.fib n : ℕ) : ZMod p) ^ 2 = 0 := by linear_combination h2
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    have d1 := (ZMod.natCast_eq_zero_iff _ _).mp hx
    have d2 := (ZMod.natCast_eq_zero_iff _ _).mp hy
    have := Nat.dvd_gcd d2 d1
    rw [Nat.fib_coprime_fib_succ n] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  · exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq hx h2 h
end

-- forge:entry an2_alt_sum_choose_mul_pow_eq_zero kind=proved origin=conjecture
section
/- The n-th finite difference of a monomial of degree m < n vanishes: sum_k (-1)^k C(n,k) k^m = 0. -/
theorem an2_alt_sum_choose_mul_pow_eq_zero (n m : ℕ) (h : m < n) : ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) * (k : ℤ) ^ m = 0 := by
  have h0 := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℤ) h) 0
  rw [fwdDiff_iter_eq_sum_shift] at h0
  simp only [zero_add, smul_eq_mul, nsmul_eq_mul, mul_one, Pi.zero_apply] at h0
  have e : ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) * (k : ℤ) ^ m
      = (-1) ^ n * ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * (n.choose k : ℤ) * (k : ℤ) ^ m := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hn : (-1 : ℤ) ^ (n - k) * (-1) ^ k = (-1) ^ n := pow_sub_mul_pow _ hk'
    have he : (-1 : ℤ) ^ (n - k) * (-1) ^ (n - k) = 1 := by
      rw [← mul_pow]; simp
    rw [← hn]
    linear_combination (-((-1 : ℤ) ^ k * (n.choose k : ℤ) * (k : ℤ) ^ m)) * he
  rw [e, h0, mul_zero]
end

-- forge:entry nt2_two_mul_sum_coprime_eq_mul_totient kind=proved origin=conjecture
section
/- For n > 1 the sum of the integers in [0,n) coprime to n is n φ(n)/2 (pair k with n-k). -/
theorem nt2_two_mul_sum_coprime_eq_mul_totient (n : ℕ) (hn : 1 < n) : 2 * ∑ k ∈ (Finset.range n).filter (fun k => Nat.Coprime k n), k = n * Nat.totient n := by
  have hmem : ∀ k ∈ (Finset.range n).filter (fun k => Nat.Coprime k n),
      n - k ∈ (Finset.range n).filter (fun k => Nat.Coprime k n) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk ⊢
    have hk0 : k ≠ 0 := by
      rintro rfl
      have := (Nat.coprime_zero_left n).mp hk.2
      omega
    exact ⟨by omega, (Nat.coprime_self_sub_left hk.1.le).mpr hk.2⟩
  have hS : ∑ k ∈ (Finset.range n).filter (fun k => Nat.Coprime k n), k
      = ∑ k ∈ (Finset.range n).filter (fun k => Nat.Coprime k n), (n - k) := by
    apply Finset.sum_nbij' (fun k => n - k) (fun k => n - k) hmem hmem
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      show n - (n - k) = k
      omega
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      show n - (n - k) = k
      omega
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      show k = n - (n - k)
      omega
  have hcard : Nat.totient n = ((Finset.range n).filter (fun k => Nat.Coprime k n)).card := by
    rw [Nat.totient_eq_card_coprime]
    congr 1
    apply Finset.filter_congr
    intro k _
    exact Nat.coprime_comm
  have hsum : ∑ k ∈ (Finset.range n).filter (fun k => Nat.Coprime k n), k
      + ∑ k ∈ (Finset.range n).filter (fun k => Nat.Coprime k n), (n - k)
      = n * Nat.totient n := by
    rw [← Finset.sum_add_distrib, hcard, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    omega
  rw [← hsum, ← hS]
  ring
end

-- forge:entry nt2_wilson_half_factorial_sq kind=proved origin=conjecture
section
/- For a prime p ≡ 1 (mod 4), ((p-1)/2)!^2 ≡ -1 (mod p): explicit square root of -1 from Wilson's theorem. -/
theorem nt2_wilson_half_factorial_sq (p : ℕ) (hp : Nat.Prime p) (h : p % 4 = 1) : p ∣ ((p - 1) / 2).factorial ^ 2 + 1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨m, hm⟩ : ∃ m, p = 4 * m + 1 := ⟨p / 4, by omega⟩
  have hk : (p - 1) / 2 = 2 * m := by omega
  rw [hk]
  have h1 : ((2 * m).factorial * (p - 1).descFactorial (2 * m) : ℕ) = (p - 1).factorial := by
    have := Nat.factorial_mul_descFactorial (n := p - 1) (k := 2 * m) (by omega)
    have e : p - 1 - 2 * m = 2 * m := by omega
    rwa [e] at this
  have h2 : (((p - 1).descFactorial (2 * m) : ℕ) : ZMod p) = (-1) ^ (2 * m) * ((2 * m).factorial : ZMod p) :=
    ZMod.cast_descFactorial (by omega)
  have h3 := ZMod.wilsons_lemma p
  rw [← h1] at h3
  push_cast at h3
  rw [h2, pow_mul] at h3
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  linear_combination h3
end

-- forge:entry nt2_x_pow_four_add_one_irreducible_int kind=proved origin=conjecture
section
/- The polynomial X^4 + 1 is irreducible over the integers (it is the 8th cyclotomic polynomial; Eisenstein after X ↦ X+1). -/
theorem nt2_x_pow_four_add_one_irreducible_int : Irreducible (Polynomial.X ^ 4 + 1 : Polynomial ℤ) := by
  have h : Polynomial.cyclotomic 8 ℤ = Polynomial.X ^ 4 + 1 := by
    have h2 : Nat.Prime 2 := Nat.prime_two
    have := Polynomial.cyclotomic_prime_pow_eq_geom_sum (R := ℤ) (p := 2) (n := 2) h2
    norm_num [Finset.sum_range_succ] at this
    rw [this]
    ring
  rw [← h]
  exact Polynomial.cyclotomic.irreducible (by norm_num)
end

-- forge:entry nt2_irrational_sqrt_two_add_sqrt_three kind=proved origin=conjecture
section
/- √2 + √3 is irrational (squaring gives 5 + 2√6, and √6 is irrational). -/
theorem nt2_irrational_sqrt_two_add_sqrt_three : Irrational (Real.sqrt 2 + Real.sqrt 3) := by
  rintro ⟨q, hq⟩
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : (0:ℝ) < Real.sqrt 2 + Real.sqrt 3 := by positivity
  have hq0 : (q : ℝ) ≠ 0 := by rw [hq]; exact hpos.ne'
  apply irrational_sqrt_two
  refine ⟨(q - 1 / q) / 2, ?_⟩
  push_cast
  field_simp
  rw [hq]
  linear_combination h3 - h2
end

-- forge:entry nt2_prod_divisors_sq kind=proved origin=conjecture
section
/- The square of the product of the divisors of n equals n^{d(n)}. -/
theorem nt2_prod_divisors_sq (n : ℕ) : (∏ d ∈ Nat.divisors n, d) ^ 2 = n ^ (Nat.divisors n).card := by
  have h := Nat.prod_div_divisors n (fun d => d)
  simp only at h
  rw [sq]
  nth_rewrite 2 [← h]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_const]
  apply Finset.prod_congr rfl
  intro d hd
  exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
end

-- forge:entry nt2_sq_sum_eq_two_mul_prod_descent kind=proved origin=conjecture
section
/- x^2 + y^2 + z^2 = 2xyz has only the zero solution in integers (2-adic infinite descent). -/
theorem nt2_sq_sum_eq_two_mul_prod_descent_aux1 (m x y z : ℤ) (h : x ^ 2 + y ^ 2 + z ^ 2 = 2 * m * x * y * z) :
    ∃ a b c : ℤ, x = 2 * a ∧ y = 2 * b ∧ z = 2 * c := by
  rcases Int.even_or_odd' x with ⟨a, rfl | rfl⟩ <;>
  rcases Int.even_or_odd' y with ⟨b, rfl | rfl⟩ <;>
  rcases Int.even_or_odd' z with ⟨c, rfl | rfl⟩ <;>
  first
    | exact ⟨a, b, c, rfl, rfl, rfl⟩
    | (exfalso; ring_nf at h; omega)

theorem nt2_sq_sum_eq_two_mul_prod_descent_aux2 (n : ℕ) : ∀ (k : ℕ) (x y z : ℤ), 1 ≤ k →
    x ^ 2 + y ^ 2 + z ^ 2 = 2 ^ k * x * y * z → (2 : ℤ) ^ n ∣ x := by
  induction n with
  | zero => intro k x y z _ _; simp
  | succ n ih =>
    intro k x y z hk h
    have hm : (2 : ℤ) ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    obtain ⟨a, b, c, rfl, rfl, rfl⟩ :=
      nt2_sq_sum_eq_two_mul_prod_descent_aux1 (2 ^ (k - 1)) x y z (by rw [h, hm])
    have h4 : 4 * (a ^ 2 + b ^ 2 + c ^ 2) = 4 * (2 ^ (k + 1) * a * b * c) := by
      rw [pow_succ]
      linear_combination h
    have h' : a ^ 2 + b ^ 2 + c ^ 2 = 2 ^ (k + 1) * a * b * c :=
      Int.eq_of_mul_eq_mul_left (by norm_num) h4
    have := ih (k + 1) a b c (by omega) h'
    rw [pow_succ']
    exact mul_dvd_mul_left 2 this

theorem nt2_sq_sum_eq_two_mul_prod_descent (x y z : ℤ) (h : x ^ 2 + y ^ 2 + z ^ 2 = 2 * x * y * z) : x = 0 ∧ y = 0 ∧ z = 0 := by
  have hx : x = 0 := by
    by_contra hne
    have hd := nt2_sq_sum_eq_two_mul_prod_descent_aux2 x.natAbs 1 x y z le_rfl (by simpa using h)
    have hd' := Int.natAbs_dvd_natAbs.mpr hd
    have hpos : 0 < x.natAbs := Int.natAbs_pos.mpr hne
    have hle := Nat.le_of_dvd hpos hd'
    rw [Int.natAbs_pow] at hle
    have : x.natAbs < 2 ^ x.natAbs := Nat.lt_two_pow_self
    simp at hle
    omega
  subst hx
  have hy : y ^ 2 = 0 := by nlinarith [sq_nonneg y, sq_nonneg z]
  have hz : z ^ 2 = 0 := by nlinarith [sq_nonneg y, sq_nonneg z]
  exact ⟨rfl, by simpa using hy, by simpa using hz⟩
end

end Mathlib2
