/- Mathlib2 分片 31（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0030
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry calc_one_add_inv_pow_lt_exp kind=proved origin=conjecture
section
/- (1+1/n)ⁿ < e — from 1 + t < exp t for t ≠ 0 (Real.add_one_lt_exp) at t = 1/n, raise to n-th power, exp(1/n)^n = e. -/
theorem calc_one_add_inv_pow_lt_exp (n : ℕ) (hn : 0 < n) : (1 + 1 / (n : ℝ)) ^ n < Real.exp 1 := by
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have h1 : 1 + 1 / (n : ℝ) < Real.exp (1 / (n : ℝ)) := by
    have := Real.add_one_lt_exp (x := 1 / (n : ℝ)) (by positivity)
    linarith
  have h2 : Real.exp (1 / (n : ℝ)) ^ n = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [← h2]
  exact pow_lt_pow_left₀ h1 (by positivity) hn.ne'
end

-- forge:entry calc_card_idempotent_functions kind=proved origin=conjecture
section
/- Number of idempotent self-maps of an n-set is ∑ₖ C(n,k) k^(n−k) — classify by the image S (= fixed-point set) of size k; the n−k other points map arbitrarily into S. -/
theorem calc_card_idempotent_functions (n : ℕ) : ((Finset.univ : Finset (Fin n → Fin n)).filter (fun f => ∀ i, f (f i) = f i)).card = ∑ k ∈ Finset.range (n + 1), n.choose k * k ^ (n - k) := by
  have hfib := Finset.card_eq_sum_card_fiberwise (f := fun f : Fin n → Fin n => Finset.univ.filter (fun i => f i = i))
    (s := (Finset.univ : Finset (Fin n → Fin n)).filter (fun f => ∀ i, f (f i) = f i)) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  rw [hfib]
  trans ∑ S : Finset (Fin n), S.card ^ (n - S.card)
  · apply Finset.sum_congr rfl
    intro S _
    have hset : ((Finset.univ : Finset (Fin n → Fin n)).filter (fun f => ∀ i, f (f i) = f i)).filter
        (fun f => Finset.univ.filter (fun i => f i = i) = S)
        = Fintype.piFinset (fun i => if i ∈ S then ({i} : Finset (Fin n)) else S) := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
      constructor
      · rintro ⟨hid, rfl⟩ i
        by_cases hi : f i = i
        · rw [if_pos (by simp [hi])]
          simp [hi]
        · rw [if_neg (by simp [hi])]
          simp [hid i]
      · intro h
        have hfix : ∀ i ∈ S, f i = i := by
          intro i hi
          have := h i
          rw [if_pos hi, Finset.mem_singleton] at this
          exact this
        have hmem : ∀ i, f i ∈ S := by
          intro i
          by_cases hi : i ∈ S
          · rw [hfix i hi]
            exact hi
          · have := h i
            rw [if_neg hi] at this
            exact this
        refine ⟨fun i => hfix _ (hmem i), ?_⟩
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hi
          rw [← hi]
          exact hmem i
        · exact hfix i
    rw [hset, Fintype.card_piFinset]
    have hcard : ∀ i : Fin n, (if i ∈ S then ({i} : Finset (Fin n)) else S).card = if i ∈ S then 1 else S.card := by
      intro i
      split_ifs <;> simp
    simp only [hcard]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    have hc : (Finset.univ : Finset (Fin n)).filter (fun i => i ∉ S) = Sᶜ := by
      ext i
      simp
    rw [hc, Finset.card_compl, Fintype.card_fin]
  · rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card (fun m => m ^ (n - m))]
    simp
end

-- forge:entry calc_exp_lt_one_add_inv_pow_succ kind=proved origin=conjecture
section
/- e < (1+1/n)^(n+1) — equivalent to 1/(n+1) < log(1+1/n), i.e. exp(−1/(n+1)) > 1 − 1/(n+1) = n/(n+1) (Real.add_one_lt_exp at t = −1/(n+1)); invert and raise to power n+1. -/
theorem calc_exp_lt_one_add_inv_pow_succ (n : ℕ) (hn : 0 < n) : Real.exp 1 < (1 + 1 / (n : ℝ)) ^ (n + 1) := by
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hE : 0 < Real.exp (1 / ((n : ℝ) + 1)) := Real.exp_pos _
  have h1 : (n : ℝ) / (n + 1) < (Real.exp (1 / ((n : ℝ) + 1)))⁻¹ := by
    rw [← Real.exp_neg]
    have := Real.add_one_lt_exp (x := -(1 / ((n : ℝ) + 1))) (by
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith)
    have e : (n : ℝ) / (n + 1) = -(1 / ((n : ℝ) + 1)) + 1 := by field_simp; ring
    rw [e]; exact this
  have h2 : (n : ℝ) / (n + 1) * Real.exp (1 / ((n : ℝ) + 1)) < 1 := by
    have := mul_lt_mul_of_pos_right h1 hE
    rwa [inv_mul_cancel₀ hE.ne'] at this
  have h3 : Real.exp (1 / ((n : ℝ) + 1)) < 1 + 1 / (n : ℝ) := by
    rw [div_mul_eq_mul_div, div_lt_one (by positivity)] at h2
    rw [show 1 + 1 / (n : ℝ) = ((n : ℝ) + 1) / n by field_simp, lt_div_iff₀ hn']
    linarith
  have h4 : Real.exp (1 / ((n : ℝ) + 1)) ^ (n + 1) = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [← h4]
  exact pow_lt_pow_left₀ h3 hE.le (Nat.succ_ne_zero n)
end

-- forge:entry calc_pi_rpow_exp_lt_exp_pi kind=proved origin=conjecture
section
/- π^e < e^π — log x / x is strictly decreasing for x ≥ e, or directly log π < π/e from log t ≤ t − 1 with t = π/e ≠ 1 (Real.log_lt_sub_one_of_pos). -/
theorem calc_pi_rpow_exp_lt_exp_pi : Real.pi ^ Real.exp 1 < Real.exp Real.pi := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hlt : Real.exp 1 < Real.pi := by
    have := Real.exp_one_lt_d9
    have := Real.pi_gt_three
    norm_num at *
    linarith
  have h := Real.log_lt_sub_one_of_pos (x := Real.pi / Real.exp 1) (by positivity) (by
    intro h
    rw [div_eq_one_iff_eq he.ne'] at h
    linarith)
  rw [Real.log_div Real.pi_pos.ne' he.ne', Real.log_exp] at h
  have h2 : Real.log Real.pi < Real.pi / Real.exp 1 := by linarith
  rw [lt_div_iff₀ he] at h2
  rw [Real.rpow_def_of_pos Real.pi_pos]
  exact Real.exp_lt_exp.mpr h2
end

-- forge:entry calc_rpow_self_ge kind=proved origin=conjecture
section
/- xˣ ≥ e^(−1/e) for x > 0 — xˣ = exp(x log x) and x log x ≥ −1/e (apply log t ≤ t − 1 to t = 1/(e x), or Real.mul_log lower bound lemmas). -/
theorem calc_rpow_self_ge (x : ℝ) (hx : 0 < x) : Real.exp (-Real.exp (-1)) ≤ x ^ x := by
  have he : 0 < Real.exp (-1) := Real.exp_pos _
  have h := Real.log_le_sub_one_of_pos (x := Real.exp (-1) / x) (by positivity)
  rw [Real.log_div he.ne' hx.ne', Real.log_exp] at h
  have h2 : -Real.log x ≤ Real.exp (-1) / x := by linarith
  rw [le_div_iff₀ hx] at h2
  rw [Real.rpow_def_of_pos hx]
  apply Real.exp_le_exp.mpr
  linarith
end

-- forge:entry calc_rpow_lt_rpow_swap_of_exp_le kind=proved origin=conjecture
section
/- For e ≤ x < y, yˣ < xʸ — log t / t is strictly decreasing on [e, ∞) (derivative (1 − log t)/t² < 0 for t > e), so log y / y < log x / x; exponentiate. -/
theorem calc_rpow_lt_rpow_swap_of_exp_le (x y : ℝ) (hx : Real.exp 1 ≤ x) (hxy : x < y) : y ^ x < x ^ y := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hx0 : 0 < x := lt_of_lt_of_le he hx
  have hy0 : 0 < y := hx0.trans hxy
  have hl : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; exact hx
  have h := Real.log_lt_sub_one_of_pos (x := y / x) (by positivity) (by
    intro h
    rw [div_eq_one_iff_eq hx0.ne'] at h
    linarith)
  rw [Real.log_div hy0.ne' hx0.ne'] at h
  have h2 : x * (Real.log y - Real.log x) < y - x := by
    have := mul_lt_mul_of_pos_left h hx0
    have e : x * (y / x - 1) = y - x := by field_simp
    rwa [e] at this
  rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hy0]
  apply Real.exp_lt_exp.mpr
  nlinarith
end

-- forge:entry arith_centralBinom_dvd_lcm kind=proved origin=conjecture
section
/- C(2n,n) divides lcm(1,…,2n) — for each prime p, v_p(C(2n,n)) ≤ log_p(2n) (Nat.factorization_choose_le_log) and p^⌊log_p 2n⌋ ≤ 2n lies in the range, so it divides the lcm; assemble via factorization. -/
theorem arith_centralBinom_dvd_lcm (n : ℕ) : n.centralBinom ∣ (Finset.Icc 1 (2 * n)).lcm id := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hL : (Finset.Icc 1 (2 * n)).lcm id ≠ 0 := by
    rw [Finset.lcm_ne_zero_iff]
    intro x hx
    rw [Finset.mem_Icc] at hx
    simp only [id]; omega
  rw [← Nat.factorization_prime_le_iff_dvd (Nat.centralBinom_ne_zero n) hL]
  intro p hp
  rw [Nat.centralBinom_eq_two_mul_choose]
  refine le_trans Nat.factorization_choose_le_log ?_
  rw [← hp.pow_dvd_iff_le_factorization hL]
  have : p ^ Nat.log p (2*n) ∈ Finset.Icc 1 (2*n) := by
    rw [Finset.mem_Icc]
    exact ⟨Nat.one_le_pow _ _ hp.pos, Nat.pow_log_le_self p (by omega)⟩
  exact Finset.dvd_lcm (f := id) this
end

-- forge:entry arith_sigma_le_mul_log kind=proved origin=conjecture
section
/- σ(n) ≤ n(1 + ⌊log₂ n⌋) — σ(n) = Σ_{d|n} n/d ≤ Σ_{k ≤ n} ⌊n/k⌋·[k|n] ≤ n·H_n and H_n ≤ 1 + ⌊log₂ n⌋ by dyadic grouping. -/
lemma arith_sigma_le_mul_log_aux1 (n k : ℕ) : ∑ e ∈ Finset.Ico 1 (2 ^ k), n / e ≤ n * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Finset.sum_Ico_consecutive _ (Nat.one_le_two_pow) (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k))]
    have h2 : ∑ e ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), n / e ≤ n := by
      calc _ ≤ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).card • (n / 2 ^ k) := by
            apply Finset.sum_le_card_nsmul
            intro x hx
            rw [Finset.mem_Ico] at hx
            exact Nat.div_le_div_left hx.1 (by positivity)
        _ = 2 ^ k * (n / 2 ^ k) := by
            rw [Nat.card_Ico, smul_eq_mul]; congr 1; rw [pow_succ]; omega
        _ ≤ n := Nat.mul_div_le n (2 ^ k)
    rw [mul_add, mul_one]; linarith

theorem arith_sigma_le_mul_log (n : ℕ) (hn : 0 < n) : ArithmeticFunction.sigma 1 n ≤ n * (Nat.log 2 n + 1) := by
  rw [ArithmeticFunction.sigma_one_apply]
  have h1 : ∑ d ∈ n.divisors, d = ∑ d ∈ n.divisors, n / d := (Nat.sum_div_divisors n (fun d => d)).symm
  rw [h1]
  refine le_trans ?_ (arith_sigma_le_mul_log_aux1 n (Nat.log 2 n + 1))
  apply Finset.sum_le_sum_of_subset
  intro d hd
  rw [Finset.mem_Ico]
  exact ⟨Nat.pos_of_mem_divisors hd, lt_of_le_of_lt (Nat.divisor_le hd) (Nat.lt_pow_succ_log_self (by norm_num) n)⟩
end

-- forge:entry calc_tsum_inv_odd_sq kind=proved origin=conjecture
section
/- ∑ 1/(2n+1)² = π²/8 — split Basel sum hasSum_zeta_two into even and odd indices (tsum_even_add_odd); even part is (1/4)·π²/6. -/
theorem calc_tsum_inv_odd_sq_aux1 : HasSum (fun n : ℕ => 1 / (2 * (n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 8) := by
  have hz := hasSum_zeta_two
  have heven : HasSum (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ 2) (1 / 4 * (Real.pi ^ 2 / 6)) := by
    convert! hz.mul_left (1 / 4) using 1
    funext k
    push_cast
    ring
  have hodd_s : Summable (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2) :=
    hz.summable.comp_injective (i := fun k : ℕ => 2 * k + 1) (by intro a b h; simpa using h)
  have h := HasSum.even_add_odd (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) heven hodd_s.hasSum
  have e := h.unique hz
  have hv : ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2 = Real.pi ^ 2 / 8 := by linarith
  have h3 := hodd_s.hasSum
  rw [hv] at h3
  convert h3 using 1
  funext n
  push_cast
  rfl

theorem calc_tsum_inv_odd_sq : ∑' n : ℕ, 1 / (2 * (n : ℝ) + 1) ^ 2 = Real.pi ^ 2 / 8 :=
  calc_tsum_inv_odd_sq_aux1.tsum_eq
end

-- forge:entry arith_even_perfect_last_digit kind=proved origin=conjecture
section
/- Every even perfect number ends in 6 or 8 — by Euclid–Euler (Mathlib) n = 2^k(2^(k+1)-1) with 2^(k+1)-1 prime; k+1 = 2 or odd; reduce 2^k mod 10 by k mod 4. -/
theorem arith_even_perfect_last_digit_aux1 (n : ℕ) (he : Even n) (hp : n.Perfect) : ∃ k, 0 < k ∧ (k + 1).Prime ∧ (2 ^ (k + 1) - 1).Prime ∧ n = 2 ^ k * (2 ^ (k + 1) - 1) := by
  have hpos := hp.2
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp at he; exact absurd he (Nat.not_even_iff_odd.mpr hm)
    · exact h
  have hgeo : ∀ j, ∑ i ∈ Finset.range j, 2 ^ i + 1 = 2 ^ j := by
    intro j; induction j with
    | zero => simp
    | succ j ih => rw [Finset.sum_range_succ, pow_succ]; omega
  have hc : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
  have hs := (Nat.perfect_iff_sum_divisors_eq_two_mul hpos).mp hp
  rw [hc.sum_divisors_mul, Nat.sum_divisors_prime_pow Nat.prime_two, Nat.sum_divisors_eq_sum_properDivisors_add_self] at hs
  have h2 := hgeo (k + 1)
  have hmS : (∑ i ∈ Finset.range (k + 1), 2 ^ i) * (∑ i ∈ m.properDivisors, i) = m := by
    have : (∑ i ∈ Finset.range (k + 1), 2 ^ i) * (∑ i ∈ m.properDivisors, i + m) = (∑ i ∈ Finset.range (k + 1), 2 ^ i + 1) * m := by
      rw [hs, h2, pow_succ]; ring
    rw [mul_add, add_mul, one_mul] at this
    linarith
  have hM : ∑ i ∈ Finset.range (k + 1), 2 ^ i = 2 ^ (k + 1) - 1 := by omega
  have hdvd : (∑ i ∈ m.properDivisors, i) ∣ m := Dvd.intro_left _ hmS
  rcases Nat.sum_properDivisors_dvd hdvd with h1 | h1
  · have hmp : m.Prime := Nat.sum_properDivisors_eq_one_iff_prime.mp h1
    have hmeq : m = 2 ^ (k + 1) - 1 := by rw [← hM, ← hmS, h1, mul_one]
    have hmer : (mersenne (k + 1)).Prime := by
      show (2 ^ (k + 1) - 1).Prime
      rw [← hmeq]; exact hmp
    refine ⟨k, hk, Nat.Prime.of_mersenne hmer, ?_, ?_⟩
    · rw [← hmeq]; exact hmp
    · rw [← hmeq]
  · exfalso
    have hmpos : 0 < m := hm.pos
    rw [h1] at hmS
    have hS1 : ∑ i ∈ Finset.range (k + 1), 2 ^ i = 1 :=
      Nat.eq_of_mul_eq_mul_right hmpos (by rw [hmS, one_mul])
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have : 0 < 2 ^ j := by positivity
    rw [pow_succ, pow_succ] at h2
    omega

theorem arith_even_perfect_last_digit (n : ℕ) (he : Even n) (hp : n.Perfect) : n % 10 = 6 ∨ n % 10 = 8 := by
  obtain ⟨k, hk, hkp, -, rfl⟩ := arith_even_perfect_last_digit_aux1 n he hp
  have h10 : ∀ j, 0 < j → 4 ^ j % 10 = 4 ∨ 4 ^ j % 10 = 6 := by
    intro j; induction j with
    | zero => intro h; omega
    | succ j ih =>
      intro _
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp
      · have := ih hj; rw [pow_succ]; omega
  rcases hkp.eq_two_or_odd' with h | ⟨c, hc⟩
  · have : k = 1 := by omega
    subst this; norm_num
  · have : k = 2 * c := by omega
    subst this
    have e1 : 2 ^ (2 * c) = 4 ^ c := by rw [pow_mul]; norm_num
    have e2 : 2 ^ (2 * c + 1) = 2 * 4 ^ c := by rw [pow_succ, e1]; ring
    have hx := h10 c (by omega)
    have hx0 : 0 < 4 ^ c := by positivity
    rw [e1, e2]
    generalize 4 ^ c = x at hx hx0
    rcases hx with h | h
    · right
      have : (2 * x - 1) % 10 = 7 := by omega
      rw [Nat.mul_mod, h, this]
    · left
      have : (2 * x - 1) % 10 = 1 := by omega
      rw [Nat.mul_mod, h, this]
end

-- forge:entry arith_even_perfect_mod_nine kind=proved origin=conjecture
section
/- Every even perfect number other than 6 is ≡ 1 (mod 9) — Euclid–Euler gives n = 2^(q-1)(2^q-1) with q an odd prime; 2 has order 6 mod 9 and q-1 is even, check the three residues of q-1 mod 6. -/
theorem arith_even_perfect_mod_nine (n : ℕ) (he : Even n) (hp : n.Perfect) (h6 : n ≠ 6) : n % 9 = 1 := by
  obtain ⟨k, hk, hkp, -, rfl⟩ := Mathlib2.arith_even_perfect_last_digit_aux1 n he hp
  have h9 : ∀ j, 4 ^ j % 9 = 1 ∨ 4 ^ j % 9 = 4 ∨ 4 ^ j % 9 = 7 := by
    intro j; induction j with
    | zero => simp
    | succ j ih => rw [pow_succ]; omega
  rcases hkp.eq_two_or_odd' with h | ⟨c, hc⟩
  · have : k = 1 := by omega
    subst this; norm_num at h6
  · have : k = 2 * c := by omega
    subst this
    have e1 : 2 ^ (2 * c) = 4 ^ c := by rw [pow_mul]; norm_num
    have e2 : 2 ^ (2 * c + 1) = 2 * 4 ^ c := by rw [pow_succ, e1]; ring
    have hx := h9 c
    have hx0 : 0 < 4 ^ c := by positivity
    rw [e1, e2]
    generalize 4 ^ c = x at hx hx0
    rcases hx with h | h | h
    · have : (2 * x - 1) % 9 = 1 := by omega
      rw [Nat.mul_mod, h, this]
    · have : (2 * x - 1) % 9 = 7 := by omega
      rw [Nat.mul_mod, h, this]
    · have : (2 * x - 1) % 9 = 4 := by omega
      rw [Nat.mul_mod, h, this]
end

-- forge:entry calc_tendsto_sum_inv_add_log_two kind=proved origin=conjecture
section
/- lim ∑_{k=1}^{n} 1/(n+k) = log 2 — squeeze: log((n+k+1)/(n+k)) ≤ 1/(n+k) … termwise bounds 1/(m+1) ≤ log(m+1) − log m ≤ 1/m telescope to log((2n+1)/(n+1)) ≤ S_n ≤ log 2; or via H_{2n} − H_n and Euler–Mascheroni asymptotics. -/
theorem calc_tendsto_sum_inv_add_log_two : Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, 1 / ((n : ℝ) + (k : ℝ) + 1)) Filter.atTop (nhds (Real.log 2)) := by
  have hup : ∀ m : ℝ, 0 < m → Real.log (m + 1) - Real.log m ≤ 1 / m := by
    intro m hm
    have h := Real.log_le_sub_one_of_pos (x := (m + 1) / m) (by positivity)
    rw [Real.log_div (by positivity) hm.ne'] at h
    have e : (m + 1) / m - 1 = 1 / m := by field_simp; ring
    linarith
  have hlo : ∀ m : ℝ, 0 < m → 1 / (m + 1) ≤ Real.log (m + 1) - Real.log m := by
    intro m hm
    have h := Real.log_le_sub_one_of_pos (x := m / (m + 1)) (by positivity)
    rw [Real.log_div hm.ne' (by positivity)] at h
    have e : m / (m + 1) - 1 = - (1 / (m + 1)) := by field_simp; ring
    linarith
  have lower : ∀ n : ℕ, Real.log ((n : ℝ) + n + 1) - Real.log ((n : ℝ) + 1) ≤ ∑ k ∈ Finset.range n, 1 / ((n : ℝ) + (k : ℝ) + 1) := by
    intro n
    have ht := Finset.sum_range_sub (fun k : ℕ => Real.log ((n : ℝ) + k + 1)) n
    simp only [Nat.cast_zero, add_zero] at ht
    rw [← ht]
    apply Finset.sum_le_sum
    intro k _
    have := hup ((n : ℝ) + k + 1) (by positivity)
    push_cast
    have e : (n : ℝ) + (k + 1) + 1 = (n : ℝ) + k + 1 + 1 := by ring
    rw [e]
    exact this
  have upper : ∀ n : ℕ, ∑ k ∈ Finset.range n, 1 / ((n : ℝ) + (k : ℝ) + 1) ≤ Real.log 2 := by
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
      exact Real.log_nonneg (by norm_num)
    · have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
      have ht := Finset.sum_range_sub (fun k : ℕ => Real.log ((n : ℝ) + k)) n
      simp only [Nat.cast_zero, add_zero] at ht
      have e2 : Real.log ((n : ℝ) + n) - Real.log n = Real.log 2 := by
        rw [← Real.log_div (by positivity) hn'.ne']
        congr 1
        field_simp
        ring
      rw [← e2, ← ht]
      apply Finset.sum_le_sum
      intro k _
      have := hlo ((n : ℝ) + k) (by positivity)
      push_cast
      have e : (n : ℝ) + (k + 1) = (n : ℝ) + k + 1 := by ring
      rw [e]
      exact this
  have hl : Filter.Tendsto (fun n : ℕ => Real.log ((n : ℝ) + n + 1) - Real.log ((n : ℝ) + 1)) Filter.atTop (nhds (Real.log 2)) := by
    have t1 : Filter.Tendsto (fun n : ℕ => (2:ℝ) - 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 2) := by
      simpa using (tendsto_const_nhds (x := (2:ℝ))).sub (tendsto_one_div_add_atTop_nhds_zero_nat : Filter.Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) Filter.atTop (nhds 0))
    have t2 := (Real.continuousAt_log (x := 2) (by norm_num)).tendsto.comp t1
    refine t2.congr (fun n => ?_)
    have hp : (0:ℝ) < (n : ℝ) + 1 := by positivity
    simp only [Function.comp]
    rw [← Real.log_div (by positivity) hp.ne']
    congr 1
    field_simp
    ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds lower upper
end

-- forge:entry arith_two_mul_dvd_totient_pow_add_one kind=proved origin=conjecture
section
/- 2n divides φ(a^n + 1) for a > 1, n ≥ 1 — a is a unit mod N = a^n + 1 with a^n = -1 ≠ 1 and a^k < N - 1 for k < n, so its order is exactly 2n, and the order divides φ(N). -/
theorem arith_two_mul_dvd_totient_pow_add_one (a n : ℕ) (ha : 1 < a) (hn : 0 < n) : 2 * n ∣ (a ^ n + 1).totient := by
  have han : a ≤ a ^ n := by
    have := Nat.pow_le_pow_right (show 0 < a by omega) hn
    simpa using this
  haveI : NeZero (a ^ n + 1) := ⟨by omega⟩
  have hx : ((a : ZMod (a ^ n + 1))) ^ n = -1 := by
    have h0 : ((a ^ n + 1 : ℕ) : ZMod (a ^ n + 1)) = 0 := ZMod.natCast_self _
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hx2 : ((a : ZMod (a ^ n + 1))) ^ (2 * n) = 1 := by
    rw [mul_comm, pow_mul, hx]
    norm_num
  have hord : orderOf (a : ZMod (a ^ n + 1)) = 2 * n := by
    rw [orderOf_eq_iff (by omega)]
    refine ⟨hx2, fun m hm hm0 hxm => ?_⟩
    by_cases hmn : m < n
    · have h1 : ((a ^ m : ℕ) : ZMod (a ^ n + 1)) = ((1 : ℕ) : ZMod (a ^ n + 1)) := by
        push_cast
        exact hxm
      rw [ZMod.natCast_eq_natCast_iff'] at h1
      have hlt : a ^ m < a ^ n := Nat.pow_lt_pow_right ha hmn
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
      have : a ^ 1 ≤ a ^ m := Nat.pow_le_pow_right (by omega) hm0
      simp at this
      omega
    · obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
      rw [pow_add, hx] at hxm
      have h1 : ((a ^ k + 1 : ℕ) : ZMod (a ^ n + 1)) = 0 := by
        push_cast
        linear_combination -hxm
      rw [ZMod.natCast_eq_zero_iff] at h1
      have := Nat.le_of_dvd (by omega) h1
      have hlt : a ^ k < a ^ n := Nat.pow_lt_pow_right ha (by omega)
      omega
  have hu : IsUnit (a : ZMod (a ^ n + 1)) := IsUnit.of_pow_eq_one hx2 (by omega)
  obtain ⟨u, hu⟩ := hu
  rw [← ZMod.card_units_eq_totient, ← hord, ← hu, orderOf_units]
  exact orderOf_dvd_card
end

-- forge:entry calc_factorial_gt_div_exp_pow kind=proved origin=conjecture
section
/- n! > (n/e)ⁿ for n ≥ 1 — eⁿ = ∑ nᵏ/k! > nⁿ/n! (a single term of the positive exponential series, Real.sum_le_exp_of_nonneg / strict since other terms are positive); or induction using (1+1/n)ⁿ < e. -/
theorem calc_factorial_gt_div_exp_pow (n : ℕ) (hn : 0 < n) : ((n : ℝ) / Real.exp 1) ^ n < (n.factorial : ℝ) := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have h1 : (1:ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := 1) one_ne_zero
    linarith
  induction n with
  | zero => omega
  | succ k ih =>
    rcases k.eq_zero_or_pos with rfl | hk
    · simp
      exact inv_lt_one_of_one_lt₀ h1
    · have hk' : (0:ℝ) < k := Nat.cast_pos.mpr hk
      have ih' := ih hk
      have b := calc_one_add_inv_pow_lt_exp k hk
      have id1 : (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1) = ((k : ℝ) / Real.exp 1) ^ k * (1 + 1 / (k : ℝ)) ^ k * (((k : ℝ) + 1) / Real.exp 1) := by
        push_cast
        have hkk : (k:ℝ) ^ k ≠ 0 := by positivity
        have hee : (Real.exp 1) ^ k ≠ 0 := by positivity
        rw [show (1 + 1 / (k:ℝ)) = ((k:ℝ) + 1) / k by field_simp, div_pow, div_pow, div_pow, pow_succ, pow_succ]
        field_simp
      rw [id1, Nat.factorial_succ]
      push_cast
      have hab : ((k : ℝ) / Real.exp 1) ^ k * (1 + 1 / (k : ℝ)) ^ k < (k.factorial : ℝ) * Real.exp 1 :=
        mul_lt_mul'' ih' b (by positivity) (by positivity)
      have := mul_lt_mul_of_pos_right hab (show 0 < ((k : ℝ) + 1) / Real.exp 1 by positivity)
      have e2 : (k.factorial : ℝ) * Real.exp 1 * (((k : ℝ) + 1) / Real.exp 1) = ((k : ℝ) + 1) * k.factorial := by
        field_simp
      linarith
end

-- forge:entry calc_tsum_alternating_inv_sq kind=proved origin=conjecture
section
/- ∑ (−1)ⁿ/(n+1)² = π²/12 — equals (odd part) − (even part) of Basel sum = π²/8 − π²/24; uses hasSum_zeta_two and even/odd splitting. -/
theorem calc_tsum_alternating_inv_sq : ∑' n : ℕ, (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 2 = Real.pi ^ 2 / 12 := by
  have hz := hasSum_zeta_two
  have hshift : HasSum (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr hz
    simpa using this
  have hodd : HasSum (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1) / (((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2) (-1 / 4 * (Real.pi ^ 2 / 6)) := by
    convert! hshift.mul_left (-1 / 4) using 1
    funext k
    have : (-1:ℝ) ^ (2 * k + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [this]
    push_cast
    field_simp
    ring
  have heven : HasSum (fun k : ℕ => (-1 : ℝ) ^ (2 * k) / (((2 * k : ℕ) : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 8) := by
    convert calc_tsum_inv_odd_sq_aux1 using 1
    funext k
    have : (-1:ℝ) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
    rw [this]
    push_cast
    rfl
  have h := HasSum.even_add_odd (f := fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 2) heven hodd
  rw [h.tsum_eq]
  ring
end

-- forge:entry arith_mersenne_prime_factor kind=proved origin=conjecture
section
/- Prime factors q of 2^p - 1 (p odd prime) satisfy q ≡ 1 mod 2p and q ≡ ±1 mod 8 — the order of 2 mod q is p so p | q-1, q odd gives 2p | q-1; 2 = (2^((p+1)/2))² mod q is a square, so q ≡ ±1 mod 8. -/
theorem arith_mersenne_prime_factor (p q : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (h : q ∣ 2 ^ p - 1) : q % (2 * p) = 1 ∧ (q % 8 = 1 ∨ q % 8 = 7) := by
  haveI := Fact.mk hp
  haveI := Fact.mk hq
  have hpow : (2 : ZMod q) ^ p = 1 := by
    have h1 : ((2 ^ p - 1 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
    rw [Nat.cast_sub (Nat.one_le_two_pow)] at h1
    push_cast at h1
    exact sub_eq_zero.mp h1
  have h20 : (2 : ZMod q) ≠ 0 := by
    intro h'; rw [h', zero_pow hp.ne_zero] at hpow; exact zero_ne_one hpow
  have hq2 : q ≠ 2 := by
    intro h2
    apply h20
    exact (ZMod.natCast_eq_zero_iff 2 q).mpr (by rw [h2])
  have h21 : (2 : ZMod q) ≠ 1 := by
    intro h'
    have : (1 : ZMod q) = 0 := by linear_combination h'
    exact one_ne_zero this
  have hord : orderOf (2 : ZMod q) = p := orderOf_eq_prime hpow h21
  have hdvd : p ∣ q - 1 := by
    rw [← hord]; exact orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h20)
  have hqodd : q % 2 = 1 := (hq.eq_two_or_odd).resolve_left hq2
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  constructor
  · obtain ⟨k, hk⟩ := hdvd
    have hk2 : k % 2 = 0 := by
      have h0 : (q - 1) % 2 = 0 := by omega
      rw [hk, Nat.mul_mod, hpodd] at h0
      omega
    obtain ⟨j, rfl⟩ := Nat.dvd_of_mod_eq_zero hk2
    have hq1 : q = 1 + 2 * p * j := by
      have := hq.one_lt
      rw [show 2 * p * j = p * (2 * j) by ring]; omega
    rw [hq1, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by have := hp.two_le; omega)
  · rw [← ZMod.exists_sq_eq_two_iff hq2]
    refine ⟨2 ^ ((p + 1) / 2), ?_⟩
    rw [← pow_add]
    have : (p+1)/2 + (p+1)/2 = p + 1 := by omega
    rw [this, pow_succ, hpow, one_mul]
end

-- forge:entry arith_dvd_two_pow_add_one_three_dvd kind=proved origin=conjecture
section
/- If n > 1 divides 2^n + 1 then 3 | n — let p be the least prime factor of n; the order of 2 mod p divides gcd(2n, p-1) = 2 (n is odd), so p | 2² - 1 = 3. -/
theorem arith_dvd_two_pow_add_one_three_dvd (n : ℕ) (hn : 1 < n) (h : n ∣ 2 ^ n + 1) : 3 ∣ n := by
  have hp : (n.minFac).Prime := Nat.minFac_prime (by omega)
  have hpn : n.minFac ∣ n := Nat.minFac_dvd n
  haveI : Fact (n.minFac).Prime := ⟨hp⟩
  have hp2 : n.minFac ≠ 2 := by
    intro h2
    have h3 : 2 ∣ 2 ^ n + 1 := (h2 ▸ hpn : 2 ∣ n).trans h
    have h4 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have := (Nat.dvd_add_right h4).mp h3
    omega
  have h20 : (2 : ZMod n.minFac) ≠ 0 := by
    intro h0
    have h1 : ((2 : ℕ) : ZMod n.minFac) = 0 := by
      push_cast
      exact h0
    rw [ZMod.natCast_eq_zero_iff] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1)
  have hx : (2 : ZMod n.minFac) ^ n = -1 := by
    have h1 : ((2 ^ n + 1 : ℕ) : ZMod n.minFac) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact hpn.trans h
    push_cast at h1
    exact eq_neg_of_add_eq_zero_left h1
  have hx2 : (2 : ZMod n.minFac) ^ (2 * n) = 1 := by
    rw [mul_comm, pow_mul, hx]
    norm_num
  have hd1 : orderOf (2 : ZMod n.minFac) ∣ 2 * n := orderOf_dvd_of_pow_eq_one hx2
  have hd2 : orderOf (2 : ZMod n.minFac) ∣ n.minFac - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h20)
  have hcop : Nat.Coprime n (n.minFac - 1) :=
    Nat.coprime_of_lt_minFac (by have := hp.two_le; omega) (by have := hp.two_le; omega)
  have hcop2 : Nat.Coprime (orderOf (2 : ZMod n.minFac)) n := (hcop.coprime_dvd_right hd2).symm
  have hd3 : orderOf (2 : ZMod n.minFac) ∣ 2 := hcop2.dvd_of_dvd_mul_right hd1
  have hsq : (2 : ZMod n.minFac) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hd3
  have h3 : ((3 : ℕ) : ZMod n.minFac) = 0 := by
    push_cast
    linear_combination hsq
  rw [ZMod.natCast_eq_zero_iff] at h3
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
  rw [← this]
  exact hpn
end

-- forge:entry arith_sigma_odd_iff kind=proved origin=conjecture
section
/- σ(n) is odd iff n is a square or twice a square — σ multiplicative; σ(2^a) is always odd, σ(p^a) for odd p is odd iff a is even. -/
theorem arith_sigma_odd_iff_aux1 (p : ℕ) (hp : Odd p) (j : ℕ) : (∑ k ∈ Finset.range j, p ^ k) % 2 = j % 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have := Nat.odd_iff.mp (hp.pow (n := j))
    rw [Finset.sum_range_succ]; omega

theorem arith_sigma_odd_iff_aux2 (m : ℕ) (hm : Odd m) : Odd (∑ d ∈ m.divisors, d) ↔ IsSquare m := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  rw [← Mathlib2.arith_card_divisors_odd_iff_isSquare m hm.pos, Nat.sum_divisors hm0, Nat.card_divisors hm0,
    Mathlib2.arith_card_divisors_odd_iff_isSquare_aux1, Mathlib2.arith_card_divisors_odd_iff_isSquare_aux1]
  refine forall₂_congr fun p hp => ?_
  have hpo : Odd p := hm.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
  rw [Nat.odd_iff, Nat.odd_iff, arith_sigma_odd_iff_aux1 p hpo]

theorem arith_sigma_odd_iff_aux3 (k m : ℕ) (hm : Odd m) : IsSquare m ↔ (IsSquare (2 ^ k * m) ∨ ∃ x : ℕ, 2 ^ k * m = 2 * x ^ 2) := by
  have hcop : ∀ j, Nat.Coprime m (2 ^ j) := fun j => Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hm)
  have key : ∀ j x, 2 ^ j * m = x ^ 2 → IsSquare m := by
    intro j x h
    have hu : IsUnit (gcd m (2 ^ j)) := by rw [Nat.isUnit_iff]; exact hcop j
    obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow hu (by rw [mul_comm]; exact h)
    exact ⟨d, by rw [hd]; ring⟩
  constructor
  · rintro ⟨r, rfl⟩
    obtain ⟨c, rfl | rfl⟩ := Nat.even_or_odd' k
    · left; exact ⟨2 ^ c * r, by ring⟩
    · right; exact ⟨2 ^ c * r, by ring⟩
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · exact key k x (by rw [hx]; ring)
    · obtain _ | j := k
      · exfalso
        rw [pow_zero, one_mul] at hx
        rw [hx] at hm
        exact absurd hm (Nat.not_odd_iff_even.mpr (even_two_mul _))
      · refine key j x ?_
        rw [pow_succ] at hx
        exact Nat.eq_of_mul_eq_mul_left two_pos (by rw [← hx]; ring)

theorem arith_sigma_odd_iff (n : ℕ) (hn : 0 < n) : Odd (ArithmeticFunction.sigma 1 n) ↔ IsSquare n ∨ ∃ m : ℕ, n = 2 * m ^ 2 := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have hgeo : ∀ j, ∑ i ∈ Finset.range j, 2 ^ i + 1 = 2 ^ j := by
    intro j; induction j with
    | zero => simp
    | succ j ih => rw [Finset.sum_range_succ, pow_succ]; omega
  have hc : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
  have h2 := hgeo (k + 1)
  have hodd : Odd (∑ i ∈ Finset.range (k + 1), 2 ^ i) := by
    rw [Nat.odd_iff]; rw [pow_succ] at h2; omega
  rw [ArithmeticFunction.sigma_one_apply, hc.sum_divisors_mul, Nat.sum_divisors_prime_pow Nat.prime_two,
    Nat.odd_mul, arith_sigma_odd_iff_aux2 m hm, ← arith_sigma_odd_iff_aux3 k m hm]
  exact and_iff_right hodd
end

-- forge:entry arith_liouville_sum_card_divisors_cube kind=proved origin=conjecture
section
/- Liouville's identity Σ_{d|n} τ(d)³ = (Σ_{d|n} τ(d))² — both sides are multiplicative in n; on p^a it is Σ_{j=1}^{a+1} j³ = (Σ j)² (Nicomachus). -/
lemma arith_liouville_sum_card_divisors_cube_aux1 (k : ℕ) : 2 * ∑ j ∈ Finset.range (k + 1), (j + 1) = (k + 1) * (k + 2) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

lemma arith_liouville_sum_card_divisors_cube_aux2 (k : ℕ) : ∑ j ∈ Finset.range (k + 1), (j + 1) ^ 3 = (∑ j ∈ Finset.range (k + 1), (j + 1)) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ _ (k+1)]
    have h := arith_liouville_sum_card_divisors_cube_aux1 k
    generalize ∑ j ∈ Finset.range (k + 1), (j + 1) = S at h ⊢
    have e : (S + (k + 1 + 1)) ^ 2 = S ^ 2 + (2 * S) * (k + 1 + 1) + (k + 1 + 1) ^ 2 := by ring
    rw [e, h]; ring

theorem arith_liouville_sum_card_divisors_cube (n : ℕ) : ∑ d ∈ n.divisors, d.divisors.card ^ 3 = (∑ d ∈ n.divisors, d.divisors.card) ^ 2 := by
  have hF : ∀ m, ∑ d ∈ m.divisors, d.divisors.card ^ 3 = ((ArithmeticFunction.sigma 0).ppow 3 * ArithmeticFunction.zeta) m := by
    intro m
    rw [ArithmeticFunction.mul_zeta_apply]
    apply Finset.sum_congr rfl; intro d _
    rw [ArithmeticFunction.ppow_apply (by norm_num), ArithmeticFunction.sigma_zero_apply]
  have hG : ∀ m, ∑ d ∈ m.divisors, d.divisors.card = (ArithmeticFunction.sigma 0 * ArithmeticFunction.zeta) m := by
    intro m; rw [ArithmeticFunction.mul_zeta_apply]; apply Finset.sum_congr rfl; intro d _; rw [ArithmeticFunction.sigma_zero_apply]
  have mF : ((ArithmeticFunction.sigma 0).ppow 3 * ArithmeticFunction.zeta).IsMultiplicative :=
    (ArithmeticFunction.isMultiplicative_sigma.ppow).mul ArithmeticFunction.isMultiplicative_zeta
  have mG : (ArithmeticFunction.sigma 0 * ArithmeticFunction.zeta).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_sigma.mul ArithmeticFunction.isMultiplicative_zeta
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp
  | prime_pow p k hp hk =>
    rw [Nat.sum_divisors_prime_pow hp, Nat.sum_divisors_prime_pow hp]
    have : ∀ j, (p^j).divisors.card = j + 1 := fun j => by
      rw [← ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
    simp_rw [this]
    exact arith_liouville_sum_card_divisors_cube_aux2 k
  | coprime a b ha hb hab iha ihb =>
    rw [hF, hG, mF.map_mul_of_coprime hab, mG.map_mul_of_coprime hab, ← hF, ← hG, ← hF, ← hG, iha, ihb]; ring
end

-- forge:entry arith_perfect_not_isSquare kind=proved origin=conjecture
section
/- No perfect number is a square — σ(m²) is odd (each σ(p^(2a)) is a sum of an odd number of odd terms, or p = 2) but σ(n) = 2n is even. -/
theorem arith_perfect_not_isSquare (n : ℕ) (hp : n.Perfect) : ¬ IsSquare n := by
  intro hsq
  have h := (Mathlib2.arith_sigma_odd_iff n hp.2).mpr (Or.inl hsq)
  rw [ArithmeticFunction.sigma_one_apply, (Nat.perfect_iff_sum_divisors_eq_two_mul hp.2).mp hp] at h
  exact absurd h (Nat.not_odd_iff_even.mpr (even_two_mul n))
end

end Mathlib2
