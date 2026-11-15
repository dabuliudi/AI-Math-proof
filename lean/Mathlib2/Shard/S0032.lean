/- Mathlib2 分片 32（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0031
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry arith_card_odd_choose kind=proved origin=conjecture
section
/- Glaisher: the number of odd entries in row n of Pascal's triangle is 2^(number of binary ones of n) — induct on binary digits using C(2n,2k) ≡ C(n,k), C(2n,2k+1) even, C(2n+1,2k) ≡ C(2n+1,2k+1) ≡ C(n,k) mod 2 (Lucas). -/
lemma arith_card_odd_choose_aux1 (n k : ℕ) : Odd (n.choose k) ↔ k % 2 ≤ n % 2 ∧ Odd ((n / 2).choose (k / 2)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat n k 2 _
  rw [Nat.odd_iff, Nat.odd_iff]
  unfold Nat.ModEq at h
  rw [h, Nat.mul_mod]
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hn with hn | hn <;> rcases hk with hk | hk <;> rw [hn, hk] <;> simp [Nat.choose]

lemma arith_card_odd_choose_aux2 (n k : ℕ) : k ∈ (Finset.range (n + 1)).filter (fun k => Odd (n.choose k)) ↔ Odd (n.choose k) := by
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    by_contra hlt
    rw [Nat.choose_eq_zero_of_lt (by omega)] at h
    simp at h

lemma arith_card_odd_choose_aux3 (m : ℕ) : ((Finset.range (2 * m + 1)).filter (fun k => Odd ((2 * m).choose k))).card = ((Finset.range (m + 1)).filter (fun k => Odd (m.choose k))).card := by
  have inj0 : Function.Injective (fun j : ℕ => 2 * j) := fun a b h => by simp only at h; omega
  rw [← Finset.card_image_of_injective ((Finset.range (m + 1)).filter (fun k => Odd (m.choose k))) inj0]
  congr 1
  ext k
  have e1 : 2 * m % 2 = 0 := by omega
  have e2 : 2 * m / 2 = m := by omega
  rw [arith_card_odd_choose_aux2, arith_card_odd_choose_aux1, e1, e2]
  simp only [Finset.mem_image, arith_card_odd_choose_aux2]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨k / 2, h2, by omega⟩
  · rintro ⟨j, hj, rfl⟩
    have : 2 * j / 2 = j := by omega
    rw [this]
    exact ⟨by omega, hj⟩

lemma arith_card_odd_choose_aux4 (m : ℕ) : ((Finset.range (2 * m + 1 + 1)).filter (fun k => Odd ((2 * m + 1).choose k))).card = 2 * ((Finset.range (m + 1)).filter (fun k => Odd (m.choose k))).card := by
  have inj0 : Function.Injective (fun j : ℕ => 2 * j) := fun a b h => by simp only at h; omega
  have inj1 : Function.Injective (fun j : ℕ => 2 * j + 1) := fun a b h => by simp only at h; omega
  have hS : (Finset.range (2 * m + 1 + 1)).filter (fun k => Odd ((2 * m + 1).choose k)) = ((Finset.range (m + 1)).filter (fun k => Odd (m.choose k))).image (fun j => 2 * j) ∪ ((Finset.range (m + 1)).filter (fun k => Odd (m.choose k))).image (fun j => 2 * j + 1) := by
    ext k
    have e1 : (2 * m + 1) % 2 = 1 := by omega
    have e2 : (2 * m + 1) / 2 = m := by omega
    rw [arith_card_odd_choose_aux2, arith_card_odd_choose_aux1, e1, e2]
    simp only [Finset.mem_union, Finset.mem_image, arith_card_odd_choose_aux2]
    constructor
    · rintro ⟨_, h2⟩
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · left; exact ⟨k / 2, h2, by omega⟩
      · right; exact ⟨k / 2, h2, by omega⟩
    · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
      · have : 2 * j / 2 = j := by omega
        rw [this]; exact ⟨by omega, hj⟩
      · have : (2 * j + 1) / 2 = j := by omega
        rw [this]; exact ⟨by omega, hj⟩
  have hdisj : Disjoint (((Finset.range (m + 1)).filter (fun k => Odd (m.choose k))).image (fun j => 2 * j)) (((Finset.range (m + 1)).filter (fun k => Odd (m.choose k))).image (fun j => 2 * j + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_image] at hx hx'
    obtain ⟨j, _, rfl⟩ := hx
    obtain ⟨j', _, h⟩ := hx'
    omega
  rw [hS, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ inj0, Finset.card_image_of_injective _ inj1]
  ring

theorem arith_card_odd_choose (n : ℕ) : ((Finset.range (n + 1)).filter (fun k => Odd (n.choose k))).card = 2 ^ (Nat.digits 2 n).sum := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · decide
    · obtain ⟨m, hm | hm⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 := ⟨n / 2, by omega⟩
      · subst hm
        rw [arith_card_odd_choose_aux3, ih m (by omega), Nat.digits_base_mul (by norm_num) (by omega)]
        simp
      · subst hm
        rw [arith_card_odd_choose_aux4, ih m (by omega), Nat.digits_def' (b := 2) (n := 2 * m + 1) (by norm_num) (by omega)]
        have e1 : (2 * m + 1) % 2 = 1 := by omega
        have e2 : (2 * m + 1) / 2 = m := by omega
        rw [e1, e2, List.sum_cons, pow_add, pow_one]
end

-- forge:entry calc_integral_beta_nat kind=proved origin=conjecture
section
/- Beta integral at naturals: ∫₀¹ xᵐ(1−x)ⁿ dx = m! n!/(m+n+1)! — induction on n with integration by parts B(m,n+1) = (n+1)/(m+1)·B(m+1,n); base ∫ xᵐ = 1/(m+1). -/
theorem calc_integral_beta_nat_aux1 (m n : ℕ) : ∫ x in (0:ℝ)..1, x ^ m * (1 - x) ^ (n + 1) = (((n : ℝ) + 1) / ((m : ℝ) + 1)) * ∫ x in (0:ℝ)..1, x ^ (m + 1) * (1 - x) ^ n := by
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hu : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun x : ℝ => (1 - x) ^ (n + 1)) (-(((n : ℝ) + 1) * (1 - x) ^ n)) x := by
    intro x _
    have h := ((hasDerivAt_id x).const_sub 1).pow (n + 1)
    convert h using 1
    simp
  have hv : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun x : ℝ => x ^ (m + 1) / ((m : ℝ) + 1)) (x ^ m) x := by
    intro x _
    have h := ((hasDerivAt_id x).pow (m + 1)).div_const ((m : ℝ) + 1)
    convert h using 1
    simp
    field_simp
  have hu' : Continuous (fun x : ℝ => -(((n : ℝ) + 1) * (1 - x) ^ n)) := by fun_prop
  have hv' : Continuous (fun x : ℝ => x ^ m) := by fun_prop
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv (hu'.intervalIntegrable _ _) (hv'.intervalIntegrable _ _)
  have e1 : ∫ x in (0:ℝ)..1, x ^ m * (1 - x) ^ (n + 1) = ∫ x in (0:ℝ)..1, (1 - x) ^ (n + 1) * x ^ m := by
    congr 1; funext x; ring
  have e2 : ∫ x in (0:ℝ)..1, -(((n : ℝ) + 1) * (1 - x) ^ n) * (x ^ (m + 1) / ((m : ℝ) + 1)) = -((((n : ℝ) + 1) / ((m : ℝ) + 1)) * ∫ x in (0:ℝ)..1, x ^ (m + 1) * (1 - x) ^ n) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    congr 1; funext x; field_simp
  rw [e1, key, e2]
  simp

theorem calc_integral_beta_nat (m n : ℕ) : ∫ x in (0:ℝ)..1, x ^ m * (1 - x) ^ n = ((m.factorial : ℝ) * n.factorial) / ((m + n + 1).factorial : ℝ) := by
  induction n generalizing m with
  | zero =>
    simp only [pow_zero, mul_one, integral_pow, Nat.factorial_zero, Nat.cast_one, add_zero]
    rw [Nat.factorial_succ]
    have : ((m.factorial : ℝ)) ≠ 0 := by positivity
    push_cast
    field_simp
    simp
  | succ n ih =>
    rw [calc_integral_beta_nat_aux1, ih (m + 1)]
    rw [show m + 1 + n + 1 = m + (n + 1) + 1 by ring, Nat.factorial_succ m, Nat.factorial_succ n]
    have : (((m + (n + 1) + 1).factorial : ℝ)) ≠ 0 := by positivity
    push_cast
    field_simp
end

-- forge:entry arith_fermat_prime_factor_mod_two_pow_add_two kind=proved origin=conjecture
section
/- Lucas' strengthening: for n ≥ 2 every prime factor of the Fermat number F_n is ≡ 1 mod 2^(n+2) — Uses Mathlib2.nt2_fermat_number_prime_factor_form at step 1 to get p ≡ 1 mod 2^(n+1), hence p ≡ 1 mod 8, so 2 is a quadratic residue mod p (ZMod.exists_sq_eq_two_iff); a square root of 2 then has order 2^(n+2), which divides p - 1. -/
theorem arith_fermat_prime_factor_mod_two_pow_add_two (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime) (h : p ∣ 2 ^ 2 ^ n + 1) : p % 2 ^ (n + 2) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := nt2_fermat_number_prime_factor_form n p hp (by obtain ⟨k, hk⟩ := h; exact ⟨k, hk.symm⟩)
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 2 := ⟨n - 2, by omega⟩
  have hpow : 2 ^ (t + 2 + 1) = 8 * 2 ^ t := by ring
  have hp8 : p = 8 * (m * 2 ^ t) + 1 := by rw [hm, hpow]; ring
  have hp81 : p % 8 = 1 := by omega
  have hp2 : p ≠ 2 := by omega
  obtain ⟨y, hy⟩ := (ZMod.exists_sq_eq_two_iff hp2).mpr (Or.inl hp81)
  have hx : (2 : ZMod p) ^ 2 ^ (t + 2) = -1 := by
    have h1 : ((2 ^ 2 ^ (t + 2) + 1 : ℕ) : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact h
    push_cast at h1
    exact eq_neg_of_add_eq_zero_left h1
  have h20 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have h1 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      exact h0
    rw [ZMod.natCast_eq_zero_iff] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1)
  have hy1 : y ^ 2 ^ (t + 2 + 1) = -1 := by
    rw [pow_succ', pow_mul, pow_two, ← hy, hx]
  have hy2 : y ^ 2 ^ (t + 2 + 1 + 1) = 1 := by
    rw [pow_succ 2 (t + 2 + 1), pow_mul, hy1]
    norm_num
  have hne : ¬ y ^ 2 ^ (t + 2 + 1) = 1 := by
    rw [hy1]
    intro h1
    apply h20
    linear_combination -h1
  have hord : orderOf y = 2 ^ (t + 2 + 1 + 1) := orderOf_eq_prime_pow hne hy2
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0] at hy
    exact h20 (by simpa using hy)
  have hdvd : 2 ^ (t + 2 + 1 + 1) ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hy0
  obtain ⟨c, hc⟩ := hdvd
  have hqe : p = 2 ^ (t + 2 + 1 + 1) * c + 1 := by
    rw [← hc]
    exact (Nat.sub_add_cancel hp.one_le).symm
  show p % 2 ^ (t + 2 + 1 + 1) = 1
  rw [hqe, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt]
  exact Nat.one_lt_two_pow (by omega)
end

-- forge:entry arith_totient_dvd_self_iff kind=proved origin=conjecture
section
/- φ(n) | n iff n = 1 or n = 2^a 3^b with a ≥ 1 — n/φ(n) = ∏ p/(p-1) must be an integer; for n>2 φ is even so 2 | n; the largest prime factor q>2 forces ∏(p-1) | ∏ p·…, compare 2-adic valuations: each odd prime contributes a factor 2 to φ, so at most one odd prime, and (q-1) | 2^a q forces q = 3. -/
lemma arith_totient_dvd_self_iff_aux1 (m : ℕ) (hodd : Odd m) (h : m.totient ∣ 2 * m) : ∃ b, m = 3 ^ b := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · exact ⟨0, by rcases hodd with ⟨k, rfl⟩; omega⟩
  have hm0 : m ≠ 0 := by omega
  have key : ∃ p e v, p.Prime ∧ 1 ≤ e ∧ p ^ e * v = m ∧ Nat.Coprime (p ^ e) v :=
    ⟨m.minFac, m.factorization m.minFac, m / m.minFac ^ m.factorization m.minFac,
      Nat.minFac_prime (by omega),
      (Nat.minFac_prime (by omega)).factorization_pos_of_dvd hm0 (Nat.minFac_dvd m),
      Nat.ordProj_mul_ordCompl_eq_self m _,
      (Nat.coprime_ordCompl (Nat.minFac_prime (by omega)) hm0).pow_left _⟩
  obtain ⟨p, e, v, hp, he1, hsplit, hcop⟩ := key
  have hpodd : Odd p := hodd.of_dvd_nat (hsplit ▸ Dvd.dvd.mul_right (dvd_pow_self p (by omega)) v)
  have hp3 : 3 ≤ p := by have := hp.two_le; rcases hpodd with ⟨k, hk⟩; omega
  have hvodd : Odd v := hodd.of_dvd_nat ⟨p ^ e, by rw [mul_comm]; exact hsplit.symm⟩
  have hu3 : 3 ≤ p ^ e := le_trans hp3 (Nat.le_self_pow (by omega) p)
  by_cases hv1 : v = 1
  · rw [hv1, mul_one] at hsplit
    obtain ⟨e', he'⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    rw [← hsplit, he', Nat.totient_prime_pow_succ hp] at h
    have h2 : p - 1 ∣ 2 * p := by
      apply Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos e')
      rw [show p ^ e' * (2 * p) = 2 * p ^ (e' + 1) by ring]; exact h
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [hq] at h2
    simp only [Nat.add_sub_cancel] at h2
    have hc : Nat.Coprime q (q + 1) := by simp
    have h3 : q ∣ 2 := hc.dvd_of_dvd_mul_right h2
    have := Nat.le_of_dvd (by norm_num) h3
    have hp3' : p = 3 := by rcases hpodd with ⟨k, hk⟩; omega
    exact ⟨e, by rw [← hsplit, hp3']⟩
  · exfalso
    have hv3 : 3 ≤ v := by
      rcases hvodd with ⟨k, hk⟩; omega
    have e1 : Even (p ^ e).totient := Nat.totient_even (by omega)
    have e2 : Even v.totient := Nat.totient_even (by omega)
    rw [← hsplit, Nat.totient_mul hcop] at h
    obtain ⟨x, hx⟩ := e1
    obtain ⟨y, hy⟩ := e2
    rw [hx, hy] at h
    have h4 : 4 ∣ 2 * (p ^ e * v) := Dvd.dvd.trans ⟨x * y, by ring⟩ h
    have hoddm : Odd (p ^ e * v) := by rw [hsplit]; exact hodd
    generalize p ^ e * v = M at h4 hoddm
    rcases hoddm with ⟨k, hk⟩
    omega

theorem arith_totient_dvd_self_iff (n : ℕ) (hn : 0 < n) : n.totient ∣ n ↔ n = 1 ∨ ∃ a b : ℕ, n = 2 ^ (a + 1) * 3 ^ b := by
  constructor
  · intro h
    by_cases h1 : n = 1
    · exact Or.inl h1
    right
    obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
    have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
    cases a with
    | zero =>
      exfalso
      simp only [pow_zero, one_mul] at h h1
      have hm3 : 2 < m := by rcases hm with ⟨k, rfl⟩; omega
      have he := Nat.totient_even hm3
      have : Even m := he.trans_dvd h
      exact (Nat.not_even_iff_odd.mpr hm) this
    | succ a =>
      rw [Nat.totient_mul hcop, Nat.totient_prime_pow_succ Nat.prime_two] at h
      simp only [Nat.reduceSub, mul_one] at h
      have h2 : m.totient ∣ 2 * m := by
        apply Nat.dvd_of_mul_dvd_mul_left (pow_pos (by norm_num : 0 < 2) a)
        rw [show 2 ^ a * (2 * m) = 2 ^ (a + 1) * m by ring]; exact h
      obtain ⟨b, rfl⟩ := arith_totient_dvd_self_iff_aux1 m hm h2
      exact ⟨a, b, rfl⟩
  · rintro (rfl | ⟨a, b, rfl⟩)
    · simp
    · have hcop : Nat.Coprime (2 ^ (a + 1)) (3 ^ b) := Nat.Coprime.pow _ _ (by norm_num)
      rw [Nat.totient_mul hcop, Nat.totient_prime_pow_succ Nat.prime_two]
      cases b with
      | zero =>
        refine ⟨2, ?_⟩
        simp only [Nat.reduceSub, pow_zero, Nat.totient_one, mul_one]
        ring
      | succ b =>
        rw [Nat.totient_prime_pow_succ Nat.prime_three]
        refine ⟨3, ?_⟩
        simp only [Nat.reduceSub, mul_one]
        ring
end

-- forge:entry calc_tsum_millin kind=proved origin=conjecture
section
/- Millin series ∑_{n≥0} 1/F_{2ⁿ} = (7−√5)/2 — partial sums ∑_{n=0}^{N} 1/F_{2ⁿ} = 3 − F_{2^N − 1}/F_{2^N} for N ≥ 1 (induction, using F_{2m} = F_m L_m and d'Ocagne/Cassini), and F_{k−1}/F_k → 1/φ = (√5−1)/2. -/
theorem calc_tsum_millin_aux1 (N : ℕ) : ∃ n : ℕ, n + 1 = 2 ^ (N + 1) ∧ (1:ℝ) ≤ Nat.fib n ∧ ((N : ℝ) + 1) ≤ Nat.fib (n + 1) ∧ (Nat.fib n : ℝ) ^ 2 + Nat.fib n * Nat.fib (n + 1) - (Nat.fib (n + 1) : ℝ) ^ 2 = 1 ∧ ∑ i ∈ Finset.range (N + 2), 1 / (Nat.fib (2 ^ i) : ℝ) = 3 - (Nat.fib n : ℝ) / Nat.fib (n + 1) := by
  induction N with
  | zero =>
    refine ⟨1, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    norm_num [Finset.sum_range_succ]
  | succ N ih =>
    obtain ⟨n, hn, ha, hb, hinv, hs⟩ := ih
    have e1 : (Nat.fib (2 * n + 1) : ℝ) = (Nat.fib (n + 1) : ℝ) ^ 2 + (Nat.fib n : ℝ) ^ 2 := by
      rw [Nat.fib_two_mul_add_one]; push_cast; ring
    have e2 : (Nat.fib (2 * n + 1 + 1) : ℝ) = (Nat.fib (n + 1) : ℝ) * (2 * (Nat.fib n : ℝ) + Nat.fib (n + 1)) := by
      rw [show 2 * n + 1 + 1 = 2 * n + 2 from rfl, Nat.fib_two_mul_add_two]; push_cast; ring
    have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
    have hb0 : (0:ℝ) < Nat.fib (n + 1) := by linarith
    have hp : 2 ^ (N + 1 + 1) = 2 * n + 1 + 1 := by rw [pow_succ, ← hn]; ring
    refine ⟨2 * n + 1, hp.symm, ?_, ?_, ?_, ?_⟩
    · rw [e1]; nlinarith
    · rw [e2]; push_cast; nlinarith
    · rw [e1, e2]
      linear_combination ((Nat.fib n : ℝ) ^ 2 + Nat.fib n * Nat.fib (n + 1) - (Nat.fib (n + 1) : ℝ) ^ 2 + 1) * hinv
    · rw [Finset.sum_range_succ, hs, hp, e1, e2]
      have h2 : (0:ℝ) < 2 * (Nat.fib n : ℝ) + Nat.fib (n + 1) := by linarith
      generalize (Nat.fib n : ℝ) = a at *
      generalize (Nat.fib (n + 1) : ℝ) = b at *
      have key : a / b - 1 / (b * (2 * a + b)) = (b ^ 2 + a ^ 2) / (b * (2 * a + b)) := by
        rw [div_sub_div _ _ hb0.ne' (by positivity), div_eq_div_iff (by positivity) (by positivity)]
        linear_combination (b * (b * (2 * a + b))) * hinv
      linarith

theorem calc_tsum_millin_aux2 (N : ℕ) : (7 - Real.sqrt 5) / 2 - 1 / ((N : ℝ) + 1) ≤ ∑ i ∈ Finset.range (N + 2), 1 / (Nat.fib (2 ^ i) : ℝ) ∧ ∑ i ∈ Finset.range (N + 2), 1 / (Nat.fib (2 ^ i) : ℝ) ≤ (7 - Real.sqrt 5) / 2 := by
  obtain ⟨n, -, ha, hbN, hinv, hs⟩ := calc_tsum_millin_aux1 N
  rw [hs]
  generalize (Nat.fib n : ℝ) = a at *
  generalize (Nat.fib (n + 1) : ℝ) = b at *
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hb : 0 < b := by linarith
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5p : 2 < Real.sqrt 5 := by
    rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (Real.sqrt 5 - 1) / 2 := ⟨_, rfl⟩
  have hc : c ^ 2 + c = 1 := by rw [hcdef]; nlinarith
  have hc0 : 0 < c := by rw [hcdef]; linarith
  have hprod : (a - c * b) * (a + (c + 1) * b) = 1 := by linear_combination hinv - b ^ 2 * hc
  have hpos : 0 < a + (c + 1) * b := by nlinarith
  have hd0 : 0 < a - c * b := by
    by_contra h
    push_neg at h
    have := mul_nonpos_of_nonpos_of_nonneg h hpos.le
    linarith
  have hd1 : a - c * b ≤ 1 := by
    have h1 : (1:ℝ) ≤ a + (c + 1) * b := by nlinarith
    have := mul_le_mul_of_nonneg_left h1 hd0.le
    linarith
  have hx1 : c ≤ a / b := by rw [le_div_iff₀ hb]; linarith
  have hx2 : a / b ≤ c + 1 / ((N : ℝ) + 1) := by
    rw [div_le_iff₀ hb]
    have h1 : 1 ≤ 1 / ((N : ℝ) + 1) * b := by
      rw [one_div, inv_mul_eq_div, one_le_div (by positivity)]; exact hbN
    have e : (c + 1 / ((N : ℝ) + 1)) * b = c * b + 1 / ((N : ℝ) + 1) * b := by ring
    linarith
  constructor <;> linarith

theorem calc_tsum_millin : ∑' n : ℕ, 1 / (Nat.fib (2 ^ n) : ℝ) = (7 - Real.sqrt 5) / 2 := by
  have ht : Filter.Tendsto (fun N : ℕ => ∑ i ∈ Finset.range (N + 2), 1 / (Nat.fib (2 ^ i) : ℝ)) Filter.atTop (nhds ((7 - Real.sqrt 5) / 2)) := by
    have t1 : Filter.Tendsto (fun N : ℕ => (7 - Real.sqrt 5) / 2 - 1 / ((N : ℝ) + 1)) Filter.atTop (nhds ((7 - Real.sqrt 5) / 2)) := by
      simpa using (tendsto_const_nhds (x := (7 - Real.sqrt 5) / 2)).sub (tendsto_one_div_add_atTop_nhds_zero_nat : Filter.Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) Filter.atTop (nhds 0))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le t1 tendsto_const_nhds (fun N => (calc_tsum_millin_aux2 N).1) (fun N => (calc_tsum_millin_aux2 N).2)
  have hs : HasSum (fun n : ℕ => 1 / (Nat.fib (2 ^ n) : ℝ)) ((7 - Real.sqrt 5) / 2) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => by positivity)]
    exact (Filter.tendsto_add_atTop_iff_nat 2).mp ht
  exact hs.tsum_eq
end

-- forge:entry arith_odd_perfect_euler_form kind=proved origin=conjecture
section
/- Euler's theorem on odd perfect numbers: n = p^a m² with p ≡ a ≡ 1 (mod 4), p ∤ m — σ(n) = 2n ≡ 2 (mod 4), so exactly one factor σ(q^e) is even and it is ≡ 2 mod 4; σ(q^e) for odd q is odd iff e even, and ≡ 2 mod 4 forces q ≡ e ≡ 1 mod 4. -/
theorem arith_odd_perfect_euler_form_aux1 (p : ℕ) (hp : p % 4 = 1) (j : ℕ) : (∑ k ∈ Finset.range j, p ^ k) % 4 = j % 4 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have : p ^ j % 4 = 1 := by simp [Nat.pow_mod, hp]
    rw [Finset.sum_range_succ]; omega

theorem arith_odd_perfect_euler_form_aux2 (p : ℕ) (hp : p % 4 = 3) (j : ℕ) : (∑ k ∈ Finset.range (2 * j), p ^ k) % 4 = 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨t, rfl⟩ : ∃ t, p = 4 * t + 3 := ⟨p / 4, by omega⟩
    have e : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
    have h : (4 * t + 3) ^ (2 * j) + (4 * t + 3) ^ (2 * j + 1) = 4 * ((4 * t + 3) ^ (2 * j) * (t + 1)) := by ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ]
    omega

theorem arith_odd_perfect_euler_form (n : ℕ) (ho : Odd n) (hp : n.Perfect) : ∃ p a m : ℕ, p.Prime ∧ p % 4 = 1 ∧ a % 4 = 1 ∧ ¬ p ∣ m ∧ n = p ^ a * m ^ 2 := by
  have hpos := hp.2
  have hs := (Nat.perfect_iff_sum_divisors_eq_two_mul hpos).mp hp
  have hnsq : ¬ IsSquare n := Mathlib2.arith_perfect_not_isSquare n hp
  have hex : ∃ p ∈ n.primeFactors, ¬ Odd (n.factorization p + 1) := by
    by_contra hcon
    push_neg at hcon
    apply hnsq
    rw [← Mathlib2.arith_card_divisors_odd_iff_isSquare n hpos, Nat.card_divisors hpos.ne',
      Mathlib2.arith_card_divisors_odd_iff_isSquare_aux1]
    exact hcon
  obtain ⟨p, hpm, hodd0⟩ := hex
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpm
  have hpo : Odd p := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hpm)
  obtain ⟨a, r, hodd, hndvd, hr⟩ : ∃ a r, ¬ Odd (a + 1) ∧ ¬ p ∣ r ∧ n = p ^ a * r :=
    ⟨_, _, hodd0, Nat.not_dvd_ordCompl hpp hpos.ne', (Nat.ordProj_mul_ordCompl_eq_self n p).symm⟩
  have hc : Nat.Coprime (p ^ a) r := Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hndvd)
  have hro : Odd r := ho.of_dvd_nat (Dvd.intro_left _ hr.symm)
  have hσ := hs
  rw [hr, hc.sum_divisors_mul, Nat.sum_divisors_prime_pow hpp, ← hr] at hσ
  have hG2 : (∑ k ∈ Finset.range (a + 1), p ^ k) % 2 = 0 := by
    rw [Mathlib2.arith_sigma_odd_iff_aux1 p hpo]
    rw [Nat.odd_iff] at hodd; omega
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp ho
  obtain ⟨g, hg⟩ : ∃ g, ∑ k ∈ Finset.range (a + 1), p ^ k = 2 * g := ⟨_, (Nat.div_add_mod _ 2).symm.trans (by rw [hG2, add_zero])⟩
  rw [hg, mul_assoc] at hσ
  have hgS : g * ∑ d ∈ r.divisors, d = n := Nat.eq_of_mul_eq_mul_left two_pos hσ
  have hgS' : Odd (g * ∑ d ∈ r.divisors, d) := by rw [hgS]; exact ho
  obtain ⟨hgo, hSo⟩ := Nat.odd_mul.mp hgS'
  obtain ⟨m, hm⟩ := (Mathlib2.arith_sigma_odd_iff_aux2 r hro).mp hSo
  have hG4 : (∑ k ∈ Finset.range (a + 1), p ^ k) % 4 = 2 := by
    rw [hg]; rw [Nat.odd_iff] at hgo; omega
  have hp4 : p % 4 = 1 := by
    by_contra h1
    have h3 : p % 4 = 3 := by rw [Nat.odd_iff] at hpo; omega
    obtain ⟨j, hj⟩ : ∃ j, a + 1 = 2 * j := by
      rw [Nat.odd_iff] at hodd; exact ⟨(a + 1) / 2, by omega⟩
    rw [hj, arith_odd_perfect_euler_form_aux2 p h3 j] at hG4
    omega
  have ha4 : a % 4 = 1 := by
    rw [arith_odd_perfect_euler_form_aux1 p hp4] at hG4; omega
  refine ⟨p, a, m, hpp, hp4, ha4, fun h => hndvd (hm ▸ Dvd.dvd.mul_right h m), ?_⟩
  rw [hr, hm]; ring
end

-- forge:entry arith_least_odd_abundant kind=proved origin=conjecture
section
/- 945 is the least odd abundant number — for odd n < 945: n has at most 3 distinct prime factors unless n ≥ 3·5·7·11; bound σ(n)/n < ∏ p/(p-1) and handle the families 3^a5^b7^c < 945 (or a finite case check). -/
theorem arith_least_odd_abundant (n : ℕ) (ho : Odd n) (ha : n.Abundant) : 945 ≤ n := by
  by_contra hlt
  push_neg at hlt
  have key : ∀ k < 945, k % 2 = 1 → ¬ (k < ∑ i ∈ k.properDivisors, i) := by decide +kernel
  exact key n hlt (Nat.odd_iff.mp ho) ha
end

-- forge:entry arith_sum_lcm kind=proved origin=conjecture
section
/- Σ_{k=1}^n lcm(k,n) = (n/2)(1 + Σ_{d|n} dφ(d)) — group k by g = gcd(k,n): lcm = n·(k/g) with k/g a totative of d = n/g; Uses Mathlib2.nt2_two_mul_sum_coprime_eq_mul_totient at the inner step for every d > 1 (twice the totative sum is dφ(d)); the d = 1 term contributes the extra 1. -/
theorem arith_sum_lcm_aux1 (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    ∑ k ∈ (Finset.Icc 1 (d * e)).filter (fun k => (d * e) / Nat.gcd k (d * e) = d), Nat.lcm k (d * e)
      = ∑ j ∈ (Finset.Icc 1 d).filter (fun j => Nat.Coprime j d), d * e * j := by
  have hfib : ∀ k, (d * e) / Nat.gcd k (d * e) = d → Nat.gcd k (d * e) = e := by
    intro k hk
    have h1 := Nat.div_mul_cancel (Nat.gcd_dvd_right k (d * e))
    rw [hk] at h1
    exact Nat.eq_of_mul_eq_mul_left hd h1
  have hcop : ∀ j, Nat.gcd (e * j) (d * e) = e → Nat.Coprime j d := by
    intro j hj
    rw [mul_comm d e, Nat.gcd_mul_left] at hj
    exact Nat.eq_of_mul_eq_mul_left he (by rw [hj, mul_one])
  apply Finset.sum_nbij' (fun k => k / e) (fun j => e * j)
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk1, hk2⟩, hk3⟩ := hk
    have hg := hfib k hk3
    obtain ⟨j, rfl⟩ : e ∣ k := hg ▸ Nat.gcd_dvd_left k (d * e)
    rw [Nat.mul_div_cancel_left j he, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, hcop j hg⟩
    · rcases Nat.eq_zero_or_pos j with h0 | h0
      · rw [h0] at hk1
        simp at hk1
      · exact h0
    · rw [mul_comm d e] at hk2
      exact Nat.le_of_mul_le_mul_left hk2 he
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_Icc] at hj
    obtain ⟨⟨hj1, hj2⟩, hj3⟩ := hj
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.mul_pos he hj1, ?_⟩, ?_⟩
    · rw [mul_comm d e]
      exact Nat.mul_le_mul_left e hj2
    · rw [mul_comm d e, Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one hj3, mul_one, Nat.mul_div_cancel_left d he]
  · intro k hk
    rw [Finset.mem_filter] at hk
    have hg := hfib k hk.2
    exact Nat.mul_div_cancel' (hg ▸ Nat.gcd_dvd_left k (d * e))
  · intro j _
    exact Nat.mul_div_cancel_left j he
  · intro k hk
    rw [Finset.mem_filter] at hk
    have hg := hfib k hk.2
    obtain ⟨j, rfl⟩ : e ∣ k := hg ▸ Nat.gcd_dvd_left k (d * e)
    have hc := hcop j hg
    rw [Nat.mul_div_cancel_left j he, mul_comm d e, Nat.lcm_mul_left, Nat.Coprime.lcm_eq_mul hc]
    ring

theorem arith_sum_lcm_aux2 (d : ℕ) (hd : 0 < d) :
    2 * ∑ j ∈ (Finset.Icc 1 d).filter (fun j => Nat.Coprime j d), j = d * d.totient + if d = 1 then 1 else 0 := by
  by_cases h1 : d = 1
  · subst h1
    decide
  · rw [if_neg h1, add_zero, ← nt2_two_mul_sum_coprime_eq_mul_totient d (by omega)]
    congr 2
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨hj1, hj2⟩, hc⟩
      refine ⟨?_, hc⟩
      rcases Nat.lt_or_ge j d with h | h
      · exact h
      · have : j = d := le_antisymm hj2 h
        rw [this, Nat.coprime_self] at hc
        exact absurd hc h1
    · rintro ⟨hj, hc⟩
      refine ⟨⟨?_, hj.le⟩, hc⟩
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · rw [h0, Nat.coprime_zero_left] at hc
        exact absurd hc h1
      · exact h0

theorem arith_sum_lcm (n : ℕ) (hn : 0 < n) : 2 * ∑ k ∈ Finset.Icc 1 n, Nat.lcm k n = n * (1 + ∑ d ∈ n.divisors, d * d.totient) := by
  have hmaps : ∀ k ∈ Finset.Icc 1 n, n / Nat.gcd k n ∈ n.divisors := fun k _ =>
    Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.gcd_dvd_right k n), hn.ne'⟩
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.Icc 1 n) (t := n.divisors) (g := fun k => n / Nat.gcd k n)
    (f := fun k => Nat.lcm k n) hmaps]
  have hd : ∀ d ∈ n.divisors, ∑ k ∈ (Finset.Icc 1 n).filter (fun k => n / Nat.gcd k n = d), Nat.lcm k n
      = n * ∑ j ∈ (Finset.Icc 1 d).filter (fun j => Nat.Coprime j d), j := by
    intro d hd
    obtain ⟨e, rfl⟩ := (Nat.mem_divisors.mp hd).1
    have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have he0 : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    rw [arith_sum_lcm_aux1 d e hd0 he0, Finset.mul_sum]
  rw [Finset.sum_congr rfl hd, Finset.mul_sum]
  have h2 : ∀ d ∈ n.divisors, 2 * (n * ∑ j ∈ (Finset.Icc 1 d).filter (fun j => Nat.Coprime j d), j)
      = n * (d * d.totient + if d = 1 then 1 else 0) := by
    intro d hd
    rw [← arith_sum_lcm_aux2 d (Nat.pos_of_mem_divisors hd)]
    ring
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  simp [hn.ne', add_comm]
end

-- forge:entry arith_odd_perfect_not_dvd_105 kind=proved origin=conjecture
section
/- No odd perfect number is divisible by 105 — by Euler's form the exponents of 3 and 7 (≡ 3 mod 4) are even, so 3²·5·7² | n and σ(n)/n ≥ (13/9)(6/5)(57/49) > 2 (σ(n)/n is monotone under divisibility), contradiction. -/
theorem arith_odd_perfect_not_dvd_105 (n : ℕ) (ho : Odd n) (hp : n.Perfect) : ¬ 105 ∣ n := by
  intro h105
  obtain ⟨p, a, m, hpp, hp4, ha4, hpm, hn⟩ := Mathlib2.arith_odd_perfect_euler_form n ho hp
  have hq : ∀ q : ℕ, q.Prime → q % 4 = 3 → q ∣ n → q ∣ m := by
    intro q hq hq4 hqn
    rw [hn] at hqn
    rcases (Nat.Prime.dvd_mul hq).mp hqn with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hq hpp).mp (hq.dvd_of_dvd_pow h)
      omega
    · exact hq.dvd_of_dvd_pow h
  have h3 : 3 ∣ m := hq 3 Nat.prime_three (by norm_num) (Dvd.dvd.trans (by norm_num) h105)
  have h7 : 7 ∣ m := hq 7 (by norm_num) (by norm_num) (Dvd.dvd.trans (by norm_num) h105)
  have h5 : 5 ∣ n := Dvd.dvd.trans (by norm_num) h105
  have h21 : 21 ∣ m := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h7
  have h441 : 441 ∣ n := by
    rw [hn]
    exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd h21 2) _
  have h2205 : 2205 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h5 h441
  obtain ⟨k, hk⟩ := h2205
  have hab : Nat.Abundant 2205 := by
    rw [Mathlib2.ab_abundant_def]; decide +kernel
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rw [mul_zero] at hk; exact absurd hp.2 (by omega)
    · exact h
  have := Mathlib2.arith_abundant_mul 2205 k hab hk0
  rw [mul_comm, ← hk] at this
  exact absurd hp.1 (ne_of_gt this)
end

-- forge:entry fld_finite_field_sum_two_squares kind=proved origin=conjecture
section
/- Every element of a finite field is a sum of two squares — in characteristic 2 every element is a square (FiniteField.isSquare_of_char_two); otherwise apply FiniteField.exists_root_sum_quadratic to X^2 and X^2 - a (card is odd), or pigeonhole on the (q+1)/2 squares. -/
theorem fld_finite_field_sum_two_squares (K : Type) [Field K] [Fintype K] (a : K) : ∃ x y : K, x ^ 2 + y ^ 2 = a := by
  by_cases h : ringChar K = 2
  · obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two h a
    exact ⟨r, 0, by rw [hr]; ring⟩
  · have hF := FiniteField.odd_card_of_char_ne_two h
    have h1 : (Polynomial.X ^ 2 : Polynomial K).degree = 2 := by simp
    have h2 : (Polynomial.X ^ 2 - Polynomial.C a : Polynomial K).degree = 2 := by
      rw [Polynomial.degree_X_pow_sub_C (by norm_num)]; rfl
    obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic h1 h2 hF
    refine ⟨x, y, ?_⟩
    simp at hxy
    linear_combination hxy
end

-- forge:entry bld6_cyclotomic_coeff_symm kind=proved origin=conjecture
section
/- Uses Mathlib2.poly_cyclotomic_reverse_eq_self: rewrite the left side with reverse Φ_n = Φ_n and apply Polynomial.coeff_reverse with natDegree Φ_n = φ(n) (Polynomial.natDegree_cyclotomic) and revAt φ(n) k = φ(n) - k for k ≤ φ(n). -/
theorem bld6_cyclotomic_coeff_symm (n k : ℕ) (hn : 2 ≤ n) (hk : k ≤ n.totient) : (Polynomial.cyclotomic n ℤ).coeff k = (Polynomial.cyclotomic n ℤ).coeff (n.totient - k) := by
  have h := Mathlib2.poly_cyclotomic_reverse_eq_self n hn
  conv_lhs => rw [← h]
  rw [Polynomial.coeff_reverse, Polynomial.natDegree_cyclotomic, Polynomial.revAt_le hk]
end

-- forge:entry fld_irrational_cbrt_two kind=proved origin=conjecture
section
/- The real cube root of 2 is irrational — Uses Mathlib2.alg_rat_pow_ne_two at the only step: if x = (q : ℝ) then q^3 = 2 in ℚ by Rat.cast injectivity, contradicting alg_rat_pow_ne_two 3. -/
theorem fld_irrational_cbrt_two (x : ℝ) (hx : x ^ 3 = 2) : Irrational x := by
  rintro ⟨q, rfl⟩
  apply Mathlib2.alg_rat_pow_ne_two 3 (by norm_num) q
  exact_mod_cast hx
end

-- forge:entry bld6_cyclotomic_eval_neg_one_of_odd kind=proved origin=conjecture
section
/- Uses Mathlib2.poly_cyclotomic_two_mul_odd_comp_neg: Φ_n(-1) = (Φ_n ∘ (-X))(1) = Φ_(2n)(1) by the library identity (eval_comp); 2n with n odd > 1 is not a prime power, so Polynomial.eval_one_cyclotomic_not_prime_pow gives Φ_(2n)(1) = 1. -/
theorem bld6_cyclotomic_eval_neg_one_of_odd (n : ℕ) (hn : Odd n) (h1 : 1 < n) : Polynomial.eval (-1) (Polynomial.cyclotomic n ℤ) = 1 := by
  have h := Mathlib2.poly_cyclotomic_two_mul_odd_comp_neg n hn h1
  have h2 : Polynomial.eval 1 (Polynomial.cyclotomic (2 * n) ℤ) = 1 := by
    apply Polynomial.eval_one_cyclotomic_not_prime_pow
    intro p hp k hk
    have h2p : 2 ∣ p ^ k := ⟨n, hk⟩
    have hp2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 (Nat.prime_two.dvd_of_dvd_pow h2p)).symm
    subst hp2
    have hnd : n ∣ 2 ^ k := ⟨2, by rw [hk]; ring⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hnd
    subst hj
    rcases Nat.eq_zero_or_pos j with rfl | hjp
    · simp at h1
    · have : Even (2 ^ j) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
      exact (Nat.not_even_iff_odd.2 hn) this
  rw [h, Polynomial.eval_comp] at h2
  simpa using h2
end

-- forge:entry fld_prime_one_mod_three_eq_sq_add_three_sq kind=proved origin=conjecture
section
/- Every prime p ≡ 1 (mod 3) is of the form a^2 + 3b^2 — -3 is a square mod p (cube roots of unity in F_p), so p | x^2 + 3 for some x; Thue's lemma / pigeonhole gives 0 < a^2 + 3b^2 ≡ 0 mod p with a, b < √p, hence a^2 + 3b^2 ∈ {p, 2p, 3p}; 2p is impossible mod 4 (or mod 3) and 3p reduces to p by a = 3a'. -/
lemma fld_prime_one_mod_three_eq_sq_add_three_sq_aux1 (p : ℕ) (hp : p.Prime) (x : ℤ) :
    ∃ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ a ^ 2 < p ∧ b ^ 2 < p ∧ (p : ℤ) ∣ a - x * b := by
  haveI := Fact.mk hp
  have hk : p < (Nat.sqrt p + 1) * (Nat.sqrt p + 1) := Nat.lt_succ_sqrt p
  have hk1 : Nat.sqrt p * Nat.sqrt p ≤ p := Nat.sqrt_le p
  have hk2 : Nat.sqrt p * Nat.sqrt p < p := by
    rcases Nat.lt_or_ge (Nat.sqrt p * Nat.sqrt p) p with h | h
    · exact h
    · exfalso
      have he : Nat.sqrt p * Nat.sqrt p = p := le_antisymm hk1 h
      have hd : Nat.sqrt p ∣ p := ⟨Nat.sqrt p, he.symm⟩
      rcases (Nat.dvd_prime hp).1 hd with h1 | h1
      · rw [h1] at he; have := hp.two_le; omega
      · rw [h1] at he; have := hp.two_le; nlinarith
  generalize Nat.sqrt p = k at hk hk1 hk2
  let f : Fin (k + 1) × Fin (k + 1) → ZMod p :=
    fun uv => ((uv.1.val : ℤ) : ZMod p) - (x : ZMod p) * ((uv.2.val : ℤ) : ZMod p)
  obtain ⟨u, v, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by
    simp only [ZMod.card, Fintype.card_prod, Fintype.card_fin]; exact hk)
  refine ⟨(u.1.val : ℤ) - v.1.val, (u.2.val : ℤ) - v.2.val, ?_, ?_, ?_, ?_⟩
  · by_contra hc
    push_neg at hc
    apply hne
    have h1 : u.1.val = v.1.val := by omega
    have h2 : u.2.val = v.2.val := by omega
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  · have h1 := u.1.isLt
    have h2 := v.1.isLt
    have h3 : ((k * k : ℕ) : ℤ) < p := by exact_mod_cast hk2
    push_cast at h3
    have h4 : (u.1.val : ℤ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.1 h1
    have h5 : (v.1.val : ℤ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.1 h2
    have h6 : (0 : ℤ) ≤ u.1.val := Int.natCast_nonneg _
    have h7 : (0 : ℤ) ≤ v.1.val := Int.natCast_nonneg _
    have : ((u.1.val : ℤ) - v.1.val) ^ 2 ≤ (k : ℤ) * k := by
      nlinarith
    linarith
  · have h1 := u.2.isLt
    have h2 := v.2.isLt
    have h3 : ((k * k : ℕ) : ℤ) < p := by exact_mod_cast hk2
    push_cast at h3
    have h4 : (u.2.val : ℤ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.1 h1
    have h5 : (v.2.val : ℤ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.1 h2
    have h6 : (0 : ℤ) ≤ u.2.val := Int.natCast_nonneg _
    have h7 : (0 : ℤ) ≤ v.2.val := Int.natCast_nonneg _
    have : ((u.2.val : ℤ) - v.2.val) ^ 2 ≤ (k : ℤ) * k := by
      nlinarith
    linarith
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp only [f] at heq
    push_cast at heq
    linear_combination heq

lemma fld_prime_one_mod_three_eq_sq_add_three_sq_aux2 (p : ℕ) (hp : p.Prime) (d : ℕ) (hd : 0 < d)
    (hsq : ∃ x : ℤ, (p : ℤ) ∣ x ^ 2 + d) :
    ∃ a b : ℤ, 0 < a ^ 2 + d * b ^ 2 ∧ a ^ 2 + d * b ^ 2 < (1 + d) * p ∧
      (p : ℤ) ∣ a ^ 2 + d * b ^ 2 := by
  obtain ⟨x, hx⟩ := hsq
  obtain ⟨a, b, hne, ha, hb, hdvd⟩ := fld_prime_one_mod_three_eq_sq_add_three_sq_aux1 p hp x
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hd0 : (1 : ℤ) ≤ d := by exact_mod_cast hd
  refine ⟨a, b, ?_, ?_, ?_⟩
  · rcases hne with h | h
    · have : 0 < a ^ 2 := by positivity
      nlinarith [sq_nonneg b]
    · have : 0 < b ^ 2 := by positivity
      nlinarith [sq_nonneg a]
  · have : (d : ℤ) * b ^ 2 < d * p := by nlinarith
    nlinarith
  · have : a ^ 2 + (d : ℤ) * b ^ 2 = (a - x * b) * (a + x * b) + (x ^ 2 + d) * b ^ 2 := by ring
    rw [this]
    exact dvd_add (Dvd.dvd.mul_right hdvd _) (Dvd.dvd.mul_right hx _)

lemma fld_prime_one_mod_three_eq_sq_add_three_sq_aux3 (p : ℕ) (hp : p.Prime) (h : p % 3 = 1) :
    ∃ x : ℤ, (p : ℤ) ∣ x ^ 2 + (3 : ℕ) := by
  haveI := Fact.mk hp
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have h2 := hp.two_le
  obtain ⟨g, hg⟩ := exists_pow_ne_one_of_isCyclic (G := (ZMod p)ˣ) (k := (p - 1) / 3)
    (by omega) (by rw [hcard]; omega)
  have hw3 : ((g ^ ((p - 1) / 3) : (ZMod p)ˣ) : ZMod p) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← pow_mul]
    have : (p - 1) / 3 * 3 = p - 1 := by omega
    rw [this, ZMod.units_pow_card_sub_one_eq_one]
    rfl
  have hw1 : ((g ^ ((p - 1) / 3) : (ZMod p)ˣ) : ZMod p) ≠ 1 := by
    intro hh; exact hg (Units.ext hh)
  generalize ((g ^ ((p - 1) / 3) : (ZMod p)ˣ) : ZMod p) = w at hw3 hw1
  have hw : w ^ 2 + w + 1 = 0 := by
    have : (w - 1) * (w ^ 2 + w + 1) = 0 := by linear_combination hw3
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd (sub_eq_zero.1 h1) hw1
    · exact h1
  refine ⟨((2 * w + 1).val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val]
  linear_combination 4 * hw

theorem fld_prime_one_mod_three_eq_sq_add_three_sq (p : ℕ) (hp : p.Prime) (h : p % 3 = 1) : ∃ a b : ℕ, p = a ^ 2 + 3 * b ^ 2 := by
  obtain ⟨a, b, hpos, hlt, k, hk⟩ := fld_prime_one_mod_three_eq_sq_add_three_sq_aux2 p hp 3 (by norm_num)
    (fld_prime_one_mod_three_eq_sq_add_three_sq_aux3 p hp h)
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  push_cast at hpos hlt hk
  have hk0 : 0 < k := by
    by_contra hc
    push_neg at hc
    nlinarith
  have hk4 : k < 4 := by
    by_contra hc
    push_neg at hc
    nlinarith
  have hpodd : (p : ℤ) % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | h2
    · omega
    · omega
  have key : (p : ℤ) = a ^ 2 + 3 * b ^ 2 ∨ ∃ c : ℤ, (p : ℤ) = b ^ 2 + 3 * c ^ 2 := by
    have hk' : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk' with rfl | rfl | rfl
    · left; linarith
    · exfalso
      have h4 : (a ^ 2 + 3 * b ^ 2) % 4 = (p * 2) % 4 := by rw [hk]
      have ha : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
      have hb : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
      have hpp : (p : ℤ) % 4 = 1 ∨ (p : ℤ) % 4 = 3 := by omega
      rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;>
        rcases hpp with hpp | hpp <;>
        simp [pow_two, Int.add_emod, Int.mul_emod, ha, hb, hpp] at h4
    · right
      have h3 : (3 : ℤ) ∣ a ^ 2 := by
        have : a ^ 2 = 3 * (p - b ^ 2) := by linarith
        exact ⟨_, this⟩
      have h3a : (3 : ℤ) ∣ a := Int.Prime.dvd_pow' (by norm_num) h3
      obtain ⟨c, rfl⟩ := h3a
      exact ⟨c, by linarith⟩
  rcases key with hh | ⟨c, hh⟩
  · refine ⟨a.natAbs, b.natAbs, ?_⟩
    zify
    simpa [sq_abs] using hh
  · refine ⟨b.natAbs, c.natAbs, ?_⟩
    zify
    simpa [sq_abs] using hh
end

-- forge:entry bld6_cyclotomic_two_mul_odd_coeff kind=proved origin=conjecture
section
/- Uses Mathlib2.poly_cyclotomic_two_mul_odd_comp_neg: rewrite Φ_(2n) = Φ_n ∘ (-X) and compute the k-th coefficient of p.comp(-X) as (-1)^k p.coeff k (write -X = C(-1)·X and use the coefficient formula for comp with C a * X). -/
theorem bld6_cyclotomic_two_mul_odd_coeff (n k : ℕ) (hn : Odd n) (h1 : 1 < n) : (Polynomial.cyclotomic (2 * n) ℤ).coeff k = (-1) ^ k * (Polynomial.cyclotomic n ℤ).coeff k := by
  rw [Mathlib2.poly_cyclotomic_two_mul_odd_comp_neg n hn h1]
  have : (-Polynomial.X : Polynomial ℤ) = Polynomial.C (-1) * Polynomial.X := by simp
  rw [this, Polynomial.comp_C_mul_X_coeff, mul_comm]
end

-- forge:entry fld_sum_pow_finite_field kind=proved origin=conjecture
section
/- Complete power-sum formula over a finite field F_q: for k > 0, the sum of x^k over all x is -1 if (q-1) | k and 0 otherwise — since k > 0 the term x = 0 contributes 0, so the sum equals the sum over units, which is FiniteField.sum_pow_units. -/
open Finset in
theorem fld_sum_pow_finite_field (K : Type) [Field K] [Fintype K] (k : ℕ) (hk : 0 < k) : ∑ x : K, x ^ k = if (Fintype.card K - 1) ∣ k then (-1 : K) else 0 := by
  classical
  rw [← FiniteField.sum_pow_units K k]
  let φ : Kˣ ↪ K := ⟨fun x ↦ x, fun _ _ h => Units.ext h⟩
  have : univ.map φ = univ \ {0} := by
    ext x
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
      mem_singleton, φ] using isUnit_iff_ne_zero
  calc
    ∑ x : K, x ^ k = ∑ x ∈ univ \ {(0 : K)}, x ^ k := by
      rw [← sum_sdiff ({0} : Finset K).subset_univ, sum_singleton, zero_pow hk.ne', add_zero]
    _ = ∑ x : Kˣ, (x ^ k : K) := by simp [← this, univ.sum_map φ, φ]
end

-- forge:entry bld6_nat_pow_lt_pow_swap kind=proved origin=conjecture
section
/- Uses Mathlib2.calc_rpow_lt_rpow_swap_of_exp_le: apply it with x = m, y = n; the hypothesis e ≤ m follows from Real.exp_one_lt_d9 (e < 3 ≤ m); then convert rpow with natural exponents to Nat powers (Real.rpow_natCast, Nat.cast_lt). -/
theorem bld6_nat_pow_lt_pow_swap (m n : ℕ) (hm : 3 ≤ m) (hmn : m < n) : n ^ m < m ^ n := by
  have h3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hm' : (3:ℝ) ≤ m := by exact_mod_cast hm
  have h := Mathlib2.calc_rpow_lt_rpow_swap_of_exp_le (m:ℝ) (n:ℝ) (by linarith) (by exact_mod_cast hmn)
  rw [Real.rpow_natCast, Real.rpow_natCast] at h
  exact_mod_cast h
end

-- forge:entry fld_prime_one_three_mod_eight_eq_sq_add_two_sq kind=proved origin=conjecture
section
/- Every prime p ≡ 1 or 3 (mod 8) is of the form a^2 + 2b^2 — -2 is a square mod p (ZMod.exists_sq_eq_neg_two_iff / FiniteField.isSquare_neg_two_iff), so p | x^2 + 2; Thue's lemma gives 0 < a^2 + 2b^2 < 3p divisible by p, so it is p or 2p; in the latter case a is even and p = b^2 + 2(a/2)^2. Alternatively use that Z[√-2] is Euclidean. -/
theorem fld_prime_one_three_mod_eight_eq_sq_add_two_sq (p : ℕ) (hp : p.Prime) (h : p % 8 = 1 ∨ p % 8 = 3) : ∃ a b : ℕ, p = a ^ 2 + 2 * b ^ 2 := by
  haveI := Fact.mk hp
  have hp2 : p ≠ 2 := by rintro rfl; omega
  obtain ⟨y, hy⟩ := (ZMod.exists_sq_eq_neg_two_iff hp2).2 h
  have hx : ∃ x : ℤ, (p : ℤ) ∣ x ^ 2 + (2 : ℕ) := by
    refine ⟨(y.val : ℤ), ?_⟩
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val]
    linear_combination -hy
  obtain ⟨a, b, hpos, hlt, k, hk⟩ := fld_prime_one_mod_three_eq_sq_add_three_sq_aux2 p hp 2 (by norm_num) hx
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  push_cast at hpos hlt hk
  have hk0 : 0 < k := by
    by_contra hc
    push_neg at hc
    nlinarith
  have hk4 : k < 3 := by
    by_contra hc
    push_neg at hc
    nlinarith
  have key : (p : ℤ) = a ^ 2 + 2 * b ^ 2 ∨ ∃ c : ℤ, (p : ℤ) = b ^ 2 + 2 * c ^ 2 := by
    have hk' : k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl
    · left; linarith
    · right
      have h3 : (2 : ℤ) ∣ a ^ 2 := by
        have : a ^ 2 = 2 * (p - b ^ 2) := by linarith
        exact ⟨_, this⟩
      have h3a : (2 : ℤ) ∣ a := Int.Prime.dvd_pow' (by norm_num) h3
      obtain ⟨c, rfl⟩ := h3a
      exact ⟨c, by linarith⟩
  rcases key with hh | ⟨c, hh⟩
  · refine ⟨a.natAbs, b.natAbs, ?_⟩
    zify
    simpa [sq_abs] using hh
  · refine ⟨b.natAbs, c.natAbs, ?_⟩
    zify
    simpa [sq_abs] using hh
end

-- forge:entry bld6_succ_pow_lt_exp_pow_mul_factorial kind=proved origin=conjecture
section
/- Uses Mathlib2.calc_one_add_inv_pow_lt_exp: induction on n via (n+1)^n/n! = ∏_{k=1}^n (1+1/k)^k (ratio of consecutive terms is (1+1/(n+1))^(n+1)); each factor is < e by calc_one_add_inv_pow_lt_exp. Strengthens Mathlib2.calc_factorial_gt_div_exp_pow from n^n to (n+1)^n. -/
theorem bld6_succ_pow_lt_exp_pow_mul_factorial (n : ℕ) (hn : 0 < n) : ((n : ℝ) + 1) ^ n < Real.exp 1 ^ n * n.factorial := by
  induction n, hn using Nat.le_induction with
  | base =>
    have h2 : (2:ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have h3 : (1:ℝ) + 1 < Real.exp 1 := by linarith
    simpa [Nat.factorial] using h3
  | succ n hn ih =>
    have h := Mathlib2.calc_one_add_inv_pow_lt_exp (n+1) (by omega)
    push_cast at h
    have hpos : (0:ℝ) < (n:ℝ)+1 := by positivity
    have e1 : ((n:ℝ) + 1 + 1)^(n+1) = ((n:ℝ)+1)^(n+1) * (1 + 1/((n:ℝ)+1))^(n+1) := by
      rw [← mul_pow]; congr 1; field_simp
    rw [Nat.factorial_succ]
    push_cast
    rw [e1]
    calc ((n:ℝ)+1)^(n+1) * (1 + 1/((n:ℝ)+1))^(n+1) < ((n:ℝ)+1)^(n+1) * Real.exp 1 :=
            mul_lt_mul_of_pos_left h (by positivity)
       _ = ((n:ℝ)+1) * ((n+1)^n) * Real.exp 1 := by ring
       _ < ((n:ℝ)+1) * (Real.exp 1 ^ n * n.factorial) * Real.exp 1 := by
            have hE := Real.exp_pos 1
            gcongr
       _ = _ := by ring
end

-- forge:entry fld_prime_eq_sq_add_mul_add_sq_iff kind=proved origin=conjecture
section
/- A prime is represented by the Eisenstein norm form a^2 + ab + b^2 (a, b ≥ 0) iff p = 3 or p ≡ 1 (mod 3) — (→) a^2 + ab + b^2 mod 3 is never 2; (←) 3 = 1 + 1 + 1, and for p ≡ 1 mod 3 write p = c^2 + 3d^2 (the a^2 + 3b^2 theorem), then with c > d: a = c - d, b = 2d, and with c < d use the equivalent form (d - c, c + d) after symmetry, checking nonnegativity. -/
theorem fld_prime_eq_sq_add_mul_add_sq_iff (p : ℕ) (hp : p.Prime) : (∃ a b : ℕ, p = a ^ 2 + a * b + b ^ 2) ↔ p = 3 ∨ p % 3 = 1 := by
  constructor
  · rintro ⟨a, b, hab⟩
    have hmod : p % 3 ≠ 2 := by
      have h3 : p % 3 = (a ^ 2 + a * b + b ^ 2) % 3 := by rw [hab]
      have ha : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
      have hb : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
      rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
        simp [pow_two, Nat.add_mod, Nat.mul_mod, ha, hb] at h3 <;> omega
    by_cases h0 : p % 3 = 0
    · left
      have : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 this).symm
    · right; omega
  · rintro (rfl | h)
    · exact ⟨1, 1, by norm_num⟩
    · obtain ⟨c, d, hcd⟩ := fld_prime_one_mod_three_eq_sq_add_three_sq p hp h
      rcases le_total d c with hle | hle
      · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hle
        exact ⟨e, 2 * d, by rw [hcd]; ring⟩
      · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hle
        exact ⟨e, c + (c + e), by rw [hcd]; ring⟩
end

end Mathlib2
