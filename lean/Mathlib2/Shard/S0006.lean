/- Mathlib2 分片 6（forge 自动维护，追加式）。 -/
import Mathlib
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry r3_exists_dvd_pair_of_card_gt_s1h1 kind=proved origin=decomposition
section
/- r3_exists_dvd_pair_of_card_gt 的证明骨架中第 1 个空洞 -/
theorem r3_exists_dvd_pair_of_card_gt_s1h1 : ∀ (n m : ℕ), m ∈ Finset.Icc 1 (2 * n) → m / 2 ^ m.factorization 2 ∈ Finset.image (fun i => 2 * i + 1) (Finset.range n) := by
  intro n m hm
  rw [Finset.mem_Icc] at hm
  have h1 := Nat.ordCompl_le m 2
  have h2 := Nat.not_dvd_ordCompl Nat.prime_two (by omega : m ≠ 0)
  rw [Finset.mem_image]
  generalize m / 2 ^ m.factorization 2 = c at *
  refine ⟨c / 2, ?_, ?_⟩
  · rw [Finset.mem_range]; omega
  · omega
end

-- forge:entry r3_exists_dvd_pair_of_card_gt_s1h2 kind=proved origin=decomposition
section
/- r3_exists_dvd_pair_of_card_gt 的证明骨架中第 2 个空洞 -/
theorem r3_exists_dvd_pair_of_card_gt_s1h2 : ∀ (a b : ℕ), 0 < a → 0 < b → a / 2 ^ a.factorization 2 = b / 2 ^ b.factorization 2 → a ∣ b ∨ b ∣ a := by
  intro a b _ _ h
  have ea := Nat.ordProj_mul_ordCompl_eq_self a 2
  have eb := Nat.ordProj_mul_ordCompl_eq_self b 2
  rw [h] at ea
  rcases le_total (a.factorization 2) (b.factorization 2) with hle | hle
  · left
    have key : 2 ^ a.factorization 2 * (b / 2 ^ b.factorization 2) ∣ 2 ^ b.factorization 2 * (b / 2 ^ b.factorization 2) :=
      mul_dvd_mul_right (pow_dvd_pow 2 hle) _
    rwa [ea, eb] at key
  · right
    have key : 2 ^ b.factorization 2 * (b / 2 ^ b.factorization 2) ∣ 2 ^ a.factorization 2 * (b / 2 ^ b.factorization 2) :=
      mul_dvd_mul_right (pow_dvd_pow 2 hle) _
    rwa [ea, eb] at key
end

-- forge:entry r3_exists_dvd_pair_of_card_gt kind=proved origin=conjecture
section
/- Erdős: among any n+1 numbers from {1,...,2n} one divides another. Proof idea: map each m to its odd part m / 2^{v_2(m)}; the odd parts lie in the n odd numbers below 2n, so by pigeonhole two distinct elements share an odd part, and then the one with the smaller 2-adic valuation divides the other. -/
theorem r3_exists_dvd_pair_of_card_gt (n : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 (2 * n)) (hc : n < S.card) : ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a ∣ b := by
  have hodd : ∀ m ∈ Finset.Icc 1 (2 * n), m / 2 ^ m.factorization 2 ∈ (Finset.range n).image (fun i => 2 * i + 1) := by
    clear hc hS S
    (first | exact Mathlib2.r3_exists_dvd_pair_of_card_gt_s1h1 | apply Mathlib2.r3_exists_dvd_pair_of_card_gt_s1h1 <;> assumption | simpa using Mathlib2.r3_exists_dvd_pair_of_card_gt_s1h1)
  have hdiv : ∀ a b : ℕ, 0 < a → 0 < b → a / 2 ^ a.factorization 2 = b / 2 ^ b.factorization 2 → a ∣ b ∨ b ∣ a := by
    clear hodd hc hS S n
    (first | exact Mathlib2.r3_exists_dvd_pair_of_card_gt_s1h2 | apply Mathlib2.r3_exists_dvd_pair_of_card_gt_s1h2 <;> assumption | simpa using Mathlib2.r3_exists_dvd_pair_of_card_gt_s1h2)
  have hcard : ((Finset.range n).image (fun i => 2 * i + 1)).card < S.card :=
    lt_of_le_of_lt (Finset.card_image_le.trans (by simp)) hc
  obtain ⟨a, ha, b, hb, hab, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard (fun m hm => hodd m (hS hm))
  have ha0 : 0 < a := (Finset.mem_Icc.mp (hS ha)).1
  have hb0 : 0 < b := (Finset.mem_Icc.mp (hS hb)).1
  rcases hdiv a b ha0 hb0 he with h | h
  · exact ⟨a, ha, b, hb, hab, h⟩
  · exact ⟨b, hb, a, ha, hab.symm, h⟩
end

-- forge:entry r3_imo1990_sq_dvd_two_pow_add_one_s2h1 kind=proved origin=decomposition
section
/- r3_imo1990_sq_dvd_two_pow_add_one 的证明骨架中第 1 个空洞 -/
theorem r3_imo1990_sq_dvd_two_pow_add_one_s2h1 : ∀ (c m q : ℕ), m ≠ 0 → Nat.Prime q → q ∣ m → (∀ (r : ℕ), Nat.Prime r → r ∣ m → q ≤ r) → q ∣ 2 ^ (c * m) + 1 → q ∣ 2 ^ (2 * c) - 1 := by
  intro c m q hm0 hq hqm hmin hd
  haveI : Fact q.Prime := ⟨hq⟩
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc; simp
  have hcm : c * m ≠ 0 := Nat.mul_ne_zero (by omega) hm0
  have hq2 : q ≠ 2 := by
    rintro rfl
    have h2' : 2 ∣ 2 ^ (c * m) := dvd_pow_self 2 hcm
    have h1 : 2 ∣ 1 := (Nat.dvd_add_right h2').mp hd
    omega
  have h2ne : (2 : ZMod q) ≠ 0 := by
    intro h0
    have h0' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h0'
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h0')
  have hpow : (2 : ZMod q) ^ (c * m) = -1 := by
    have h0 : ((2 ^ (c * m) + 1 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hpow2 : (2 : ZMod q) ^ (2 * c * m) = 1 := by
    rw [mul_assoc, mul_comm, pow_mul, hpow]; norm_num
  have ho1 : orderOf (2 : ZMod q) ∣ 2 * c * m := orderOf_dvd_of_pow_eq_one hpow2
  have ho2 : orderOf (2 : ZMod q) ∣ q - 1 := ZMod.orderOf_dvd_card_sub_one h2ne
  have hcop : Nat.Coprime (q - 1) m := by
    by_contra hnc
    obtain ⟨r, hr, hr1, hr2⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    have h1 := hmin r hr hr2
    have h2 := Nat.le_of_dvd (by have := hq.two_le; omega) hr1
    have := hq.two_le
    omega
  have ho3 : orderOf (2 : ZMod q) ∣ 2 * c := (Nat.Coprime.coprime_dvd_left ho2 hcop).dvd_of_dvd_mul_right ho1
  have hfin : (2 : ZMod q) ^ (2 * c) = 1 := orderOf_dvd_iff_pow_eq_one.mp ho3
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow]
  push_cast
  rw [hfin]; ring
end

-- forge:entry r3_imo2000_q2_s1h1 kind=proved origin=decomposition
section
/- r3_imo2000_q2 的证明骨架中第 1 个空洞 -/
theorem r3_imo2000_q2_s1h1 : ∀ (a b c : ℝ), 0 < a → 0 < b → 0 < c → a * b * c = 1 → ∀ (x y z : ℝ), 0 < x → 0 < y → 0 < z → x * y * z = 1 → (x - 1 + 1 / y) * (y - 1 + 1 / z) ≤ x ^ 2 * y := by
  intro _ _ _ _ _ _ _ x y z hx hy hz h
  have hz' : 1 / z = x * y := by rw [div_eq_iff hz.ne']; linarith
  have hu : y * (x - 1 + 1 / y) = x * y - y + 1 := by field_simp
  rw [hz']
  have key : y * ((x - 1 + 1 / y) * (y - 1 + x * y)) ≤ y * (x ^ 2 * y) := by
    have : y * ((x - 1 + 1 / y) * (y - 1 + x * y)) = (x * y - y + 1) * (y - 1 + x * y) := by
      rw [← mul_assoc, hu]
    rw [this]; nlinarith [sq_nonneg (y - 1)]
  exact le_of_mul_le_mul_left key hy
end

-- forge:entry r3_imo1990_sq_dvd_two_pow_add_one_s2h2 kind=proved origin=decomposition
section
/- r3_imo1990_sq_dvd_two_pow_add_one 的证明骨架中第 2 个空洞 -/
theorem r3_imo1990_sq_dvd_two_pow_add_one_s2h2 : (∀ (c m q : ℕ), m ≠ 0 → Nat.Prime q → q ∣ m → (∀ (r : ℕ), Nat.Prime r → r ∣ m → q ≤ r) → q ∣ 2 ^ (c * m) + 1 → q ∣ 2 ^ (2 * c) - 1) → ∀ (n : ℕ), n ^ 2 ∣ 2 ^ n + 1 → ¬9 ∣ n := by
  intro _ n h h9
  have hn0 : n ≠ 0 := by
    rintro rfl
    norm_num at h
  have hodd : Odd n := by
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    have h2n : 2 ∣ n := hne.two_dvd
    have h2 : 2 ∣ 2 ^ n + 1 := (h2n.trans (dvd_pow_self n two_ne_zero)).trans h
    have h2' : 2 ∣ 2 ^ n := dvd_pow_self 2 hn0
    have h1 : 2 ∣ 1 := (Nat.dvd_add_right h2').mp h2
    omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hl := padicValNat.pow_add_pow (x := 2) (y := 1) (p := 3) (by decide) (by norm_num) (by norm_num) hodd
  rw [one_pow] at hl
  have e1 : padicValNat 3 (2 + 1) = 1 := by norm_num
  have hv : 3 ^ (padicValNat 3 n) ∣ n := pow_padicValNat_dvd
  have h4 : 3 ^ (padicValNat 3 n * 2) ∣ 2 ^ n + 1 := by
    rw [pow_mul]; exact (pow_dvd_pow_of_dvd hv 2).trans h
  have h5 := (padicValNat_dvd_iff_le (by positivity)).mp h4
  have h6 : 2 ≤ padicValNat 3 n :=
    (padicValNat_dvd_iff_le hn0).mp (by rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact h9)
  omega
end

-- forge:entry r3_imo2000_q2_s1h2 kind=proved origin=decomposition
section
/- r3_imo2000_q2 的证明骨架中第 2 个空洞 -/
theorem r3_imo2000_q2_s1h2 : ∀ (a b c : ℝ), 0 < a → 0 < b → 0 < c → a * b * c = 1 → (∀ (x y z : ℝ), 0 < x → 0 < y → 0 < z → x * y * z = 1 → (x - 1 + 1 / y) * (y - 1 + 1 / z) ≤ x ^ 2 * y) → ∀ (x y z : ℝ), 0 < x → 0 < y → 0 < z → x * y * z = 1 → 0 ≤ x - 1 + 1 / y ∨ 0 ≤ y - 1 + 1 / z := by
  intro _ _ _ _ _ _ _ _ x y z hx hy hz h
  have hz' : 1 / z = x * y := by rw [div_eq_iff hz.ne']; linarith
  have hu : y * (x - 1 + 1 / y) = x * y - y + 1 := by field_simp
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have e : y * (x - 1 + 1 / y) + (y - 1 + 1 / z) = 2 * (x * y) := by rw [hz', hu]; ring
  have := mul_pos hx hy
  have := mul_neg_of_pos_of_neg hy h1
  linarith
end

-- forge:entry r3_imo1990_sq_dvd_two_pow_add_one_s2h3 kind=proved origin=decomposition
section
/- r3_imo1990_sq_dvd_two_pow_add_one 的证明骨架中第 3 个空洞 -/
theorem r3_imo1990_sq_dvd_two_pow_add_one_s2h3 : (∀ (c m q : ℕ), m ≠ 0 → Nat.Prime q → q ∣ m → (∀ (r : ℕ), Nat.Prime r → r ∣ m → q ≤ r) → q ∣ 2 ^ (c * m) + 1 → q ∣ 2 ^ (2 * c) - 1) → (∀ (n : ℕ), n ^ 2 ∣ 2 ^ n + 1 → ¬9 ∣ n) → ∀ (n : ℕ), ¬7 ∣ 2 ^ n + 1 := by
  intro _ _ n hd
  have key : ∀ k : ℕ, 2 ^ k % 7 = 1 ∨ 2 ^ k % 7 = 2 ∨ 2 ^ k % 7 = 4 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      generalize 2 ^ k = x at ih ⊢
      omega
  have hk := key n
  generalize 2 ^ n = x at hk hd
  omega
end

-- forge:entry r3_imo2000_q2_s1h3 kind=proved origin=decomposition
section
/- r3_imo2000_q2 的证明骨架中第 3 个空洞 -/
theorem r3_imo2000_q2_s1h3 : ∀ (a b c : ℝ), 0 < a → 0 < b → 0 < c → a * b * c = 1 → (∀ (x y z : ℝ), 0 < x → 0 < y → 0 < z → x * y * z = 1 → (x - 1 + 1 / y) * (y - 1 + 1 / z) ≤ x ^ 2 * y) → (∀ (x y z : ℝ), 0 < x → 0 < y → 0 < z → x * y * z = 1 → 0 ≤ x - 1 + 1 / y ∨ 0 ≤ y - 1 + 1 / z) → ∀ (u v w p q r : ℝ), 0 ≤ u → 0 ≤ v → 0 ≤ w → u * v ≤ p → v * w ≤ q → w * u ≤ r → p * q * r = 1 → u * v * w ≤ 1 := by
  intro _ _ _ _ _ _ _ _ _ u v w p q r hu hv hw huv hvw hwu hpqr
  have a1 : (u * v) * (v * w) ≤ p * q :=
    mul_le_mul huv hvw (mul_nonneg hv hw) (le_trans (mul_nonneg hu hv) huv)
  have a2 : (u * v) * (v * w) * (w * u) ≤ p * q * r :=
    mul_le_mul a1 hwu (mul_nonneg hw hu)
      (le_trans (mul_nonneg (mul_nonneg hu hv) (mul_nonneg hv hw)) a1)
  have e : (u * v * w) ^ 2 = (u * v) * (v * w) * (w * u) := by ring
  have h0 := mul_nonneg (mul_nonneg hu hv) hw
  by_contra hlt
  push_neg at hlt
  nlinarith
end

-- forge:entry r3_hardy_inequality_finite_s1h1 kind=proved origin=decomposition
section
/- r3_hardy_inequality_finite 的证明骨架中第 1 个空洞 -/
theorem r3_hardy_inequality_finite_s1h1 : ∀ (a : ℕ → ℝ) (k : ℕ), ((∑ i ∈ Finset.range (k + 1), a i) / (↑k + 1)) ^ 2 - 2 * ((∑ i ∈ Finset.range (k + 1), a i) / (↑k + 1)) * a k ≤ (∑ i ∈ Finset.range k, a i) ^ 2 / ↑k - (∑ i ∈ Finset.range (k + 1), a i) ^ 2 / (↑k + 1) := by
  intro a k
  rcases k with _ | k
  · norm_num [Finset.sum_range_one]
    nlinarith [sq_nonneg (a 0)]
  · rw [Finset.sum_range_succ _ (k + 1)]
    have hK : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    generalize ((k + 1 : ℕ) : ℝ) = K at *
    generalize ∑ i ∈ Finset.range (k + 1), a i = s
    generalize a (k + 1) = x
    have hK1 : (0 : ℝ) < K + 1 := by linarith
    obtain ⟨A', rfl⟩ : ∃ A', s = K * A' := ⟨s / K, by field_simp⟩
    obtain ⟨A, rfl⟩ : ∃ A, x = (K + 1) * A - K * A' := ⟨(x + K * A') / (K + 1), by field_simp <;> ring⟩
    have e1 : (K * A' + ((K + 1) * A - K * A')) / (K + 1) = A := by
      rw [div_eq_iff hK1.ne']; ring
    have e2 : (K * A') ^ 2 / K = K * A' ^ 2 := by
      rw [div_eq_iff hK.ne']; ring
    have e3 : (K * A' + ((K + 1) * A - K * A')) ^ 2 / (K + 1) = (K + 1) * A ^ 2 := by
      rw [div_eq_iff hK1.ne']; ring
    rw [e1, e2, e3]
    nlinarith [mul_nonneg hK.le (sq_nonneg (A - A'))]
end

-- forge:entry r3_imo1990_sq_dvd_two_pow_add_one kind=proved origin=conjecture
section
/- IMO 1990 Q3: n^2 | 2^n + 1 only for n = 1, 3. Builds on Mathlib2.nt2_lte_three_two_pow_three_pow_add_one (LTE at 3; here one needs the general form v_3(2^n+1) = v_3(n)+1 for odd n) and the least-prime-factor/order technique of Mathlib2.nt2_dvd_two_pow_sub_one_eq_one. Proof idea: n is odd; least prime factor is 3 (order of 2 mod p divides gcd(2n, p-1) = 2); LTE gives 2 v_3(n) ≤ v_3(n)+1 so n = 3m with 3 ∤ m; the least prime factor q of m has ord_q(2) | gcd(6m, q-1) | 6, so q | 63, q = 7, but 2^n+1 mod 7 ∈ {2,3,5}: contradiction, so m = 1. -/
theorem r3_imo1990_sq_dvd_two_pow_add_one (n : ℕ) (h : n ^ 2 ∣ 2 ^ n + 1) : n = 1 ∨ n = 3 := by
  revert n
  have h_ord : ∀ c m q : ℕ, m ≠ 0 → q.Prime → q ∣ m → (∀ r : ℕ, r.Prime → r ∣ m → q ≤ r) →
      q ∣ 2 ^ (c * m) + 1 → q ∣ 2 ^ (2 * c) - 1 := by
    (first | exact Mathlib2.r3_imo1990_sq_dvd_two_pow_add_one_s2h1 | apply Mathlib2.r3_imo1990_sq_dvd_two_pow_add_one_s2h1 <;> assumption | simpa using Mathlib2.r3_imo1990_sq_dvd_two_pow_add_one_s2h1)
  have h_lte : ∀ n : ℕ, n ^ 2 ∣ 2 ^ n + 1 → ¬ 9 ∣ n := by
    (first | exact Mathlib2.r3_imo1990_sq_dvd_two_pow_add_one_s2h2 | apply Mathlib2.r3_imo1990_sq_dvd_two_pow_add_one_s2h2 <;> assumption | simpa using Mathlib2.r3_imo1990_sq_dvd_two_pow_add_one_s2h2)
  have h7 : ∀ n : ℕ, ¬ 7 ∣ 2 ^ n + 1 := by
    (first | exact Mathlib2.r3_imo1990_sq_dvd_two_pow_add_one_s2h3 | apply Mathlib2.r3_imo1990_sq_dvd_two_pow_add_one_s2h3 <;> assumption | simpa using Mathlib2.r3_imo1990_sq_dvd_two_pow_add_one_s2h3)
  intro n h
  have hn0 : n ≠ 0 := by
    rintro rfl
    norm_num at h
  by_cases hn1 : n = 1
  · left; exact hn1
  right
  have hdvd : n ∣ 2 ^ n + 1 := (dvd_pow_self n two_ne_zero).trans h
  have hp := Nat.minFac_prime hn1
  have hpn := Nat.minFac_dvd n
  have h3 : n.minFac ∣ 2 ^ (2 * 1) - 1 :=
    h_ord 1 n n.minFac hn0 hp hpn (fun r hr hrn => Nat.minFac_le_of_dvd hr.two_le hrn)
      (by rw [one_mul]; exact hpn.trans hdvd)
  have e3 : (2 ^ (2 * 1) - 1 : ℕ) = 3 := by norm_num
  rw [e3] at h3
  have hp3 : n.minFac = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
  have h3n : 3 ∣ n := by rw [← hp3]; exact hpn
  obtain ⟨m, rfl⟩ := h3n
  have hm3 : ¬ 3 ∣ m := fun ⟨k, hk⟩ => h_lte (3 * m) h ⟨k, by rw [hk]; ring⟩
  by_cases hm1 : m = 1
  · subst hm1; rfl
  exfalso
  have hq := Nat.minFac_prime hm1
  have hqm := Nat.minFac_dvd m
  have h63 : m.minFac ∣ 2 ^ (2 * 3) - 1 :=
    h_ord 3 m m.minFac (by omega) hq hqm (fun r hr hrm => Nat.minFac_le_of_dvd hr.two_le hrm)
      (hqm.trans ((dvd_mul_left m 3).trans hdvd))
  have e63 : (2 ^ (2 * 3) - 1 : ℕ) = 3 ^ 2 * 7 := by norm_num
  rw [e63] at h63
  rcases (Nat.Prime.dvd_mul hq).mp h63 with h9 | h7'
  · have h3' := hq.dvd_of_dvd_pow h9
    have e : m.minFac = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3'
    exact hm3 (by rw [← e]; exact hqm)
  · have e : m.minFac = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h7'
    exact h7 (3 * m) (by rw [← e]; exact hqm.trans ((dvd_mul_left m 3).trans hdvd))
end

-- forge:entry r3_imo2000_q2_s1h4 kind=proved origin=decomposition
section
/- r3_imo2000_q2 的证明骨架中第 4 个空洞 -/
theorem r3_imo2000_q2_s1h4 : ∀ (a b c : ℝ), 0 < a → 0 < b → 0 < c → a * b * c = 1 → (∀ (x y z : ℝ), 0 < x → 0 < y → 0 < z → x * y * z = 1 → (x - 1 + 1 / y) * (y - 1 + 1 / z) ≤ x ^ 2 * y) → (∀ (x y z : ℝ), 0 < x → 0 < y → 0 < z → x * y * z = 1 → 0 ≤ x - 1 + 1 / y ∨ 0 ≤ y - 1 + 1 / z) → (∀ (u v w p q r : ℝ), 0 ≤ u → 0 ≤ v → 0 ≤ w → u * v ≤ p → v * w ≤ q → w * u ≤ r → p * q * r = 1 → u * v * w ≤ 1) → ∀ (u v w : ℝ), 0 ≤ u ∨ 0 ≤ v → 0 ≤ v ∨ 0 ≤ w → 0 ≤ w ∨ 0 ≤ u → 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ w ∨ u * v * w ≤ 0 := by
  intro _ _ _ _ _ _ _ _ _ _ u v w s1 s2 s3
  rcases lt_or_ge u 0 with hu | hu
  · have hv : 0 ≤ v := by rcases s1 with h | h; · linarith
                          · exact h
    have hw : 0 ≤ w := by rcases s3 with h | h; · exact h
                          · linarith
    right
    have : u * v * w = u * (v * w) := by ring
    rw [this]
    exact mul_nonpos_iff.2 (Or.inr ⟨hu.le, mul_nonneg hv hw⟩)
  rcases lt_or_ge v 0 with hv | hv
  · have hw : 0 ≤ w := by rcases s2 with h | h; · linarith
                          · exact h
    right
    have : u * v * w = v * (u * w) := by ring
    rw [this]
    exact mul_nonpos_iff.2 (Or.inr ⟨hv.le, mul_nonneg hu hw⟩)
  rcases lt_or_ge w 0 with hw | hw
  · right
    have : u * v * w = w * (u * v) := by ring
    rw [this]
    exact mul_nonpos_iff.2 (Or.inr ⟨hw.le, mul_nonneg hu hv⟩)
  · exact Or.inl ⟨hu, hv, hw⟩
end

-- forge:entry r3_hardy_inequality_finite_s1h2 kind=proved origin=decomposition
section
/- r3_hardy_inequality_finite 的证明骨架中第 2 个空洞 -/
theorem r3_hardy_inequality_finite_s1h2 : ∀ (a : ℕ → ℝ) (n : ℕ), (∀ (k : ℕ), ((∑ i ∈ Finset.range (k + 1), a i) / (↑k + 1)) ^ 2 - 2 * ((∑ i ∈ Finset.range (k + 1), a i) / (↑k + 1)) * a k ≤ (∑ i ∈ Finset.range k, a i) ^ 2 / ↑k - (∑ i ∈ Finset.range (k + 1), a i) ^ 2 / (↑k + 1)) → ∑ k ∈ Finset.range n, ((∑ i ∈ Finset.range (k + 1), a i) / (↑k + 1)) ^ 2 ≤ 2 * ∑ k ∈ Finset.range n, (∑ i ∈ Finset.range (k + 1), a i) / (↑k + 1) * a k := by
  intro a n hpt
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ, ∀ k, f k = (∑ i ∈ Finset.range k, a i) ^ 2 / (k : ℝ) := ⟨_, fun _ => rfl⟩
  have h1 : ∀ k : ℕ, ((∑ i ∈ Finset.range (k + 1), a i) / ((k : ℝ) + 1)) ^ 2 - 2 * ((∑ i ∈ Finset.range (k + 1), a i) / ((k : ℝ) + 1)) * a k ≤ f k - f (k + 1) := by
    intro k
    rw [hf, hf, Nat.cast_add_one]
    exact hpt k
  have h2 := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range n) => h1 k)
  rw [Finset.sum_range_sub', Finset.sum_sub_distrib] at h2
  have h3 : 0 ≤ f n := by rw [hf]; positivity
  have h4 : f 0 = 0 := by rw [hf]; simp
  have h5 : ∑ k ∈ Finset.range n, 2 * ((∑ i ∈ Finset.range (k + 1), a i) / ((k : ℝ) + 1)) * a k = 2 * ∑ k ∈ Finset.range n, (∑ i ∈ Finset.range (k + 1), a i) / ((k : ℝ) + 1) * a k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  linarith
end

-- forge:entry r3_imo1990_sq_dvd_two_pow_add_one_s1h1 kind=disproved origin=decomposition
section
/- r3_imo1990_sq_dvd_two_pow_add_one 的证明骨架中第 1 个空洞 -/
theorem r3_imo1990_sq_dvd_two_pow_add_one_s1h1_disproof : ¬ (∀ (c m q : ℕ), Nat.Prime q → q ∣ m → (∀ (r : ℕ), Nat.Prime r → r ∣ m → q ≤ r) → q ∣ 2 ^ (c * m) + 1 → q ∣ 2 ^ (2 * c) - 1) := by
  intro h
  have := h 1 0 2 Nat.prime_two (dvd_zero 2) (fun r hr _ => hr.two_le) (by norm_num)
  norm_num at this
end

-- forge:entry r3_hardy_inequality_finite_s1h3 kind=disproved origin=decomposition
section
/- r3_hardy_inequality_finite 的证明骨架中第 3 个空洞 -/
theorem r3_hardy_inequality_finite_s1h3_disproof : ¬ (∀ (T B Q : ℝ), 0 ≤ T → T ≤ 2 * Q → Q ^ 2 ≤ T * B → T ≤ 4 * B) := by
  intro h
  have := h 0 (-1) 0 (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
end

-- forge:entry r3_imo2000_q2 kind=proved origin=conjecture
section
/- IMO 2000 Q2. Proof idea: substitute a = x/y, b = y/z, c = z/x to get (x-y+z)(y-z+x)(z-x+y) ≤ xyz (Schur-type); at most one factor is negative (sum of any two is positive), in which case the product is ≤ 0; otherwise multiply the three pairwise AM-GM bounds (x-y+z)(y-z+x) ≤ x^2 and take square roots. -/
theorem r3_imo2000_q2 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : (a - 1 + 1 / b) * (b - 1 + 1 / c) * (c - 1 + 1 / a) ≤ 1 := by
  have pair : ∀ x y z : ℝ, 0 < x → 0 < y → 0 < z → x * y * z = 1 →
      (x - 1 + 1 / y) * (y - 1 + 1 / z) ≤ x ^ 2 * y := by
    exact Mathlib2.r3_imo2000_q2_s1h1 a b c ha hb hc habc
  have sgn : ∀ x y z : ℝ, 0 < x → 0 < y → 0 < z → x * y * z = 1 →
      0 ≤ x - 1 + 1 / y ∨ 0 ≤ y - 1 + 1 / z := by
    exact Mathlib2.r3_imo2000_q2_s1h2 a b c ha hb hc habc pair
  have comb_nonneg : ∀ u v w p q r : ℝ, 0 ≤ u → 0 ≤ v → 0 ≤ w → u * v ≤ p → v * w ≤ q → w * u ≤ r →
      p * q * r = 1 → u * v * w ≤ 1 := by
    exact Mathlib2.r3_imo2000_q2_s1h3 a b c ha hb hc habc pair sgn
  have comb_sign : ∀ u v w : ℝ, (0 ≤ u ∨ 0 ≤ v) → (0 ≤ v ∨ 0 ≤ w) → (0 ≤ w ∨ 0 ≤ u) →
      (0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ w) ∨ u * v * w ≤ 0 := by
    exact Mathlib2.r3_imo2000_q2_s1h4 a b c ha hb hc habc pair sgn comb_nonneg
  have e2 : b * c * a = 1 := by rw [← habc]; ring
  have e3 : c * a * b = 1 := by rw [← habc]; ring
  have h1 := pair a b c ha hb hc habc
  have h2 := pair b c a hb hc ha e2
  have h3 := pair c a b hc ha hb e3
  have s1 := sgn a b c ha hb hc habc
  have s2 := sgn b c a hb hc ha e2
  have s3 := sgn c a b hc ha hb e3
  rcases comb_sign _ _ _ s1 s2 s3 with ⟨hu, hv, hw⟩ | hneg
  · refine comb_nonneg _ _ _ _ _ _ hu hv hw h1 h2 h3 ?_
    have : a ^ 2 * b * (b ^ 2 * c) * (c ^ 2 * a) = (a * b * c) ^ 3 := by ring
    rw [this, habc]; norm_num
  · linarith
end

-- forge:entry r3_hardy_inequality_finite_s2h1 kind=proved origin=decomposition
section
/- r3_hardy_inequality_finite 的证明骨架中第 1 个空洞 -/
theorem r3_hardy_inequality_finite_s2h1 : ∀ (T B Q : ℝ), 0 ≤ T → 0 ≤ B → T ≤ 2 * Q → Q ^ 2 ≤ T * B → T ≤ 4 * B := by
  intro T B Q hT hB h1 h2
  by_contra hlt
  push_neg at hlt
  have hQ : 0 ≤ Q := by linarith
  have h3 : T ^ 2 ≤ 4 * Q ^ 2 := by nlinarith
  have hT' : 0 < T := by linarith
  have h4 : 4 * (T * B) < T * T := by nlinarith
  nlinarith
end

-- forge:entry r3_hardy_inequality_finite kind=proved origin=conjecture
section
/- Hardy's inequality for finite sums with the sharp constant 4 (p = 2): the sum of squares of the running averages is at most 4 times the sum of squares. Proof idea: with α_k the k-th average, a_k = kα_k - (k-1)α_{k-1}, show α_k^2 - 2α_k a_k ≤ (k-1)α_{k-1}^2 - kα_k^2 (AM-GM on the cross term), telescope to get Σα_k^2 ≤ 2Σα_k a_k, then Cauchy–Schwarz and cancel sqrt(Σα_k^2). -/
theorem r3_hardy_inequality_finite (a : ℕ → ℝ) (n : ℕ) : ∑ k ∈ Finset.range n, ((∑ i ∈ Finset.range (k + 1), a i) / ((k : ℝ) + 1)) ^ 2 ≤ 4 * ∑ k ∈ Finset.range n, a k ^ 2 := by
  have htel := r3_hardy_inequality_finite_s1h2 a n (r3_hardy_inequality_finite_s1h1 a)
  have hfin : ∀ T B Q : ℝ, 0 ≤ T → 0 ≤ B → T ≤ 2 * Q → Q ^ 2 ≤ T * B → T ≤ 4 * B := by
    clear htel a n
    (first | exact Mathlib2.r3_hardy_inequality_finite_s2h1 | apply Mathlib2.r3_hardy_inequality_finite_s2h1 <;> assumption | simpa using Mathlib2.r3_hardy_inequality_finite_s2h1)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n)
    (fun k => (∑ i ∈ Finset.range (k + 1), a i) / ((k : ℝ) + 1)) a
  exact hfin _ _ _ (Finset.sum_nonneg (fun k _ => sq_nonneg _)) (Finset.sum_nonneg (fun k _ => sq_nonneg _)) htel hcs
end

-- forge:entry r3_recursive_seq_add_inv_bounds kind=proved origin=conjecture
section
/- Classic: for a_0 = 1, a_{n+1} = a_n + 1/a_n one has 14 < a_100 < 15. Proof idea: a_n > 0 and a_{n+1}^2 = a_n^2 + 2 + 1/a_n^2, so by induction a_n^2 ≥ 2n+1 (lower bound 201 > 196); feeding this back, a_n^2 ≤ 2n + 1 + Σ_{k<n} 1/(2k+1), and the sum for n = 100 must be bounded numerically (e.g. < 24) to get a_100^2 < 225. -/
theorem r3_recursive_seq_add_inv_bounds (a : ℕ → ℝ) (h0 : a 0 = 1) (h : ∀ n, a (n + 1) = a n + 1 / a n) : 14 < a 100 ∧ a 100 < 15 := by
  have hpos : ∀ n, 0 < a n := by
    intro n
    induction n with
    | zero => rw [h0]; norm_num
    | succ n ih => rw [h]; positivity
  have hsq : ∀ n, a (n + 1) ^ 2 = a n ^ 2 + 2 + 1 / a n ^ 2 := by
    intro n
    have := hpos n
    rw [h]; field_simp; ring
  have hlow : ∀ n : ℕ, 2 * (n : ℝ) + 1 ≤ a n ^ 2 := by
    intro n
    induction n with
    | zero => rw [h0]; norm_num
    | succ n ih =>
      rw [hsq]
      have : 0 < 1 / a n ^ 2 := by have := hpos n; positivity
      push_cast; linarith
  have hup : ∀ n : ℕ, a (n + 4) ^ 2 ≤ 2 * ((n : ℝ) + 4) + 3 + n / 9 := by
    intro n
    induction n with
    | zero =>
      have h1 : a 1 = 2 := by rw [h, h0]; norm_num
      have h2 : a 2 = 5 / 2 := by rw [h, h1]; norm_num
      have h3 : a 3 = 29 / 10 := by rw [h, h2]; norm_num
      have h4 : a 4 = 941 / 290 := by rw [h, h3]; norm_num
      simp only [Nat.zero_add]
      rw [h4]; norm_num
    | succ n ih =>
      rw [show n + 1 + 4 = (n + 4) + 1 by ring, hsq]
      have hl := hlow (n + 4)
      push_cast at hl
      have h9 : (9 : ℝ) ≤ a (n + 4) ^ 2 := by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
      have : 1 / a (n + 4) ^ 2 ≤ 1 / 9 := one_div_le_one_div_of_le (by norm_num) h9
      push_cast; linarith
  have hp := hpos 100
  have l := hlow 100
  have u := hup 96
  norm_num at l u
  constructor <;> nlinarith
end

-- forge:entry r3_fib_iff_five_sq_pm_four_is_square_s1h1 kind=proved origin=decomposition
section
/- r3_fib_iff_five_sq_pm_four_is_square 的证明骨架中第 1 个空洞 -/
theorem r3_fib_iff_five_sq_pm_four_is_square_s1h1 : ∀ (n : ℕ), ((Nat.fib (n + 1)) : ℤ) ^ 2 - ((Nat.fib (n + 1)) : ℤ) * ((Nat.fib n) : ℤ) - ((Nat.fib n) : ℤ) ^ 2 = (-1) ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.fib_add_two, pow_succ]
    push_cast
    linear_combination -ih
end

end Mathlib2
