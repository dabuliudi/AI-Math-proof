/- Mathlib2 分片 2（forge 自动维护，追加式）。 -/
import Mathlib
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry nt_pow4_add_four_not_prime kind=proved origin=conjecture
section
/- n^4 + 4 is composite for n > 1 (Sophie Germain identity). -/
theorem nt_pow4_add_four_not_prime (n : ℕ) (h : 1 < n) : ¬ (n ^ 4 + 4).Prime := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e : (m + 2) ^ 4 + 4 = (m * m + 2 * m + 2) * (m * m + 6 * m + 10) := by ring
  intro hp
  rw [e] at hp
  rcases hp.eq_one_or_self_of_dvd (m * m + 2 * m + 2) (Dvd.intro _ rfl) with h1 | h1
  · nlinarith [Nat.zero_le (m * m), Nat.zero_le m]
  · have h2 : (m * m + 2 * m + 2) * 1 = (m * m + 2 * m + 2) * (m * m + 6 * m + 10) := by
      rw [mul_one]; exact h1
    have h3 := Nat.eq_of_mul_eq_mul_left (by positivity) h2
    nlinarith [Nat.zero_le (m * m), Nat.zero_le m]
end

-- forge:entry ms_divrad_dvd_derivative_v2 kind=proved origin=paper
section
/- For nonzero a in k[t], a/rad(a) divides the derivative a'. -/
theorem ms_divrad_dvd_derivative_v2 {k : Type*} [Field k] [DecidableEq k] (a : Polynomial k) (ha : a ≠ 0) : a / UniqueFactorizationMonoid.radical a ∣ Polynomial.derivative a :=
  _root_.divRadical_dvd_derivative a
end

-- forge:entry ms_divrad_dvd_wronskian_v2 kind=proved origin=paper
section
/- For nonzero a in k[t], a/rad(a) divides the Wronskian W(a,b) = ab' - a'b. -/
theorem ms_divrad_dvd_wronskian_v2 {k : Type*} [Field k] [DecidableEq k] (a b : Polynomial k) (ha : a ≠ 0) : a / UniqueFactorizationMonoid.radical a ∣ a * Polynomial.derivative b - Polynomial.derivative a * b :=
  _root_.divRadical_dvd_wronskian_left a b
end

-- forge:entry nt_five_consec_prod_dvd_120 kind=proved origin=conjecture
section
/- n^5 - 5n^3 + 4n = (n-2)(n-1)n(n+1)(n+2) is divisible by 120. -/
theorem nt_five_consec_prod_dvd_120_aux1 (m : ℕ) (hm : m = 8 ∨ m = 3 ∨ m = 5) (n : ℤ) :
    (m : ℤ) ∣ n ^ 5 - 5 * n ^ 3 + 4 * n := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  generalize (n : ZMod m) = x
  rcases hm with rfl | rfl | rfl <;> revert x <;> decide

theorem nt_five_consec_prod_dvd_120 (n : ℤ) : 120 ∣ n ^ 5 - 5 * n ^ 3 + 4 * n := by
  have h8 := nt_five_consec_prod_dvd_120_aux1 8 (by simp) n
  have h3 := nt_five_consec_prod_dvd_120_aux1 3 (by simp) n
  have h5 := nt_five_consec_prod_dvd_120_aux1 5 (by simp) n
  have h15 : (15 : ℤ) ∣ n ^ 5 - 5 * n ^ 3 + 4 * n :=
    (IsCoprime.mul_dvd (by norm_num : IsCoprime (3 : ℤ) 5) h3 h5)
  exact (IsCoprime.mul_dvd (by norm_num : IsCoprime (8 : ℤ) 15) h8 h15)
end

-- forge:entry an_schur_deg_one kind=proved origin=conjecture
section
/- Schur's inequality (t = 1) for nonnegative reals. -/
theorem an_schur_deg_one_aux1 (a b c : ℝ) (hc : 0 ≤ c) (hab : b ≤ a) (hbc : c ≤ b) : 0 ≤ a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b) := by
  have h1 : 0 ≤ c * (a - c) * (b - c) :=
    mul_nonneg (mul_nonneg hc (by linarith)) (by linarith)
  have h2 : 0 ≤ (a - b) * (a - b) * (a + b - c) :=
    mul_nonneg (mul_self_nonneg _) (by linarith)
  nlinarith [h1, h2]

theorem an_schur_deg_one (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 0 ≤ a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b) := by
  rcases le_total a b with h1 | h1 <;> rcases le_total b c with h2 | h2 <;> rcases le_total a c with h3 | h3
  · linarith [an_schur_deg_one_aux1 c b a ha h2 h1]
  · linarith [an_schur_deg_one_aux1 c b a ha h2 h1]
  · linarith [an_schur_deg_one_aux1 b c a ha h2 h3]
  · linarith [an_schur_deg_one_aux1 b a c hc h1 h3]
  · linarith [an_schur_deg_one_aux1 c a b hb h3 h1]
  · linarith [an_schur_deg_one_aux1 a c b hb h3 h2]
  · linarith [an_schur_deg_one_aux1 a b c hc h1 h2]
  · linarith [an_schur_deg_one_aux1 a b c hc h1 h2]
end

-- forge:entry ms_radical_degree_pos_v2 kind=proved origin=paper
section
/- A polynomial over a field of degree ≥ 1 has radical of degree ≥ 1. -/
open UniqueFactorizationMonoid
theorem ms_radical_degree_pos_v2 {k : Type*} [Field k] [DecidableEq k] (a : Polynomial k) (ha : 1 ≤ a.natDegree) : 1 ≤ (UniqueFactorizationMonoid.radical a).natDegree := by
  by_contra h
  have h0 : (radical a).natDegree = 0 := by omega
  have hne : radical a ≠ 0 := radical_ne_zero
  have hu : IsUnit (radical a) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hne, h0]
    rfl
  have h1 : radical a = 1 := by
    rw [← radical_radical]
    exact radical_of_isUnit hu
  rcases radical_eq_one_iff.mp h1 with h | h
  · subst h; simp at ha
  · have := Polynomial.natDegree_eq_zero_of_isUnit h
    omega
end

-- forge:entry an_sum_mul_two_pow kind=proved origin=conjecture
section
/- sum_{i≤n} i*2^i = (n-1)*2^(n+1) + 2, rearranged to avoid natural subtraction. -/
theorem an_sum_mul_two_pow (n : ℕ) : ∑ i ∈ Finset.range (n + 1), i * 2 ^ i + 2 ^ (n + 1) = n * 2 ^ (n + 1) + 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have e : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
    rw [e]
    nlinarith [ih]
end

-- forge:entry nt_sq_sub_three_sq_ne_two kind=proved origin=conjecture
section
/- The equation x^2 - 3y^2 = 2 has no integer solutions. -/
theorem nt_sq_sub_three_sq_ne_two (x y : ℤ) : x ^ 2 - 3 * y ^ 2 ≠ 2 := by
  intro h
  have h3 : x ^ 2 % 3 = 2 := by omega
  have : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  rcases this with h1 | h1 | h1 <;> simp [pow_two, Int.mul_emod, h1] at h3
end

-- forge:entry ms_mason_stothers_v2 kind=proved origin=paper
section
/- Mason–Stothers: nonzero pairwise coprime a+b+c=0 in k[t] have all derivatives zero or max degree < deg rad(abc). -/
theorem ms_mason_stothers_v2 {k : Type*} [Field k] [DecidableEq k] (a b c : Polynomial k) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b) (hbc : IsCoprime b c) (hca : IsCoprime c a) (hsum : a + b + c = 0) : (Polynomial.derivative a = 0 ∧ Polynomial.derivative b = 0 ∧ Polynomial.derivative c = 0) ∨ max (max a.natDegree b.natDegree) c.natDegree < (UniqueFactorizationMonoid.radical (a * b * c)).natDegree := by
  rcases Polynomial.abc ha hb hc hab hsum with h | h
  · right
    obtain ⟨h1, h2, h3⟩ := h
    simp only [max_lt_iff]
    omega
  · left; exact h
end

-- forge:entry an_card_lt_pairs kind=proved origin=conjecture
section
/- The number of pairs (i,j) with i<j<n is n(n-1)/2. -/
theorem an_card_lt_pairs (n : ℕ) : ((Finset.range n ×ˢ Finset.range n).filter (fun p => p.1 < p.2)).card = n * (n - 1) / 2 := by
  rw [Finset.card_filter, Finset.sum_product_right, ← Finset.sum_range_id]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← Finset.card_filter]
  have : (Finset.range n).filter (fun x => x < y) = Finset.range y := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range] at *
    omega
  rw [this, Finset.card_range]
end

-- forge:entry nt_lcm_consecutive kind=proved origin=conjecture
section
/- lcm of consecutive naturals is their product. -/
theorem nt_lcm_consecutive (n : ℕ) : Nat.lcm n (n + 1) = n * (n + 1) := by
  have h : Nat.Coprime n (n + 1) := by simp
  exact h.lcm_eq_mul
end

-- forge:entry ms_flt_poly kind=proved origin=paper
section
/- Fermat's Last Theorem for polynomials: for n ≥ 3 prime to char k, nonzero pairwise coprime solutions of a^n+b^n=c^n in k[t] are constants. -/
theorem ms_flt_poly {k : Type*} [Field k] (n : ℕ) (hn : 3 ≤ n) (chn : ¬ ringChar k ∣ n) (a b c : Polynomial k) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b) (hbc : IsCoprime b c) (hca : IsCoprime c a) (heq : a ^ n + b ^ n = c ^ n) : a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 :=
  Polynomial.flt hn (fun h => chn ((ringChar.spec k n).mp h)) ha hb hc hab heq
end

-- forge:entry an_amgm_three_cube kind=proved origin=conjecture
section
/- AM-GM for three nonnegative reals in cubed form. -/
theorem an_amgm_three_cube (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : a * b * c ≤ ((a + b + c) / 3) ^ 3 := by
  have hs : 0 ≤ a + b + c := by linarith
  nlinarith [mul_nonneg ha (sq_nonneg (b - c)), mul_nonneg hb (sq_nonneg (c - a)),
    mul_nonneg hc (sq_nonneg (a - b)), mul_nonneg hs (sq_nonneg (a - b)),
    mul_nonneg hs (sq_nonneg (b - c)), mul_nonneg hs (sq_nonneg (c - a))]
end

-- forge:entry an_div_add_div_ge_two_ne kind=disproved origin=conjecture
section
/- [suspected false] a/b + b/a ≥ 2 assuming only a, b nonzero (fails for opposite signs). -/
theorem an_div_add_div_ge_two_ne_disproof : ¬ (∀ (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0), 2 ≤ a / b + b / a) := by
  intro h
  have := h 1 (-1) (by norm_num) (by norm_num)
  norm_num at this
end

-- forge:entry ms_fermat_catalan kind=proved origin=paper
section
/- Fermat–Catalan for polynomials: u a^p + v b^q + w c^r = 0 with 1/p+1/q+1/r ≤ 1, exponents prime to char, forces coprime nonzero a,b,c to be constant. -/
theorem ms_fermat_catalan {k : Type*} [Field k] (p q r : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (chp : ¬ ringChar k ∣ p) (chq : ¬ ringChar k ∣ q) (chr : ¬ ringChar k ∣ r) (hineq : (1 : ℚ) / p + 1 / q + 1 / r ≤ 1) (u v w : k) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) (a b c : Polynomial k) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b) (hbc : IsCoprime b c) (hca : IsCoprime c a) (heq : Polynomial.C u * a ^ p + Polynomial.C v * b ^ q + Polynomial.C w * c ^ r = 0) : a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 := by
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  have hin : q * r + r * p + p * q ≤ p * q * r := by
    have h2 : ((q * r + r * p + p * q : ℕ) : ℚ) ≤ ((p * q * r : ℕ) : ℚ) := by
      have h3 : (1 : ℚ) / p + 1 / q + 1 / r = (q * r + r * p + p * q) / (p * q * r) := by
        field_simp
      rw [h3, div_le_one (by positivity)] at hineq
      push_cast
      exact hineq
    exact_mod_cast h2
  exact Polynomial.flt_catalan (by omega) (by omega) (by omega) hin
    (fun h => chp ((ringChar.spec k p).mp h)) (fun h => chq ((ringChar.spec k q).mp h))
    (fun h => chr ((ringChar.spec k r).mp h)) ha hb hc hab hu hv hw heq
end

-- forge:entry an_sum_sq_range_closed kind=disproved origin=conjecture
section
/- [suspected false] off-by-one closed form for the sum of squares below n. -/
theorem an_sum_sq_range_closed_disproof : ¬ (∀ (n : ℕ), ∑ i ∈ Finset.range n, i ^ 2 = n * (n + 1) * (2 * n + 1) / 6) := by
  intro h
  have := h 1
  simp at this
end

-- forge:entry ms_abc_noncoprime_char0_v2 kind=proved origin=paper
section
/- Non-coprime Mason–Stothers in char 0: nonzero a+b+c=0 are all constant or max degree < deg rad(a) + deg rad(b) + deg(c). -/
open Polynomial UniqueFactorizationMonoid
theorem ms_abc_noncoprime_char0_v2 {k : Type*} [Field k] [DecidableEq k] [CharZero k] (a b c : Polynomial k) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hsum : a + b + c = 0) : (a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0) ∨ max (max a.natDegree b.natDegree) c.natDegree < (UniqueFactorizationMonoid.radical a).natDegree + (UniqueFactorizationMonoid.radical b).natDegree + c.natDegree := by
  have h1 := EuclideanDomain.gcd_dvd_left a b
  have h2 := EuclideanDomain.gcd_dvd_right a b
  have h3 := EuclideanDomain.gcd_eq_gcd_ab a b
  generalize EuclideanDomain.gcd a b = d at h1 h2 h3
  generalize EuclideanDomain.gcdA a b = x at h3
  generalize EuclideanDomain.gcdB a b = y at h3
  obtain ⟨a0, rfl⟩ := h1
  obtain ⟨b0, rfl⟩ := h2
  have hd : d ≠ 0 := left_ne_zero_of_mul ha
  have ha0 : a0 ≠ 0 := right_ne_zero_of_mul ha
  have hb0 : b0 ≠ 0 := right_ne_zero_of_mul hb
  have hcop : IsCoprime a0 b0 := ⟨x, y, by
    apply mul_left_cancel₀ hd
    linear_combination -h3⟩
  obtain ⟨c0, rfl⟩ : ∃ c0, c = d * c0 := ⟨-(a0 + b0), by linear_combination hsum⟩
  have hc0 : c0 ≠ 0 := right_ne_zero_of_mul hc
  have hsum0 : a0 + b0 + c0 = 0 := by
    apply mul_left_cancel₀ hd
    linear_combination hsum
  have hra : (radical a0).natDegree ≤ (radical (d * a0)).natDegree :=
    natDegree_le_of_dvd (radical_dvd_radical (dvd_mul_left a0 d) ha) radical_ne_zero
  have hrb : (radical b0).natDegree ≤ (radical (d * b0)).natDegree :=
    natDegree_le_of_dvd (radical_dvd_radical (dvd_mul_left b0 d) hb) radical_ne_zero
  have hrabc : (radical (a0 * b0 * c0)).natDegree ≤
      (radical a0).natDegree + (radical b0).natDegree + c0.natDegree := by
    have e1 := natDegree_le_of_dvd (radical_mul_dvd (a := a0 * b0) (b := c0))
      (mul_ne_zero radical_ne_zero radical_ne_zero)
    have e2 := natDegree_le_of_dvd (radical_mul_dvd (a := a0) (b := b0))
      (mul_ne_zero radical_ne_zero radical_ne_zero)
    rw [natDegree_mul radical_ne_zero radical_ne_zero] at e1 e2
    have e3 := natDegree_radical_le (a := c0)
    omega
  rw [natDegree_mul hd ha0, natDegree_mul hd hb0, natDegree_mul hd hc0]
  rcases Polynomial.abc ha0 hb0 hc0 hcop hsum0 with ⟨i1, i2, i3⟩ | ⟨da, db, dc⟩
  · right
    simp only [max_lt_iff]
    omega
  · have za := natDegree_eq_zero_of_derivative_eq_zero da
    have zb := natDegree_eq_zero_of_derivative_eq_zero db
    have zc := natDegree_eq_zero_of_derivative_eq_zero dc
    by_cases hdz : d.natDegree = 0
    · left; omega
    · right
      have l3 := ms_radical_degree_pos_v2 (d * a0) (by rw [natDegree_mul hd ha0]; omega)
      simp only [max_lt_iff]
      omega
end

-- forge:entry ms_davenport kind=proved origin=paper
section
/- Davenport: in characteristic zero, non-constant f,g with f^3 ≠ g^2 satisfy deg(f^3 - g^2) ≥ deg(f)/2 + 1. -/
open Polynomial UniqueFactorizationMonoid
theorem ms_davenport {k : Type*} [Field k] [CharZero k] (f g : Polynomial k) (hf : 0 < f.natDegree) (hg : 0 < g.natDegree) (hne : f ^ 3 ≠ g ^ 2) : f.natDegree + 2 ≤ 2 * (f ^ 3 - g ^ 2).natDegree := by
  classical
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  have hg0 : g ≠ 0 := by rintro rfl; simp at hg
  have h := ms_abc_noncoprime_char0_v2 (-f ^ 3) (g ^ 2) (f ^ 3 - g ^ 2)
    (neg_ne_zero.mpr (pow_ne_zero 3 hf0)) (pow_ne_zero 2 hg0) (sub_ne_zero.mpr hne) (by ring)
  rw [UniqueFactorizationDomain.radical_neg, radical_pow f (by norm_num), radical_pow g (by norm_num), natDegree_neg,
    natDegree_pow, natDegree_pow] at h
  have rf := natDegree_radical_le (a := f)
  have rg := natDegree_radical_le (a := g)
  rcases h with ⟨h1, -, -⟩ | h
  · omega
  · simp only [max_lt_iff] at h
    omega
end

-- forge:entry ms_no_param_y2_x3_1 kind=proved origin=paper
section
/- If char k ≠ 2,3 and rational functions f,g in k(t) satisfy g^2 = f^3 + 1 then f and g are constants. -/
open Polynomial

theorem ms_no_param_y2_x3_1_aux1 {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (a b c d : k[X]) (hc : c.Monic) (hd : d.Monic) (hac : IsCoprime a c) (hbd : IsCoprime b d)
    (h : b ^ 2 * c ^ 3 = (a ^ 3 + c ^ 3) * d ^ 2) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 ∧ d.natDegree = 0 := by
  have hc0 : c ≠ 0 := hc.ne_zero
  have h1 : d ^ 2 ∣ c ^ 3 :=
    (IsCoprime.pow hbd.symm : IsCoprime (d ^ 2) (b ^ 2)).dvd_of_dvd_mul_right
      ⟨a ^ 3 + c ^ 3, by linear_combination h⟩
  have hcop : IsCoprime (c ^ 3) (a ^ 3 + c ^ 3) := by
    obtain ⟨u, v, huv⟩ := (IsCoprime.pow hac.symm : IsCoprime (c ^ 3) (a ^ 3))
    exact ⟨u - v, v, by linear_combination huv⟩
  have h1' : c ^ 3 ∣ d ^ 2 :=
    hcop.dvd_of_dvd_mul_left ⟨b ^ 2, by linear_combination -h⟩
  have heq3 : c ^ 3 = d ^ 2 :=
    Polynomial.eq_of_monic_of_associated (hc.pow 3) (hd.pow 2) (associated_of_dvd_dvd h1' h1)
  have hb : b ^ 2 = a ^ 3 + c ^ 3 := by
    apply mul_right_cancel₀ (pow_ne_zero 3 hc0)
    rw [h, heq3]
  have hcd : c ∣ d := by
    rw [← IsIntegrallyClosed.pow_dvd_pow_iff (two_ne_zero : (2 : ℕ) ≠ 0)]
    exact ⟨c, by linear_combination -heq3⟩
  obtain ⟨e, rfl⟩ := hcd
  have hce : c = e ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hc0)
    linear_combination heq3
  subst hce
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hc0 (by simp)
  have hae : IsCoprime a e := by
    have := hac
    rw [pow_two] at this
    exact this.of_mul_right_left
  suffices hs : a.natDegree = 0 ∧ b.natDegree = 0 ∧ e.natDegree = 0 by
    obtain ⟨ha, hb', he⟩ := hs
    refine ⟨ha, hb', ?_, ?_⟩
    · simp [he]
    · rw [Polynomial.natDegree_mul (pow_ne_zero 2 he0) he0]
      simp [he]
  by_cases ha : a = 0
  · subst ha
    have hu : IsUnit e := isCoprime_zero_left.mp hae
    have he := Polynomial.natDegree_eq_zero_of_isUnit hu
    have hb2 : b ^ 2 = e ^ 6 := by linear_combination hb
    have := congrArg Polynomial.natDegree hb2
    simp only [Polynomial.natDegree_pow] at this
    refine ⟨by simp, by omega, he⟩
  by_cases hb0 : b = 0
  · subst hb0
    have hdvd : e ∣ a ^ 3 := ⟨-e ^ 5, by linear_combination -hb⟩
    have hu : IsUnit e := (hae.symm.pow_right (n := 3)).isUnit_of_dvd hdvd
    have he := Polynomial.natDegree_eq_zero_of_isUnit hu
    have ha3 : a ^ 3 = -e ^ 6 := by linear_combination -hb
    have := congrArg Polynomial.natDegree ha3
    simp only [Polynomial.natDegree_pow, Polynomial.natDegree_neg] at this
    refine ⟨by omega, by simp, he⟩
  have hab : IsCoprime a b := by
    have h6 : IsCoprime a (b ^ 2) := by
      rw [hb]
      obtain ⟨u, v, huv⟩ := (hae.pow_right (n := 6))
      exact ⟨u - v * a ^ 2, v, by linear_combination huv⟩
    rw [pow_two] at h6
    exact h6.of_mul_right_left
  have h6k : ((6 : ℕ) : k) ≠ 0 := by
    have : ((6 : ℕ) : k) = 2 * 3 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h3
  exact Polynomial.flt_catalan (p := 3) (q := 2) (r := 6) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by exact_mod_cast h3) (by exact_mod_cast h2) h6k ha hb0 he0 hab
    (u := 1) (v := -1) (w := 1) one_ne_zero (neg_ne_zero.mpr one_ne_zero) one_ne_zero
    (by simp only [map_one, map_neg]; linear_combination -hb)

theorem ms_no_param_y2_x3_1 {k : Type*} [Field k] (h2 : ringChar k ≠ 2) (h3 : ringChar k ≠ 3) (f g : RatFunc k) (heq : g ^ 2 = f ^ 3 + 1) : (∃ c : k, f = RatFunc.C c) ∧ (∃ d : k, g = RatFunc.C d) := by
  have h2' : (2 : k) ≠ 0 := Ring.two_ne_zero h2
  have h3' : (3 : k) ≠ 0 := by
    intro h
    have hd : ringChar k ∣ 3 := (ringChar.spec k 3).mp (by exact_mod_cast h)
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · exact h3 h1
  have hf : f = algebraMap k[X] (RatFunc k) f.num / algebraMap k[X] (RatFunc k) f.denom :=
    (RatFunc.num_div_denom f).symm
  have hg : g = algebraMap k[X] (RatFunc k) g.num / algebraMap k[X] (RatFunc k) g.denom :=
    (RatFunc.num_div_denom g).symm
  have hinj := RatFunc.algebraMap_injective k
  have hc0 : algebraMap k[X] (RatFunc k) f.denom ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact f.denom_ne_zero
  have hd0 : algebraMap k[X] (RatFunc k) g.denom ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact g.denom_ne_zero
  have key : g.num ^ 2 * f.denom ^ 3 = (f.num ^ 3 + f.denom ^ 3) * g.denom ^ 2 := by
    apply hinj
    simp only [map_mul, map_pow, map_add]
    have h := heq
    rw [hf, hg] at h
    rw [div_pow, div_pow, div_add_one (pow_ne_zero 3 hc0),
      div_eq_div_iff (pow_ne_zero 2 hd0) (pow_ne_zero 3 hc0)] at h
    exact h
  obtain ⟨ha, hb, hc, hd⟩ := ms_no_param_y2_x3_1_aux1 h2' h3' f.num g.num f.denom g.denom
    f.monic_denom g.monic_denom f.isCoprime_num_denom g.isCoprime_num_denom key
  refine ⟨⟨f.num.coeff 0 / f.denom.coeff 0, ?_⟩, ⟨g.num.coeff 0 / g.denom.coeff 0, ?_⟩⟩
  · rw [map_div₀, ← RatFunc.algebraMap_C, ← RatFunc.algebraMap_C,
      ← Polynomial.eq_C_of_natDegree_eq_zero ha, ← Polynomial.eq_C_of_natDegree_eq_zero hc]
    exact hf
  · rw [map_div₀, ← RatFunc.algebraMap_C, ← RatFunc.algebraMap_C,
      ← Polynomial.eq_C_of_natDegree_eq_zero hb, ← Polynomial.eq_C_of_natDegree_eq_zero hd]
    exact hg
end

-- forge:entry an2_sum_sqrt_le_sqrt_card_mul_sum kind=proved origin=conjecture
section
/- n-term QM-AM in sqrt form: sum of sqrt(a_i) ≤ sqrt(n * sum a_i). Generalizes Mathlib2.an_sqrt_add_le_sqrt_two_mul (the case n = 2). -/
theorem an2_sum_sqrt_le_sqrt_card_mul_sum (n : ℕ) (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) : ∑ i ∈ Finset.range n, Real.sqrt (a i) ≤ Real.sqrt (n * ∑ i ∈ Finset.range n, a i) := by
  apply Real.le_sqrt_of_sq_le
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.range n) (f := fun i => Real.sqrt (a i))
  simp only [Finset.card_range] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  exact Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (ha i))
end

end Mathlib2
