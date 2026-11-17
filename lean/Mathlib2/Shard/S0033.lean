/- Mathlib2 分片 33（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0007
import Mathlib2.Shard.S0012
import Mathlib2.Shard.S0013
import Mathlib2.Shard.S0017
import Mathlib2.Shard.S0020
import Mathlib2.Shard.S0026
import Mathlib2.Shard.S0031
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry bld6_factorial_lt_exp_mul_pow kind=proved origin=conjecture
section
/- Uses Mathlib2.calc_exp_lt_one_add_inv_pow_succ: put a_n = n!·e^n/(n·n^n); a_1 = e and a_(n+1)/a_n = e/(1+1/n)^(n+1) < 1 by calc_exp_lt_one_add_inv_pow_succ (the induction step), so a_n < e for n ≥ 2. This is the upper companion of Mathlib2.calc_factorial_gt_div_exp_pow. -/
theorem bld6_factorial_lt_exp_mul_pow (n : ℕ) (hn : 2 ≤ n) : (n.factorial : ℝ) < Real.exp 1 * n * ((n : ℝ) / Real.exp 1) ^ n := by
  have hE := Real.exp_pos 1
  induction n, hn using Nat.le_induction with
  | base =>
    have h4 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have : (2:ℝ) < Real.exp 1 * 2 * ((2:ℝ) / Real.exp 1) ^ 2 := by
      rw [div_pow]
      have : Real.exp 1 * 2 * (2 ^ 2 / Real.exp 1 ^ 2) = 8 / Real.exp 1 := by field_simp; ring
      rw [this, lt_div_iff₀ hE]; linarith
    simpa [Nat.factorial] using this
  | succ n hn ih =>
    have h := Mathlib2.calc_exp_lt_one_add_inv_pow_succ n (by omega)
    have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have key : Real.exp 1 * (n:ℝ)^(n+1) < ((n:ℝ)+1)^(n+1) := by
      have e : ((n:ℝ)+1)^(n+1) = (1 + 1/(n:ℝ))^(n+1) * (n:ℝ)^(n+1) := by
        rw [← mul_pow]; congr 1; field_simp
      rw [e]
      exact mul_lt_mul_of_pos_right h (by positivity)
    rw [Nat.factorial_succ]
    push_cast
    calc ((n:ℝ)+1) * n.factorial < ((n:ℝ)+1) * (Real.exp 1 * n * ((n : ℝ) / Real.exp 1) ^ n) := by
            gcongr
       _ = ((n:ℝ)+1) * (Real.exp 1 * (n:ℝ)^(n+1) / Real.exp 1 ^ n) := by
            rw [div_pow]; field_simp; ring
       _ < ((n:ℝ)+1) * (((n:ℝ)+1)^(n+1) / Real.exp 1 ^ n) := by
            gcongr
       _ = _ := by rw [div_pow]; field_simp; ring
end

-- forge:entry fld_card_hyperbola_zmod kind=proved origin=conjecture
section
/- For odd p and a ≠ 0 the equation x^2 - y^2 = a has exactly p-1 solutions in F_p — the change of variables u = x+y, v = x-y is a bijection of F_p^2 (2 invertible) turning it into uv = a, whose solutions are (u, a/u) for the p-1 units u. -/
theorem fld_card_hyperbola_zmod (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a : ZMod p) (ha : a ≠ 0) : ((Finset.univ : Finset (ZMod p × ZMod p)).filter (fun v => v.1 ^ 2 - v.2 ^ 2 = a)).card = p - 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h')
  have hcard : ((Finset.univ : Finset (ZMod p)).filter (fun u => u ≠ 0)).card = p - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  rw [← hcard]
  refine Finset.card_nbij' (fun v => v.1 + v.2) (fun u => ((u + a / u) / 2, (u - a / u) / 2)) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv ⊢
    intro h0
    apply ha
    rw [← hv]
    linear_combination (v.1 - v.2) * h0
  · intro u hu
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hu ⊢
    field_simp
    ring
  · intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
    have h0 : v.1 + v.2 ≠ 0 := by
      intro h0
      apply ha
      rw [← hv]
      linear_combination (v.1 - v.2) * h0
    have hq : a / (v.1 + v.2) = v.1 - v.2 := by
      rw [div_eq_iff h0, ← hv]; ring
    ext
    · simp only [hq]; field_simp; ring
    · simp only [hq]; field_simp; ring
  · intro u hu
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hu
    field_simp
    ring
end

-- forge:entry fld_isSquare_three_zmod_iff kind=proved origin=conjecture
section
/- 3 is a quadratic residue mod a prime p > 3 iff p ≡ ±1 (mod 12) — quadratic reciprocity (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one / _three) reduces to whether p is a square mod 3, i.e. p ≡ 1 mod 3, with a sign flip when p ≡ 3 mod 4; combine residues mod 4 and mod 3. -/
theorem fld_isSquare_three_zmod_iff (p : ℕ) [Fact p.Prime] (hp : 3 < p) : IsSquare (3 : ZMod p) ↔ p % 12 = 1 ∨ p % 12 = 11 := by
  have e1 : IsSquare ((1:ℕ) : ZMod 3) ↔ 1 = 1 := by simp only [isSquare_iff_exists_sq]; decide
  have e2 : IsSquare ((2:ℕ) : ZMod 3) ↔ 2 = 1 := by simp only [isSquare_iff_exists_sq]; decide
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hpp : p.Prime := Fact.out
  have h3c : ((3:ℕ) : ZMod p) = 3 := by norm_cast
  have hodd : p % 2 = 1 := by
    rcases hpp.eq_two_or_odd with h | h <;> omega
  have hne : p % 3 ≠ 0 := by
    intro h0
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hpp).mp (Nat.dvd_of_mod_eq_zero h0)
    omega
  have hsq : IsSquare ((p : ℕ) : ZMod 3) ↔ p % 3 = 1 := by
    have hmod : (p : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by simp
    rw [hmod]
    have hlt : p % 3 < 3 := Nat.mod_lt _ (by norm_num)
    revert hne hlt
    generalize p % 3 = r
    intro hne hlt
    interval_cases r
    · exact absurd rfl hne
    · exact e1
    · exact e2
  have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · have h := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := p) (q := 3) h4 (by norm_num)
    rw [h3c] at h; rw [h, hsq]; omega
  · have h := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three (p := p) (q := 3) h4 (by norm_num) (by omega)
    rw [h3c] at h; rw [h, hsq]; omega
end

-- forge:entry fld_pell_two_pm_one_solutions kind=proved origin=conjecture
section
/- Every solution of x^2 - 2y^2 = ±1 with x > 0, y ≥ 0 is a power of the fundamental unit: x + y√2 = (1 + √2)^n — strong induction on y: if y = 0 then x = 1, n = 0; otherwise multiply by (1+√2)^{-1} = -1 + √2 to get (x', y') = (2y - x, x - y), which is again a solution with x' > 0 and 0 ≤ y' < y (from y ≤ x < 2y for y ≥ 1, with the edge case (1,1)). -/
theorem fld_pell_two_pm_one_solutions (x y : ℤ) (hx : 0 < x) (hy : 0 ≤ y) (h : x ^ 2 - 2 * y ^ 2 = 1 ∨ x ^ 2 - 2 * y ^ 2 = -1) : ∃ n : ℕ, (⟨x, y⟩ : Zsqrtd 2) = (⟨1, 1⟩ : Zsqrtd 2) ^ n := by
  have key : ∀ n : ℕ, ∀ x y : ℤ, 0 < x → 0 ≤ y → y.toNat ≤ n →
      (x ^ 2 - 2 * y ^ 2 = 1 ∨ x ^ 2 - 2 * y ^ 2 = -1) →
      ∃ m : ℕ, (⟨x, y⟩ : Zsqrtd 2) = (⟨1, 1⟩ : Zsqrtd 2) ^ m := by
    intro n
    induction n with
    | zero =>
      intro x y hx hy hn h
      have h0 : y = 0 := by omega
      subst h0
      have h1 : x = 1 := by rcases h with h | h <;> nlinarith
      subst h1
      exact ⟨0, by rw [pow_zero]; rfl⟩
    | succ n ih =>
      intro x y hx hy hn h
      rcases eq_or_lt_of_le hy with h0 | hpos
      · subst h0
        have h1 : x = 1 := by rcases h with h | h <;> nlinarith
        subst h1
        exact ⟨0, by rw [pow_zero]; rfl⟩
      · have hxy : y ≤ x := by
          by_contra hc
          push_neg at hc
          have : x + 1 ≤ y := hc
          rcases h with h | h <;> nlinarith
        have hx2 : x < 2 * y := by
          by_contra hc
          push_neg at hc
          rcases h with h | h <;> nlinarith
        obtain ⟨m, hm⟩ := ih (2 * y - x) (x - y) (by linarith) (by linarith) (by omega)
          (by rcases h with h | h
              · right; nlinarith
              · left; nlinarith)
        refine ⟨m + 1, ?_⟩
        rw [pow_succ, ← hm]
        ext <;> simp <;> ring
  exact key y.toNat x y hx hy le_rfl h
end

-- forge:entry fld_irrational_logb_two_three kind=proved origin=conjecture
section
/- log_2 3 is irrational — if log_2 3 = a/b with b > 0 then (a > 0 and) 2^a = 3^b in ℕ after clearing rpow, impossible by parity (2^a even, 3^b odd). -/
theorem fld_irrational_logb_two_three : Irrational (Real.logb 2 3) := by
  rintro ⟨q, hq⟩
  have hpos : (0:ℝ) < Real.logb 2 3 := Real.logb_pos (by norm_num) (by norm_num)
  have hq0 : 0 < q := by rw [← hq] at hpos; exact_mod_cast hpos
  have h1 : (2:ℝ) ^ (q:ℝ) = 3 := by rw [hq]; exact Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)
  have hnum : 0 < q.num := Rat.num_pos.mpr hq0
  obtain ⟨n, hn⟩ : ∃ n : ℕ, q.num = n := ⟨q.num.toNat, (Int.toNat_of_nonneg hnum.le).symm⟩
  have h2 : (2:ℝ) ^ n = 3 ^ q.den := by
    have : (q:ℝ) * q.den = n := by
      have := Rat.mul_den_eq_num q
      have h3 : ((q * q.den : ℚ) : ℝ) = ((q.num : ℚ) : ℝ) := by rw [this]
      push_cast at h3; rw [h3, hn]; simp
    rw [← Real.rpow_natCast, ← this, Real.rpow_mul (by norm_num), h1, Real.rpow_natCast]
  have h3 : 2 ^ n = 3 ^ q.den := by exact_mod_cast h2
  have hn0 : n ≠ 0 := by rintro rfl; rw [hn] at hnum; simp at hnum
  have : Even (3 ^ q.den) := by rw [← h3]; exact (Nat.even_pow.mpr ⟨even_two, hn0⟩)
  rw [Nat.even_pow] at this
  exact absurd this.1 (by decide)
end

-- forge:entry fld_isSquare_five_zmod_iff kind=proved origin=conjecture
section
/- 5 is a quadratic residue mod a prime p ≠ 2, 5 iff p ≡ ±1 (mod 5) — since 5 ≡ 1 mod 4, ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one gives IsSquare (5 : ZMod p) ↔ IsSquare (p : ZMod 5), and the nonzero squares mod 5 are 1 and 4. (Makes the hypotheses of Mathlib2.bld4_pisano_prime_dvd_pred_of_isSquare_five checkable.) -/
theorem fld_isSquare_five_zmod_iff (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp5 : p ≠ 5) : IsSquare (5 : ZMod p) ↔ p % 5 = 1 ∨ p % 5 = 4 := by
  have e1 : IsSquare ((1:ℕ) : ZMod 5) ↔ 1 = 1 ∨ 1 = 4 := by simp only [isSquare_iff_exists_sq]; decide
  have e2 : IsSquare ((2:ℕ) : ZMod 5) ↔ 2 = 1 ∨ 2 = 4 := by simp only [isSquare_iff_exists_sq]; decide
  have e3 : IsSquare ((3:ℕ) : ZMod 5) ↔ 3 = 1 ∨ 3 = 4 := by simp only [isSquare_iff_exists_sq]; decide
  have e4 : IsSquare ((4:ℕ) : ZMod 5) ↔ 4 = 1 ∨ 4 = 4 := by simp only [isSquare_iff_exists_sq]; decide
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p) (by norm_num) hp2
  have h5 : ((5:ℕ) : ZMod p) = 5 := by norm_cast
  rw [h5] at h
  rw [← h]
  have hmod : (p : ZMod 5) = ((p % 5 : ℕ) : ZMod 5) := by simp
  have hne : p % 5 ≠ 0 := by
    intro h0
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) (Fact.out : p.Prime)).mp (Nat.dvd_of_mod_eq_zero h0)
    exact hp5 this.symm
  have hlt : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  rw [hmod]
  revert hne hlt
  generalize p % 5 = r
  intro hne hlt
  interval_cases r
  · exact absurd rfl hne
  exacts [e1, e2, e3, e4]
end

-- forge:entry fld_zsqrtd_neg_five_two_irreducible_not_prime kind=proved origin=conjecture
section
/- In ℤ[√-5] the element 2 is irreducible but not prime (the classical non-UFD example) — norm a^2 + 5b^2 never equals 2, so a factorization 2 = xy (norms multiply to 4) has a factor of norm 1, a unit; yet 2 | 6 = (1+√-5)(1-√-5) while 2 divides neither factor (compare coefficients). -/
theorem fld_zsqrtd_neg_five_two_irreducible_not_prime : Irreducible (2 : Zsqrtd (-5)) ∧ ¬ Prime (2 : Zsqrtd (-5)) := by
  have hn2 : (2 : Zsqrtd (-5)).norm = 4 := by
    rw [Zsqrtd.norm_def]; simp
  constructor
  · rw [irreducible_iff]
    constructor
    · intro hu
      have := (Zsqrtd.norm_eq_one_iff' (by norm_num) _).2 hu
      rw [hn2] at this
      norm_num at this
    · intro a b hab
      have hm : a.norm * b.norm = 4 := by rw [← Zsqrtd.norm_mul, ← hab, hn2]
      have ha0 : 0 ≤ a.norm := Zsqrtd.norm_nonneg (by norm_num) a
      have hb0 : 0 ≤ b.norm := Zsqrtd.norm_nonneg (by norm_num) b
      have hane : a.norm ≠ 2 := by
        rw [Zsqrtd.norm_def]
        intro h2
        have h3 : a.re * a.re + 5 * (a.im * a.im) = 2 := by linarith
        have him : a.im = 0 := by
          by_contra hne
          have : 0 < a.im * a.im := mul_self_pos.2 hne
          nlinarith [mul_self_nonneg a.re]
        rw [him] at h3
        have : a.re * a.re = 2 := by linarith
        have h4 : a.re ≤ 1 := by nlinarith
        have h5 : -1 ≤ a.re := by nlinarith
        interval_cases a.re <;> omega
      have hle : a.norm ≤ 4 := by
        by_contra hc
        push_neg at hc
        have : 1 ≤ b.norm := by
          by_contra hb
          have : b.norm = 0 := by omega
          rw [this] at hm; omega
        nlinarith
      have hcases : a.norm = 1 ∨ b.norm = 1 := by
        interval_cases h : a.norm
        · omega
        · left; rfl
        · exact absurd rfl hane
        · omega
        · right; omega
      rcases hcases with h1 | h1
      · left; exact (Zsqrtd.norm_eq_one_iff' (by norm_num) _).1 h1
      · right; exact (Zsqrtd.norm_eq_one_iff' (by norm_num) _).1 h1
  · intro hp
    have hd : (2 : Zsqrtd (-5)) ∣ (⟨1, 1⟩ : Zsqrtd (-5)) * ⟨1, -1⟩ := by
      refine ⟨3, ?_⟩
      ext <;> simp
    rcases hp.dvd_or_dvd hd with ⟨c, hc⟩ | ⟨c, hc⟩
    · have := congrArg Zsqrtd.re hc
      simp at this
      omega
    · have := congrArg Zsqrtd.re hc
      simp at this
      omega
end

-- forge:entry fld_minpoly_sqrt_two kind=proved origin=conjecture
section
/- The minimal polynomial of √2 over ℚ is X^2 - 2 — it is monic, annihilates √2, and is irreducible over ℚ (degree 2 without rational root since √2 is irrational); conclude with minpoly.eq_of_irreducible_of_monic. -/
theorem fld_minpoly_sqrt_two : minpoly ℚ (Real.sqrt 2) = Polynomial.X ^ 2 - 2 := by
  have hmonic : (Polynomial.X ^ 2 - Polynomial.C 2 : Polynomial ℚ).Monic := Polynomial.monic_X_pow_sub_C 2 (by norm_num)
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C 2 : Polynomial ℚ).natDegree = 2 := Polynomial.natDegree_X_pow_sub_C
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C 2 : Polynomial ℚ) := by
    rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
    apply Multiset.eq_zero_of_forall_notMem
    intro q hq
    rw [Polynomial.mem_roots hmonic.ne_zero] at hq
    simp at hq
    exact Mathlib2.alg_rat_pow_ne_two 2 le_rfl q (by linarith)
  have h := minpoly.eq_of_irreducible_of_monic hirr (x := Real.sqrt 2)
    (by rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, Real.sq_sqrt (by norm_num)]; simp) hmonic
  rw [← h]; congr 1
end

-- forge:entry fld_sum_quadraticChar_sq_add kind=proved origin=conjecture
section
/- Quadratic character sum Σ_x χ(x^2 + a) = -1 for a ≠ 0 in F_p, p odd — count solutions of y^2 = x^2 + a two ways: it equals Σ_x (1 + χ(x^2 + a)) by quadraticChar_card_sqrts and equals p - 1 by the hyperbola count (y-x)(y+x) = a. -/
lemma fld_sum_quadraticChar_sq_add_aux1 (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (c : ZMod p) :
    (((Finset.univ : Finset (ZMod p)).filter (fun y => y ^ 2 = c)).card : ℤ) =
      quadraticChar (ZMod p) c + 1 := by
  have := quadraticChar_card_sqrts (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp) c
  rw [← this]
  congr 2
  ext y
  simp

lemma fld_sum_quadraticChar_sq_add_aux2 (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (f : ZMod p → ZMod p) :
    (((Finset.univ : Finset (ZMod p × ZMod p)).filter (fun v => v.2 ^ 2 = f v.1)).card : ℤ) =
      p + ∑ x : ZMod p, quadraticChar (ZMod p) (f x) := by
  have h1 : ∀ x : ZMod p, quadraticChar (ZMod p) (f x) =
      (((Finset.univ : Finset (ZMod p)).filter (fun y => y ^ 2 = f x)).card : ℤ) - 1 := by
    intro x; rw [fld_sum_quadraticChar_sq_add_aux1 p hp]; ring
  rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  rw [Finset.card_filter, Fintype.sum_prod_type]
  push_cast
  simp only [Finset.card_filter]
  push_cast
  ring

theorem fld_sum_quadraticChar_sq_add (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a : ZMod p) (ha : a ≠ 0) : ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 2 + a) = -1 := by
  have h1 := fld_sum_quadraticChar_sq_add_aux2 p hp (fun x => x ^ 2 + a)
  have h2 := fld_card_hyperbola_zmod p hp (-a) (neg_ne_zero.2 ha)
  have h3 : (Finset.univ : Finset (ZMod p × ZMod p)).filter (fun v => v.2 ^ 2 = (fun x => x ^ 2 + a) v.1)
      = (Finset.univ : Finset (ZMod p × ZMod p)).filter (fun v => v.1 ^ 2 - v.2 ^ 2 = -a) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; rw [h]; ring
    · intro h; linear_combination -h
  rw [h3, h2] at h1
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  push_cast [Nat.cast_sub hp1] at h1
  linarith
end

-- forge:entry fld_minpoly_sqrt_two_add_sqrt_three kind=proved origin=conjecture
section
/- The minimal polynomial of √2 + √3 over ℚ is X^4 - 10X^2 + 1 — the polynomial is monic and vanishes at √2+√3 ((√2+√3)^2 = 5 + 2√6); Uses Mathlib2.poly_x4_sub_10x2_add_1_irreducible_int for irreducibility over ℤ, transferred to ℚ by Gauss's lemma (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map), then minpoly.eq_of_irreducible_of_monic. -/
theorem fld_minpoly_sqrt_two_add_sqrt_three : minpoly ℚ (Real.sqrt 2 + Real.sqrt 3) = Polynomial.X ^ 4 - 10 * Polynomial.X ^ 2 + 1 := by
  have hmonZ : (Polynomial.X ^ 4 - 10 * Polynomial.X ^ 2 + 1 : Polynomial ℤ).Monic := by
    have : (Polynomial.X ^ 4 - 10 * Polynomial.X ^ 2 + 1 : Polynomial ℤ) = Polynomial.X ^ 4 - (10 * Polynomial.X ^ 2 - 1) := by ring
    rw [this]
    apply Polynomial.monic_X_pow_sub
    have : (10 * Polynomial.X ^ 2 - 1 : Polynomial ℤ).degree ≤ 2 := by compute_degree
    exact lt_of_le_of_lt this (by norm_num)
  have hmap : Polynomial.map (algebraMap ℤ ℚ) (Polynomial.X ^ 4 - 10 * Polynomial.X ^ 2 + 1 : Polynomial ℤ) = Polynomial.X ^ 4 - 10 * Polynomial.X ^ 2 + 1 := by simp
  have hirr : Irreducible (Polynomial.X ^ 4 - 10 * Polynomial.X ^ 2 + 1 : Polynomial ℚ) := by
    rw [← hmap]
    exact (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map hmonZ).mp Mathlib2.poly_x4_sub_10x2_add_1_irreducible_int
  have hmon : (Polynomial.X ^ 4 - 10 * Polynomial.X ^ 2 + 1 : Polynomial ℚ).Monic := by
    rw [← hmap]; exact hmonZ.map _
  symm
  refine minpoly.eq_of_irreducible_of_monic hirr ?_ hmon
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : (Real.sqrt 2 + Real.sqrt 3) ^ 2 = 5 + 2 * Real.sqrt 2 * Real.sqrt 3 := by linear_combination h2 + h3
  have hab : (Real.sqrt 2 * Real.sqrt 3) ^ 2 = 6 := by rw [mul_pow, h2, h3]; norm_num
  simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, map_one, map_ofNat]
  linear_combination ((Real.sqrt 2 + Real.sqrt 3) ^ 2 + 5 + 2 * Real.sqrt 2 * Real.sqrt 3 - 10) * hs + 4 * hab
end

-- forge:entry fld_card_image_sq_finite_field kind=proved origin=conjecture
section
/- A finite field of odd characteristic with q elements has exactly (q+1)/2 squares. Generalizes Mathlib2.alg_card_range_sq_zmod_prime from ZMod p to all finite fields — squaring is 2-to-1 on nonzero elements (x^2 = y^2 iff x = ±y, and x ≠ -x as char ≠ 2), plus 0; q is odd. -/
theorem fld_card_image_sq_finite_field (K : Type) [Field K] [Fintype K] [DecidableEq K] (h : ringChar K ≠ 2) : (Finset.univ.image (fun x : K => x ^ 2)).card = (Fintype.card K + 1) / 2 := by
  have h2 : (2:K) ≠ 0 := Ring.two_ne_zero h
  set S := Finset.univ.image (fun x : K => x ^ 2) with hS
  have hcard : Fintype.card K = ∑ y ∈ S, (Finset.univ.filter (fun x : K => x ^ 2 = y)).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x))
  have h0 : (0:K) ∈ S := Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by simp⟩
  have hf0 : (Finset.univ.filter (fun x : K => x ^ 2 = 0)).card = 1 := by
    rw [Finset.card_eq_one]; refine ⟨0, ?_⟩; ext x; simp
  have hfy : ∀ y ∈ S.erase 0, (Finset.univ.filter (fun x : K => x ^ 2 = y)).card = 2 := by
    intro y hy
    rw [Finset.mem_erase] at hy
    obtain ⟨hy0, hyS⟩ := hy
    obtain ⟨x0, -, rfl⟩ := Finset.mem_image.mp hyS
    have hx0 : x0 ≠ 0 := by rintro rfl; simp at hy0
    have : Finset.univ.filter (fun x : K => x ^ 2 = x0 ^ 2) = {x0, -x0} := by
      ext x; simp [sq_eq_sq_iff_eq_or_eq_neg]
    rw [this, Finset.card_pair]
    intro hh
    have : (2:K) * x0 = 0 := by linear_combination hh
    rcases mul_eq_zero.mp this with h' | h' <;> contradiction
  rw [← Finset.add_sum_erase S _ h0, hf0, Finset.sum_congr rfl hfy, Finset.sum_const, smul_eq_mul] at hcard
  have h5 : (S.erase 0).card = S.card - 1 := Finset.card_erase_of_mem h0
  have h6 : 0 < S.card := Finset.card_pos.mpr ⟨0, h0⟩
  omega
end

-- forge:entry bld6_hardy_odd_harmonic_means kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_hardy_inequality_tsum and Mathlib2.calc_tsum_inv_odd_sq: apply Hardy's inequality to a_k = 1/(2k+1); summability of a_k^2 and the value ∑ a_k^2 = π^2/8 come from calc_tsum_inv_odd_sq (rewrite (1/(2k+1))^2 = 1/(2k+1)^2), so the bound is 4·π^2/8. -/
theorem bld6_hardy_odd_harmonic_means : ∑' k : ℕ, ((∑ i ∈ Finset.range (k + 1), 1 / (2 * (i : ℝ) + 1)) / ((k : ℝ) + 1)) ^ 2 ≤ Real.pi ^ 2 / 2 := by
  have e := Mathlib2.calc_tsum_inv_odd_sq
  have fe : (fun k : ℕ => (1 / (2 * (k : ℝ) + 1)) ^ 2) = fun k : ℕ => 1 / (2 * (k:ℝ) + 1)^2 := by
    funext k; rw [one_div_pow]
  have hs : Summable (fun k : ℕ => (1 / (2 * (k : ℝ) + 1)) ^ 2) := by
    rw [fe]
    by_contra h
    rw [tsum_eq_zero_of_not_summable h] at e
    have := Real.pi_pos
    nlinarith
  have h2 := (Mathlib2.bld2_hardy_inequality_tsum (fun k : ℕ => 1 / (2 * (k : ℝ) + 1)) hs).2
  beta_reduce at h2
  rw [fe, e] at h2
  linarith
end

-- forge:entry fld_card_circle_zmod kind=proved origin=conjecture
section
/- The circle x^2 + y^2 = 1 over F_p (p odd) has p - (-1/p) points: p-1 if p ≡ 1 mod 4 and p+1 if p ≡ 3 mod 4 — if -1 = i^2 the substitution u = x+iy, v = x-iy gives the hyperbola uv = 1 with p-1 points; otherwise count via N = Σ_x (1 + χ(1-x^2)) and the Jacobsthal sum Σ χ(x^2 - 1)·χ(-1) = -χ(-1), or parametrize rationally by lines through (1,0). -/
theorem fld_card_circle_zmod (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : ((Finset.univ : Finset (ZMod p × ZMod p)).filter (fun v => v.1 ^ 2 + v.2 ^ 2 = 1)).card = if p % 4 = 1 then p - 1 else p + 1 := by
  have h1 := fld_sum_quadraticChar_sq_add_aux2 p hp (fun x => 1 - x ^ 2)
  have h3 : (Finset.univ : Finset (ZMod p × ZMod p)).filter (fun v => v.2 ^ 2 = (fun x => 1 - x ^ 2) v.1)
      = (Finset.univ : Finset (ZMod p × ZMod p)).filter (fun v => v.1 ^ 2 + v.2 ^ 2 = 1) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; rw [h]; ring
    · intro h; linear_combination h
  rw [h3] at h1
  have h4 : ∑ x : ZMod p, quadraticChar (ZMod p) (1 - x ^ 2) = - quadraticChar (ZMod p) (-1) := by
    have : ∀ x : ZMod p, quadraticChar (ZMod p) (1 - x ^ 2) =
        quadraticChar (ZMod p) (-1) * quadraticChar (ZMod p) (x ^ 2 + (-1)) := by
      intro x; rw [← map_mul]; congr 1; ring
    rw [Finset.sum_congr rfl (fun x _ => this x), ← Finset.mul_sum,
      fld_sum_quadraticChar_sq_add p hp (-1) (by simp)]
    ring
  rw [h4, quadraticChar_neg_one (by rw [ZMod.ringChar_zmod_n]; exact hp), ZMod.card] at h1
  have hp1 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp
    · exact h
  split_ifs with h
  · rw [ZMod.χ₄_nat_one_mod_four h] at h1
    omega
  · rw [ZMod.χ₄_nat_three_mod_four (by omega)] at h1
    omega
end

-- forge:entry fld_mul_isSquare_of_not_isSquare kind=proved origin=conjecture
section
/- In a finite field the product of two non-squares is a square — in characteristic 2 everything is a square; otherwise the quadratic character is multiplicative with values ±1 on nonzero elements and equals -1 exactly on non-squares (quadraticChar_neg_one_iff_not_isSquare), so χ(ab) = 1. -/
theorem fld_mul_isSquare_of_not_isSquare (K : Type) [Field K] [Fintype K] (a b : K) (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) : IsSquare (a * b) := by
  classical
  by_cases h : ringChar K = 2
  · exact FiniteField.isSquare_of_char_two h _
  · have ha' := (quadraticChar_neg_one_iff_not_isSquare (F := K)).mpr ha
    have hb' := (quadraticChar_neg_one_iff_not_isSquare (F := K)).mpr hb
    have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by simp⟩
    have hb0 : b ≠ 0 := by rintro rfl; exact hb ⟨0, by simp⟩
    rw [← quadraticChar_one_iff_isSquare (mul_ne_zero ha0 hb0), map_mul, ha', hb']; norm_num
end

-- forge:entry fld_gaussianInt_prime_of_norm_prime kind=proved origin=conjecture
section
/- A Gaussian integer whose norm is a rational prime is a Gaussian prime — if z = xy then N(x)N(y) = p so one of x, y has norm 1 and is a unit (Zsqrtd.norm_eq_one_iff), so z is irreducible; ℤ[i] is a PID so irreducible elements are prime. -/
theorem fld_gaussianInt_prime_of_norm_prime (z : GaussianInt) (h : Nat.Prime z.norm.natAbs) : Prime z := by
  apply Irreducible.prime
  refine ⟨fun hu => ?_, fun x y hxy => ?_⟩
  · rw [← Zsqrtd.norm_eq_one_iff] at hu; rw [hu] at h; exact Nat.not_prime_one h
  · rw [← Zsqrtd.norm_eq_one_iff, ← Zsqrtd.norm_eq_one_iff]
    rw [hxy, Zsqrtd.norm_mul, Int.natAbs_mul] at h
    by_contra hc; push_neg at hc
    exact Nat.not_prime_mul hc.1 hc.2 h
end

-- forge:entry fld_card_four_sq_add_self_add_one kind=proved origin=conjecture
section
/- In a field with 4 elements every element other than 0, 1 is a root of X^2 + X + 1 — x^3 = 1 by FiniteField.pow_card_sub_one_eq_one, so (x - 1)(x^2 + x + 1) = 0 and x ≠ 1. -/
theorem fld_card_four_sq_add_self_add_one (K : Type) [Field K] [Fintype K] (h : Fintype.card K = 4) (x : K) (h0 : x ≠ 0) (h1 : x ≠ 1) : x ^ 2 + x + 1 = 0 := by
  have h3 : x ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one x h0
    rwa [h] at this
  have : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd (sub_eq_zero.mp h') h1
  · exact h'
end

-- forge:entry fld_irreducible_X_sq_add_one_zmod_iff kind=proved origin=conjecture
section
/- X^2 + 1 is irreducible over F_p iff p ≡ 3 (mod 4) — a monic quadratic is irreducible iff it has no root (Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three), and a root is a square root of -1, which exists iff p % 4 ≠ 3 (ZMod.exists_sq_eq_neg_one_iff). -/
theorem fld_irreducible_X_sq_add_one_zmod_iff (p : ℕ) [Fact p.Prime] : Irreducible (Polynomial.X ^ 2 + 1 : Polynomial (ZMod p)) ↔ p % 4 = 3 := by
  have hdeg : (Polynomial.X ^ 2 + 1 : Polynomial (ZMod p)).natDegree = 2 := by
    have := Polynomial.natDegree_X_pow_add_C (R := ZMod p) (n := 2) (r := 1)
    simpa using this
  have hne : (Polynomial.X ^ 2 + 1 : Polynomial (ZMod p)) ≠ 0 := by
    intro h; rw [h] at hdeg; simp at hdeg
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  have key : IsSquare (-1 : ZMod p) ↔ ¬ (Polynomial.X ^ 2 + 1 : Polynomial (ZMod p)).roots = 0 := by
    constructor
    · rintro ⟨r, hr⟩ h0
      have : r ∈ (Polynomial.X ^ 2 + 1 : Polynomial (ZMod p)).roots := by
        rw [Polynomial.mem_roots hne]
        simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
        linear_combination -hr
      rw [h0] at this; simp at this
    · intro h
      obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero h
      rw [Polynomial.mem_roots hne] at hr
      simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at hr
      exact ⟨r, by linear_combination -hr⟩
  have := ZMod.exists_sq_eq_neg_one_iff (p := p)
  rw [this] at key
  tauto
end

-- forge:entry fld_gaussianInt_isUnit_iff kind=proved origin=conjecture
section
/- The units of ℤ[i] are exactly 1, -1, i, -i — by Zsqrtd.norm_eq_one_iff' a unit has norm re^2 + im^2 = 1, forcing (re, im) ∈ {(±1, 0), (0, ±1)}; the converse is a direct check. -/
theorem fld_gaussianInt_isUnit_iff (z : GaussianInt) : IsUnit z ↔ z = 1 ∨ z = -1 ∨ z = ⟨0, 1⟩ ∨ z = ⟨0, -1⟩ := by
  have hu := Zsqrtd.norm_eq_one_iff' (d := -1) (by norm_num) z
  rw [← hu]
  obtain ⟨x, y⟩ := z
  simp only [Zsqrtd.norm, Zsqrtd.ext_iff, Zsqrtd.re_one, Zsqrtd.im_one, Zsqrtd.re_neg, Zsqrtd.im_neg]
  constructor
  · intro h
    have hx : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg y]
    have hy : y ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
    have hx1 : -1 ≤ x ∧ x ≤ 1 := by constructor <;> nlinarith
    have hy1 : -1 ≤ y ∧ y ≤ 1 := by constructor <;> nlinarith
    obtain ⟨a, b⟩ := hx1; obtain ⟨c, d⟩ := hy1
    interval_cases x <;> interval_cases y <;> simp_all
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
end

-- forge:entry fld_zsqrtd_neg_five_isUnit_iff kind=proved origin=conjecture
section
/- The only units of ℤ[√-5] are ±1 — by Zsqrtd.norm_eq_one_iff' (d ≤ 0) units are the elements with re^2 + 5 im^2 = 1, which forces im = 0 and re = ±1. -/
theorem fld_zsqrtd_neg_five_isUnit_iff (z : Zsqrtd (-5)) : IsUnit z ↔ z = 1 ∨ z = -1 := by
  have hu := Zsqrtd.norm_eq_one_iff' (d := -5) (by norm_num) z
  rw [← hu]
  obtain ⟨x, y⟩ := z
  simp only [Zsqrtd.norm, Zsqrtd.ext_iff, Zsqrtd.re_one, Zsqrtd.im_one, Zsqrtd.re_neg, Zsqrtd.im_neg]
  constructor
  · intro h
    have hx : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg y]
    have hy : 5 * y ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
    have hx1 : -1 ≤ x ∧ x ≤ 1 := by constructor <;> nlinarith
    have hy1 : -1 < y ∧ y < 1 := by constructor <;> nlinarith
    obtain ⟨a, b⟩ := hx1; obtain ⟨c, d⟩ := hy1
    interval_cases x <;> interval_cases y <;> simp_all
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
end

-- forge:entry bld6_pisano_prime_not_dvd_succ_of_not_isSquare_five kind=proved origin=conjecture
section
/- Uses Mathlib2.bld5_prime_dvd_fib_succ_of_not_isSquare_five, Mathlib2.lib_pisano_dvd_iff_period and Mathlib2.lib_fib_period_iff: if π(p) ∣ p+1 then (lib_pisano_dvd_iff_period + lib_fib_period_iff) F_(p+2) ≡ 1 mod p. But p ∣ F_(p+1) (bld5 theorem) gives F_(p+2) ≡ F_p, and F_p ≡ 5^((p-1)/2) ≡ -1 mod p (Euler criterion, from 2^(p-1) F_p = ∑ C(p,2j+1) 5^j; or Cassini F_p^2 ≡ 1 plus F_(p-1) ≡ -F_p and p ∤ F_(p-1)·… ), contradiction as p ≠ 2. Complements bld4_pisano_prime_dvd_two_mul_succ_of_not_isSquare_five: the period divides 2(p+1) but not p+1. -/
theorem bld6_pisano_prime_not_dvd_succ_of_not_isSquare_five (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (h : ¬ IsSquare (5 : ZMod p)) : ¬ p3_pisano p ∣ p + 1 := by
  intro hd
  have hper := (lib_pisano_dvd_iff_period p (p + 1) (by omega)).1 hd
  have h1 := ((lib_fib_period_iff p (p + 1)).1 hper).2
  have h0 := bld5_prime_dvd_fib_succ_of_not_isSquare_five p h
  have ha := (p3_aux_fib_prime p Fact.out hp2).1
  have h1z : ((Nat.fib (p + 1 + 1) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 h1
  have h0z : ((Nat.fib (p + 1) : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h0
  have haz : ((2 * (Nat.fib (p + 1) : ℤ) - (Nat.fib p : ℤ) : ℤ) : ZMod p) = ((1 : ℤ) : ZMod p) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).2 ha
  rw [Nat.fib_add_two] at h1z
  push_cast at h1z haz
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by
    push_cast
    linear_combination 3 * h0z - h1z - haz
  rw [ZMod.natCast_eq_zero_iff] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h2)
end

end Mathlib2
