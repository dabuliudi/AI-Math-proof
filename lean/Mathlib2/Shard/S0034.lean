/- Mathlib2 分片 34（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0007
import Mathlib2.Shard.S0012
import Mathlib2.Shard.S0023
import Mathlib2.Shard.S0027
import Mathlib2.Shard.S0028
import Mathlib2.Shard.S0029
import Mathlib2.Shard.S0030
import Mathlib2.Shard.S0031
import Mathlib2.Shard.S0032
import Mathlib2.Shard.S0033
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry fld_isSquare_neg_three_zmod_iff kind=proved origin=conjecture
section
/- -3 is a quadratic residue mod a prime p > 3 iff p ≡ 1 (mod 3) — either via legendreSym multiplicativity, (-1/p) and quadratic reciprocity for 3, or directly: -3 = (2ω+1)^2 where ω is a primitive cube root of unity, which exists in F_p iff 3 | p-1. -/
lemma fld_isSquare_neg_three_zmod_iff_aux1 (p : ℕ) [Fact p.Prime] (hp : 3 < p) (w : ZMod p)
    (hw : w ^ 2 + w + 1 = 0) : p % 3 = 1 := by
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_three).1 h'
    omega
  have hw3 : w ^ 3 = 1 := by linear_combination (w - 1) * hw
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply h3
    linear_combination hw
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : orderOf w = 3 := orderOf_eq_prime hw3 hw1
  have hd := ZMod.orderOf_dvd_card_sub_one hw0
  rw [ho] at hd
  omega

theorem fld_isSquare_neg_three_zmod_iff (p : ℕ) [Fact p.Prime] (hp : 3 < p) : IsSquare (-3 : ZMod p) ↔ p % 3 = 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h'
    omega
  constructor
  · rintro ⟨y, hy⟩
    apply fld_isSquare_neg_three_zmod_iff_aux1 p hp ((y - 1) / 2)
    field_simp
    linear_combination -hy
  · intro h
    obtain ⟨x, hx⟩ := fld_prime_one_mod_three_eq_sq_add_three_sq_aux3 p Fact.out h
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hx
    push_cast at hx
    exact ⟨(x : ZMod p), by linear_combination -hx⟩
end

-- forge:entry bld6_pisano_ten_pow kind=proved origin=conjecture
section
/- Uses Mathlib2.bld4_pisano_mul_of_coprime, Mathlib2.bld5_pisano_two_pow and Mathlib2.bld5_pisano_five_pow: 10^(k+3) = 2^(k+3)·5^(k+3) with coprime factors, so π = lcm(π(2^(k+3)), π(5^(k+3))) (bld4_pisano_mul_of_coprime) = lcm(3·2^(k+2), 4·5^(k+3)) by the two prime-power formulas; since k+2 ≥ 2 the lcm is 3·2^(k+2)·5^(k+3) = 15·10^(k+2). -/
theorem bld6_pisano_ten_pow (k : ℕ) : p3_pisano (10 ^ (k + 3)) = 15 * 10 ^ (k + 2) := by
  have e : 10 ^ (k+3) = 2 ^ (k+2+1) * 5 ^ (k+2+1) := by rw [← mul_pow]; norm_num
  have hc : Nat.Coprime (2 ^ (k+2+1)) (5 ^ (k+2+1)) := Nat.Coprime.pow _ _ (by norm_num)
  rw [e, Mathlib2.bld4_pisano_mul_of_coprime _ _ hc, Mathlib2.bld5_pisano_two_pow, Mathlib2.bld5_pisano_five_pow]
  have h1 : 3 * 2 ^ (k+2) = 4 * (3 * 2^k) := by ring
  have h2 : Nat.Coprime (3 * 2^k) (5^(k+2+1)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_mul_iff_left.2 ⟨by norm_num, Nat.Coprime.pow_left _ (by norm_num)⟩)
  rw [h1, Nat.lcm_mul_left, h2.lcm_eq_mul]
  rw [show (10:ℕ) = 2*5 by norm_num, mul_pow]; ring
end

-- forge:entry bld6_pisano_two_pow_mul_five_pow_eq_six_mul_iff kind=proved origin=conjecture
section
/- Uses Mathlib2.bld4_pisano_mul_of_coprime, Mathlib2.bld5_pisano_two_pow and Mathlib2.bld5_pisano_five_pow: π(2^(a+1)5^(b+1)) = lcm(3·2^a, 4·5^(b+1)) by the coprime-lcm rule and the two prime-power formulas; this equals 12·5^(b+1) for a ≤ 1 and 3·2^a·5^(b+1) for a ≥ 2, i.e. 6n, 3n, 3n/2 respectively — so the extremal ratio π(n) = 6n occurs exactly for a = 0 (n = 2·5^(b+1)). -/
theorem bld6_pisano_two_pow_mul_five_pow_eq_six_mul_iff (a b : ℕ) : p3_pisano (2 ^ (a + 1) * 5 ^ (b + 1)) = 6 * (2 ^ (a + 1) * 5 ^ (b + 1)) ↔ a = 0 := by
  have hc : Nat.Coprime (2 ^ (a+1)) (5 ^ (b+1)) := Nat.Coprime.pow _ _ (by norm_num)
  rw [Mathlib2.bld4_pisano_mul_of_coprime _ _ hc, Mathlib2.bld5_pisano_two_pow, Mathlib2.bld5_pisano_five_pow]
  constructor
  · intro h
    by_contra ha
    obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
    have hd : Nat.lcm (3 * 2 ^ (c+1)) (4 * 5 ^ (b+1)) ∣ 12 * (2^c * 5^(b+1)) :=
      Nat.lcm_dvd ⟨2 * 5^(b+1), by ring⟩ ⟨3 * 2^c, by ring⟩
    have hp : 0 < 2^c * 5^(b+1) := by positivity
    have hle := Nat.le_of_dvd (by positivity) hd
    have h' : Nat.lcm (3 * 2 ^ (c+1)) (4 * 5 ^ (b+1)) = 24 * (2^c * 5^(b+1)) := by
      rw [h]; ring
    rw [h'] at hle
    omega
  · rintro rfl
    have h2 : Nat.Coprime 3 (4 * 5^(b+1)) :=
      Nat.coprime_mul_iff_right.2 ⟨by norm_num, Nat.Coprime.pow_right _ (by norm_num)⟩
    simp only [pow_zero, mul_one]
    rw [h2.lcm_eq_mul]; ring
end

-- forge:entry fld_irreducible_X_sq_add_X_add_one_zmod_iff kind=proved origin=conjecture
section
/- X^2 + X + 1 is irreducible over F_p iff p ≡ 2 (mod 3) — a monic quadratic is irreducible iff it has no root; for p = 3 it is (X-1)^2; for p ≠ 3 a root is exactly an element of multiplicative order 3, which exists iff 3 | p - 1 (cyclic unit group). -/
lemma fld_irreducible_X_sq_add_X_add_one_zmod_iff_aux1 : ∀ v : ZMod 2, v * v + v + 1 ≠ 0 := by decide

theorem fld_irreducible_X_sq_add_X_add_one_zmod_iff (p : ℕ) [Fact p.Prime] : Irreducible (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod p)) ↔ p % 3 = 2 := by
  have hpp : p.Prime := Fact.out
  have hdeg : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod p)).natDegree = 2 := by
    compute_degree!
  have hne : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod p)) ≠ 0 := by
    intro h; rw [h] at hdeg; simp at hdeg
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  have hroot : ∀ w : ZMod p, w ∈ (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod p)).roots ↔
      w ^ 2 + w + 1 = 0 := by
    intro w
    rw [Polynomial.mem_roots hne]
    simp [Polynomial.IsRoot]
  constructor
  · intro hr
    have hno : ∀ w : ZMod p, w ^ 2 + w + 1 ≠ 0 := by
      intro w hw
      have := (hroot w).2 hw
      rw [hr] at this
      simp at this
    by_contra hmod
    have h01 : p % 3 = 0 ∨ p % 3 = 1 := by omega
    rcases h01 with h0 | h1
    · have h3 : p = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).1 (Nat.dvd_of_mod_eq_zero h0)).symm
      apply hno 1
      have : ((3 : ℕ) : ZMod p) = 0 := by rw [ZMod.natCast_eq_zero_iff, h3]
      push_cast at this
      linear_combination this
    · obtain ⟨x, hx⟩ := fld_prime_one_mod_three_eq_sq_add_three_sq_aux3 p hpp h1
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hx
      push_cast at hx
      have h2 : (2 : ZMod p) ≠ 0 := by
        intro h
        have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
        rw [ZMod.natCast_eq_zero_iff] at h'
        have := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 h'
        omega
      apply hno (((x : ZMod p) - 1) / 2)
      field_simp
      linear_combination hx
  · intro hmod
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro w hw
    rw [hroot, pow_two] at hw
    by_cases hp2 : p = 2
    · subst hp2
      exact fld_irreducible_X_sq_add_X_add_one_zmod_iff_aux1 w (by convert hw)
    · have hp3 : 3 < p := by
        have := hpp.two_le
        have : p ≠ 3 := by rintro rfl; omega
        omega
      have := fld_isSquare_neg_three_zmod_iff_aux1 p hp3 w (by rw [pow_two]; exact hw)
      omega
end

-- forge:entry bld6_tsum_lucas_div_two_pow kind=proved origin=conjecture
section
/- Uses Mathlib2.calc_tsum_fib_div_two_pow and Mathlib2.lib_p3_lucas_cast: by lib_p3_lucas_cast L_n = 2F_(n+1) - F_n in ℝ; ∑ F_n/2^n = 2 (calc_tsum_fib_div_two_pow, also giving summability), and dropping the zero term n = 0 gives ∑ F_(n+1)/2^n = 2·2 = 4; so the sum is 2·4 - 2 = 6. -/
theorem bld6_tsum_lucas_div_two_pow : ∑' n : ℕ, (p3_lucas n : ℝ) / 2 ^ n = 6 := by
  have e := Mathlib2.calc_tsum_fib_div_two_pow
  have hs : Summable (fun n : ℕ => (Nat.fib n : ℝ) / 2 ^ n) := by
    by_contra h
    rw [tsum_eq_zero_of_not_summable h] at e
    norm_num at e
  have h0 : HasSum (fun n : ℕ => (Nat.fib n : ℝ) / 2 ^ n) 2 := by
    have := hs.hasSum
    rwa [e] at this
  have h1 : HasSum (fun n : ℕ => (Nat.fib (n+1) : ℝ) / 2 ^ (n+1)) 2 := by
    have := (hasSum_nat_add_iff' 1).2 h0
    simpa using this
  have h2 := (h1.mul_left 4).sub h0
  have fe : (fun n : ℕ => (p3_lucas n : ℝ) / 2 ^ n) = fun n => 4 * ((Nat.fib (n+1) : ℝ) / 2 ^ (n+1)) - (Nat.fib n : ℝ) / 2 ^ n := by
    funext n
    rw [Mathlib2.lib_p3_lucas_cast ℝ n, pow_succ]; field_simp; ring
  rw [fe, h2.tsum_eq]; norm_num
end

-- forge:entry bld6_integral_dalzell_companion kind=proved origin=conjecture
section
/- Uses Mathlib2.calc_integral_dalzell and Mathlib2.calc_integral_beta_nat: x^6(1-x)^4/(1+x^2) = x^4(1-x)^4 - x^4(1-x)^4/(1+x^2) pointwise; split the integral (intervalIntegral.integral_sub), the first piece is 1/630 by calc_integral_beta_nat 4 4 and the second is 22/7 - π by calc_integral_dalzell. -/
theorem bld6_integral_dalzell_companion : ∫ x in (0:ℝ)..1, x ^ 6 * (1 - x) ^ 4 / (1 + x ^ 2) = Real.pi - 22 / 7 + 1 / 630 := by
  have h1 := Mathlib2.calc_integral_dalzell
  have h2 : ∫ x in (0:ℝ)..1, x ^ 4 * (1 - x) ^ 4 = 1/630 := by
    rw [Mathlib2.calc_integral_beta_nat 4 4]; norm_num [Nat.factorial]
  have fe : ∀ x : ℝ, x ^ 6 * (1 - x) ^ 4 / (1 + x ^ 2) = x ^ 4 * (1 - x) ^ 4 - x ^ 4 * (1 - x) ^ 4 / (1 + x ^ 2) := by
    intro x
    have : (1 + x^2) ≠ 0 := by positivity
    field_simp; ring
  simp_rw [fe]
  rw [intervalIntegral.integral_sub, h1, h2]
  · ring
  · exact (by fun_prop : Continuous fun x : ℝ => x ^ 4 * (1 - x) ^ 4).intervalIntegrable _ _
  · apply Continuous.intervalIntegrable
    exact Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity)
end

-- forge:entry bld6_pi_dalzell_beta_bounds kind=proved origin=conjecture
section
/- Uses Mathlib2.calc_integral_dalzell and Mathlib2.calc_integral_beta_nat: on (0,1) one has x^4(1-x)^4/2 < x^4(1-x)^4/(1+x^2) < x^4(1-x)^4; integrate (strict monotonicity of the interval integral for continuous functions). The middle integral is 22/7 - π by calc_integral_dalzell, the outer one is 4!4!/9! = 1/630 by calc_integral_beta_nat 4 4. -/
theorem bld6_pi_dalzell_beta_bounds : 22 / 7 - 1 / 630 < Real.pi ∧ Real.pi < 22 / 7 - 1 / 1260 := by
  have h1 := Mathlib2.calc_integral_dalzell
  have h2 : ∫ x in (0:ℝ)..1, x ^ 4 * (1 - x) ^ 4 = 1/630 := by
    rw [Mathlib2.calc_integral_beta_nat 4 4]; norm_num [Nat.factorial]
  have cB : Continuous fun x : ℝ => x ^ 4 * (1 - x) ^ 4 := by fun_prop
  have cD : Continuous fun x : ℝ => x ^ 4 * (1 - x) ^ 4 / (1 + x ^ 2) :=
    Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity)
  have half : (1/2:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have i1 : ∫ x in (0:ℝ)..1, x ^ 4 * (1 - x) ^ 4 / (1 + x ^ 2) < ∫ x in (0:ℝ)..1, x ^ 4 * (1 - x) ^ 4 := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt zero_lt_one cD.continuousOn cB.continuousOn
    · intro x hx
      exact div_le_self (by positivity) (by nlinarith [sq_nonneg x])
    · exact ⟨1/2, half, by norm_num⟩
  have i2 : ∫ x in (0:ℝ)..1, x ^ 4 * (1 - x) ^ 4 < ∫ x in (0:ℝ)..1, 2 * (x ^ 4 * (1 - x) ^ 4 / (1 + x ^ 2)) := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt zero_lt_one cB.continuousOn (continuous_const.mul cD).continuousOn
    · intro x hx
      have hB : 0 ≤ x^4*(1-x)^4 := by positivity
      have hx2 : x^2 ≤ 1 := by nlinarith [hx.1, hx.2]
      change x ^ 4 * (1 - x) ^ 4 ≤ 2 * (x ^ 4 * (1 - x) ^ 4 / (1 + x ^ 2))
      rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
      nlinarith [mul_nonneg hB (sub_nonneg.2 hx2)]
    · exact ⟨1/2, half, by norm_num⟩
  rw [intervalIntegral.integral_const_mul] at i2
  rw [h1] at i1 i2; rw [h2] at i1 i2
  constructor <;> linarith
end

-- forge:entry bld6_tsum_inv_fib_mul_fib_add_two kind=proved origin=conjecture
section
/- Uses Mathlib2.calc_tsum_inv_three_consecutive_aux1 (general telescoping HasSum lemma): take g n = 1/(F_(n+1) F_(n+2)); then g n - g (n+1) = (F_(n+3) - F_(n+1))/(F_(n+1)F_(n+2)F_(n+3)) = 1/(F_(n+1)F_(n+3)) by Nat.fib_add_two, g → 0 since F_(n+1) ≥ n/…→∞ (Nat.fib_lt_fib_succ / le_fib_self), and g 0 = 1. -/
theorem bld6_tsum_inv_fib_mul_fib_add_two_aux1 (n : ℕ) : n + 1 ≤ Nat.fib (n + 2) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have := Nat.fib_add_two (n := k+1)
    have hp : 0 < Nat.fib (k+1) := Nat.fib_pos.2 (by omega)
    have ih' : k + 1 ≤ Nat.fib (k+1+1) := ih
    omega

theorem bld6_tsum_inv_fib_mul_fib_add_two : ∑' n : ℕ, 1 / ((Nat.fib (n + 1) : ℝ) * (Nat.fib (n + 3) : ℝ)) = 1 := by
  have hpos : ∀ n : ℕ, (0:ℝ) < Nat.fib (n+1) := fun n => by exact_mod_cast Nat.fib_pos.2 (by omega)
  have hg : Filter.Tendsto (fun n : ℕ => 1 / ((Nat.fib (n + 1) : ℝ) * (Nat.fib (n + 1 + 1) : ℝ))) Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : (1:ℝ) ≤ Nat.fib (n+1) := by exact_mod_cast Nat.fib_pos.2 (by omega)
    have h2 : (n:ℝ) + 1 ≤ Nat.fib (n+1+1) := by exact_mod_cast bld6_tsum_inv_fib_mul_fib_add_two_aux1 n
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hstep : ∀ n : ℕ, 1 / ((Nat.fib (n + 1) : ℝ) * (Nat.fib (n + 3) : ℝ)) = 1 / ((Nat.fib (n + 1) : ℝ) * (Nat.fib (n + 1 + 1) : ℝ)) - 1 / ((Nat.fib (n + 1 + 1) : ℝ) * (Nat.fib (n + 1 + 1 + 1) : ℝ)) := by
    intro n
    have a := hpos n
    have b := hpos (n+1)
    have e : (Nat.fib (n+1+1+1) : ℝ) = Nat.fib (n+1) + Nat.fib (n+1+1) := by
      rw [Nat.fib_add_two]; push_cast; rfl
    have e' : (Nat.fib (n+3) : ℝ) = Nat.fib (n+1) + Nat.fib (n+1+1) := e
    rw [e]; field_simp; ring
  have h := Mathlib2.calc_tsum_inv_three_consecutive_aux1 (fun n : ℕ => 1 / ((Nat.fib (n + 1) : ℝ) * (Nat.fib (n + 3) : ℝ))) (fun n : ℕ => 1 / ((Nat.fib (n + 1) : ℝ) * (Nat.fib (n + 1 + 1) : ℝ))) (fun n => by positivity) hstep hg
  rw [h.tsum_eq]; simp
end

-- forge:entry fld_finrank_adjoin_sqrt_two_add_sqrt_three kind=proved origin=conjecture
section
/- [ℚ(√2+√3) : ℚ] = 4 — IntermediateField.adjoin.finrank reduces to the degree of the minimal polynomial, which is X^4 - 10X^2 + 1; Uses Mathlib2.poly_x4_sub_10x2_add_1_irreducible_int (irreducibility over ℤ, hence over ℚ by Gauss) to identify the minimal polynomial. -/
theorem fld_finrank_adjoin_sqrt_two_add_sqrt_three : Module.finrank ℚ (IntermediateField.adjoin ℚ ({Real.sqrt 2 + Real.sqrt 3} : Set ℝ)) = 4 := by
  have hdeg : (Polynomial.X ^ 4 - 10 * Polynomial.X ^ 2 + 1 : Polynomial ℚ).natDegree = 4 := by
    compute_degree!
  have hint : IsIntegral ℚ (Real.sqrt 2 + Real.sqrt 3) := by
    by_contra h
    have h0 := minpoly.eq_zero h
    rw [fld_minpoly_sqrt_two_add_sqrt_three] at h0
    rw [h0] at hdeg
    simp at hdeg
  rw [IntermediateField.adjoin.finrank hint, fld_minpoly_sqrt_two_add_sqrt_three, hdeg]
end

-- forge:entry fld_adjoin_sqrt_two_sqrt_three_eq_adjoin_sum kind=proved origin=conjecture
section
/- ℚ(√2, √3) = ℚ(√2 + √3): the sum is a primitive element — ⊇ is clear; for ⊆, with s = √2+√3 one has s^3 = 11√2 + 9√3, so √2 = (s^3 - 9s)/2 and √3 = (11s - s^3)/2 lie in ℚ(s). -/
theorem fld_adjoin_sqrt_two_sqrt_three_eq_adjoin_sum : IntermediateField.adjoin ℚ ({Real.sqrt 2, Real.sqrt 3} : Set ℝ) = IntermediateField.adjoin ℚ ({Real.sqrt 2 + Real.sqrt 3} : Set ℝ) := by
  have ha : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hb : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    have hs : Real.sqrt 2 + Real.sqrt 3 ∈ IntermediateField.adjoin ℚ ({Real.sqrt 2 + Real.sqrt 3} : Set ℝ) :=
      IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)
    have hq : ∀ q : ℚ, (q : ℝ) ∈ IntermediateField.adjoin ℚ ({Real.sqrt 2 + Real.sqrt 3} : Set ℝ) := by
      intro q
      have := IntermediateField.algebraMap_mem (IntermediateField.adjoin ℚ ({Real.sqrt 2 + Real.sqrt 3} : Set ℝ)) q
      simpa using this
    have h9 := hq 9
    have h11 := hq 11
    have h2 := hq 2
    push_cast at h9 h11 h2
    intro x hx
    rcases hx with rfl | rfl
    · have : Real.sqrt 2 = ((Real.sqrt 2 + Real.sqrt 3) ^ 3 - 9 * (Real.sqrt 2 + Real.sqrt 3)) / 2 := by
        linear_combination (-((Real.sqrt 2 + 3 * Real.sqrt 3) / 2)) * ha - ((3 * Real.sqrt 2 + Real.sqrt 3) / 2) * hb
      have hm := div_mem (sub_mem (pow_mem hs 3) (mul_mem h9 hs)) h2
      rwa [← this] at hm
    · have : Real.sqrt 3 = (11 * (Real.sqrt 2 + Real.sqrt 3) - (Real.sqrt 2 + Real.sqrt 3) ^ 3) / 2 := by
        linear_combination ((Real.sqrt 2 + 3 * Real.sqrt 3) / 2) * ha + ((3 * Real.sqrt 2 + Real.sqrt 3) / 2) * hb
      have hm := div_mem (sub_mem (mul_mem h11 hs) (pow_mem hs 3)) h2
      rwa [← this] at hm
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact add_mem (IntermediateField.subset_adjoin ℚ _ (by simp)) (IntermediateField.subset_adjoin ℚ _ (by simp))
end

-- forge:entry bld6_tsum_inv_odd_sq_mul_odd_sq kind=proved origin=conjecture
section
/- Uses Mathlib2.calc_tsum_inv_odd_sq and Mathlib2.calc_tsum_inv_odd_consecutive: 1/(a^2(a+2)^2) = (1/4)(1/a^2 + 1/(a+2)^2) - (1/2)·1/(a(a+2)) with a = 2n+1. The sum of 1/a^2 is π^2/8 (calc_tsum_inv_odd_sq), the shifted sum is π^2/8 - 1, and the sum of 1/(a(a+2)) is 1/2 (calc_tsum_inv_odd_consecutive): total (1/4)(π^2/4 - 1) - 1/4. -/
theorem bld6_tsum_inv_odd_sq_mul_odd_sq : ∑' n : ℕ, 1 / ((2 * (n : ℝ) + 1) ^ 2 * (2 * (n : ℝ) + 3) ^ 2) = Real.pi ^ 2 / 16 - 1 / 2 := by
  have eA := Mathlib2.calc_tsum_inv_odd_sq
  have eC := Mathlib2.calc_tsum_inv_odd_consecutive
  have sA : Summable (fun n : ℕ => 1 / (2 * (n : ℝ) + 1) ^ 2) := by
    by_contra h
    rw [tsum_eq_zero_of_not_summable h] at eA
    have := Real.pi_pos
    nlinarith
  have sC : Summable (fun n : ℕ => 1 / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3))) := by
    by_contra h
    rw [tsum_eq_zero_of_not_summable h] at eC
    norm_num at eC
  have hA : HasSum (fun n : ℕ => 1 / (2 * (n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 8) := by
    have := sA.hasSum
    rwa [eA] at this
  have hC : HasSum (fun n : ℕ => 1 / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3))) (1 / 2) := by
    have := sC.hasSum
    rwa [eC] at this
  have hA1 : HasSum (fun n : ℕ => 1 / (2 * (n : ℝ) + 3) ^ 2) (Real.pi ^ 2 / 8 - 1) := by
    have := (hasSum_nat_add_iff' 1).2 hA
    have e3 : ∀ n : ℕ, 2 * (((n + 1 : ℕ)) : ℝ) + 1 = 2 * (n : ℝ) + 3 := fun n => by push_cast; ring
    simp only [e3] at this
    simpa using this
  have h := ((hA.add hA1).mul_left (1/4)).sub (hC.mul_left (1/2))
  have fe : (fun n : ℕ => 1 / ((2 * (n : ℝ) + 1) ^ 2 * (2 * (n : ℝ) + 3) ^ 2)) = fun n : ℕ => 1/4 * (1 / (2 * (n : ℝ) + 1) ^ 2 + 1 / (2 * (n : ℝ) + 3) ^ 2) - 1/2 * (1 / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3))) := by
    funext n
    have h1 : (2*(n:ℝ)+1) ≠ 0 := by positivity
    have h3 : (2*(n:ℝ)+3) ≠ 0 := by positivity
    field_simp; ring
  rw [fe, h.tsum_eq]; ring
end

-- forge:entry bld6_sum_choose_alternating_div_eq_beta kind=proved origin=conjecture
section
/- Uses Mathlib2.calc_integral_beta_nat: expand (1-x)^n by the binomial theorem, so x^m(1-x)^n = ∑ (-1)^k C(n,k) x^(m+k); integrate termwise over [0,1] (integral_pow) to get the left side, and the right side is the value of the same integral by calc_integral_beta_nat m n (final step). -/
theorem bld6_sum_choose_alternating_div_eq_beta (m n : ℕ) : ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (n.choose k : ℝ) / ((m : ℝ) + k + 1) = ((m.factorial : ℝ) * n.factorial) / ((m + n + 1).factorial : ℝ) := by
  rw [← Mathlib2.calc_integral_beta_nat m n]
  have fe : ∀ x : ℝ, x ^ m * (1 - x) ^ n = ∑ k ∈ Finset.range (n+1), (-1:ℝ)^k * (n.choose k) * x^(m+k) := by
    intro x
    rw [sub_eq_add_neg, add_comm, add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [one_pow, neg_pow, pow_add]; ring
  simp_rw [fe]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_const_mul, integral_pow, one_pow, zero_pow (by omega), sub_zero]
    push_cast; ring
  · intro k _
    exact (by fun_prop : Continuous fun x : ℝ => (-1:ℝ)^k * (n.choose k) * x^(m+k)).intervalIntegrable _ _
end

-- forge:entry fld_sqrt_three_not_in_Q_sqrt_two kind=proved origin=conjecture
section
/- √3 ∉ ℚ(√2) — squaring gives 3 = a^2 + 2b^2 + 2ab√2, so ab = 0 by irrationality of √2; b = 0 gives √3 = a rational, a = 0 gives 3 = 2b^2, i.e. (2b)^2 = 6, contradicting irrationality of √6. -/
theorem fld_sqrt_three_not_in_Q_sqrt_two (a b : ℚ) : Real.sqrt 3 ≠ (a : ℝ) + (b : ℝ) * Real.sqrt 2 := by
  intro h
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsq : (3:ℝ) = a ^ 2 + 2 * b ^ 2 + 2 * a * b * Real.sqrt 2 := by
    rw [← h3, h]; linear_combination (b:ℝ)^2 * h2
  by_cases hab : a * b = 0
  · rcases mul_eq_zero.mp hab with ha | hb
    · subst ha
      simp only [Rat.cast_zero, zero_add, mul_zero, zero_mul, add_zero] at hsq h
      have h6 : Irrational (Real.sqrt 6) := by
        rw [irrational_sqrt_ofNat_iff]
        rintro ⟨k, hk⟩
        change 6 = k * k at hk
        have : k < 3 := by nlinarith
        interval_cases k <;> omega
      apply h6
      refine ⟨|2 * b|, ?_⟩
      have : (6:ℝ) = (2 * (b:ℝ)) ^ 2 := by nlinarith
      rw [this, Real.sqrt_sq_eq_abs]; push_cast; rfl
    · subst hb
      have := Nat.prime_three.irrational_sqrt
      apply this
      refine ⟨a, ?_⟩
      push_cast; rw [h]; simp
  · have hab' : (2 * (a:ℝ) * b) ≠ 0 := by
      have : ((2 * a * b : ℚ) : ℝ) ≠ 0 := by
        norm_cast; intro h0; apply hab; linarith
      simpa using this
    apply irrational_sqrt_two
    refine ⟨(3 - a ^ 2 - 2 * b ^ 2) / (2 * a * b), ?_⟩
    push_cast
    rw [div_eq_iff hab']; linear_combination hsq
end

-- forge:entry bld6_lcm_mul_integral_central_beta_nat kind=proved origin=conjecture
section
/- Uses Mathlib2.calc_integral_beta_nat and Mathlib2.arith_centralBinom_dvd_lcm: by mul_pow and calc_integral_beta_nat n n the integral is (n!)^2/(2n+1)! = 1/((2n+1)·centralBinom n) (Nat.centralBinom, Nat.choose factorial formula); so the left side equals lcm(1..2n)/centralBinom n, which is a positive natural number q by arith_centralBinom_dvd_lcm (Nair's integrality argument made explicit). -/
theorem bld6_lcm_mul_integral_central_beta_nat (n : ℕ) : ∃ q : ℕ, 0 < q ∧ (((Finset.Icc 1 (2 * n)).lcm id : ℕ) : ℝ) * (2 * (n : ℝ) + 1) * (∫ x in (0:ℝ)..1, (x * (1 - x)) ^ n) = (q : ℝ) := by
  obtain ⟨q, hq⟩ := Mathlib2.arith_centralBinom_dvd_lcm n
  have hL : (Finset.Icc 1 (2 * n)).lcm id ≠ 0 := by
    rw [Ne, Finset.lcm_eq_zero_iff]
    simp
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with rfl | h
    · rw [mul_zero] at hq; exact absurd hq hL
    · exact h
  refine ⟨q, hqpos, ?_⟩
  have hcb : n.centralBinom * n.factorial * n.factorial = (2*n).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2*n by omega)
    rw [show 2*n - n = n by omega] at this
    rw [Nat.centralBinom_eq_two_mul_choose]; exact this
  have hfac : ((n+n+1).factorial : ℝ) = (2*(n:ℝ)+1) * (n.centralBinom * n.factorial * n.factorial) := by
    rw [show n+n+1 = 2*n+1 by ring, Nat.factorial_succ, ← hcb]; push_cast; ring
  have h1 : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h2 : (n.centralBinom : ℝ) ≠ 0 := by exact_mod_cast n.centralBinom_ne_zero
  have h3 : (2*(n:ℝ)+1) ≠ 0 := by positivity
  rw [hq]
  simp_rw [mul_pow]
  rw [Mathlib2.calc_integral_beta_nat n n, hfac]
  push_cast
  field_simp
end

-- forge:entry fld_cbrt_two_not_in_Q_sqrt_two kind=proved origin=conjecture
section
/- The cube root of 2 does not lie in ℚ(√2) — expand (a + b√2)^3 = (a^3 + 6ab^2) + (3a^2 b + 2b^3)√2 = 2; irrationality of √2 forces b(3a^2 + 2b^2) = 0, so b = 0 and a^3 = 2; Uses Mathlib2.alg_rat_pow_ne_two at this last step. -/
theorem fld_cbrt_two_not_in_Q_sqrt_two (x : ℝ) (hx : x ^ 3 = 2) (a b : ℚ) : x ≠ (a : ℝ) + (b : ℝ) * Real.sqrt 2 := by
  intro h
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hc : ((a:ℝ)^3 + 6*a*b^2) + (3*a^2*b + 2*b^3) * Real.sqrt 2 = 2 := by
    have h3 : ((a:ℝ) + b * Real.sqrt 2)^3 = 2 := by rw [← h]; exact hx
    linear_combination h3 - (3*(a:ℝ)*b^2 + (b:ℝ)^3 * Real.sqrt 2) * h2
  by_cases hb : b = 0
  · subst hb
    apply Mathlib2.alg_rat_pow_ne_two 3 (by norm_num) a
    simp at hc
    exact_mod_cast hc
  · have hne : 3*a^2*b + 2*b^3 ≠ 0 := by
      have e : 3*a^2*b + 2*b^3 = b * (3*a^2 + 2*b^2) := by ring
      rw [e]; apply mul_ne_zero hb
      have hb2 : 0 < b^2 := by positivity
      have : 0 < 3*a^2+2*b^2 := by nlinarith [sq_nonneg a]
      exact this.ne'
    have hne' : (3*(a:ℝ)^2*b + 2*b^3) ≠ 0 := by exact_mod_cast hne
    apply irrational_sqrt_two
    refine ⟨(2 - (a^3 + 6*a*b^2)) / (3*a^2*b + 2*b^3), ?_⟩
    push_cast
    rw [div_eq_iff hne']; linear_combination -hc
end

-- forge:entry fld_sum_quadratic_residues_one_mod_four kind=proved origin=conjecture
section
/- For a prime p ≡ 1 (mod 4) the sum of the quadratic residues in [1, p-1] equals p(p-1)/4 — -1 is a residue, so r ↦ p - r is a fixed-point-free involution on the (p-1)/2 residues, pairing them into (p-1)/4 pairs each of sum p. -/
lemma fld_sum_quadratic_residues_one_mod_four_aux1 (p : ℕ) (hpp : p.Prime) (r : ℕ) :
    r ∈ (Finset.Icc 1 (p - 1)).image (fun x => x ^ 2 % p) ↔
      (1 ≤ r ∧ r < p) ∧ IsSquare ((r : ℕ) : ZMod p) := by
  haveI := Fact.mk hpp
  have hp2 := hpp.two_le
  simp only [Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    have hnd : ¬ p ∣ x ^ 2 := fun h => by
      have h1 := hpp.dvd_of_dvd_pow h
      have h2 := Nat.le_of_dvd (by omega) h1
      omega
    refine ⟨⟨Nat.pos_of_ne_zero (fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0)), Nat.mod_lt _ hpp.pos⟩,
      (x : ZMod p), ?_⟩
    rw [ZMod.natCast_mod]; push_cast; ring
  · rintro ⟨⟨h1, h2⟩, y, hy⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [mul_zero, ZMod.natCast_eq_zero_iff] at hy
      have := Nat.le_of_dvd (by omega) hy
      omega
    have hv0 : y.val ≠ 0 := fun h => hy0 ((ZMod.val_eq_zero y).1 h)
    have hvl := ZMod.val_lt y
    refine ⟨y.val, ⟨by omega, by omega⟩, ?_⟩
    have hc : ((y.val ^ 2 % p : ℕ) : ZMod p) = ((r : ℕ) : ZMod p) := by
      rw [ZMod.natCast_mod]; push_cast; rw [ZMod.natCast_zmod_val, hy]; ring
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hc
    rw [Nat.mod_mod, Nat.mod_eq_of_lt h2] at this
    exact this

theorem fld_sum_quadratic_residues_one_mod_four (p : ℕ) (hp : p.Prime) (h : p % 4 = 1) : ∑ a ∈ (Finset.Icc 1 (p - 1)).image (fun x => x ^ 2 % p), a = p * (p - 1) / 4 := by
  classical
  haveI := Fact.mk hp
  have hp2 := hp.two_le
  have hmem := fld_sum_quadratic_residues_one_mod_four_aux1 p hp
  generalize (Finset.Icc 1 (p - 1)).image (fun x => x ^ 2 % p) = S at hmem
  have hneg : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.2 (by omega)
  -- involution
  have hinv : ∀ r ∈ S, p - r ∈ S := by
    intro r hr
    obtain ⟨⟨h1, h2⟩, hsq⟩ := (hmem r).1 hr
    refine (hmem _).2 ⟨⟨by omega, by omega⟩, ?_⟩
    have : ((p - r : ℕ) : ZMod p) = (-1) * (r : ZMod p) := by
      rw [Nat.cast_sub h2.le, ZMod.natCast_self]; ring
    rw [this]
    exact hneg.mul hsq
  have hsum : ∑ r ∈ S, r = ∑ r ∈ S, (p - r) := by
    refine Finset.sum_nbij' (fun r => p - r) (fun r => p - r) hinv hinv ?_ ?_ ?_
    · intro r hr
      have := ((hmem r).1 hr).1
      show p - (p - r) = r
      omega
    · intro r hr
      have := ((hmem r).1 hr).1
      show p - (p - r) = r
      omega
    · intro r hr
      have := ((hmem r).1 hr).1
      show r = p - (p - r)
      omega
  have htwo : 2 * ∑ r ∈ S, r = S.card * p := by
    have : ∑ r ∈ S, r + ∑ r ∈ S, (p - r) = S.card * p := by
      rw [← Finset.sum_add_distrib, ← smul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_congr rfl (fun r hr => ?_)
      have := ((hmem r).1 hr).1
      omega
    rw [← hsum] at this
    omega
  -- cardinality
  have hcard : S.card + 1 = (p + 1) / 2 := by
    have hK := fld_card_image_sq_finite_field (ZMod p) (by rw [ZMod.ringChar_zmod_n]; omega)
    rw [ZMod.card] at hK
    have himg : (Finset.univ.image (fun x : ZMod p => x ^ 2)) =
        insert 0 (S.image (fun r : ℕ => (r : ZMod p))) := by
      ext z
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨x, rfl⟩
        by_cases hx : x = 0
        · left; rw [hx]; ring
        · right
          have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
          have hv0 : (x ^ 2).val ≠ 0 := fun h => hx2 ((ZMod.val_eq_zero _).1 h)
          have hvl := ZMod.val_lt (x ^ 2)
          refine ⟨(x ^ 2).val, (hmem _).2 ⟨⟨by omega, hvl⟩, ?_⟩, ZMod.natCast_zmod_val _⟩
          rw [ZMod.natCast_zmod_val]
          exact ⟨x, by ring⟩
      · rintro (rfl | ⟨r, hr, rfl⟩)
        · exact ⟨0, by ring⟩
        · obtain ⟨y, hy⟩ := ((hmem r).1 hr).2
          exact ⟨y, by rw [hy]; ring⟩
    rw [himg, Finset.card_insert_of_notMem, Finset.card_image_of_injOn] at hK
    · exact hK
    · intro a ha b hb hab
      have ha' := ((hmem a).1 ha).1
      have hb' := ((hmem b).1 hb).1
      have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hab
      rwa [Nat.mod_eq_of_lt ha'.2, Nat.mod_eq_of_lt hb'.2] at this
    · simp only [Finset.mem_image, not_exists, not_and]
      intro r hr h0
      have hr' := ((hmem r).1 hr).1
      rw [ZMod.natCast_eq_zero_iff] at h0
      have := Nat.le_of_dvd (by omega) h0
      omega
  obtain ⟨k, rfl⟩ : ∃ k, p = 4 * k + 1 := ⟨p / 4, by omega⟩
  have hc : S.card = 2 * k := by omega
  rw [hc] at htwo
  have hs : ∑ r ∈ S, r = (4 * k + 1) * k := by nlinarith
  rw [hs]
  have : (4 * k + 1) * (4 * k + 1 - 1) = 4 * ((4 * k + 1) * k) := by
    rw [Nat.add_sub_cancel]; ring
  rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
end

-- forge:entry fld_pow_char_eq_self_iff_natCast kind=proved origin=conjecture
section
/- In any field of characteristic p the fixed points of Frobenius are exactly the prime field: x^p = x iff x is the image of a natural number — (←) Fermat's little theorem in ZMod p pushed along the cast; (→) X^p - X has at most p roots in K and the p distinct elements 0, 1, …, p-1 are roots, so they are all the roots. -/
theorem fld_pow_char_eq_self_iff_natCast (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (x : K) : x ^ p = x ↔ ∃ n : ℕ, x = (n : K) := by
  classical
  have hp : p.Prime := Fact.out
  have hnat : ∀ n : ℕ, ((n : K)) ^ p = n := by
    intro n
    have := map_natCast (frobenius K p) n
    rwa [frobenius_def] at this
  constructor
  · intro hx
    have hne := FiniteField.X_pow_card_sub_X_ne_zero K hp.one_lt
    have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq K hp.one_lt
    set f : Polynomial K := Polynomial.X ^ p - Polynomial.X with hf
    have hroot : ∀ y : K, y ^ p = y → y ∈ f.roots.toFinset := by
      intro y hy
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
      simp [hf, hy]
    have hinj : Set.InjOn (fun n : ℕ => (n : K)) (Finset.range p) := by
      intro m hm n hn hmn
      simp only [Finset.coe_range, Set.mem_Iio] at hm hn
      have := (CharP.natCast_eq_natCast K p).mp hmn
      exact Nat.ModEq.eq_of_lt_of_lt this hm hn
    have hsub : (Finset.range p).image (fun n : ℕ => (n : K)) ⊆ f.roots.toFinset := by
      intro y hy
      obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hy
      exact hroot _ (hnat n)
    have hcard : f.roots.toFinset.card ≤ ((Finset.range p).image (fun n : ℕ => (n : K))).card := by
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
      calc f.roots.toFinset.card ≤ f.roots.card := Multiset.toFinset_card_le _
        _ ≤ f.natDegree := Polynomial.card_roots' f
        _ = p := hdeg
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have := hroot x hx
    rw [← heq] at this
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp this
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact hnat n
end

-- forge:entry fld_gaussianInt_one_add_i_prime kind=proved origin=conjecture
section
/- 1 + i is prime in ℤ[i] — its norm is 2, a rational prime, so it is irreducible (a factorization gives norms multiplying to 2, one factor is a unit); ℤ[i] is a Euclidean domain hence a PID, so irreducible implies prime. -/
theorem fld_gaussianInt_one_add_i_prime : Prime (⟨1, 1⟩ : GaussianInt) := by
  apply Mathlib2.fld_gaussianInt_prime_of_norm_prime
  norm_num [Zsqrtd.norm]
end

-- forge:entry fld_eval_eq_zero_forall_iff_dvd kind=proved origin=conjecture
section
/- A polynomial over a finite field F_q vanishes at every point iff it is divisible by X^q - X — X^q - X = ∏_{a} (X - a) (FiniteField.roots_X_pow_card_sub_X, separable with all q roots); the factors X - a are pairwise coprime, so each dividing f gives the product dividing f; the converse is FiniteField.pow_card. -/
theorem fld_eval_eq_zero_forall_iff_dvd (K : Type) [Field K] [Fintype K] (f : Polynomial K) : (∀ a : K, Polynomial.eval a f = 0) ↔ (Polynomial.X ^ Fintype.card K - Polynomial.X) ∣ f := by
  classical
  constructor
  · intro h
    have hq : 1 < Fintype.card K := Fintype.one_lt_card
    have hmon : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K).Monic := by
      apply Polynomial.monic_X_pow_sub
      rw [Polynomial.degree_X]; exact_mod_cast hq
    have hroots := FiniteField.roots_X_pow_card_sub_X K
    have hcard : Multiset.card (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K).roots = (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K).natDegree := by
      rw [hroots, FiniteField.X_pow_card_sub_X_natDegree_eq K hq]; simp [Finset.card_univ]
    have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon hcard
    rw [hroots] at hprod
    rw [← hprod]
    change (∏ a : K, (Polynomial.X - Polynomial.C a)) ∣ f
    apply Finset.prod_dvd_of_coprime
    · exact (Polynomial.pairwise_coprime_X_sub_C (s := fun a : K => a) Function.injective_id).set_pairwise _
    · intro a _
      exact Polynomial.dvd_iff_isRoot.mpr (h a)
  · rintro ⟨g, rfl⟩ a
    simp [FiniteField.pow_card]
end

-- forge:entry fld_pow_bijective_iff_coprime kind=proved origin=conjecture
section
/- For k > 0 the power map x ↦ x^k is a permutation of F_q iff gcd(k, q-1) = 1 — it fixes 0 and on the cyclic group of units of order q-1 the k-th power map is injective iff gcd(k, q-1) = 1 (if d = gcd > 1 there is an element of order d in the kernel; conversely use Bezout u*k ≡ 1 mod q-1). -/
theorem fld_pow_bijective_iff_coprime (K : Type) [Field K] [Fintype K] (k : ℕ) (hk : 0 < k) : Function.Bijective (fun x : K => x ^ k) ↔ Nat.Coprime k (Fintype.card K - 1) := by
  classical
  have hq : 0 < Fintype.card K - 1 := Nat.sub_pos_of_lt Fintype.one_lt_card
  constructor
  · intro hb
    by_contra hc
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
    have hord : orderOf g = Fintype.card K - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units]
    set d := Nat.gcd k (Fintype.card K - 1) with hd
    have hd1 : d ≠ 1 := hc
    have hd0 : 0 < d := Nat.gcd_pos_of_pos_left _ hk
    have hdk : d ∣ k := Nat.gcd_dvd_left _ _
    have hdq : d ∣ Fintype.card K - 1 := Nat.gcd_dvd_right _ _
    have h1 : (g ^ ((Fintype.card K - 1) / d)) ^ k = 1 := by
      obtain ⟨c, hc'⟩ := hdk
      rw [← pow_mul, hc', ← mul_assoc, Nat.div_mul_cancel hdq, pow_mul, ← hord, pow_orderOf_eq_one, one_pow]
    have h2 : ((g ^ ((Fintype.card K - 1) / d) : Kˣ) : K) = 1 := by
      apply hb.1
      show ((g ^ ((Fintype.card K - 1) / d) : Kˣ) : K) ^ k = 1 ^ k
      rw [one_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one]
    have h3 : g ^ ((Fintype.card K - 1) / d) = 1 := Units.ext h2
    have h4 := orderOf_dvd_of_pow_eq_one h3
    rw [hord] at h4
    have h5 := Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd hq hdq) hd0) h4
    have h6 := Nat.div_lt_self hq (by omega : 1 < d)
    omega
  · intro hc
    have hc' : Nat.gcd k (Fintype.card K - 1) = 1 := hc
    apply (Finite.injective_iff_bijective).mp
    intro x y hxy
    simp only at hxy
    by_cases hy : y = 0
    · subst hy
      rw [zero_pow hk.ne'] at hxy
      exact (pow_eq_zero_iff hk.ne').mp hxy
    · have hx : x ≠ 0 := by
        rintro rfl; rw [zero_pow hk.ne'] at hxy; exact hy ((pow_eq_zero_iff hk.ne').mp hxy.symm)
      have a1 : (x / y) ^ k = 1 := by rw [div_pow, hxy, div_self (pow_ne_zero _ hy)]
      have a2 : (x / y) ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one _ (div_ne_zero hx hy)
      have a3 := pow_gcd_eq_one.mpr ⟨a1, a2⟩
      rw [hc', pow_one] at a3
      exact (div_eq_one_iff_eq hy).mp a3
end

end Mathlib2
