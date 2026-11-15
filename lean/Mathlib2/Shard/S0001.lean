/- Mathlib2 分片 1（forge 自动维护，追加式）。 -/
import Mathlib
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry nt_four_consec_add_one_is_square kind=proved origin=conjecture
section
/- The product of four consecutive naturals plus 1 is a perfect square. -/
theorem nt_four_consec_add_one_is_square (n : ℕ) : IsSquare (n * (n + 1) * (n + 2) * (n + 3) + 1) := by
  exact ⟨n * n + 3 * n + 1, by ring⟩
end

-- forge:entry nt_pow5_sub_self_dvd_30 kind=proved origin=conjecture
section
/- n^5 - n is divisible by 30 for every integer n. -/
theorem nt_pow5_sub_self_dvd_30_aux1 : ∀ x : ZMod 30, x ^ 5 - x = 0 := by
  decide

theorem nt_pow5_sub_self_dvd_30 (n : ℤ) : 30 ∣ n ^ 5 - n := by
  have h := nt_pow5_sub_self_dvd_30_aux1 (n : ZMod 30)
  have h2 : ((n ^ 5 - n : ℤ) : ZMod 30) = 0 := by
    push_cast
    exact h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 30).mp h2
end

-- forge:entry an_sum_cubes_eq_sq_sum kind=proved origin=conjecture
section
/- Nicomachus: the sum of the first n cubes equals the square of the sum of the first n integers. -/
theorem an_sum_cubes_eq_sq_sum_aux1 (n : ℕ) : (∑ i ∈ Finset.range (n + 1), i) * 2 = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    ring

theorem an_sum_cubes_eq_sq_sum (n : ℕ) : ∑ i ∈ Finset.range (n + 1), i ^ 3 = (∑ i ∈ Finset.range (n + 1), i) ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ _ (k + 1)]
    have h := an_sum_cubes_eq_sq_sum_aux1 k
    have h2 : (∑ i ∈ Finset.range (k + 1), i) * 2 * (k + 1) = k * (k + 1) * (k + 1) := by rw [h]
    nlinarith [h2]
end

-- forge:entry nt_seven_dvd_sq_add_sq kind=proved origin=conjecture
section
/- If 7 divides a^2 + b^2 then 7 divides both a and b. -/
theorem nt_seven_dvd_sq_add_sq_aux1 : ∀ x y : ZMod 7, x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0 := by
  decide

theorem nt_seven_dvd_sq_add_sq (a b : ℤ) (h : 7 ∣ a ^ 2 + b ^ 2) : 7 ∣ a ∧ 7 ∣ b := by
  have h2 : ((a ^ 2 + b ^ 2 : ℤ) : ZMod 7) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr h
  push_cast at h2
  obtain ⟨ha, hb⟩ := nt_seven_dvd_sq_add_sq_aux1 _ _ h2
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp ha, (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hb⟩
end

-- forge:entry an_sum_fib_sq kind=proved origin=conjecture
section
/- Sum of squares of Fibonacci numbers F_0..F_n equals F_n * F_{n+1}. -/
theorem an_sum_fib_sq (n : ℕ) : ∑ i ∈ Finset.range (n + 1), Nat.fib i ^ 2 = Nat.fib n * Nat.fib (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Nat.fib_add_two]
    ring
end

-- forge:entry an_cyclic_div_ge_three kind=proved origin=conjecture
section
/- For positive reals a, b, c: a/b + b/c + c/a ≥ 3. -/
theorem an_cyclic_div_ge_three_aux1 (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h1 : c ≤ a) (h2 : c ≤ b) :
    3 * (a * b * c) ≤ a * a * c + b * b * a + c * c * b := by
  nlinarith [mul_nonneg hc.le (sq_nonneg (a - b)), mul_nonneg hb.le (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2))]

theorem an_cyclic_div_ge_three (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 3 ≤ a / b + b / c + c / a := by
  have key : 3 * (a * b * c) ≤ a * a * c + b * b * a + c * c * b := by
    rcases le_total a b with h1 | h1
    · rcases le_total a c with h2 | h2
      · have := an_cyclic_div_ge_three_aux1 b c a hc ha h1 h2
        linarith
      · exact an_cyclic_div_ge_three_aux1 a b c hb hc h2 (h2.trans h1)
    · rcases le_total b c with h2 | h2
      · have := an_cyclic_div_ge_three_aux1 c a b ha hb h2 h1
        linarith
      · exact an_cyclic_div_ge_three_aux1 a b c hb hc (h2.trans h1) h2
  have e : a / b + b / c + c / a = (a * a * c + b * b * a + c * c * b) / (a * b * c) := by
    field_simp
  rw [e, le_div_iff₀ (by positivity)]
  exact key
end

-- forge:entry nt_nine_dvd_sum_cubes_three_dvd_prod kind=proved origin=conjecture
section
/- If 9 divides a^3+b^3+c^3 then 3 divides abc. -/
theorem nt_nine_dvd_sum_cubes_three_dvd_prod_aux1 : ∀ x y z : ZMod 9, x ^ 3 + y ^ 3 + z ^ 3 = 0 → 3 * (x * y * z) = 0 := by
  decide

theorem nt_nine_dvd_sum_cubes_three_dvd_prod (a b c : ℤ) (h : 9 ∣ a ^ 3 + b ^ 3 + c ^ 3) : 3 ∣ a * b * c := by
  have h2 : ((a ^ 3 + b ^ 3 + c ^ 3 : ℤ) : ZMod 9) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).mpr h
  push_cast at h2
  have h3 := nt_nine_dvd_sum_cubes_three_dvd_prod_aux1 _ _ _ h2
  have h4 : ((3 * (a * b * c) : ℤ) : ZMod 9) = 0 := by
    push_cast
    exact h3
  have h5 : (9 : ℤ) ∣ 3 * (a * b * c) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).mp h4
  omega
end

-- forge:entry an_sum_mul_choose kind=proved origin=conjecture
section
/- Sum over k ≤ m of k*C(m,k) equals m*2^(m-1), stated with m = n+1. -/
theorem an_sum_mul_choose (n : ℕ) : ∑ k ∈ Finset.range (n + 2), k * Nat.choose (n + 1) k = (n + 1) * 2 ^ n := by
  rw [Finset.sum_range_succ', ← Nat.sum_range_choose n, Finset.mul_sum]
  simp only [Nat.zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro k _
  have := Nat.succ_mul_choose_eq n k
  simp only [Nat.succ_eq_add_one] at this
  linarith
end

-- forge:entry nt_prime_sq_sub_one_dvd_24 kind=proved origin=conjecture
section
/- For a prime p > 3, 24 divides p^2 - 1. -/
theorem nt_prime_sq_sub_one_dvd_24 (p : ℕ) (hp : p.Prime) (h : 3 < p) : 24 ∣ p ^ 2 - 1 := by
  have h2 : p % 2 ≠ 0 := by
    intro h0
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 (Nat.dvd_of_mod_eq_zero h0)
    omega
  have h3 : p % 3 ≠ 0 := by
    intro h0
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h0)
    omega
  have hr : p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 7 ∨ p % 24 = 11 ∨ p % 24 = 13 ∨ p % 24 = 17 ∨ p % 24 = 19 ∨ p % 24 = 23 := by
    omega
  apply Nat.dvd_of_mod_eq_zero
  apply Nat.sub_mod_eq_zero_of_mod_eq
  rcases hr with h | h | h | h | h | h | h | h <;> simp [Nat.pow_mod, h]
end

-- forge:entry nt_gcd_factorial_succ_add_one kind=disproved origin=conjecture
section
/- [suspected false] n!+1 and (n+1)!+1 are always coprime (fails at n = 0, where both are 2). -/
theorem nt_gcd_factorial_succ_add_one_disproof : ¬ (∀ (n : ℕ), Nat.gcd (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) = 1) := by
  intro h
  have := h 0
  revert this
  decide
end

-- forge:entry an_nesbitt kind=proved origin=conjecture
section
/- Nesbitt's inequality for positive reals. -/
theorem an_nesbitt (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) := by
  have h1 : 0 < b + c := by linarith
  have h2 : 0 < c + a := by linarith
  have h3 : 0 < a + b := by linarith
  rw [div_add_div _ _ h1.ne' h2.ne', div_add_div _ _ (mul_pos h1 h2).ne' h3.ne', div_le_div_iff₀ (by norm_num) (mul_pos (mul_pos h1 h2) h3)]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
    mul_nonneg ha.le (sq_nonneg (b - c)), mul_nonneg hb.le (sq_nonneg (a - c)), mul_nonneg hc.le (sq_nonneg (a - b)),
    mul_nonneg ha.le (sq_nonneg (a - b)), mul_nonneg ha.le (sq_nonneg (a - c)), mul_nonneg hb.le (sq_nonneg (a - b)),
    mul_nonneg hb.le (sq_nonneg (b - c)), mul_nonneg hc.le (sq_nonneg (a - c)), mul_nonneg hc.le (sq_nonneg (b - c))]
end

-- forge:entry nt_gcd_21n4_14n3 kind=proved origin=conjecture
section
/- The fraction (21n+4)/(14n+3) is irreducible (IMO 1959 P1). -/
theorem nt_gcd_21n4_14n3 (n : ℕ) : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
  have h1 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ 2 * (21 * n + 4) :=
    Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) 2
  have h2 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ 2 * (21 * n + 4) + 1 := by
    have h : 2 * (21 * n + 4) + 1 = 3 * (14 * n + 3) := by ring
    rw [h]
    exact Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) 3
  exact Nat.dvd_one.1 ((Nat.dvd_add_right h1).1 h2)
end

-- forge:entry an_sqrt_add_le_sqrt_two_mul kind=proved origin=conjecture
section
/- For nonnegative a, b: sqrt a + sqrt b ≤ sqrt(2(a+b)). -/
theorem an_sqrt_add_le_sqrt_two_mul (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : Real.sqrt a + Real.sqrt b ≤ Real.sqrt (2 * (a + b)) := by
  apply Real.le_sqrt_of_sq_le
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b)]
end

-- forge:entry nt_seven_dvd_pow_sum kind=proved origin=conjecture
section
/- 7 divides 3^(2n+1) + 2^(n+2) for all n. -/
theorem nt_seven_dvd_pow_sum (n : ℕ) : 7 ∣ 3 ^ (2 * n + 1) + 2 ^ (n + 2) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨2 * m + 3 ^ (2 * k + 1), ?_⟩
    have e1 : 3 ^ (2 * (k + 1) + 1) = 9 * 3 ^ (2 * k + 1) := by ring
    have e2 : 2 ^ (k + 1 + 2) = 2 * 2 ^ (k + 2) := by ring
    omega
end

-- forge:entry nt_euler_poly_prime kind=disproved origin=conjecture
section
/- [suspected false] Euler's polynomial n^2+n+41 is always prime (fails at n = 40). -/
theorem nt_euler_poly_prime_disproof : ¬ (∀ (n : ℕ), Nat.Prime (n ^ 2 + n + 41)) := by
  intro h
  have h1 := h 40
  have h2 : ¬ Nat.Prime (40 ^ 2 + 40 + 41) := by norm_num
  exact h2 h1
end

-- forge:entry an_cassini_int kind=proved origin=conjecture
section
/- Cassini's identity: F_{n+2} F_n - F_{n+1}^2 = (-1)^{n+1} over the integers. -/
theorem an_cassini_int (n : ℕ) : (Nat.fib (n + 2) : ℤ) * (Nat.fib n : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : (Nat.fib (k + 1 + 2) : ℤ) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
      rw [Nat.fib_add_two]; push_cast; ring
    have h2 : (Nat.fib (k + 2) : ℤ) = Nat.fib k + Nat.fib (k + 1) := by
      rw [Nat.fib_add_two]; push_cast; ring
    have h3 : ((-1 : ℤ)) ^ (k + 1 + 1) = -((-1) ^ (k + 1)) := by ring
    rw [h1, h3, ← ih, show k + 1 + 1 = k + 2 from rfl, h2]
    ring
end

-- forge:entry an_telescoping_inv_mul kind=proved origin=conjecture
section
/- Telescoping sum: sum_{i<n} 1/((i+1)(i+2)) = n/(n+1). -/
theorem an_telescoping_inv_mul (n : ℕ) : ∑ i ∈ Finset.range n, (1 : ℝ) / (((i : ℝ) + 1) * ((i : ℝ) + 2)) = (n : ℝ) / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (k : ℝ) + 2 ≠ 0 := by positivity
    have h3 : (k : ℝ) + 1 + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
end

-- forge:entry nt_odd_sq_add_odd_sq_not_square kind=proved origin=conjecture
section
/- The sum of two odd squares is never a perfect square. -/
theorem nt_odd_sq_add_odd_sq_not_square_aux1 : ∀ k m c : ZMod 4, (2 * k + 1) ^ 2 + (2 * m + 1) ^ 2 ≠ c * c := by
  decide

theorem nt_odd_sq_add_odd_sq_not_square (a b : ℤ) (ha : Odd a) (hb : Odd b) : ¬ IsSquare (a ^ 2 + b ^ 2) := by
  rintro ⟨c, hc⟩
  obtain ⟨k, rfl⟩ := ha
  obtain ⟨m, rfl⟩ := hb
  have h := congrArg (fun x : ℤ => (x : ZMod 4)) hc
  simp only at h
  push_cast at h
  exact nt_odd_sq_add_odd_sq_not_square_aux1 _ _ _ h
end

-- forge:entry nt_prime_sq_add_two_prime kind=proved origin=conjecture
section
/- If p and p^2+2 are both prime then p = 3. -/
theorem nt_prime_sq_add_two_prime (p : ℕ) (hp : p.Prime) (h : (p ^ 2 + 2).Prime) : p = 3 := by
  by_cases h0 : p % 3 = 0
  · exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h0)).symm
  · exfalso
    have hm : (p ^ 2 + 2) % 3 = 0 := by
      have hr : p % 3 = 1 ∨ p % 3 = 2 := by omega
      rcases hr with h1 | h1 <;> simp [Nat.add_mod, Nat.pow_mod, h1]
    have h3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three h).1 (Nat.dvd_of_mod_eq_zero hm)
    have h2 := hp.two_le
    nlinarith
end

-- forge:entry an_sum_fib_odd kind=proved origin=conjecture
section
/- Sum of the first n odd-indexed Fibonacci numbers is F_{2n}. -/
theorem an_sum_fib_odd (n : ℕ) : ∑ i ∈ Finset.range n, Nat.fib (2 * i + 1) = Nat.fib (2 * n) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, show 2 * (k + 1) = 2 * k + 2 by ring, Nat.fib_add_two]
end

end Mathlib2
