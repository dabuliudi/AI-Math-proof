/- Mathlib2 分片 23（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0003
import Mathlib2.Shard.S0011
import Mathlib2.Shard.S0012
import Mathlib2.Shard.S0013
import Mathlib2.Shard.S0017
import Mathlib2.Shard.S0019
import Mathlib2.Shard.S0020
import Mathlib2.Shard.S0021
import Mathlib2.Shard.S0022
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry lib_monotone_sub_of_convex_seq kind=proved origin=conjecture
section
/- A convex sequence (second differences nonnegative) in an ordered abelian group has monotone increments f(k+1) - f(k). Promoted and generalised from Mathlib2.bld3_rank_pow_card_stabilizes_aux1 (also used with bld2_rank_pow_convex, bld3_nilpotent_rank_pow_le). -/
theorem lib_monotone_sub_of_convex_seq {α : Type*} [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] (f : ℕ → α) (h : ∀ k, f (k + 1) + f (k + 1) ≤ f k + f (k + 2)) : Monotone (fun k => f (k + 1) - f k) := by
  apply monotone_nat_of_le_succ
  intro k
  show f (k + 1) - f k ≤ f (k + 1 + 1) - f (k + 1)
  rw [sub_le_sub_iff]
  have := h k
  rwa [add_comm (f k)] at this
end

-- forge:entry p5_lemma2 kind=proved origin=paper
section
/- Lemma 2 (Sandor-Atanassov): phi(n)+sigma(n) >= 2n for n >= 2. -/
theorem p5_lemma2_aux1 (n : ℕ) (hn : n ≠ 0) : p5_dedekind_psi n ≤ ArithmeticFunction.sigma 1 n := by
  induction n using induction_on_primes with
  | zero => exact absurd rfl hn
  | one => simp [Mathlib2.p5_psi_ge_succ_aux2]
  | prime_mul p a hp ih =>
    have ha : a ≠ 0 := by rintro rfl; simp at hn
    have ih' := ih ha
    by_cases hd : p ∣ a
    · rw [Mathlib2.p5_psi_prime_mul_of_dvd p a hp hd ha]
      have := Mathlib2.p5_sigma_prime_mul_of_dvd p a hp hd ha
      nlinarith
    · rw [Mathlib2.p5_psi_ge_succ_aux1 p a hp hd,
        ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime ((Nat.Prime.coprime_iff_not_dvd hp).2 hd)]
      have hs : ArithmeticFunction.sigma 1 p = p + 1 := by
        rw [ArithmeticFunction.sigma_one_apply, hp.divisors, Finset.sum_pair hp.ne_one.symm]
        omega
      rw [hs]
      exact Nat.mul_le_mul_left _ ih'

theorem p5_lemma2 (n : ℕ) (hn : 2 ≤ n) : 2 * n ≤ n.totient + ArithmeticFunction.sigma 1 n := by
  have h1 := Mathlib2.p5_lemma1 n hn
  have h2 := p5_lemma2_aux1 n (by omega)
  omega
end

-- forge:entry lib_p3_lucas_cast kind=proved origin=conjecture
section
/- Cast formula for the Lucas numbers L_n = 2 F_(n+1) - F_n (Mathlib2.p3_lucas) in an arbitrary ring: the truncated subtraction in the definition is exact. Promoted and generalised from Mathlib2.p3_remark3_aux1 (the case R = ℤ; re-derived in bld2_lucas_sq_sub_five_fib_sq, bld2_pell_five_solutions_lucas, bld3_pell_five_neg_four_solutions_lucas). -/
theorem lib_p3_lucas_cast (R : Type*) [Ring R] (n : ℕ) : ((p3_lucas n : ℕ) : R) = 2 * (Nat.fib (n + 1) : R) - (Nat.fib n : R) := by
  unfold p3_lucas
  have hle : Nat.fib n ≤ 2 * Nat.fib (n + 1) := by
    have := Nat.fib_le_fib_succ (n := n)
    omega
  rw [Nat.cast_sub hle]
  push_cast
  rfl
end

-- forge:entry lib_pow_mul_pow_eq_of_mul_eq_central_mul kind=proved origin=conjecture
section
/- Commutation of powers when the commutator is central (class-2 / Heisenberg relation): if c commutes with a, b and b*a = c*a*b then b^k * a^l = c^(k*l) * a^l * b^k. Promoted and generalised from Mathlib2.bld3_mul_pow_prime_of_card_prime_cube_aux1 (the l = 1 case; see also _aux2 for (a*b)^k = a^k*b^k*c^(k.choose 2)). -/
theorem lib_pow_mul_pow_eq_of_mul_eq_central_mul {M : Type*} [Monoid M] (a b c : M) (hca : Commute c a) (hcb : Commute c b) (h : b * a = c * a * b) (k l : ℕ) : b ^ k * a ^ l = c ^ (k * l) * a ^ l * b ^ k := by
  have h1 : b ^ k * a = c ^ k * a * b ^ k :=
    Mathlib2.bld3_mul_pow_prime_of_card_prime_cube_aux1 a b c hca hcb h k
  have hck : Commute (c ^ k) a := hca.pow_left k
  induction l with
  | zero => simp
  | succ l ih =>
    have hcl : Commute (c ^ k) (a ^ l) := hck.pow_right l
    calc b ^ k * a ^ (l + 1) = b ^ k * a ^ l * a := by rw [pow_succ, mul_assoc]
      _ = c ^ (k * l) * a ^ l * (b ^ k * a) := by rw [ih]; simp only [mul_assoc]
      _ = c ^ (k * l) * a ^ l * (c ^ k * a * b ^ k) := by rw [h1]
      _ = c ^ (k * l) * (a ^ l * c ^ k) * a * b ^ k := by simp only [mul_assoc]
      _ = c ^ (k * l) * (c ^ k * a ^ l) * a * b ^ k := by rw [hcl.eq]
      _ = c ^ (k * (l + 1)) * a ^ (l + 1) * b ^ k := by
        rw [Nat.mul_succ, pow_add, pow_succ]; simp only [mul_assoc]
end

-- forge:entry lib_real_sqrt_sub_sqrt_bounds kind=proved origin=conjecture
section
/- Two-sided mean-value bound for the square root: (b-a)/(2√b) ≤ √b - √a ≤ (b-a)/(2√a) for 0 < a ≤ b (the telescoping estimate behind ∑ 1/√k ~ 2√n). Promoted and generalised from Mathlib2.an2_sum_inv_sqrt_bounds_aux1 (the case b = a + 1; used in bld_sum_inv_sqrt_div_sqrt_tendsto). -/
theorem lib_real_sqrt_sub_sqrt_bounds (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) : (b - a) / (2 * Real.sqrt b) ≤ Real.sqrt b - Real.sqrt a ∧ Real.sqrt b - Real.sqrt a ≤ (b - a) / (2 * Real.sqrt a) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hle : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt hab
  have ea : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
  have eb : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
  constructor
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.2 hle) (sub_nonneg.2 hle)]
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.2 hle) (sub_nonneg.2 hle)]
end

-- forge:entry lib_sylow_card_eq_pow_and_index_eq kind=proved origin=conjecture
section
/- Order and index of a Sylow p-subgroup: if |G| = p^n * m with p ∤ m then |P| = p^n and [G : P] = m. Promoted and generalised from Mathlib2.bld3_card_sylow_of_card_prime_mul_prime_aux1 (the case |G| = r*s; same computation inline in alg_isCyclic_of_card_eq_prime_mul_prime, bld_center_eq_bot_of_card_prime_mul_prime). -/
theorem lib_sylow_card_eq_pow_and_index_eq (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (n m : ℕ) (hG : Nat.card G = p ^ n * m) (hm : ¬ p ∣ m) (P : Sylow p G) : Nat.card P = p ^ n ∧ (P : Subgroup G).index = m := by
  have hp : p.Prime := Fact.out
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  have hpos : 0 < Nat.card G := by rw [hG]; exact Nat.mul_pos (pow_pos hp.pos n) (Nat.pos_of_ne_zero hm0)
  haveI : Finite G := Nat.finite_of_card_ne_zero hpos.ne'
  have hc : Nat.card P = p ^ n := by
    rw [Sylow.card_eq_multiplicity, hG, Nat.factorization_mul (pow_ne_zero n hp.ne_zero) hm0]
    simp [hp.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hm]
  refine ⟨hc, ?_⟩
  have h2 := Subgroup.card_mul_index (P : Subgroup G)
  have h3 : Nat.card (P : Subgroup G) = p ^ n := hc
  rw [h3, hG] at h2
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos n) h2
end

-- forge:entry p5_thm1 kind=proved origin=paper
section
/- Theorem 1: phi^3+psi^3+sigma^3 >= 3n^3+3n^2+9n+1 for n >= 2. -/
theorem p5_thm1_aux1 (n x y z : ℕ) (hn : 2 ≤ n) (hy : n + 1 ≤ y) (hz : n + 1 ≤ z) (hxy : 2 * n ≤ x + y) (hxz : 2 * n ≤ x + z) : 3 * n ^ 3 + 3 * n ^ 2 + 9 * n + 1 ≤ x ^ 3 + y ^ 3 + z ^ 3 := by
  wlog hyz : y ≤ z generalizing y z
  · have h := this z y hz hy hxz hxy (by omega)
    calc 3 * n ^ 3 + 3 * n ^ 2 + 9 * n + 1 ≤ x ^ 3 + z ^ 3 + y ^ 3 := h
      _ = x ^ 3 + y ^ 3 + z ^ 3 := by ring
  have h1 : x ^ 3 + y ^ 3 + y ^ 3 ≤ x ^ 3 + y ^ 3 + z ^ 3 := by gcongr
  refine le_trans ?_ h1
  rcases le_or_gt (2 * n) y with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, y = 2 * (k + 2) + s := ⟨y - 2 * (k + 2), by omega⟩
    calc 3 * (k + 2) ^ 3 + 3 * (k + 2) ^ 2 + 9 * (k + 2) + 1 ≤ 3 * (k + 2) ^ 3 + 3 * (k + 2) ^ 2 + 9 * (k + 2) + 1 + (13 * k^3 + 24 * k^2 * s + 75 * k^2 + 12 * k * s^2 + 96 * k * s + 135 * k + 2 * s^3 + 24 * s^2 + 96 * s + 1 * x^3 + 73) := Nat.le_add_right _ _
      _ = x ^ 3 + (2 * (k + 2) + s) ^ 3 + (2 * (k + 2) + s) ^ 3 := by ring
  · obtain ⟨s, rfl⟩ : ∃ s, y = n + 1 + s := ⟨y - (n + 1), by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = s + 2 + k := ⟨n - (s + 2), by omega⟩
    obtain ⟨r, rfl⟩ : ∃ r, x = k + 1 + r := ⟨x - (k + 1), by omega⟩
    calc 3 * (s + 2 + k) ^ 3 + 3 * (s + 2 + k) ^ 2 + 9 * (s + 2 + k) + 1 ≤ 3 * (s + 2 + k) ^ 3 + 3 * (s + 2 + k) ^ 2 + 9 * (s + 2 + k) + 1 + (3 * k^2 * s + 3 * k^2 * r + 15 * k * s^2 + 30 * k * s + 3 * k * r^2 + 6 * k * r + 13 * s^3 + 51 * s^2 + 51 * s + 1 * r^3 + 3 * r^2 + 3 * r) := Nat.le_add_right _ _
      _ = (k + 1 + r) ^ 3 + (s + 2 + k + 1 + s) ^ 3 + (s + 2 + k + 1 + s) ^ 3 := by ring

theorem p5_thm1 (n : ℕ) (hn : 2 ≤ n) : 3 * n ^ 3 + 3 * n ^ 2 + 9 * n + 1 ≤ n.totient ^ 3 + p5_dedekind_psi n ^ 3 + ArithmeticFunction.sigma 1 n ^ 3 :=
  p5_thm1_aux1 n _ _ _ hn (Mathlib2.p5_psi_ge_succ n hn) (Mathlib2.p5_sigma_ge_succ n hn) (Mathlib2.p5_lemma1 n hn) (Mathlib2.p5_lemma2 n hn)
end

-- forge:entry lib_fib_add_modEq_mul_fib_succ kind=proved origin=conjecture
section
/- Fibonacci shift congruence: if N ∣ F_m then F_(i+m) ≡ F_i * F_(m+1) (mod N), i.e. shifting by a zero of the sequence mod N multiplies by F_(m+1). Promoted and generalised from Mathlib2.p3_cor1_aux3 (the case N = F_(n+1); re-derived in p3_cor1_aux4, p3_aux_period_aux4, bld2_pisano_fib_dvd_four_mul). -/
theorem lib_fib_add_modEq_mul_fib_succ (N m i : ℕ) (h : N ∣ Nat.fib m) : Nat.fib (i + m) ≡ Nat.fib i * Nat.fib (m + 1) [MOD N] := by
  cases i with
  | zero => simp [Nat.ModEq, Nat.mod_eq_zero_of_dvd h]
  | succ j =>
    have e : j + 1 + m = m + j + 1 := by omega
    rw [e, Nat.fib_add]
    have h0 : Nat.fib m * Nat.fib j ≡ 0 [MOD N] :=
      (Nat.modEq_zero_iff_dvd.2 (Dvd.dvd.mul_right h _))
    have := h0.add_right (Nat.fib (m + 1) * Nat.fib (j + 1))
    rw [zero_add] at this
    rw [mul_comm (Nat.fib (j + 1)) (Nat.fib (m + 1))]
    exact this
end

-- forge:entry p5_thm2 kind=proved origin=paper
section
/- Theorem 2: phi^4+psi^4+sigma^4 >= 3n^4+4n^3+18n^2+4n+3 for n >= 2. -/
theorem p5_thm2_aux1 (n x y z : ℕ) (hn : 2 ≤ n) (hy : n + 1 ≤ y) (hz : n + 1 ≤ z) (hxy : 2 * n ≤ x + y) (hxz : 2 * n ≤ x + z) : 3 * n ^ 4 + 4 * n ^ 3 + 18 * n ^ 2 + 4 * n + 3 ≤ x ^ 4 + y ^ 4 + z ^ 4 := by
  wlog hyz : y ≤ z generalizing y z
  · have h := this z y hz hy hxz hxy (by omega)
    calc 3 * n ^ 4 + 4 * n ^ 3 + 18 * n ^ 2 + 4 * n + 3 ≤ x ^ 4 + z ^ 4 + y ^ 4 := h
      _ = x ^ 4 + y ^ 4 + z ^ 4 := by ring
  have h1 : x ^ 4 + y ^ 4 + y ^ 4 ≤ x ^ 4 + y ^ 4 + z ^ 4 := by gcongr
  refine le_trans ?_ h1
  rcases le_or_gt (2 * n) y with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, y = 2 * (k + 2) + s := ⟨y - 2 * (k + 2), by omega⟩
    calc 3 * (k + 2) ^ 4 + 4 * (k + 2) ^ 3 + 18 * (k + 2) ^ 2 + 4 * (k + 2) + 3 ≤ 3 * (k + 2) ^ 4 + 4 * (k + 2) ^ 3 + 18 * (k + 2) ^ 2 + 4 * (k + 2) + 3 + (29 * k^4 + 64 * k^3 * s + 228 * k^3 + 48 * k^2 * s^2 + 384 * k^2 * s + 654 * k^2 + 16 * k * s^3 + 192 * k * s^2 + 768 * k * s + 804 * k + 2 * s^4 + 32 * s^3 + 192 * s^2 + 512 * s + 1 * x^4 + 349) := Nat.le_add_right _ _
      _ = x ^ 4 + (2 * (k + 2) + s) ^ 4 + (2 * (k + 2) + s) ^ 4 := by ring
  · obtain ⟨s, rfl⟩ : ∃ s, y = n + 1 + s := ⟨y - (n + 1), by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = s + 2 + k := ⟨n - (s + 2), by omega⟩
    obtain ⟨r, rfl⟩ : ∃ r, x = k + 1 + r := ⟨x - (k + 1), by omega⟩
    calc 3 * (s + 2 + k) ^ 4 + 4 * (s + 2 + k) ^ 3 + 18 * (s + 2 + k) ^ 2 + 4 * (s + 2 + k) + 3 ≤ 3 * (s + 2 + k) ^ 4 + 4 * (s + 2 + k) ^ 3 + 18 * (s + 2 + k) ^ 2 + 4 * (s + 2 + k) + 3 + (4 * k^3 * s + 4 * k^3 * r + 30 * k^2 * s^2 + 60 * k^2 * s + 6 * k^2 * r^2 + 12 * k^2 * r + 52 * k * s^3 + 204 * k * s^2 + 204 * k * s + 4 * k * r^3 + 12 * k * r^2 + 12 * k * r + 29 * s^4 + 164 * s^3 + 318 * s^2 + 212 * s + 1 * r^4 + 4 * r^3 + 6 * r^2 + 4 * r) := Nat.le_add_right _ _
      _ = (k + 1 + r) ^ 4 + (s + 2 + k + 1 + s) ^ 4 + (s + 2 + k + 1 + s) ^ 4 := by ring

theorem p5_thm2 (n : ℕ) (hn : 2 ≤ n) : 3 * n ^ 4 + 4 * n ^ 3 + 18 * n ^ 2 + 4 * n + 3 ≤ n.totient ^ 4 + p5_dedekind_psi n ^ 4 + ArithmeticFunction.sigma 1 n ^ 4 :=
  p5_thm2_aux1 n _ _ _ hn (Mathlib2.p5_psi_ge_succ n hn) (Mathlib2.p5_sigma_ge_succ n hn) (Mathlib2.p5_lemma1 n hn) (Mathlib2.p5_lemma2 n hn)
end

-- forge:entry bld4_pell_five_one_iff kind=proved origin=conjecture
section
/- Uses Mathlib2.bld3_pell_five_one_solutions and Mathlib2.bld2_lucas_sq_sub_five_fib_sq: the forward direction is exactly bld3_pell_five_one_solutions. Conversely bld2_lucas_sq_sub_five_fib_sq at index 6n gives L^2 − 5F^2 = 4 over ℤ; substituting L = 2x, F = 2y and cancelling 4 gives x^2 = 5y^2 + 1. -/
theorem bld4_pell_five_one_iff (x y : ℕ) : x ^ 2 = 5 * y ^ 2 + 1 ↔ ∃ n : ℕ, 2 * y = Nat.fib (6 * n) ∧ 2 * x = p3_lucas (6 * n) := by
  constructor
  · exact bld3_pell_five_one_solutions x y
  · rintro ⟨n, hy, hx⟩
    have h := bld2_lucas_sq_sub_five_fib_sq (6 * n)
    rw [← hy, ← hx] at h
    have he : ((-1 : ℤ)) ^ (6 * n) = 1 := by
      rw [pow_mul]; norm_num
    rw [he] at h
    push_cast at h
    have : (x : ℤ) ^ 2 = 5 * (y : ℤ) ^ 2 + 1 := by linarith
    exact_mod_cast this
end

-- forge:entry bld4_tripotent_trace_eq_rank_sub_rank kind=proved origin=conjecture
section
/- Uses Mathlib2.gen_lin_idempotent_trace_eq_rank_field and Mathlib2.lib_matrix_rank_smul: P = (1/2)(A^2 + A) and Q = (1/2)(A^2 − A) are idempotent when A^3 = A, and A = P − Q. So tr A = tr P − tr Q = rank P − rank Q by gen_lin_idempotent_trace_eq_rank_field, and lib_matrix_rank_smul removes the scalar 1/2 from the ranks. -/
theorem bld4_tripotent_trace_eq_rank_sub_rank (K : Type*) [Field K] [CharZero K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (hA : A * A * A = A) : A.trace = ((A * A + A).rank : K) - ((A * A - A).rank : K) := by
  have h4 : A * A * (A * A) = A * A := by rw [← mul_assoc, hA]
  have h3 : A * (A * A) = A := by rw [← mul_assoc, hA]
  have h2 : (1 / 2 : K) ≠ 0 := by norm_num
  have eP : (A * A + A) * (A * A + A) = (2 : K) • (A * A + A) := by
    rw [mul_add, add_mul, add_mul, h4, hA, h3, two_smul]; abel
  have eQ : (A * A - A) * (A * A - A) = (2 : K) • (A * A - A) := by
    rw [mul_sub, sub_mul, sub_mul, h4, hA, h3, two_smul]; abel
  have hP : ((1 / 2 : K) • (A * A + A)) * ((1 / 2 : K) • (A * A + A)) = (1 / 2 : K) • (A * A + A) := by
    rw [smul_mul_smul_comm, eP, smul_smul]; norm_num
  have hQ : ((1 / 2 : K) • (A * A - A)) * ((1 / 2 : K) • (A * A - A)) = (1 / 2 : K) • (A * A - A) := by
    rw [smul_mul_smul_comm, eQ, smul_smul]; norm_num
  have tP := gen_lin_idempotent_trace_eq_rank_field K ι _ hP
  have tQ := gen_lin_idempotent_trace_eq_rank_field K ι _ hQ
  rw [lib_matrix_rank_smul K ι ι _ h2] at tP tQ
  have hAeq : A = (1 / 2 : K) • (A * A + A) - (1 / 2 : K) • (A * A - A) := by
    rw [← smul_sub, add_sub_sub_cancel, ← two_smul K, smul_smul]; norm_num
  rw [← tP, ← tQ, ← Matrix.trace_sub, ← hAeq]
end

-- forge:entry p5_thm3 kind=proved origin=paper
section
/- Theorem 3: phi^2 psi^2 + phi^2 sigma^2 + sigma^2 psi^2 >= 3n^4+4n^3+2n^2+4n+3 for n >= 2. -/
theorem p5_thm3_aux1 (n x y z : ℕ) (hn : 2 ≤ n) (hy : n + 1 ≤ y) (hz : n + 1 ≤ z) (hxy : 2 * n ≤ x + y) (hxz : 2 * n ≤ x + z) : 3 * n ^ 4 + 4 * n ^ 3 + 2 * n ^ 2 + 4 * n + 3 ≤ x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + z ^ 2 * y ^ 2 := by
  wlog hyz : y ≤ z generalizing y z
  · have h := this z y hz hy hxz hxy (by omega)
    calc 3 * n ^ 4 + 4 * n ^ 3 + 2 * n ^ 2 + 4 * n + 3 ≤ x ^ 2 * z ^ 2 + x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 := h
      _ = x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + z ^ 2 * y ^ 2 := by ring
  have h1 : x ^ 2 * y ^ 2 + x ^ 2 * y ^ 2 + y ^ 2 * y ^ 2 ≤ x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + z ^ 2 * y ^ 2 := by gcongr
  refine le_trans ?_ h1
  rcases le_or_gt (2 * n) y with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, y = 2 * (k + 2) + s := ⟨y - 2 * (k + 2), by omega⟩
    calc 3 * (k + 2) ^ 4 + 4 * (k + 2) ^ 3 + 2 * (k + 2) ^ 2 + 4 * (k + 2) + 3 ≤ 3 * (k + 2) ^ 4 + 4 * (k + 2) ^ 3 + 2 * (k + 2) ^ 2 + 4 * (k + 2) + 3 + (13 * k^4 + 32 * k^3 * s + 100 * k^3 + 24 * k^2 * s^2 + 192 * k^2 * s + 8 * k^2 * x^2 + 286 * k^2 + 8 * k * s^3 + 96 * k * s^2 + 8 * k * s * x^2 + 384 * k * s + 32 * k * x^2 + 356 * k + 1 * s^4 + 16 * s^3 + 2 * s^2 * x^2 + 96 * s^2 + 16 * s * x^2 + 256 * s + 32 * x^2 + 157) := Nat.le_add_right _ _
      _ = x ^ 2 * (2 * (k + 2) + s) ^ 2 + x ^ 2 * (2 * (k + 2) + s) ^ 2 + (2 * (k + 2) + s) ^ 2 * (2 * (k + 2) + s) ^ 2 := by ring
  · obtain ⟨s, rfl⟩ : ∃ s, y = n + 1 + s := ⟨y - (n + 1), by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = s + 2 + k := ⟨n - (s + 2), by omega⟩
    obtain ⟨r, rfl⟩ : ∃ r, x = k + 1 + r := ⟨x - (k + 1), by omega⟩
    calc 3 * (s + 2 + k) ^ 4 + 4 * (s + 2 + k) ^ 3 + 2 * (s + 2 + k) ^ 2 + 4 * (s + 2 + k) + 3 ≤ 3 * (s + 2 + k) ^ 4 + 4 * (s + 2 + k) ^ 3 + 2 * (s + 2 + k) ^ 2 + 4 * (s + 2 + k) + 3 + (4 * k^3 * s + 4 * k^3 * r + 14 * k^2 * s^2 + 16 * k^2 * s * r + 28 * k^2 * s + 2 * k^2 * r^2 + 28 * k^2 * r + 20 * k * s^3 + 16 * k * s^2 * r + 76 * k * s^2 + 8 * k * s * r^2 + 64 * k * s * r + 76 * k * s + 12 * k * r^2 + 60 * k * r + 13 * s^4 + 68 * s^3 + 8 * s^2 * r^2 + 16 * s^2 * r + 126 * s^2 + 24 * s * r^2 + 48 * s * r + 84 * s + 18 * r^2 + 36 * r) := Nat.le_add_right _ _
      _ = (k + 1 + r) ^ 2 * (s + 2 + k + 1 + s) ^ 2 + (k + 1 + r) ^ 2 * (s + 2 + k + 1 + s) ^ 2 + (s + 2 + k + 1 + s) ^ 2 * (s + 2 + k + 1 + s) ^ 2 := by ring

theorem p5_thm3 (n : ℕ) (hn : 2 ≤ n) : 3 * n ^ 4 + 4 * n ^ 3 + 2 * n ^ 2 + 4 * n + 3 ≤ n.totient ^ 2 * p5_dedekind_psi n ^ 2 + n.totient ^ 2 * ArithmeticFunction.sigma 1 n ^ 2 + ArithmeticFunction.sigma 1 n ^ 2 * p5_dedekind_psi n ^ 2 :=
  p5_thm3_aux1 n _ _ _ hn (Mathlib2.p5_psi_ge_succ n hn) (Mathlib2.p5_sigma_ge_succ n hn) (Mathlib2.p5_lemma1 n hn) (Mathlib2.p5_lemma2 n hn)
end

-- forge:entry bld4_pisano_mul_of_coprime kind=proved origin=conjecture
section
/- Uses Mathlib2.bld3_pisano_dvd_pisano_of_dvd, Mathlib2.bld3_pisano_pos_and_period and Mathlib2.bld3_pisano_dvd_of_period: pisano_dvd_pisano_of_dvd (m ∣ mn, n ∣ mn) gives lcm ∣ π(mn). Conversely pos_and_period makes L = lcm(π m, π n) a period mod m and mod n (iterate the period), hence mod mn by Nat.modEq_and_modEq_iff_modEq_mul for coprime m n, and dvd_of_period gives π(mn) ∣ L. Case m = 0 forces n = 1 (both sides 0). -/
theorem bld4_pisano_mul_of_coprime_aux1 : p3_pisano 0 = 0 := by
  unfold p3_pisano
  rw [Nat.sInf_eq_zero]
  right
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hk hper
  have h2 := hper 2
  rw [Nat.modEq_zero_iff] at h2
  have h3 := Nat.fib_add_two_strictMono hk
  simp only [zero_add] at h3
  rw [add_comm] at h2
  omega

theorem bld4_pisano_mul_of_coprime (m n : ℕ) (h : Nat.Coprime m n) : p3_pisano (m * n) = Nat.lcm (p3_pisano m) (p3_pisano n) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [bld4_pisano_mul_of_coprime_aux1]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [bld4_pisano_mul_of_coprime_aux1]
  have hL : 0 < Nat.lcm (p3_pisano m) (p3_pisano n) :=
    Nat.lcm_pos (bld3_pisano_pos_and_period m hm).1 (bld3_pisano_pos_and_period n hn).1
  apply Nat.dvd_antisymm
  · apply bld3_pisano_dvd_of_period
    intro i
    exact (Nat.modEq_and_modEq_iff_modEq_mul h).mp
      ⟨(lib_pisano_dvd_iff_period m _ hL).mp (Nat.dvd_lcm_left _ _) i,
       (lib_pisano_dvd_iff_period n _ hL).mp (Nat.dvd_lcm_right _ _) i⟩
  · exact Nat.lcm_dvd (bld3_pisano_dvd_pisano_of_dvd _ _ (dvd_mul_right m n))
      (bld3_pisano_dvd_pisano_of_dvd _ _ (dvd_mul_left n m))
end

-- forge:entry bld4_pell_five_neg_four_y_sum_two_squares kind=proved origin=conjecture
section
/- Uses Mathlib2.bld3_pell_five_neg_four_solutions_lucas: the classification gives y = F_{2n+1}, and Nat.fib_two_mul_add_one gives F_{2n+1} = F_{n+1}^2 + F_n^2, so a = F_{n+1}, b = F_n. -/
theorem bld4_pell_five_neg_four_y_sum_two_squares (x y : ℕ) (h : x ^ 2 + 4 = 5 * y ^ 2) : ∃ a b : ℕ, y = a ^ 2 + b ^ 2 := by
  obtain ⟨n, hy, -⟩ := bld3_pell_five_neg_four_solutions_lucas x y h
  exact ⟨Nat.fib (n + 1), Nat.fib n, by rw [hy, Nat.fib_two_mul_add_one]⟩
end

-- forge:entry p5_thm4 kind=proved origin=paper
section
/- Theorem 4: phi^2(psi+sigma)+psi^2(phi+sigma)+sigma^2(phi+psi) >= 6n^3+6n^2+2n+2 for n >= 2. -/
theorem p5_thm4_aux1 (n x y z : ℕ) (hn : 2 ≤ n) (hy : n + 1 ≤ y) (hz : n + 1 ≤ z) (hxy : 2 * n ≤ x + y) (hxz : 2 * n ≤ x + z) : 6 * n ^ 3 + 6 * n ^ 2 + 2 * n + 2 ≤ x ^ 2 * (y + z) + y ^ 2 * (x + z) + z ^ 2 * (x + y) := by
  wlog hyz : y ≤ z generalizing y z
  · have h := this z y hz hy hxz hxy (by omega)
    calc 6 * n ^ 3 + 6 * n ^ 2 + 2 * n + 2 ≤ x ^ 2 * (z + y) + z ^ 2 * (x + y) + y ^ 2 * (x + z) := h
      _ = x ^ 2 * (y + z) + y ^ 2 * (x + z) + z ^ 2 * (x + y) := by ring
  have h1 : x ^ 2 * (y + y) + y ^ 2 * (x + y) + y ^ 2 * (x + y) ≤ x ^ 2 * (y + z) + y ^ 2 * (x + z) + z ^ 2 * (x + y) := by gcongr
  refine le_trans ?_ h1
  rcases le_or_gt (2 * n) y with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, y = 2 * (k + 2) + s := ⟨y - 2 * (k + 2), by omega⟩
    calc 6 * (k + 2) ^ 3 + 6 * (k + 2) ^ 2 + 2 * (k + 2) + 2 ≤ 6 * (k + 2) ^ 3 + 6 * (k + 2) ^ 2 + 2 * (k + 2) + 2 + (10 * k^3 + 24 * k^2 * s + 8 * k^2 * x + 54 * k^2 + 12 * k * s^2 + 8 * k * s * x + 96 * k * s + 4 * k * x^2 + 32 * k * x + 94 * k + 2 * s^3 + 2 * s^2 * x + 24 * s^2 + 2 * s * x^2 + 16 * s * x + 96 * s + 8 * x^2 + 32 * x + 50) := Nat.le_add_right _ _
      _ = x ^ 2 * ((2 * (k + 2) + s) + (2 * (k + 2) + s)) + (2 * (k + 2) + s) ^ 2 * (x + (2 * (k + 2) + s)) + (2 * (k + 2) + s) ^ 2 * (x + (2 * (k + 2) + s)) := by ring
  · obtain ⟨s, rfl⟩ : ∃ s, y = n + 1 + s := ⟨y - (n + 1), by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = s + 2 + k := ⟨n - (s + 2), by omega⟩
    obtain ⟨r, rfl⟩ : ∃ r, x = k + 1 + r := ⟨x - (k + 1), by omega⟩
    calc 6 * (s + 2 + k) ^ 3 + 6 * (s + 2 + k) ^ 2 + 2 * (s + 2 + k) + 2 ≤ 6 * (s + 2 + k) ^ 3 + 6 * (s + 2 + k) ^ 2 + 2 * (s + 2 + k) + 2 + (6 * k^2 * s + 6 * k^2 * r + 14 * k * s^2 + 16 * k * s * r + 28 * k * s + 2 * k * r^2 + 28 * k * r + 10 * s^3 + 8 * s^2 * r + 38 * s^2 + 4 * s * r^2 + 32 * s * r + 38 * s + 6 * r^2 + 30 * r) := Nat.le_add_right _ _
      _ = (k + 1 + r) ^ 2 * ((s + 2 + k + 1 + s) + (s + 2 + k + 1 + s)) + (s + 2 + k + 1 + s) ^ 2 * ((k + 1 + r) + (s + 2 + k + 1 + s)) + (s + 2 + k + 1 + s) ^ 2 * ((k + 1 + r) + (s + 2 + k + 1 + s)) := by ring

theorem p5_thm4 (n : ℕ) (hn : 2 ≤ n) : 6 * n ^ 3 + 6 * n ^ 2 + 2 * n + 2 ≤ n.totient ^ 2 * (p5_dedekind_psi n + ArithmeticFunction.sigma 1 n) + p5_dedekind_psi n ^ 2 * (n.totient + ArithmeticFunction.sigma 1 n) + ArithmeticFunction.sigma 1 n ^ 2 * (n.totient + p5_dedekind_psi n) :=
  p5_thm4_aux1 n _ _ _ hn (Mathlib2.p5_psi_ge_succ n hn) (Mathlib2.p5_sigma_ge_succ n hn) (Mathlib2.p5_lemma1 n hn) (Mathlib2.p5_lemma2 n hn)
end

-- forge:entry bld4_tripotent_trace_eq_rank_idempotent kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_tripotent_rank_split, Mathlib2.gen_lin_idempotent_trace_eq_rank_field, Mathlib2.lib_matrix_rank_smul and Mathlib2.lib_matrix_rank_eq_zero_iff: as for the trace formula, tr A = rank(A^2 + A) − rank(A^2 − A) (idempotents (A^2 ± A)/2, trace = rank, rank_smul), while bld2_tripotent_rank_split gives rank A = rank(A^2 + A) + rank(A^2 − A). The hypothesis then forces 2·rank(A^2 − A) = 0 in K, so rank(A^2 − A) = 0 by CharZero and A^2 − A = 0 by lib_matrix_rank_eq_zero_iff. -/
theorem bld4_tripotent_trace_eq_rank_idempotent (K : Type*) [Field K] [CharZero K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (hA : A * A * A = A) (ht : A.trace = (A.rank : K)) : A * A = A := by
  have h1 := bld4_tripotent_trace_eq_rank_sub_rank K ι A hA
  have h2 := bld2_tripotent_rank_split K ι A hA
  rw [ht, h2] at h1
  push_cast at h1
  have h3 : (((A * A - A).rank : ℕ) : K) = 0 := by linear_combination (1 / 2 : K) * h1
  have h4 : (A * A - A).rank = 0 := by exact_mod_cast h3
  exact sub_eq_zero.mp ((lib_matrix_rank_eq_zero_iff K ι ι _).mp h4)
end

-- forge:entry bld4_pell_five_neg_four_prime_mul_y_not_rat_sum_sq kind=proved origin=conjecture
section
/- Uses Mathlib2.bld3_pell_five_neg_four_solutions_lucas, Mathlib2.nt2_fib_odd_index_no_prime_factor_three_mod_four and Mathlib2.bld2_rat_sq_add_sq_ne_prime_mul_coprime: the Pell classification gives y = F_{2n+1}; nt2_fib_odd_index_no_prime_factor_three_mod_four gives ¬ p ∣ y; then bld2_rat_sq_add_sq_ne_prime_mul_coprime with m = y is the claim. -/
theorem bld4_pell_five_neg_four_prime_mul_y_not_rat_sum_sq (x y p : ℕ) (h : x ^ 2 + 4 = 5 * y ^ 2) (hp : p.Prime) (hp3 : p % 4 = 3) (u v : ℚ) : u ^ 2 + v ^ 2 ≠ (p : ℚ) * (y : ℚ) := by
  obtain ⟨n, hy, -⟩ := bld3_pell_five_neg_four_solutions_lucas x y h
  refine bld2_rat_sq_add_sq_ne_prime_mul_coprime p y hp hp3 ?_ u v
  rw [hy]
  exact nt2_fib_odd_index_no_prime_factor_three_mod_four n p hp hp3
end

-- forge:entry p5_thm5 kind=proved origin=paper
section
/- Theorem 5: phi^3(psi+sigma)+psi^3(phi+sigma)+sigma^3(phi+psi) >= 6n^4+8n^3+12n^2+8n-2 for n >= 2 (the -2 moved to the other side to avoid natural subtraction). -/
theorem p5_thm5_aux1 (n x y z : ℕ) (hn : 2 ≤ n) (hy : n + 1 ≤ y) (hz : n + 1 ≤ z) (hxy : 2 * n ≤ x + y) (hxz : 2 * n ≤ x + z) : 6 * n ^ 4 + 8 * n ^ 3 + 12 * n ^ 2 + 8 * n ≤ x ^ 3 * (y + z) + y ^ 3 * (x + z) + z ^ 3 * (x + y) + 2 := by
  wlog hyz : y ≤ z generalizing y z
  · have h := this z y hz hy hxz hxy (by omega)
    calc 6 * n ^ 4 + 8 * n ^ 3 + 12 * n ^ 2 + 8 * n ≤ x ^ 3 * (z + y) + z ^ 3 * (x + y) + y ^ 3 * (x + z) + 2 := h
      _ = x ^ 3 * (y + z) + y ^ 3 * (x + z) + z ^ 3 * (x + y) + 2 := by ring
  have h1 : x ^ 3 * (y + y) + y ^ 3 * (x + y) + y ^ 3 * (x + y) + 2 ≤ x ^ 3 * (y + z) + y ^ 3 * (x + z) + z ^ 3 * (x + y) + 2 := by gcongr
  refine le_trans ?_ h1
  rcases le_or_gt (2 * n) y with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, y = 2 * (k + 2) + s := ⟨y - 2 * (k + 2), by omega⟩
    calc 6 * (k + 2) ^ 4 + 8 * (k + 2) ^ 3 + 12 * (k + 2) ^ 2 + 8 * (k + 2) ≤ 6 * (k + 2) ^ 4 + 8 * (k + 2) ^ 3 + 12 * (k + 2) ^ 2 + 8 * (k + 2) + (26 * k^4 + 64 * k^3 * s + 16 * k^3 * x + 200 * k^3 + 48 * k^2 * s^2 + 24 * k^2 * s * x + 384 * k^2 * s + 96 * k^2 * x + 564 * k^2 + 16 * k * s^3 + 12 * k * s^2 * x + 192 * k * s^2 + 96 * k * s * x + 768 * k * s + 4 * k * x^3 + 192 * k * x + 680 * k + 2 * s^4 + 2 * s^3 * x + 32 * s^3 + 24 * s^2 * x + 192 * s^2 + 2 * s * x^3 + 96 * s * x + 512 * s + 8 * x^3 + 128 * x + 290) := Nat.le_add_right _ _
      _ = x ^ 3 * ((2 * (k + 2) + s) + (2 * (k + 2) + s)) + (2 * (k + 2) + s) ^ 3 * (x + (2 * (k + 2) + s)) + (2 * (k + 2) + s) ^ 3 * (x + (2 * (k + 2) + s)) + 2 := by ring
  · obtain ⟨s, rfl⟩ : ∃ s, y = n + 1 + s := ⟨y - (n + 1), by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = s + 2 + k := ⟨n - (s + 2), by omega⟩
    obtain ⟨r, rfl⟩ : ∃ r, x = k + 1 + r := ⟨x - (k + 1), by omega⟩
    calc 6 * (s + 2 + k) ^ 4 + 8 * (s + 2 + k) ^ 3 + 12 * (s + 2 + k) ^ 2 + 8 * (s + 2 + k) ≤ 6 * (s + 2 + k) ^ 4 + 8 * (s + 2 + k) ^ 3 + 12 * (s + 2 + k) ^ 2 + 8 * (s + 2 + k) + (8 * k^3 * s + 8 * k^3 * r + 36 * k^2 * s^2 + 24 * k^2 * s * r + 72 * k^2 * s + 6 * k^2 * r^2 + 48 * k^2 * r + 56 * k * s^3 + 24 * k * s^2 * r + 216 * k * s^2 + 12 * k * s * r^2 + 96 * k * s * r + 216 * k * s + 2 * k * r^3 + 24 * k * r^2 + 96 * k * r + 26 * s^4 + 16 * s^3 * r + 152 * s^3 + 72 * s^2 * r + 300 * s^2 + 4 * s * r^3 + 12 * s * r^2 + 120 * s * r + 200 * s + 6 * r^3 + 18 * r^2 + 72 * r) := Nat.le_add_right _ _
      _ = (k + 1 + r) ^ 3 * ((s + 2 + k + 1 + s) + (s + 2 + k + 1 + s)) + (s + 2 + k + 1 + s) ^ 3 * ((k + 1 + r) + (s + 2 + k + 1 + s)) + (s + 2 + k + 1 + s) ^ 3 * ((k + 1 + r) + (s + 2 + k + 1 + s)) + 2 := by ring

theorem p5_thm5 (n : ℕ) (hn : 2 ≤ n) : 6 * n ^ 4 + 8 * n ^ 3 + 12 * n ^ 2 + 8 * n ≤ n.totient ^ 3 * (p5_dedekind_psi n + ArithmeticFunction.sigma 1 n) + p5_dedekind_psi n ^ 3 * (n.totient + ArithmeticFunction.sigma 1 n) + ArithmeticFunction.sigma 1 n ^ 3 * (n.totient + p5_dedekind_psi n) + 2 :=
  p5_thm5_aux1 n _ _ _ hn (Mathlib2.p5_psi_ge_succ n hn) (Mathlib2.p5_sigma_ge_succ n hn) (Mathlib2.p5_lemma1 n hn) (Mathlib2.p5_lemma2 n hn)
end

-- forge:entry bld4_pisano_prime_dvd_pred_of_isSquare_five kind=proved origin=conjecture
section
/- Uses Mathlib2.p3_aux_fib_prime, Mathlib2.lib_fib_period_iff and Mathlib2.bld3_pisano_dvd_of_period: by Euler's criterion (ZMod.euler_criterion) 5^(p/2) = 1 in ZMod p, so p3_aux_fib_prime gives F_p ≡ 1 and 2F_{p+1} − F_p ≡ 1, hence F_{p+1} ≡ 1 and F_{p−1} = F_{p+1} − F_p ≡ 0 mod p. lib_fib_period_iff (with m = p − 1) turns this into p − 1 being a period, and bld3_pisano_dvd_of_period concludes. -/
theorem bld4_pisano_prime_dvd_pred_of_isSquare_five (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp5 : p ≠ 5) (h : IsSquare (5 : ZMod p)) : p3_pisano p ∣ p - 1 := by
  have hp : p.Prime := Fact.out
  have h5 : (5 : ZMod p) ≠ 0 := by
    intro h0
    have : ((5 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp this)
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp this)
  have he := (ZMod.euler_criterion p h5).mp h
  obtain ⟨hA, hB⟩ := p3_aux_fib_prime p hp hp2
  have hA' := (ZMod.intCast_eq_intCast_iff _ _ p).mpr hA
  have hB' := (ZMod.intCast_eq_intCast_iff _ _ p).mpr hB
  push_cast at hA' hB'
  rw [he] at hB'
  rw [hB'] at hA'
  have hb : ((Nat.fib (p + 1) : ℕ) : ZMod p) = 1 := by
    have : (2 : ZMod p) * ((Nat.fib (p + 1) : ℕ) : ZMod p) = 2 * 1 := by
      linear_combination hA'
    exact mul_left_cancel₀ h2 this
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
  have hrec : Nat.fib (p + 1) = Nat.fib (p - 1) + Nat.fib p := by
    have := Nat.fib_add_two (n := p - 1)
    rw [show p - 1 + 2 = p + 1 by omega, hp1] at this
    exact this
  have hc : ((Nat.fib (p - 1) : ℕ) : ZMod p) = 0 := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) hrec
    simp only [Nat.cast_add] at this
    rw [hb, hB'] at this
    linear_combination -this
  apply bld3_pisano_dvd_of_period
  rw [lib_fib_period_iff, hp1]
  refine ⟨?_, ?_⟩
  · rw [← ZMod.natCast_eq_natCast_iff]; simpa using hc
  · rw [← ZMod.natCast_eq_natCast_iff]; simpa using hB'
end

-- forge:entry bld4_nilpotent_corank_one_rank_pow kind=proved origin=conjecture
section
/- Uses Mathlib2.bld3_nilpotent_rank_pow_le and Mathlib2.lib_matrix_mul_rank_le_add_rank_pow: the upper bound rank A^k ≤ n − k is bld3_nilpotent_rank_pow_le. For the lower bound, lib_matrix_mul_rank_le_add_rank_pow gives k(n − 1) ≤ (k − 1)n + rank A^k, i.e. rank A^k ≥ n − k (k = 0 separately: rank 1 = n). This is the single-Jordan-block case. -/
theorem bld4_nilpotent_corank_one_rank_pow (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (hA : IsNilpotent A) (hr : A.rank + 1 = Fintype.card ι) (k : ℕ) (hk : k ≤ Fintype.card ι) : (A ^ k).rank = Fintype.card ι - k := by
  have hu := bld3_nilpotent_rank_pow_le K ι A hA k
  have hl := lib_matrix_mul_rank_le_add_rank_pow K ι A k
  rcases k with _ | m
  · simp [Matrix.rank_one]
  · rw [← hr] at hl hu hk ⊢
    simp only [Nat.add_sub_cancel] at hl
    have e1 : (m + 1) * A.rank = m * A.rank + A.rank := by ring
    have e2 : m * (A.rank + 1) = m * A.rank + m := by ring
    rw [e1, e2] at hl
    omega
end

end Mathlib2
