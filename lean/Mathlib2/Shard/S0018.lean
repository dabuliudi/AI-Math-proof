/- Mathlib2 分片 18（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0017
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry bld2_pell_five_solutions_lucas kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_fib_even_index_iff_five_sq_add_four and Mathlib2.an_cassini_int: the characterisation gives y = fib (2n); the Lucas identity L(2n)^2 = 5 fib(2n)^2 + 4 (from Cassini, with L = Mathlib2.p3_lucas) gives x^2 = L(2n)^2, hence x = L(2n) in ℕ. -/
theorem bld2_pell_five_solutions_lucas (x y : ℕ) (h : x ^ 2 = 5 * y ^ 2 + 4) : ∃ n : ℕ, y = Nat.fib (2 * n) ∧ x = p3_lucas (2 * n) := by
  obtain ⟨n, hn⟩ := (Mathlib2.bld_fib_even_index_iff_five_sq_add_four y).2 ⟨x, h⟩
  refine ⟨n, hn, ?_⟩
  have hL := Mathlib2.bld2_lucas_sq_sub_five_fib_sq (2 * n)
  have e : ((-1 : ℤ)) ^ (2 * n) = 1 := by
    rw [pow_mul]; norm_num
  rw [e, ← hn] at hL
  have h' : (x : ℤ) ^ 2 = 5 * (y : ℤ) ^ 2 + 4 := by exact_mod_cast h
  have h2 : (x : ℤ) ^ 2 = (p3_lucas (2 * n) : ℤ) ^ 2 := by linarith
  have h3 : x ^ 2 = p3_lucas (2 * n) ^ 2 := by exact_mod_cast h2
  exact Nat.pow_left_injective (by norm_num) h3
end

-- forge:entry bld2_pisano_fib_dvd_four_mul kind=proved origin=conjecture
section
/- Uses Mathlib2.p3_aux_period (and the argument of Mathlib2.p3_prop2): p3_aux_period with index 2n gives fib (i + 4n) ≡ fib i mod fib (2n), and fib n ∣ fib (2n), so 4n is a period modulo fib n; the least period divides every period (division with remainder), as in p3_prop2. -/
lemma bld2_pisano_fib_dvd_four_mul_aux1 (m N : ℕ) (hN : 0 < N) (hper : ∀ i : ℕ, Nat.fib (i + N) ≡ Nat.fib i [MOD m]) : p3_pisano m ∣ N := by
  have hS : (N : ℕ) ∈ {k : ℕ | 0 < k ∧ ∀ i : ℕ, Nat.fib (i + k) ≡ Nat.fib i [MOD m]} := ⟨hN, hper⟩
  have hP : p3_pisano m ∈ {k : ℕ | 0 < k ∧ ∀ i : ℕ, Nat.fib (i + k) ≡ Nat.fib i [MOD m]} := by
    unfold p3_pisano
    exact Nat.sInf_mem ⟨N, hS⟩
  obtain ⟨hP0, hPper⟩ := hP
  have hmul : ∀ q i : ℕ, Nat.fib (i + p3_pisano m * q) ≡ Nat.fib i [MOD m] := by
    intro q
    induction q with
    | zero => intro i; simp [Nat.ModEq.refl]
    | succ q ih =>
      intro i
      have e : i + p3_pisano m * (q + 1) = (i + p3_pisano m * q) + p3_pisano m := by ring
      rw [e]
      exact (hPper _).trans (ih i)
  rw [Nat.dvd_iff_mod_eq_zero]
  by_contra hr
  have hr0 : 0 < N % p3_pisano m := Nat.pos_of_ne_zero hr
  have hlt : N % p3_pisano m < p3_pisano m := Nat.mod_lt _ hP0
  have hrS : N % p3_pisano m ∈ {k : ℕ | 0 < k ∧ ∀ i : ℕ, Nat.fib (i + k) ≡ Nat.fib i [MOD m]} := by
    refine ⟨hr0, fun i => ?_⟩
    have h1 := hmul (N / p3_pisano m) (i + N % p3_pisano m)
    have e : i + N % p3_pisano m + p3_pisano m * (N / p3_pisano m) = i + N := by
      have := Nat.mod_add_div N (p3_pisano m)
      omega
    rw [e] at h1
    exact h1.symm.trans (hper i)
  have hle : p3_pisano m ≤ N % p3_pisano m := by
    conv_lhs => unfold p3_pisano
    exact Nat.sInf_le hrS
  omega

theorem bld2_pisano_fib_dvd_four_mul (n : ℕ) (hn : 0 < n) : p3_pisano (Nat.fib n) ∣ 4 * n := by
  apply bld2_pisano_fib_dvd_four_mul_aux1 _ _ (by omega)
  intro i
  have h := Mathlib2.p3_aux_period (2 * n) 1 i (dvd_mul_right 2 n)
  have e : i + 2 * (2 * n) * 1 = i + 4 * n := by ring
  rw [e] at h
  exact h.of_dvd (Nat.fib_dvd n (2 * n) (dvd_mul_left n 2))
end

-- forge:entry p4_z_spec kind=proved origin=paper
section
/- The Lean definition p4_z agrees with the paper's: z(n) is the largest integer with 3 z(n) < 2n. -/
theorem p4_z_spec (n : ℕ) : 3 * p4_z n < 2 * (n : ℤ) ∧ ∀ k : ℤ, 3 * k < 2 * (n : ℤ) → k ≤ p4_z n := by
  unfold p4_z
  constructor
  · omega
  · intro k hk
    omega
end

-- forge:entry p4_m_spec kind=proved origin=paper
section
/- The Lean definition p4_m agrees with the paper's: m(n) is the largest integer with m(n)^2 <= 2n. -/
theorem p4_m_spec (n : ℕ) : (p4_m n : ℤ) ^ 2 ≤ 2 * (n : ℤ) ∧ ∀ k : ℤ, k ^ 2 ≤ 2 * (n : ℤ) → k ≤ (p4_m n : ℤ) := by
  unfold p4_m
  have h := Nat.sqrt_le' (2 * n)
  have h' := Nat.lt_succ_sqrt' (2 * n)
  constructor
  · exact_mod_cast h
  · intro k hk
    by_contra hc
    push_neg at hc
    have h1 : ((Nat.sqrt (2 * n) : ℤ) + 1) ≤ k := by omega
    have h2 : ((Nat.sqrt (2 * n) : ℤ) + 1) ^ 2 ≤ k ^ 2 := by
      have h0 : (0 : ℤ) ≤ (Nat.sqrt (2 * n) : ℤ) := by positivity
      nlinarith
    have h3 : (2 * (n : ℤ)) < ((Nat.sqrt (2 * n) : ℤ) + 1) ^ 2 := by
      exact_mod_cast h'
    linarith
end

-- forge:entry p4_r_spec kind=proved origin=paper
section
/- The Lean definition p4_r agrees with the paper's: r(n) is the least non-negative integer with n <= 2^r(n). -/
theorem p4_r_spec (n : ℕ) : n ≤ 2 ^ p4_r n ∧ ∀ k : ℕ, n ≤ 2 ^ k → p4_r n ≤ k := by
  unfold p4_r
  exact ⟨Nat.le_pow_clog one_lt_two n, fun k hk => (Nat.clog_le_iff_le_pow one_lt_two).2 hk⟩
end

-- forge:entry p4_ex1_mono kind=proved origin=paper
section
/- The sequences z, m, r are non-decreasing. -/
theorem p4_ex1_mono (a b : ℕ) (h : a ≤ b) : p4_z a ≤ p4_z b ∧ p4_m a ≤ p4_m b ∧ p4_r a ≤ p4_r b := by
  refine ⟨?_, ?_, ?_⟩
  · unfold p4_z
    omega
  · unfold p4_m
    exact Nat.sqrt_le_sqrt (by omega)
  · unfold p4_r
    exact Nat.clog_mono_right 2 h
end

-- forge:entry p4_ex1_levels kind=proved origin=paper
section
/- Level sets: z(n)=k iff 3k < 2n <= 3k+3; m(n)=k iff k^2 <= 2n < (k+1)^2; for k>=1, r(n)=k iff 2^(k-1) < n <= 2^k. -/
theorem p4_ex1_levels (n k : ℕ) (hn : 0 < n) : (p4_z n = (k : ℤ) ↔ 3 * k < 2 * n ∧ 2 * n ≤ 3 * k + 3) ∧ (p4_m n = k ↔ k ^ 2 ≤ 2 * n ∧ 2 * n < (k + 1) ^ 2) ∧ (1 ≤ k → (p4_r n = k ↔ 2 ^ (k - 1) < n ∧ n ≤ 2 ^ k)) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold p4_z
    constructor
    · intro h
      omega
    · intro h
      omega
  · unfold p4_m
    rw [eq_comm, Nat.eq_sqrt']
  · intro hk
    unfold p4_r
    constructor
    · intro h
      subst h
      refine ⟨?_, Nat.le_pow_clog one_lt_two n⟩
      by_contra hc
      push_neg at hc
      have := (Nat.clog_le_iff_le_pow one_lt_two).2 hc
      omega
    · rintro ⟨h1, h2⟩
      apply le_antisymm
      · exact (Nat.clog_le_iff_le_pow one_lt_two).2 h2
      · by_contra hc
        push_neg at hc
        have h5 : Nat.clog 2 n ≤ k - 1 := by omega
        have h6 := (Nat.clog_le_iff_le_pow one_lt_two).1 h5
        omega
end

-- forge:entry p4_ex1_table kind=proved origin=paper
section
/- The table of values of x(n) in Exercise 1. -/
theorem p4_ex1_table : List.map p4_x [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 20, 50, 100, 200, 300, 400, 500, 1000] = [-1, -3, -5, -4, -9, -9, -8, -11, -15, -14, -13, -13, -17, -23, -37, -46, -47, -41, -14, 23, 182] := by
  simp only [List.map_cons, List.map_nil]
  rw [p4_x_block 1 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    p4_x_block 2 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    p4_x_block 3 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    p4_x_block 4 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    p4_x_block 5 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    p4_x_block 6 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    p4_x_block 7 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    p4_x_block 8 3 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    p4_x_block 9 4 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    p4_x_block 10 4 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    p4_x_block 11 4 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    p4_x_block 12 4 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    p4_x_block 13 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    p4_x_block 20 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    p4_x_block 50 6 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    p4_x_block 100 7 14 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    p4_x_block 200 8 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    p4_x_block 300 9 24 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    p4_x_block 400 9 28 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    p4_x_block 500 9 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    p4_x_block 1000 10 44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num
end

-- forge:entry p4_lem1_i kind=proved origin=paper
section
/- Lemma 1(i): for positive integers a <= n <= b, z(a)-(r(b)+1)m(b) <= x(n) <= z(b)-(r(a)+1)m(a). -/
theorem p4_lem1_i (a b n : ℕ) (ha : 0 < a) (h1 : a ≤ n) (h2 : n ≤ b) : p4_z a - ((p4_r b : ℤ) + 1) * (p4_m b : ℤ) ≤ p4_x n ∧ p4_x n ≤ p4_z b - ((p4_r a : ℤ) + 1) * (p4_m a : ℤ) := by
  obtain ⟨hz1, hm1, hr1⟩ := p4_ex1_mono a n h1
  obtain ⟨hz2, hm2, hr2⟩ := p4_ex1_mono n b h2
  have hr1' : (p4_r a : ℤ) ≤ p4_r n := by exact_mod_cast hr1
  have hm1' : (p4_m a : ℤ) ≤ p4_m n := by exact_mod_cast hm1
  have hr2' : (p4_r n : ℤ) ≤ p4_r b := by exact_mod_cast hr2
  have hm2' : (p4_m n : ℤ) ≤ p4_m b := by exact_mod_cast hm2
  have e1 := mul_le_mul (add_le_add_right hr1' 1) hm1' (by positivity) (by positivity)
  have e2 := mul_le_mul (add_le_add_right hr2' 1) hm2' (by positivity) (by positivity)
  unfold p4_x
  constructor <;> linarith
end

-- forge:entry bld2_pisano_fib_odd_eq kind=proved origin=conjecture
section
/- Uses Mathlib2.p3_aux_period and Mathlib2.an_cassini_int: 4n is a period (p3_aux_period at index 2n, fib n ∣ fib (2n)), so the period k divides 4n and n ∣ k, k ∈ {n, 2n, 4n}; k = n fails since fib (n+1) ≡ fib (n-1) ≢ 1; k = 2n fails since fib (2n+1) = fib(n)^2 + fib(n+1)^2 ≡ fib(n-1)^2 ≡ (-1)^n = -1 mod fib n by Cassini, and fib n > 2. -/
lemma bld2_pisano_fib_odd_eq_aux1 (m N : ℕ) (hN : 0 < N) (hper : ∀ i : ℕ, Nat.fib (i + N) ≡ Nat.fib i [MOD m]) :
    0 < p3_pisano m ∧ ∀ i : ℕ, Nat.fib (i + p3_pisano m) ≡ Nat.fib i [MOD m] := by
  have hS : (N : ℕ) ∈ {k : ℕ | 0 < k ∧ ∀ i : ℕ, Nat.fib (i + k) ≡ Nat.fib i [MOD m]} := ⟨hN, hper⟩
  have hP : p3_pisano m ∈ {k : ℕ | 0 < k ∧ ∀ i : ℕ, Nat.fib (i + k) ≡ Nat.fib i [MOD m]} := by
    unfold p3_pisano
    exact Nat.sInf_mem ⟨N, hS⟩
  exact hP

lemma bld2_pisano_fib_odd_eq_aux2 (n k : ℕ) (hn : 3 ≤ n) (hk : 0 < k)
    (h0 : Nat.fib (0 + k) ≡ Nat.fib 0 [MOD Nat.fib n]) : n ∣ k := by
  have hd : Nat.fib n ∣ Nat.fib k := by
    have := (Nat.modEq_zero_iff_dvd).mp (by simpa using h0)
    exact this
  have hg : Nat.fib (Nat.gcd n k) = Nat.fib n := by
    rw [Nat.fib_gcd]; exact Nat.gcd_eq_left hd
  have hgle : Nat.gcd n k ≤ n := Nat.gcd_le_left _ (by omega)
  have hgeq : Nat.gcd n k = n := by
    by_contra hne
    have hlt : Nat.gcd n k ≤ n - 1 := by omega
    have h1 : Nat.fib (Nat.gcd n k) ≤ Nat.fib (n - 1) := Nat.fib_mono hlt
    have h2 : Nat.fib (n - 1) < Nat.fib (n - 1 + 1) := Nat.fib_lt_fib_succ (by omega)
    have e : n - 1 + 1 = n := by omega
    rw [e] at h2
    omega
  exact hgeq ▸ Nat.gcd_dvd_right n k

theorem bld2_pisano_fib_odd_eq (n : ℕ) (h5 : 5 ≤ n) (hodd : Odd n) : p3_pisano (Nat.fib n) = 4 * n := by
  have hdvd := Mathlib2.bld2_pisano_fib_dvd_four_mul n (by omega)
  have h4per : ∀ i : ℕ, Nat.fib (i + 4 * n) ≡ Nat.fib i [MOD Nat.fib n] := by
    intro i
    have h := Mathlib2.p3_aux_period (2 * n) 1 i (dvd_mul_right 2 n)
    have e : i + 2 * (2 * n) * 1 = i + 4 * n := by ring
    rw [e] at h
    exact h.of_dvd (Nat.fib_dvd n (2 * n) (dvd_mul_left n 2))
  obtain ⟨hk0, hkper⟩ := bld2_pisano_fib_odd_eq_aux1 (Nat.fib n) (4 * n) (by omega) h4per
  have hnk := bld2_pisano_fib_odd_eq_aux2 n _ (by omega) hk0 (hkper 0)
  obtain ⟨c, hc⟩ := hnk
  have hc4 : c ∣ 4 := by
    rw [hc, mul_comm 4 n] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by omega) hdvd
  have hcle : c ≤ 4 := Nat.le_of_dvd (by norm_num) hc4
  have hF5 : 5 ≤ Nat.fib n := by
    have := Nat.fib_mono h5
    have e : Nat.fib 5 = 5 := by decide
    omega
  have h1 := hkper 1
  rw [hc] at h1 ⊢
  have h1z := (Nat.modEq_iff_dvd).mp h1
  interval_cases c
  · omega
  · -- period n
    exfalso
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have e : 1 + (m + 2) * 1 = (m + 1) + 2 := by ring
    rw [e] at h1z
    have hfib : Nat.fib (m + 1 + 2) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
    have hm1 : 3 ≤ Nat.fib (m + 1) := by
      have := Nat.fib_mono (show 4 ≤ m + 1 by omega)
      have e : Nat.fib 4 = 3 := by decide
      omega
    have hm2 : Nat.fib (m + 1) < Nat.fib (m + 2) := Nat.fib_lt_fib_succ (by omega)
    have hd : (Nat.fib (m + 2) : ℤ) ∣ (Nat.fib (m + 1) : ℤ) - 1 := by
      obtain ⟨t, ht⟩ := h1z
      refine ⟨-t - 1, ?_⟩
      push_cast [hfib] at ht
      simp only [Nat.fib_one, Nat.cast_one] at ht
      linear_combination -ht
    have := Int.le_of_dvd (by omega) hd
    omega
  · -- period 2n
    exfalso
    have e : 1 + n * 2 = 2 * n + 1 := by ring
    rw [e, Nat.fib_two_mul_add_one] at h1z
    have hcas := Mathlib2.an_cassini_int n
    have hpow : ((-1 : ℤ)) ^ (n + 1) = 1 := Even.neg_one_pow hodd.add_one
    rw [hpow] at hcas
    have hd : (Nat.fib n : ℤ) ∣ 2 := by
      obtain ⟨t, ht⟩ := h1z
      refine ⟨(Nat.fib (n + 2) : ℤ) + (Nat.fib n : ℤ) + t, ?_⟩
      push_cast at ht
      simp only [Nat.fib_one, Nat.cast_one] at ht
      linear_combination ht - hcas
    have := Int.le_of_dvd (by norm_num) hd
    omega
  · omega
  · ring
end

-- forge:entry p4_lem1_ii kind=proved origin=paper
section
/- Lemma 1(ii): if x(a) < 0 and b is the largest integer with 2b <= 3(r(a)+1)m(a), then x(n) < 0 for a <= n <= b. -/
theorem p4_lem1_ii (a b n : ℕ) (ha : 0 < a) (h1 : a ≤ n) (h2 : n ≤ b) (hx : p4_x a < 0) (hb : 2 * b ≤ 3 * (p4_r a + 1) * p4_m a) (hbmax : ∀ c : ℕ, 2 * c ≤ 3 * (p4_r a + 1) * p4_m a → c ≤ b) : p4_x n < 0 := by
  have h := (p4_lem1_i a b n ha h1 h2).2
  have hz := (p4_z_spec b).1
  have hb' : 2 * (b : ℤ) ≤ 3 * ((p4_r a : ℤ) + 1) * (p4_m a : ℤ) := by exact_mod_cast hb
  linarith
end

-- forge:entry bld2_pisano_fib_even_eq kind=proved origin=conjecture
section
/- Uses Mathlib2.p3_prop2: the period k divides 2n; being a period forces fib n ∣ fib k, hence n ∣ k (gcd property of Fibonacci numbers, n ≥ 3), so k = n or k = 2n; k = n is impossible because fib (n+1) ≡ fib (n-1) mod fib n and 1 < fib (n-1) < fib n for n ≥ 4. -/
theorem bld2_pisano_fib_even_eq (n : ℕ) (h4 : 4 ≤ n) (h2 : 2 ∣ n) : p3_pisano (Nat.fib n) = 2 * n := by
  have hdvd := Mathlib2.p3_prop2 n (by omega) h2
  have h2per : ∀ i : ℕ, Nat.fib (i + 2 * n) ≡ Nat.fib i [MOD Nat.fib n] := by
    intro i
    have h := Mathlib2.p3_aux_period n 1 i h2
    rwa [mul_one] at h
  obtain ⟨hk0, hkper⟩ := Mathlib2.bld2_pisano_fib_odd_eq_aux1 (Nat.fib n) (2 * n) (by omega) h2per
  have hnk := Mathlib2.bld2_pisano_fib_odd_eq_aux2 n _ (by omega) hk0 (hkper 0)
  obtain ⟨c, hc⟩ := hnk
  have hc4 : c ∣ 2 := by
    rw [hc, mul_comm 2 n] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by omega) hdvd
  have hcle : c ≤ 2 := Nat.le_of_dvd (by norm_num) hc4
  have h1 := hkper 1
  rw [hc] at h1 ⊢
  have h1z := (Nat.modEq_iff_dvd).mp h1
  interval_cases c
  · omega
  · exfalso
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have e : 1 + (m + 2) * 1 = (m + 1) + 2 := by ring
    rw [e] at h1z
    have hfib : Nat.fib (m + 1 + 2) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
    have hm1 : 2 ≤ Nat.fib (m + 1) := by
      have := Nat.fib_mono (show 3 ≤ m + 1 by omega)
      have e : Nat.fib 3 = 2 := by decide
      omega
    have hm2 : Nat.fib (m + 1) < Nat.fib (m + 2) := Nat.fib_lt_fib_succ (by omega)
    have hd : (Nat.fib (m + 2) : ℤ) ∣ (Nat.fib (m + 1) : ℤ) - 1 := by
      obtain ⟨t, ht⟩ := h1z
      refine ⟨-t - 1, ?_⟩
      push_cast [hfib] at ht
      simp only [Nat.fib_one, Nat.cast_one] at ht
      linear_combination -ht
    have := Int.le_of_dvd (by omega) hd
    omega
  · ring
end

-- forge:entry p4_lem1_iii kind=proved origin=paper
section
/- Lemma 1(iii): if x(b) > 0 and a is the least integer with 2a >= 3(r(b)+1)m(b)+4, then x(n) > 0 for a <= n <= b. -/
theorem p4_lem1_iii (a b n : ℕ) (ha : 0 < a) (h1 : a ≤ n) (h2 : n ≤ b) (hx : 0 < p4_x b) (hamin : 3 * (p4_r b + 1) * p4_m b + 4 ≤ 2 * a) (haleast : ∀ c : ℕ, 3 * (p4_r b + 1) * p4_m b + 4 ≤ 2 * c → a ≤ c) : 0 < p4_x n := by
  have h := (p4_lem1_i a b n ha h1 h2).1
  have hz : 2 * (a : ℤ) ≤ 3 * p4_z a + 3 := by
    unfold p4_z
    omega
  have ha' : 3 * ((p4_r b : ℤ) + 1) * (p4_m b : ℤ) + 4 ≤ 2 * (a : ℤ) := by exact_mod_cast hamin
  linarith
end

-- forge:entry p4_thm1_v_step kind=disproved origin=paper
section
/- Claim made inside the proof of Theorem 1(v), formalized literally: if B is a positive integer and 2^(k+2) > 3B+1 then x(2^(2k+2)) > B. (Numerically false: k=1, B=2 gives x(16) = -15.) -/
theorem p4_thm1_v_step_disproof : ¬ (∀ (B k : ℕ) (hB : 0 < B) (hk : 3 * B + 1 < 2 ^ (k + 2)), (B : ℤ) < p4_x (2 ^ (2 * k + 2))) := by
  intro h
  have h1 := h 1 1 (by norm_num) (by norm_num)
  have h2 : p4_x 16 = -15 := by
    rw [p4_x_block 16 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  norm_num at h1
  rw [h2] at h1
  omega
end

-- forge:entry bld2_card_le_sum_of_prod_eq_one kind=proved origin=conjecture
section
/- Uses Mathlib2.gen_an_amgm_finset_ordered_ring: with ∏ a = 1 the AM-GM inequality reads card^card ≤ (∑ a)^card; both bases are nonnegative, so for s nonempty taking card-th roots (pow_le_pow_left contrapositive) gives card ≤ ∑ a; s empty is trivial. -/
theorem bld2_card_le_sum_of_prod_eq_one (R : Type*) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (ι : Type*) (s : Finset ι) (a : ι → R) (ha : ∀ i ∈ s, 0 ≤ a i) (hp : ∏ i ∈ s, a i = 1) : (s.card : R) ≤ ∑ i ∈ s, a i := by
  have h := Mathlib2.gen_an_amgm_finset_ordered_ring R ι s a ha
  rw [hp, mul_one] at h
  rcases Nat.eq_zero_or_pos s.card with h0 | h0
  · rw [Finset.card_eq_zero] at h0
    subst h0
    simp
  · have hs : (0 : R) ≤ ∑ i ∈ s, a i := Finset.sum_nonneg ha
    exact le_of_pow_le_pow_left₀ (by omega) hs h
end

-- forge:entry p4_rem1_4096 kind=proved origin=paper
section
/- Remark 1: z(4096)=2730, m(4096)=90, r(4096)=12, x(4096)=1560. -/
theorem p4_rem1_4096 : p4_z 4096 = 2730 ∧ p4_m 4096 = 90 ∧ p4_r 4096 = 12 ∧ p4_x 4096 = 1560 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold p4_z
    norm_num
  · exact ((p4_ex1_levels 4096 90 (by norm_num)).2.1).2 (by norm_num)
  · exact ((p4_ex1_levels 4096 12 (by norm_num)).2.2 (by norm_num)).2 (by norm_num)
  · rw [p4_x_block 4096 12 90 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
end

-- forge:entry p4_small_classify kind=proved origin=conjecture
section
/- Auditor's helper lemma (not a numbered statement of the paper): the finite verification for 1 <= n <= 4096 underlying Theorem 1, done block by block on the maximal intervals where r and m are constant (the paper's Lemma 2 / table). -/
theorem p4_small_classify_aux1 (n s t p : ℕ) (c : ℤ) (hp : 2 ^ s = p) (hc : ((s : ℤ) + 1) * (t : ℤ) = c) (h1 : n ≤ p) (h2 : p < 2 * n) (h3 : t * t ≤ 2 * n) (h4 : 2 * n < (t + 1) * (t + 1)) : p4_x n = (2 * (n : ℤ) - 1) / 3 - c := by
  subst hp
  subst hc
  exact p4_x_block n s t h1 h2 h3 h4

theorem p4_small_classify_aux_b0 (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 1) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 0 1 1 1 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b1 (n : ℕ) (h1 : 2 ≤ n) (h2 : n ≤ 2) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 1 2 2 4 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b2 (n : ℕ) (h1 : 3 ≤ n) (h2 : n ≤ 4) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 2 2 4 6 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b3 (n : ℕ) (h1 : 5 ≤ n) (h2 : n ≤ 7) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 3 3 8 12 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b4 (n : ℕ) (h1 : 8 ≤ n) (h2 : n ≤ 8) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 3 4 8 16 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b5 (n : ℕ) (h1 : 9 ≤ n) (h2 : n ≤ 12) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 4 4 16 20 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b6 (n : ℕ) (h1 : 13 ≤ n) (h2 : n ≤ 16) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 4 5 16 25 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b7 (n : ℕ) (h1 : 17 ≤ n) (h2 : n ≤ 17) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 5 5 32 30 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b8 (n : ℕ) (h1 : 18 ≤ n) (h2 : n ≤ 24) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 5 6 32 36 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b9 (n : ℕ) (h1 : 25 ≤ n) (h2 : n ≤ 31) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 5 7 32 42 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b10 (n : ℕ) (h1 : 32 ≤ n) (h2 : n ≤ 32) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 5 8 32 48 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b11 (n : ℕ) (h1 : 33 ≤ n) (h2 : n ≤ 40) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 6 8 64 56 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b12 (n : ℕ) (h1 : 41 ≤ n) (h2 : n ≤ 49) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 6 9 64 63 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b13 (n : ℕ) (h1 : 50 ≤ n) (h2 : n ≤ 60) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 6 10 64 70 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b14 (n : ℕ) (h1 : 61 ≤ n) (h2 : n ≤ 64) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 6 11 64 77 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b15 (n : ℕ) (h1 : 65 ≤ n) (h2 : n ≤ 71) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 7 11 128 88 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b16 (n : ℕ) (h1 : 72 ≤ n) (h2 : n ≤ 84) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 7 12 128 96 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b17 (n : ℕ) (h1 : 85 ≤ n) (h2 : n ≤ 97) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 7 13 128 104 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b18 (n : ℕ) (h1 : 98 ≤ n) (h2 : n ≤ 112) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 7 14 128 112 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b19 (n : ℕ) (h1 : 113 ≤ n) (h2 : n ≤ 127) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 7 15 128 120 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b20 (n : ℕ) (h1 : 128 ≤ n) (h2 : n ≤ 128) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 7 16 128 128 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b21 (n : ℕ) (h1 : 129 ≤ n) (h2 : n ≤ 144) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 8 16 256 144 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b22 (n : ℕ) (h1 : 145 ≤ n) (h2 : n ≤ 161) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 8 17 256 153 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b23 (n : ℕ) (h1 : 162 ≤ n) (h2 : n ≤ 180) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 8 18 256 162 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b24 (n : ℕ) (h1 : 181 ≤ n) (h2 : n ≤ 199) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 8 19 256 171 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b25 (n : ℕ) (h1 : 200 ≤ n) (h2 : n ≤ 220) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 8 20 256 180 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b26 (n : ℕ) (h1 : 221 ≤ n) (h2 : n ≤ 241) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 8 21 256 189 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b27 (n : ℕ) (h1 : 242 ≤ n) (h2 : n ≤ 256) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 8 22 256 198 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b28 (n : ℕ) (h1 : 257 ≤ n) (h2 : n ≤ 264) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 9 22 512 220 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b29 (n : ℕ) (h1 : 265 ≤ n) (h2 : n ≤ 287) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 9 23 512 230 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b30 (n : ℕ) (h1 : 288 ≤ n) (h2 : n ≤ 312) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 9 24 512 240 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b31 (n : ℕ) (h1 : 313 ≤ n) (h2 : n ≤ 337) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 9 25 512 250 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b32 (n : ℕ) (h1 : 338 ≤ n) (h2 : n ≤ 364) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 9 26 512 260 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b33 (n : ℕ) (h1 : 365 ≤ n) (h2 : n ≤ 391) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 9 27 512 270 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b34 (n : ℕ) (h1 : 392 ≤ n) (h2 : n ≤ 420) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 9 28 512 280 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b35 (n : ℕ) (h1 : 421 ≤ n) (h2 : n ≤ 449) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 9 29 512 290 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b36 (n : ℕ) (h1 : 450 ≤ n) (h2 : n ≤ 480) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 9 30 512 300 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b37 (n : ℕ) (h1 : 481 ≤ n) (h2 : n ≤ 511) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 9 31 512 310 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b38 (n : ℕ) (h1 : 512 ≤ n) (h2 : n ≤ 512) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 9 32 512 320 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b39 (n : ℕ) (h1 : 513 ≤ n) (h2 : n ≤ 544) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 10 32 1024 352 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b40 (n : ℕ) (h1 : 545 ≤ n) (h2 : n ≤ 577) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 10 33 1024 363 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b41 (n : ℕ) (h1 : 578 ≤ n) (h2 : n ≤ 612) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 10 34 1024 374 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b42 (n : ℕ) (h1 : 613 ≤ n) (h2 : n ≤ 647) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 10 35 1024 385 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b43 (n : ℕ) (h1 : 648 ≤ n) (h2 : n ≤ 684) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 10 36 1024 396 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b44 (n : ℕ) (h1 : 685 ≤ n) (h2 : n ≤ 721) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 10 37 1024 407 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b45 (n : ℕ) (h1 : 722 ≤ n) (h2 : n ≤ 760) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 10 38 1024 418 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b46 (n : ℕ) (h1 : 761 ≤ n) (h2 : n ≤ 799) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 10 39 1024 429 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b47 (n : ℕ) (h1 : 800 ≤ n) (h2 : n ≤ 840) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 10 40 1024 440 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b48 (n : ℕ) (h1 : 841 ≤ n) (h2 : n ≤ 881) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 10 41 1024 451 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b49 (n : ℕ) (h1 : 882 ≤ n) (h2 : n ≤ 924) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 10 42 1024 462 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b50 (n : ℕ) (h1 : 925 ≤ n) (h2 : n ≤ 967) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 10 43 1024 473 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b51 (n : ℕ) (h1 : 968 ≤ n) (h2 : n ≤ 1012) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 10 44 1024 484 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b52 (n : ℕ) (h1 : 1013 ≤ n) (h2 : n ≤ 1024) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 10 45 1024 495 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b53 (n : ℕ) (h1 : 1025 ≤ n) (h2 : n ≤ 1057) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 11 45 2048 540 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b54 (n : ℕ) (h1 : 1058 ≤ n) (h2 : n ≤ 1104) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 11 46 2048 552 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b55 (n : ℕ) (h1 : 1105 ≤ n) (h2 : n ≤ 1151) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 11 47 2048 564 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b56 (n : ℕ) (h1 : 1152 ≤ n) (h2 : n ≤ 1200) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 11 48 2048 576 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b57 (n : ℕ) (h1 : 1201 ≤ n) (h2 : n ≤ 1249) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 11 49 2048 588 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b58 (n : ℕ) (h1 : 1250 ≤ n) (h2 : n ≤ 1300) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 11 50 2048 600 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b59 (n : ℕ) (h1 : 1301 ≤ n) (h2 : n ≤ 1351) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 11 51 2048 612 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b60 (n : ℕ) (h1 : 1352 ≤ n) (h2 : n ≤ 1404) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 11 52 2048 624 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b61 (n : ℕ) (h1 : 1405 ≤ n) (h2 : n ≤ 1457) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 11 53 2048 636 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b62 (n : ℕ) (h1 : 1458 ≤ n) (h2 : n ≤ 1512) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 11 54 2048 648 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b63 (n : ℕ) (h1 : 1513 ≤ n) (h2 : n ≤ 1567) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 11 55 2048 660 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b64 (n : ℕ) (h1 : 1568 ≤ n) (h2 : n ≤ 1624) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 11 56 2048 672 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b65 (n : ℕ) (h1 : 1625 ≤ n) (h2 : n ≤ 1681) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 11 57 2048 684 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b66 (n : ℕ) (h1 : 1682 ≤ n) (h2 : n ≤ 1740) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 11 58 2048 696 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b67 (n : ℕ) (h1 : 1741 ≤ n) (h2 : n ≤ 1799) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 11 59 2048 708 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b68 (n : ℕ) (h1 : 1800 ≤ n) (h2 : n ≤ 1860) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 11 60 2048 720 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b69 (n : ℕ) (h1 : 1861 ≤ n) (h2 : n ≤ 1921) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 11 61 2048 732 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b70 (n : ℕ) (h1 : 1922 ≤ n) (h2 : n ≤ 1984) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 11 62 2048 744 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b71 (n : ℕ) (h1 : 1985 ≤ n) (h2 : n ≤ 2047) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 11 63 2048 756 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b72 (n : ℕ) (h1 : 2048 ≤ n) (h2 : n ≤ 2048) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 11 64 2048 768 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b73 (n : ℕ) (h1 : 2049 ≤ n) (h2 : n ≤ 2112) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 64 4096 832 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b74 (n : ℕ) (h1 : 2113 ≤ n) (h2 : n ≤ 2177) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 65 4096 845 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b75 (n : ℕ) (h1 : 2178 ≤ n) (h2 : n ≤ 2244) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 66 4096 858 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b76 (n : ℕ) (h1 : 2245 ≤ n) (h2 : n ≤ 2311) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 67 4096 871 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b77 (n : ℕ) (h1 : 2312 ≤ n) (h2 : n ≤ 2380) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 68 4096 884 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b78 (n : ℕ) (h1 : 2381 ≤ n) (h2 : n ≤ 2449) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 69 4096 897 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b79 (n : ℕ) (h1 : 2450 ≤ n) (h2 : n ≤ 2520) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 70 4096 910 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b80 (n : ℕ) (h1 : 2521 ≤ n) (h2 : n ≤ 2591) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 71 4096 923 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b81 (n : ℕ) (h1 : 2592 ≤ n) (h2 : n ≤ 2664) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 72 4096 936 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b82 (n : ℕ) (h1 : 2665 ≤ n) (h2 : n ≤ 2737) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 73 4096 949 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b83 (n : ℕ) (h1 : 2738 ≤ n) (h2 : n ≤ 2812) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 74 4096 962 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b84 (n : ℕ) (h1 : 2813 ≤ n) (h2 : n ≤ 2887) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 75 4096 975 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b85 (n : ℕ) (h1 : 2888 ≤ n) (h2 : n ≤ 2964) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 76 4096 988 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b86 (n : ℕ) (h1 : 2965 ≤ n) (h2 : n ≤ 3041) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 77 4096 1001 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b87 (n : ℕ) (h1 : 3042 ≤ n) (h2 : n ≤ 3120) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 78 4096 1014 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b88 (n : ℕ) (h1 : 3121 ≤ n) (h2 : n ≤ 3199) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 79 4096 1027 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b89 (n : ℕ) (h1 : 3200 ≤ n) (h2 : n ≤ 3280) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 80 4096 1040 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b90 (n : ℕ) (h1 : 3281 ≤ n) (h2 : n ≤ 3361) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 81 4096 1053 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b91 (n : ℕ) (h1 : 3362 ≤ n) (h2 : n ≤ 3444) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 82 4096 1066 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b92 (n : ℕ) (h1 : 3445 ≤ n) (h2 : n ≤ 3527) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 83 4096 1079 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b93 (n : ℕ) (h1 : 3528 ≤ n) (h2 : n ≤ 3612) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 84 4096 1092 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b94 (n : ℕ) (h1 : 3613 ≤ n) (h2 : n ≤ 3697) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 85 4096 1105 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b95 (n : ℕ) (h1 : 3698 ≤ n) (h2 : n ≤ 3784) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 86 4096 1118 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b96 (n : ℕ) (h1 : 3785 ≤ n) (h2 : n ≤ 3871) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 87 4096 1131 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b97 (n : ℕ) (h1 : 3872 ≤ n) (h2 : n ≤ 3960) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 88 4096 1144 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b98 (n : ℕ) (h1 : 3961 ≤ n) (h2 : n ≤ 4049) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 89 4096 1157 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify_aux_b99 (n : ℕ) (h1 : 4050 ≤ n) (h2 : n ≤ 4096) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  rw [p4_small_classify_aux1 n 12 90 4096 1170 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem p4_small_classify (n : ℕ) (hn : 0 < n) (h : n ≤ 4096) : (p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) ∧ (n ≠ 129 → -58 ≤ p4_x n) := by
  by_cases h0 : n ≤ 1
  · exact p4_small_classify_aux_b0 n (by omega) h0
  replace hn : 1 < n := by omega
  clear h0
  by_cases h1 : n ≤ 2
  · exact p4_small_classify_aux_b1 n (by omega) h1
  replace hn : 2 < n := by omega
  clear h1
  by_cases h2 : n ≤ 4
  · exact p4_small_classify_aux_b2 n (by omega) h2
  replace hn : 4 < n := by omega
  clear h2
  by_cases h3 : n ≤ 7
  · exact p4_small_classify_aux_b3 n (by omega) h3
  replace hn : 7 < n := by omega
  clear h3
  by_cases h4 : n ≤ 8
  · exact p4_small_classify_aux_b4 n (by omega) h4
  replace hn : 8 < n := by omega
  clear h4
  by_cases h5 : n ≤ 12
  · exact p4_small_classify_aux_b5 n (by omega) h5
  replace hn : 12 < n := by omega
  clear h5
  by_cases h6 : n ≤ 16
  · exact p4_small_classify_aux_b6 n (by omega) h6
  replace hn : 16 < n := by omega
  clear h6
  by_cases h7 : n ≤ 17
  · exact p4_small_classify_aux_b7 n (by omega) h7
  replace hn : 17 < n := by omega
  clear h7
  by_cases h8 : n ≤ 24
  · exact p4_small_classify_aux_b8 n (by omega) h8
  replace hn : 24 < n := by omega
  clear h8
  by_cases h9 : n ≤ 31
  · exact p4_small_classify_aux_b9 n (by omega) h9
  replace hn : 31 < n := by omega
  clear h9
  by_cases h10 : n ≤ 32
  · exact p4_small_classify_aux_b10 n (by omega) h10
  replace hn : 32 < n := by omega
  clear h10
  by_cases h11 : n ≤ 40
  · exact p4_small_classify_aux_b11 n (by omega) h11
  replace hn : 40 < n := by omega
  clear h11
  by_cases h12 : n ≤ 49
  · exact p4_small_classify_aux_b12 n (by omega) h12
  replace hn : 49 < n := by omega
  clear h12
  by_cases h13 : n ≤ 60
  · exact p4_small_classify_aux_b13 n (by omega) h13
  replace hn : 60 < n := by omega
  clear h13
  by_cases h14 : n ≤ 64
  · exact p4_small_classify_aux_b14 n (by omega) h14
  replace hn : 64 < n := by omega
  clear h14
  by_cases h15 : n ≤ 71
  · exact p4_small_classify_aux_b15 n (by omega) h15
  replace hn : 71 < n := by omega
  clear h15
  by_cases h16 : n ≤ 84
  · exact p4_small_classify_aux_b16 n (by omega) h16
  replace hn : 84 < n := by omega
  clear h16
  by_cases h17 : n ≤ 97
  · exact p4_small_classify_aux_b17 n (by omega) h17
  replace hn : 97 < n := by omega
  clear h17
  by_cases h18 : n ≤ 112
  · exact p4_small_classify_aux_b18 n (by omega) h18
  replace hn : 112 < n := by omega
  clear h18
  by_cases h19 : n ≤ 127
  · exact p4_small_classify_aux_b19 n (by omega) h19
  replace hn : 127 < n := by omega
  clear h19
  by_cases h20 : n ≤ 128
  · exact p4_small_classify_aux_b20 n (by omega) h20
  replace hn : 128 < n := by omega
  clear h20
  by_cases h21 : n ≤ 144
  · exact p4_small_classify_aux_b21 n (by omega) h21
  replace hn : 144 < n := by omega
  clear h21
  by_cases h22 : n ≤ 161
  · exact p4_small_classify_aux_b22 n (by omega) h22
  replace hn : 161 < n := by omega
  clear h22
  by_cases h23 : n ≤ 180
  · exact p4_small_classify_aux_b23 n (by omega) h23
  replace hn : 180 < n := by omega
  clear h23
  by_cases h24 : n ≤ 199
  · exact p4_small_classify_aux_b24 n (by omega) h24
  replace hn : 199 < n := by omega
  clear h24
  by_cases h25 : n ≤ 220
  · exact p4_small_classify_aux_b25 n (by omega) h25
  replace hn : 220 < n := by omega
  clear h25
  by_cases h26 : n ≤ 241
  · exact p4_small_classify_aux_b26 n (by omega) h26
  replace hn : 241 < n := by omega
  clear h26
  by_cases h27 : n ≤ 256
  · exact p4_small_classify_aux_b27 n (by omega) h27
  replace hn : 256 < n := by omega
  clear h27
  by_cases h28 : n ≤ 264
  · exact p4_small_classify_aux_b28 n (by omega) h28
  replace hn : 264 < n := by omega
  clear h28
  by_cases h29 : n ≤ 287
  · exact p4_small_classify_aux_b29 n (by omega) h29
  replace hn : 287 < n := by omega
  clear h29
  by_cases h30 : n ≤ 312
  · exact p4_small_classify_aux_b30 n (by omega) h30
  replace hn : 312 < n := by omega
  clear h30
  by_cases h31 : n ≤ 337
  · exact p4_small_classify_aux_b31 n (by omega) h31
  replace hn : 337 < n := by omega
  clear h31
  by_cases h32 : n ≤ 364
  · exact p4_small_classify_aux_b32 n (by omega) h32
  replace hn : 364 < n := by omega
  clear h32
  by_cases h33 : n ≤ 391
  · exact p4_small_classify_aux_b33 n (by omega) h33
  replace hn : 391 < n := by omega
  clear h33
  by_cases h34 : n ≤ 420
  · exact p4_small_classify_aux_b34 n (by omega) h34
  replace hn : 420 < n := by omega
  clear h34
  by_cases h35 : n ≤ 449
  · exact p4_small_classify_aux_b35 n (by omega) h35
  replace hn : 449 < n := by omega
  clear h35
  by_cases h36 : n ≤ 480
  · exact p4_small_classify_aux_b36 n (by omega) h36
  replace hn : 480 < n := by omega
  clear h36
  by_cases h37 : n ≤ 511
  · exact p4_small_classify_aux_b37 n (by omega) h37
  replace hn : 511 < n := by omega
  clear h37
  by_cases h38 : n ≤ 512
  · exact p4_small_classify_aux_b38 n (by omega) h38
  replace hn : 512 < n := by omega
  clear h38
  by_cases h39 : n ≤ 544
  · exact p4_small_classify_aux_b39 n (by omega) h39
  replace hn : 544 < n := by omega
  clear h39
  by_cases h40 : n ≤ 577
  · exact p4_small_classify_aux_b40 n (by omega) h40
  replace hn : 577 < n := by omega
  clear h40
  by_cases h41 : n ≤ 612
  · exact p4_small_classify_aux_b41 n (by omega) h41
  replace hn : 612 < n := by omega
  clear h41
  by_cases h42 : n ≤ 647
  · exact p4_small_classify_aux_b42 n (by omega) h42
  replace hn : 647 < n := by omega
  clear h42
  by_cases h43 : n ≤ 684
  · exact p4_small_classify_aux_b43 n (by omega) h43
  replace hn : 684 < n := by omega
  clear h43
  by_cases h44 : n ≤ 721
  · exact p4_small_classify_aux_b44 n (by omega) h44
  replace hn : 721 < n := by omega
  clear h44
  by_cases h45 : n ≤ 760
  · exact p4_small_classify_aux_b45 n (by omega) h45
  replace hn : 760 < n := by omega
  clear h45
  by_cases h46 : n ≤ 799
  · exact p4_small_classify_aux_b46 n (by omega) h46
  replace hn : 799 < n := by omega
  clear h46
  by_cases h47 : n ≤ 840
  · exact p4_small_classify_aux_b47 n (by omega) h47
  replace hn : 840 < n := by omega
  clear h47
  by_cases h48 : n ≤ 881
  · exact p4_small_classify_aux_b48 n (by omega) h48
  replace hn : 881 < n := by omega
  clear h48
  by_cases h49 : n ≤ 924
  · exact p4_small_classify_aux_b49 n (by omega) h49
  replace hn : 924 < n := by omega
  clear h49
  by_cases h50 : n ≤ 967
  · exact p4_small_classify_aux_b50 n (by omega) h50
  replace hn : 967 < n := by omega
  clear h50
  by_cases h51 : n ≤ 1012
  · exact p4_small_classify_aux_b51 n (by omega) h51
  replace hn : 1012 < n := by omega
  clear h51
  by_cases h52 : n ≤ 1024
  · exact p4_small_classify_aux_b52 n (by omega) h52
  replace hn : 1024 < n := by omega
  clear h52
  by_cases h53 : n ≤ 1057
  · exact p4_small_classify_aux_b53 n (by omega) h53
  replace hn : 1057 < n := by omega
  clear h53
  by_cases h54 : n ≤ 1104
  · exact p4_small_classify_aux_b54 n (by omega) h54
  replace hn : 1104 < n := by omega
  clear h54
  by_cases h55 : n ≤ 1151
  · exact p4_small_classify_aux_b55 n (by omega) h55
  replace hn : 1151 < n := by omega
  clear h55
  by_cases h56 : n ≤ 1200
  · exact p4_small_classify_aux_b56 n (by omega) h56
  replace hn : 1200 < n := by omega
  clear h56
  by_cases h57 : n ≤ 1249
  · exact p4_small_classify_aux_b57 n (by omega) h57
  replace hn : 1249 < n := by omega
  clear h57
  by_cases h58 : n ≤ 1300
  · exact p4_small_classify_aux_b58 n (by omega) h58
  replace hn : 1300 < n := by omega
  clear h58
  by_cases h59 : n ≤ 1351
  · exact p4_small_classify_aux_b59 n (by omega) h59
  replace hn : 1351 < n := by omega
  clear h59
  by_cases h60 : n ≤ 1404
  · exact p4_small_classify_aux_b60 n (by omega) h60
  replace hn : 1404 < n := by omega
  clear h60
  by_cases h61 : n ≤ 1457
  · exact p4_small_classify_aux_b61 n (by omega) h61
  replace hn : 1457 < n := by omega
  clear h61
  by_cases h62 : n ≤ 1512
  · exact p4_small_classify_aux_b62 n (by omega) h62
  replace hn : 1512 < n := by omega
  clear h62
  by_cases h63 : n ≤ 1567
  · exact p4_small_classify_aux_b63 n (by omega) h63
  replace hn : 1567 < n := by omega
  clear h63
  by_cases h64 : n ≤ 1624
  · exact p4_small_classify_aux_b64 n (by omega) h64
  replace hn : 1624 < n := by omega
  clear h64
  by_cases h65 : n ≤ 1681
  · exact p4_small_classify_aux_b65 n (by omega) h65
  replace hn : 1681 < n := by omega
  clear h65
  by_cases h66 : n ≤ 1740
  · exact p4_small_classify_aux_b66 n (by omega) h66
  replace hn : 1740 < n := by omega
  clear h66
  by_cases h67 : n ≤ 1799
  · exact p4_small_classify_aux_b67 n (by omega) h67
  replace hn : 1799 < n := by omega
  clear h67
  by_cases h68 : n ≤ 1860
  · exact p4_small_classify_aux_b68 n (by omega) h68
  replace hn : 1860 < n := by omega
  clear h68
  by_cases h69 : n ≤ 1921
  · exact p4_small_classify_aux_b69 n (by omega) h69
  replace hn : 1921 < n := by omega
  clear h69
  by_cases h70 : n ≤ 1984
  · exact p4_small_classify_aux_b70 n (by omega) h70
  replace hn : 1984 < n := by omega
  clear h70
  by_cases h71 : n ≤ 2047
  · exact p4_small_classify_aux_b71 n (by omega) h71
  replace hn : 2047 < n := by omega
  clear h71
  by_cases h72 : n ≤ 2048
  · exact p4_small_classify_aux_b72 n (by omega) h72
  replace hn : 2048 < n := by omega
  clear h72
  by_cases h73 : n ≤ 2112
  · exact p4_small_classify_aux_b73 n (by omega) h73
  replace hn : 2112 < n := by omega
  clear h73
  by_cases h74 : n ≤ 2177
  · exact p4_small_classify_aux_b74 n (by omega) h74
  replace hn : 2177 < n := by omega
  clear h74
  by_cases h75 : n ≤ 2244
  · exact p4_small_classify_aux_b75 n (by omega) h75
  replace hn : 2244 < n := by omega
  clear h75
  by_cases h76 : n ≤ 2311
  · exact p4_small_classify_aux_b76 n (by omega) h76
  replace hn : 2311 < n := by omega
  clear h76
  by_cases h77 : n ≤ 2380
  · exact p4_small_classify_aux_b77 n (by omega) h77
  replace hn : 2380 < n := by omega
  clear h77
  by_cases h78 : n ≤ 2449
  · exact p4_small_classify_aux_b78 n (by omega) h78
  replace hn : 2449 < n := by omega
  clear h78
  by_cases h79 : n ≤ 2520
  · exact p4_small_classify_aux_b79 n (by omega) h79
  replace hn : 2520 < n := by omega
  clear h79
  by_cases h80 : n ≤ 2591
  · exact p4_small_classify_aux_b80 n (by omega) h80
  replace hn : 2591 < n := by omega
  clear h80
  by_cases h81 : n ≤ 2664
  · exact p4_small_classify_aux_b81 n (by omega) h81
  replace hn : 2664 < n := by omega
  clear h81
  by_cases h82 : n ≤ 2737
  · exact p4_small_classify_aux_b82 n (by omega) h82
  replace hn : 2737 < n := by omega
  clear h82
  by_cases h83 : n ≤ 2812
  · exact p4_small_classify_aux_b83 n (by omega) h83
  replace hn : 2812 < n := by omega
  clear h83
  by_cases h84 : n ≤ 2887
  · exact p4_small_classify_aux_b84 n (by omega) h84
  replace hn : 2887 < n := by omega
  clear h84
  by_cases h85 : n ≤ 2964
  · exact p4_small_classify_aux_b85 n (by omega) h85
  replace hn : 2964 < n := by omega
  clear h85
  by_cases h86 : n ≤ 3041
  · exact p4_small_classify_aux_b86 n (by omega) h86
  replace hn : 3041 < n := by omega
  clear h86
  by_cases h87 : n ≤ 3120
  · exact p4_small_classify_aux_b87 n (by omega) h87
  replace hn : 3120 < n := by omega
  clear h87
  by_cases h88 : n ≤ 3199
  · exact p4_small_classify_aux_b88 n (by omega) h88
  replace hn : 3199 < n := by omega
  clear h88
  by_cases h89 : n ≤ 3280
  · exact p4_small_classify_aux_b89 n (by omega) h89
  replace hn : 3280 < n := by omega
  clear h89
  by_cases h90 : n ≤ 3361
  · exact p4_small_classify_aux_b90 n (by omega) h90
  replace hn : 3361 < n := by omega
  clear h90
  by_cases h91 : n ≤ 3444
  · exact p4_small_classify_aux_b91 n (by omega) h91
  replace hn : 3444 < n := by omega
  clear h91
  by_cases h92 : n ≤ 3527
  · exact p4_small_classify_aux_b92 n (by omega) h92
  replace hn : 3527 < n := by omega
  clear h92
  by_cases h93 : n ≤ 3612
  · exact p4_small_classify_aux_b93 n (by omega) h93
  replace hn : 3612 < n := by omega
  clear h93
  by_cases h94 : n ≤ 3697
  · exact p4_small_classify_aux_b94 n (by omega) h94
  replace hn : 3697 < n := by omega
  clear h94
  by_cases h95 : n ≤ 3784
  · exact p4_small_classify_aux_b95 n (by omega) h95
  replace hn : 3784 < n := by omega
  clear h95
  by_cases h96 : n ≤ 3871
  · exact p4_small_classify_aux_b96 n (by omega) h96
  replace hn : 3871 < n := by omega
  clear h96
  by_cases h97 : n ≤ 3960
  · exact p4_small_classify_aux_b97 n (by omega) h97
  replace hn : 3960 < n := by omega
  clear h97
  by_cases h98 : n ≤ 4049
  · exact p4_small_classify_aux_b98 n (by omega) h98
  replace hn : 4049 < n := by omega
  clear h98
  by_cases h99 : n ≤ 4096
  · exact p4_small_classify_aux_b99 n (by omega) h99
  replace hn : 4096 < n := by omega
  clear h99
  omega
end

-- forge:entry bld2_commutator_eq_center_of_card_prime_cube kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_center_card_of_card_prime_cube: the centre has order p, so G / Z(G) has order p^2 and is abelian, giving commutator G ≤ Z(G); the commutator subgroup is nontrivial (G non-abelian) and Z(G) has prime order, so the inclusion is an equality. -/
theorem bld2_commutator_eq_center_of_card_prime_cube (p : ℕ) (hp : p.Prime) (G : Type*) [Group G] (hG : Nat.card G = p ^ 3) (hnc : ∃ a b : G, a * b ≠ b * a) : commutator G = Subgroup.center G := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact pow_ne_zero _ hp.ne_zero)
  have hZ := Mathlib2.bld_center_card_of_card_prime_cube p hp G hG hnc
  have hq : Nat.card (G ⧸ Subgroup.center G) = p ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)
    rw [hG, hZ] at h
    have hp0 : 0 < p := hp.pos
    have : p ^ 2 * p = Nat.card (G ⧸ Subgroup.center G) * p := by rw [← h]; ring
    exact (Nat.eq_of_mul_eq_mul_right hp0 this).symm
  have hle : commutator G ≤ Subgroup.center G := by
    rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
    exact ⟨IsPGroup.commutative_of_card_eq_prime_sq hq⟩
  have hdvd : Nat.card (commutator G) ∣ p := hZ ▸ Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    rw [← commutatorElement_eq_one_iff_mul_comm]
    have hbot : commutator G = ⊥ := Subgroup.card_eq_one.mp h1
    have hm : ⁅a, b⁆ ∈ commutator G := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [hbot] at hm
    exact Subgroup.mem_bot.mp hm
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hZ, h1])
end

-- forge:entry p4_lem2_greatest kind=proved origin=paper
section
/- Lemma 2, first part: with s=r(a), t=m(a), q the largest integer with 2q < (t+1)^2 and b(a)=min(q,2^s), b(a) is the largest positive integer k with r(k)=s and m(k)=t. -/
theorem p4_lem2_greatest_aux1 (a q : ℕ) (ha : 0 < a) (hq : 2 * q < (p4_m a + 1) ^ 2) (hqmax : ∀ c : ℕ, 2 * c < (p4_m a + 1) ^ 2 → c ≤ q) (n : ℕ) (h1 : a ≤ n) (h2 : n ≤ min q (2 ^ p4_r a)) : p4_r n = p4_r a ∧ p4_m n = p4_m a := by
  have hnq : n ≤ q := le_trans h2 (min_le_left _ _)
  have hns : n ≤ 2 ^ p4_r a := le_trans h2 (min_le_right _ _)
  obtain ⟨-, hm, hr⟩ := p4_ex1_mono a n h1
  constructor
  · exact le_antisymm ((p4_r_spec n).2 _ hns) hr
  · apply le_antisymm _ hm
    have h3 : 2 * n < (p4_m a + 1) ^ 2 := by omega
    have h4 : p4_m n < p4_m a + 1 := by
      unfold p4_m at h3 ⊢
      exact Nat.sqrt_lt'.2 h3
    omega

theorem p4_lem2_greatest (a q : ℕ) (ha : 0 < a) (hq : 2 * q < (p4_m a + 1) ^ 2) (hqmax : ∀ c : ℕ, 2 * c < (p4_m a + 1) ^ 2 → c ≤ q) : IsGreatest {k : ℕ | 0 < k ∧ p4_r k = p4_r a ∧ p4_m k = p4_m a} (min q (2 ^ p4_r a)) := by
  have haq : a ≤ q := by
    apply hqmax
    have := Nat.lt_succ_sqrt' (2 * a)
    unfold p4_m
    exact this
  have hab : a ≤ min q (2 ^ p4_r a) := le_min haq (p4_r_spec a).1
  constructor
  · refine ⟨by omega, ?_⟩
    exact p4_lem2_greatest_aux1 a q ha hq hqmax _ hab le_rfl
  · rintro k ⟨hk0, hkr, hkm⟩
    apply le_min
    · apply hqmax
      rw [← hkm]
      have := Nat.lt_succ_sqrt' (2 * k)
      unfold p4_m
      exact this
    · rw [← hkr]
      exact (p4_r_spec k).1
end

-- forge:entry p4_lem2_chain kind=proved origin=paper
section
/- Lemma 2, second part: for a <= n1 <= n2 <= b(a): x(a) <= x(n1) = z(n1)-(r(a)+1)m(a) <= x(n2) <= x(b(a)). -/
theorem p4_lem2_chain_aux1 (a q : ℕ) (ha : 0 < a) (hq : 2 * q < (p4_m a + 1) ^ 2) (hqmax : ∀ c : ℕ, 2 * c < (p4_m a + 1) ^ 2 → c ≤ q) (n : ℕ) (h1 : a ≤ n) (h2 : n ≤ min q (2 ^ p4_r a)) : p4_r n = p4_r a ∧ p4_m n = p4_m a := by
  have hnq : n ≤ q := le_trans h2 (min_le_left _ _)
  have hns : n ≤ 2 ^ p4_r a := le_trans h2 (min_le_right _ _)
  obtain ⟨-, hm, hr⟩ := p4_ex1_mono a n h1
  constructor
  · exact le_antisymm ((p4_r_spec n).2 _ hns) hr
  · apply le_antisymm _ hm
    have h3 : 2 * n < (p4_m a + 1) ^ 2 := by omega
    have h4 : p4_m n < p4_m a + 1 := by
      unfold p4_m at h3 ⊢
      exact Nat.sqrt_lt'.2 h3
    omega

theorem p4_lem2_chain (a q : ℕ) (ha : 0 < a) (hq : 2 * q < (p4_m a + 1) ^ 2) (hqmax : ∀ c : ℕ, 2 * c < (p4_m a + 1) ^ 2 → c ≤ q) (n1 n2 : ℕ) (h1 : a ≤ n1) (h2 : n1 ≤ n2) (h3 : n2 ≤ min q (2 ^ p4_r a)) : p4_x a ≤ p4_x n1 ∧ p4_x n1 = p4_z n1 - ((p4_r a : ℤ) + 1) * (p4_m a : ℤ) ∧ p4_x n1 ≤ p4_x n2 ∧ p4_x n2 ≤ p4_x (min q (2 ^ p4_r a)) := by
  obtain ⟨e1r, e1m⟩ := p4_lem2_chain_aux1 a q ha hq hqmax n1 h1 (le_trans h2 h3)
  obtain ⟨e2r, e2m⟩ := p4_lem2_chain_aux1 a q ha hq hqmax n2 (le_trans h1 h2) h3
  obtain ⟨e3r, e3m⟩ := p4_lem2_chain_aux1 a q ha hq hqmax _ (le_trans h1 (le_trans h2 h3)) le_rfl
  have z1 := (p4_ex1_mono a n1 h1).1
  have z2 := (p4_ex1_mono n1 n2 h2).1
  have z3 := (p4_ex1_mono n2 _ h3).1
  unfold p4_x
  rw [e1r, e1m, e2r, e2m, e3r, e3m]
  refine ⟨?_, rfl, ?_, ?_⟩ <;> linarith
end

end Mathlib2
