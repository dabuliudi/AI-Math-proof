/- Mathlib2 分片 4（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0003
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry nt2_pow_four_add_four_mul_pow_four_not_prime kind=proved origin=conjecture
section
/- Generalization of Mathlib2.nt_pow4_add_four_not_prime (the case k = 1): n^4 + 4k^4 = ((n-k)^2 + k^2)((n+k)^2 + k^2) is composite for n > 1, k ≥ 1. -/
theorem nt2_pow_four_add_four_mul_pow_four_not_prime (n k : ℕ) (hn : 1 < n) (hk : 0 < k) : ¬ Nat.Prime (n ^ 4 + 4 * k ^ 4) := by
  have hle : 2 * n * k ≤ n ^ 2 + 2 * k ^ 2 := by
    zify
    nlinarith [sq_nonneg ((n:ℤ) - k), sq_nonneg (k:ℤ)]
  obtain ⟨a, ha⟩ : ∃ a, a + 2 * n * k = n ^ 2 + 2 * k ^ 2 := ⟨_, Nat.sub_add_cancel hle⟩
  have ha' : (a:ℤ) = n ^ 2 + 2 * k ^ 2 - 2 * n * k := by
    have := congrArg (Nat.cast : ℕ → ℤ) ha
    push_cast at this
    linarith
  have hn' : (2:ℤ) ≤ n := by exact_mod_cast hn
  have hk' : (1:ℤ) ≤ k := by exact_mod_cast hk
  have hmul : a * (n ^ 2 + 2 * k ^ 2 + 2 * n * k) = n ^ 4 + 4 * k ^ 4 := by
    zify
    rw [ha']
    ring
  apply Nat.not_prime_of_mul_eq hmul
  · intro h1
    rw [h1] at ha'
    push_cast at ha'
    have e : ((n:ℤ) - k) ^ 2 + (k:ℤ) ^ 2 = 1 := by linarith
    have hk2 : (1:ℤ) ≤ (k:ℤ) ^ 2 := by nlinarith
    have h0 : ((n:ℤ) - k) ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
    have hnk : (n:ℤ) = k := by
      have := pow_eq_zero_iff (two_ne_zero) |>.mp h0
      linarith
    have : (k:ℤ) ^ 2 = 1 := by linarith
    nlinarith
  · have : 4 ≤ n ^ 2 := by nlinarith
    omega
end

-- forge:entry nt2_totient_pow_sub_one_multiple kind=proved origin=conjecture
section
/- For a > 1, n divides φ(a^n - 1): a has multiplicative order exactly n modulo a^n - 1. (Stated with an explicit cofactor.) -/
theorem nt2_totient_pow_sub_one_multiple (a n : ℕ) (ha : 1 < a) : ∃ k, Nat.totient (a ^ n - 1) = n * k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, by simp⟩
  obtain ⟨N, hN⟩ : ∃ N, a ^ n = N + 1 :=
    ⟨a ^ n - 1, by have := Nat.one_le_pow n a (by omega); omega⟩
  have hNpos : 0 < N := by
    have := Nat.one_lt_pow hn.ne' ha
    omega
  have hN' : a ^ n - 1 = N := by omega
  rw [hN']
  haveI : NeZero N := ⟨hNpos.ne'⟩
  have hcop : Nat.Coprime a N := by
    have h1 : Nat.Coprime (N + 1) N := by simp
    rw [← hN] at h1
    exact Nat.Coprime.coprime_dvd_left (dvd_pow_self a hn.ne') h1
  have hord : orderOf (ZMod.unitOfCoprime a hcop) = n := by
    rw [orderOf_eq_iff hn]
    refine ⟨?_, ?_⟩
    · apply Units.ext
      rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one, ← Nat.cast_pow, hN]
      simp
    · intro m hmn hm0 h
      have h2 := congrArg Units.val h
      rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one, ← Nat.cast_pow] at h2
      have h3 : ((a ^ m : ℕ) : ZMod N) = ((1 : ℕ) : ZMod N) := by rw [h2]; simp
      rw [ZMod.natCast_eq_natCast_iff] at h3
      have h4 := (Nat.modEq_iff_dvd' (Nat.one_le_pow m a (by omega))).mp h3.symm
      have h5 := Nat.pow_lt_pow_right ha hmn
      have h6 := Nat.one_lt_pow hm0.ne' ha
      have h7 := Nat.le_of_dvd (by omega) h4
      omega
  have hdvd : n ∣ Nat.totient N := by
    rw [← hord, ← ZMod.card_units_eq_totient]
    exact orderOf_dvd_card
  obtain ⟨k, hk⟩ := hdvd
  exact ⟨k, hk⟩
end

-- forge:entry nt2_fermat_number_prime_factor_form kind=proved origin=conjecture
section
/- Every prime factor p of the Fermat number 2^(2^n)+1 has the form m·2^(n+1) + 1: the order of 2 mod p is exactly 2^(n+1), which divides p - 1. -/
theorem nt2_fermat_number_prime_factor_form (n p : ℕ) (hp : Nat.Prime p) (h : ∃ k, p * k = 2 ^ 2 ^ n + 1) : ∃ m, p = m * 2 ^ (n + 1) + 1 := by
  obtain ⟨k, hk⟩ := h
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 2 ^ 2 ^ n + 1 := ⟨k, hk.symm⟩
    have h2 : 2 ∣ 2 ^ 2 ^ n := dvd_pow_self 2 (by positivity)
    have := (Nat.dvd_add_right h2).mp h1
    omega
  have hp3 : 2 < p := by have := hp.two_le; omega
  haveI : Fact (2 < p) := ⟨hp3⟩
  have hz : ((2:ZMod p)) ^ 2 ^ n = -1 := by
    have : ((2 ^ 2 ^ n + 1 : ℕ) : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]; exact ⟨k, hk.symm⟩
    push_cast at this
    linear_combination this
  have hnot : ¬ (2:ZMod p) ^ 2 ^ n = 1 := by
    rw [hz]; exact ZMod.neg_one_ne_one
  have hfin : (2:ZMod p) ^ 2 ^ (n + 1) = 1 := by
    rw [pow_succ, pow_mul, hz]; norm_num
  have hord : orderOf (2:ZMod p) = 2 ^ (n + 1) := orderOf_eq_prime_pow hnot hfin
  have h20 : (2:ZMod p) ≠ 0 := by
    intro h0
    have : ((2:ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hdvd := ZMod.orderOf_dvd_card_sub_one h20
  rw [hord] at hdvd
  obtain ⟨m, hm⟩ := hdvd
  refine ⟨m, ?_⟩
  have := hp.one_le
  rw [mul_comm m]
  omega
end

-- forge:entry nt2_lte_three_two_pow_three_pow_add_one kind=proved origin=conjecture
section
/- Lifting the exponent: the exact power of 3 dividing 2^(3^n) + 1 is 3^(n+1). -/
theorem nt2_lte_three_two_pow_three_pow_add_one (n : ℕ) : ∃ k, 2 ^ 3 ^ n + 1 = 3 ^ (n + 1) * k ∧ ¬ 3 ∣ k := by
  induction n with
  | zero => exact ⟨1, by norm_num, by norm_num⟩
  | succ n ih =>
    obtain ⟨k, hk, h3⟩ := ih
    have hk' : 2 ^ 3 ^ n + 1 = 3 * (3 ^ n * k) := by rw [hk]; ring
    obtain ⟨A, hAdef⟩ : ∃ A, A = 2 ^ 3 ^ n := ⟨_, rfl⟩
    obtain ⟨m, hmdef⟩ : ∃ m, m = 3 ^ n * k := ⟨_, rfl⟩
    rw [← hAdef, ← hmdef] at hk'
    obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    have hA : A = 3 * j + 2 := by omega
    refine ⟨k * (3 * (j + 1) * j + 1), ?_, ?_⟩
    · have e : 3 ^ (n + 1 + 1) * (k * (3 * (j + 1) * j + 1))
          = 9 * (3 ^ n * k) * (3 * (j + 1) * j + 1) := by ring
      rw [e, ← hmdef, hj, pow_succ 3 n, pow_mul, ← hAdef, hA]
      ring
    · intro hd
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hd with h | h
      · exact h3 h
      · have h' : 3 ∣ 3 * ((j + 1) * j) + 1 := by rwa [mul_assoc] at h
        omega
end

-- forge:entry nt2_pow_four_add_four_pow_factors kind=proved origin=conjecture
section
/- n^4 + 4^n is composite for n > 1. Generalizes Mathlib2.nt_pow4_add_four_not_prime: for odd n apply the Sophie Germain identity a^4 + 4 b^4 with b = 2^((n-1)/2) (cf. nt2_pow_four_add_four_mul_pow_four_not_prime); for even n the number is even and > 2. -/
theorem nt2_pow_four_add_four_pow_factors (n : ℕ) (hn : 1 < n) : ∃ a b, 1 < a ∧ 1 < b ∧ n ^ 4 + 4 ^ n = a * b := by
  have hbig : 16 ≤ n ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ n ^ 4 := Nat.pow_le_pow_left hn 4
  have hnp : ¬ Nat.Prime (n ^ 4 + 4 ^ n) := by
    rcases Nat.even_or_odd n with he | ho
    · intro hpr
      have h1 : 2 ∣ n ^ 4 := (he.pow_of_ne_zero (by norm_num)).two_dvd
      have h2 : 2 ∣ 4 ^ n := dvd_pow (by norm_num : (2:ℕ) ∣ 4) (by omega : n ≠ 0)
      have h3 : 2 ∣ n ^ 4 + 4 ^ n := Nat.dvd_add h1 h2
      rcases (Nat.dvd_prime hpr).mp h3 with h | h
      · omega
      · linarith [Nat.zero_le (4 ^ n)]
    · obtain ⟨m, rfl⟩ := ho
      have e : 4 ^ (2 * m + 1) = 4 * (2 ^ m) ^ 4 := by
        have e2 : (2 ^ m) ^ 4 = 4 ^ (2 * m) := by
          rw [← pow_mul, show (4:ℕ) ^ (2 * m) = (2 ^ 2) ^ (2 * m) by norm_num, ← pow_mul]
          congr 1; ring
        rw [e2, pow_succ, mul_comm]
      rw [e]
      exact nt2_pow_four_add_four_mul_pow_four_not_prime _ _ hn (by positivity)
  have hN : 2 ≤ n ^ 4 + 4 ^ n := by linarith [Nat.zero_le (4 ^ n)]
  obtain ⟨a, b, ha, hb, hab⟩ := (Nat.not_prime_iff_exists_mul_eq hN).mp hnp
  refine ⟨a, b, ?_, ?_, hab.symm⟩
  · rcases Nat.lt_or_ge 1 a with h | h
    · exact h
    · interval_cases a
      · rw [zero_mul] at hab; linarith
      · rw [one_mul] at hab; linarith
  · rcases Nat.lt_or_ge 1 b with h | h
    · exact h
    · interval_cases b
      · rw [mul_zero] at hab; linarith
      · rw [mul_one] at hab; linarith
end

-- forge:entry an2_harmonic_two_pow_ge_v3 kind=proved origin=conjecture
section
/- Oresme's bound: the harmonic number H_{2^n} is at least 1 + n/2. -/
theorem an2_harmonic_two_pow_ge_v3 (n : ℕ) : 1 + (n : ℝ) / 2 ≤ ∑ i ∈ Finset.range (2 ^ n), (1 : ℝ) / ((i : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; omega
    rw [e, Finset.sum_range_add]
    have hne : (2 : ℝ) ^ n ≠ 0 := by positivity
    have h2 : (1 : ℝ) / 2 ≤ ∑ x ∈ Finset.range (2 ^ n), (1 : ℝ) / (((2 ^ n + x : ℕ) : ℝ) + 1) := by
      calc (1 : ℝ) / 2 = (Finset.range (2 ^ n)).card • ((1 : ℝ) / (2 ^ (n + 1) : ℝ)) := by
            rw [Finset.card_range, nsmul_eq_mul]
            push_cast
            rw [pow_succ, one_div, one_div, mul_inv, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
        _ ≤ _ := by
            apply Finset.card_nsmul_le_sum
            intro x hx
            rw [Finset.mem_range] at hx
            apply one_div_le_one_div_of_le (by positivity)
            have h : ((2 ^ n + x + 1 : ℕ) : ℝ) ≤ ((2 ^ (n + 1) : ℕ) : ℝ) := by
              apply Nat.cast_le.mpr
              omega
            push_cast at h ⊢
            linarith
    push_cast at h2 ⊢
    linarith
end

-- forge:entry an2_num_derangements_bounds_v3 kind=proved origin=conjecture
section
/- For N ≥ 2 the derangement number satisfies N!/3 ≤ D_N ≤ N!/2. -/
theorem an2_num_derangements_bounds_v3_aux1 (n : ℕ) :
    (Nat.factorial (n + 2) ≤ 3 * numDerangements (n + 2) ∧ 2 * numDerangements (n + 2) ≤ Nat.factorial (n + 2)) ∧
    (Nat.factorial (n + 3) ≤ 3 * numDerangements (n + 3) ∧ 2 * numDerangements (n + 3) ≤ Nat.factorial (n + 3)) := by
  induction n with
  | zero => simp [numDerangements, Nat.factorial]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := ih
    have hD : numDerangements (n + 1 + 3) = (n + 3) * (numDerangements (n + 2) + numDerangements (n + 3)) :=
      numDerangements_add_two (n + 2)
    have hf3 : Nat.factorial (n + 3) = (n + 3) * Nat.factorial (n + 2) := Nat.factorial_succ (n + 2)
    have hf4 : Nat.factorial (n + 1 + 3) = (n + 4) * ((n + 3) * Nat.factorial (n + 2)) := by
      rw [← hf3]; exact Nat.factorial_succ (n + 3)
    rw [hD, hf4]
    rw [hf3] at h3 h4
    generalize numDerangements (n + 2) = a at *
    generalize numDerangements (n + 3) = b at *
    generalize Nat.factorial (n + 2) = f at *
    have k1 := Nat.mul_le_mul_left (n + 3) h1
    have k2 := Nat.mul_le_mul_left (n + 3) h2
    have k3 := Nat.mul_le_mul_left (n + 3) h3
    have k4 := Nat.mul_le_mul_left (n + 3) h4
    constructor <;> nlinarith
theorem an2_num_derangements_bounds_v3 (n : ℕ) : Nat.factorial (n + 2) ≤ 3 * numDerangements (n + 2) ∧ 2 * numDerangements (n + 2) ≤ Nat.factorial (n + 2) :=
  (an2_num_derangements_bounds_v3_aux1 n).1
end

-- forge:entry an2_card_no_consecutive_fib_v3 kind=proved origin=conjecture
section
/- The number of subsets of {0,...,n-1} containing no two consecutive integers is the Fibonacci number F_{n+2}. -/
theorem an2_card_no_consecutive_fib_v3_aux1 (n : ℕ) :
    (Finset.filter (fun s : Finset ℕ => ∀ i ∈ s, i + 1 ∉ s) (Finset.range (n + 2)).powerset).card
    = (Finset.filter (fun s : Finset ℕ => ∀ i ∈ s, i + 1 ∉ s) (Finset.range (n + 1)).powerset).card
    + (Finset.filter (fun s : Finset ℕ => ∀ i ∈ s, i + 1 ∉ s) (Finset.range n).powerset).card := by
  have hset : Finset.filter (fun s : Finset ℕ => ∀ i ∈ s, i + 1 ∉ s) (Finset.range (n + 2)).powerset
      = Finset.filter (fun s : Finset ℕ => ∀ i ∈ s, i + 1 ∉ s) (Finset.range (n + 1)).powerset
      ∪ (Finset.filter (fun s : Finset ℕ => ∀ i ∈ s, i + 1 ∉ s) (Finset.range n).powerset).image
          (fun t => insert (n + 1) t) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨hs, hP⟩
      by_cases hmem : n + 1 ∈ s
      · right
        refine ⟨s.erase (n + 1), ⟨?_, ?_⟩, Finset.insert_erase hmem⟩
        · intro i hi
          have hi' := Finset.mem_erase.mp hi
          have hlt := Finset.mem_range.mp (hs hi'.2)
          have hn : i ≠ n := by
            rintro rfl
            exact hP i hi'.2 hmem
          have hn1 := hi'.1
          rw [Finset.mem_range]
          omega
        · intro i hi hi1
          exact hP i (Finset.mem_of_mem_erase hi) (Finset.mem_of_mem_erase hi1)
      · left
        refine ⟨?_, hP⟩
        intro i hi
        have hlt := Finset.mem_range.mp (hs hi)
        have hne : i ≠ n + 1 := by
          rintro rfl
          exact hmem hi
        rw [Finset.mem_range]
        omega
    · rintro (⟨hs, hP⟩ | ⟨t, ⟨ht, hP⟩, rfl⟩)
      · exact ⟨hs.trans (Finset.range_mono (by omega)), hP⟩
      · refine ⟨?_, ?_⟩
        · intro i hi
          rw [Finset.mem_range]
          rcases Finset.mem_insert.mp hi with h | h
          · omega
          · have := Finset.mem_range.mp (ht h)
            omega
        · intro i hi hi1
          rcases Finset.mem_insert.mp hi with h | h
          · rcases Finset.mem_insert.mp hi1 with h1 | h1
            · omega
            · have := Finset.mem_range.mp (ht h1)
              omega
          · have hin := Finset.mem_range.mp (ht h)
            rcases Finset.mem_insert.mp hi1 with h1 | h1
            · omega
            · exact hP i h h1
  have hdisj : Disjoint
      (Finset.filter (fun s : Finset ℕ => ∀ i ∈ s, i + 1 ∉ s) (Finset.range (n + 1)).powerset)
      ((Finset.filter (fun s : Finset ℕ => ∀ i ∈ s, i + 1 ∉ s) (Finset.range n).powerset).image
          (fun t => insert (n + 1) t)) := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    rw [Finset.mem_filter, Finset.mem_powerset] at hs
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hs'
    have := Finset.mem_range.mp (hs.1 (Finset.mem_insert_self _ _))
    omega
  have hinj : Set.InjOn (fun t : Finset ℕ => insert (n + 1) t)
      (↑(Finset.filter (fun s : Finset ℕ => ∀ i ∈ s, i + 1 ∉ s) (Finset.range n).powerset) : Set (Finset ℕ)) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at ha hb
    have ha' : n + 1 ∉ a := fun h => by
      have := Finset.mem_range.mp (ha.1 h)
      omega
    have hb' : n + 1 ∉ b := fun h => by
      have := Finset.mem_range.mp (hb.1 h)
      omega
    have hab' : insert (n + 1) a = insert (n + 1) b := hab
    calc a = (insert (n + 1) a).erase (n + 1) := (Finset.erase_insert ha').symm
      _ = (insert (n + 1) b).erase (n + 1) := by rw [hab']
      _ = b := Finset.erase_insert hb'
  rw [hset, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj]

theorem an2_card_no_consecutive_fib_v3 (n : ℕ) : (Finset.filter (fun s : Finset ℕ => ∀ i ∈ s, i + 1 ∉ s) (Finset.range n).powerset).card = Nat.fib (n + 2) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih0 ih1 =>
    rw [an2_card_no_consecutive_fib_v3_aux1, ih0, ih1, Nat.fib_add_two (n := n + 2)]
    exact add_comm _ _
end

-- forge:entry ab_t2_mul_ne_one kind=proved origin=paper
section
/- Table 2 step 6: k d_i ≠ 1 since k > 1. -/
theorem ab_t2_mul_ne_one (k d : ℕ) (hk : 1 < k) : k * d ≠ 1 := by
  aesop
end

-- forge:entry ab_fine_add kind=proved origin=paper
section
/- Sum of two fine functions (vanishing at every integer) is fine. -/
theorem ab_fine_add (f g : ℝ → ℝ) (hf : ∀ n : ℤ, f (n : ℝ) = 0) (hg : ∀ n : ℤ, g (n : ℝ) = 0) : ∀ n : ℤ, (f + g) (n : ℝ) = 0 := by
  aesop
end

-- forge:entry ab_abundant_def kind=proved origin=paper
section
/- Paper's definition of abundant (all divisors sum to more than 2n) agrees with Mathlib's Nat.Abundant (proper divisors sum > n). -/
theorem ab_abundant_def (n : ℕ) : Nat.Abundant n ↔ 2 * n < ∑ d ∈ Nat.divisors n, d := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.Abundant]
  · rw [Nat.sum_divisors_eq_sum_properDivisors_add_self]
    unfold Nat.Abundant
    omega
end

-- forge:entry ab_eight_not_perfect kind=proved origin=paper
section
/- 8 is not perfect. -/
theorem ab_eight_not_perfect : ¬ Nat.Perfect 8 := by
  unfold Nat.Perfect
  decide
end

-- forge:entry ab_fine_shift kind=proved origin=paper
section
/- Shift of a fine function by a natural number is fine. -/
theorem ab_fine_shift (f : ℝ → ℝ) (k : ℕ) (hf : ∀ n : ℤ, f (n : ℝ) = 0) : ∀ n : ℤ, (fun x : ℝ => f (x - (k : ℝ))) (n : ℝ) = 0 := by
  intro n
  have h := hf (n - (k : ℤ))
  push_cast at h
  exact h
end

-- forge:entry ab_perfect_mul_abundant_any kind=disproved origin=paper
section
/- Task 3(a) literally, k any natural number (including 0). FALSE (k = 1, k = 0). -/
theorem ab_perfect_mul_abundant_any_disproof : ¬ (∀ (n k : ℕ) (hn : Nat.Perfect n), Nat.Abundant (k * n)) := by
  intro h
  have h6 : Nat.Perfect 6 := by
    unfold Nat.Perfect
    decide
  have h2 : 1 * 6 < ∑ i ∈ Nat.properDivisors (1 * 6), i := h 6 1 h6
  revert h2
  decide
end

-- forge:entry ab_perfect_mul_abundant_pos kind=disproved origin=paper
section
/- Task 3(a) literally with N = positive integers. FALSE at k = 1, as the paper notes. -/
theorem ab_perfect_mul_abundant_pos_disproof : ¬ (∀ (n k : ℕ) (hn : Nat.Perfect n) (hk : 0 < k), Nat.Abundant (k * n)) := by
  intro h
  have h6 : Nat.Perfect 6 := by
    unfold Nat.Perfect
    decide
  have h2 : 1 * 6 < ∑ i ∈ Nat.properDivisors (1 * 6), i := h 6 1 h6 one_pos
  revert h2
  decide
end

-- forge:entry ab_perfect_one_mul_not_abundant kind=proved origin=paper
section
/- The task statement fails at k = 1 for every perfect n. -/
theorem ab_perfect_one_mul_not_abundant (n : ℕ) (hn : Nat.Perfect n) : ¬ Nat.Abundant (1 * n) := by
  rw [one_mul]
  intro h
  have h1 : ∑ i ∈ Nat.properDivisors n, i = n := hn.1
  have h2 : n < ∑ i ∈ Nat.properDivisors n, i := h
  omega
end

-- forge:entry ab_perfect_six kind=proved origin=paper
section
/- 6 is perfect. -/
theorem ab_perfect_six : Nat.Perfect 6 := by
  unfold Nat.Perfect
  decide
end

-- forge:entry ab_perfect_twenty_eight kind=proved origin=paper
section
/- 28 is perfect. -/
theorem ab_perfect_twenty_eight : Nat.Perfect 28 := by
  unfold Nat.Perfect
  decide
end

-- forge:entry ab_preserved_mul kind=proved origin=paper
section
/- If A is closed under multiplication and f, g are preserved in A then f × g is preserved in A. -/
theorem ab_preserved_mul (f g : ℝ → ℝ) (A : Set ℝ) (hA : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ A) (hf : f '' A ⊆ A) (hg : g '' A ⊆ A) : (fun x => f x * g x) '' A ⊆ A := by
  rintro _ ⟨x, hx, rfl⟩
  exact hA _ (hf ⟨x, hx, rfl⟩) _ (hg ⟨x, hx, rfl⟩)
end

-- forge:entry ab_prime_mul_prime_abundant kind=disproved origin=paper
section
/- Task 3(b) literally: product of two primes is abundant. FALSE (2*3 = 6 is perfect). -/
theorem ab_prime_mul_prime_abundant_disproof : ¬ (∀ (p q : ℕ) (hp : p.Prime) (hq : q.Prime), Nat.Abundant (p * q)) := by
  intro h
  have h2 : 2 * 3 < ∑ i ∈ Nat.properDivisors (2 * 3), i := h 2 3 Nat.prime_two Nat.prime_three
  revert h2
  decide
end

end Mathlib2
