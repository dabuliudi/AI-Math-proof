/- Mathlib2 分片 5（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0004
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry ab_prime_mul_prime_not_abundant kind=proved origin=paper
section
/- Auditor's correction of Task 3(b) (not stated in paper): a product of two primes is never abundant. -/
theorem ab_prime_mul_prime_not_abundant (p q : ℕ) (hp : p.Prime) (hq : q.Prime) : ¬ Nat.Abundant (p * q) := by
  intro h
  have hab : p * q < ∑ i ∈ Nat.properDivisors (p * q), i := h
  by_cases hpq : p = q
  · subst hpq
    have hd : ∑ i ∈ Nat.properDivisors (p ^ 2), i < p ^ 2 := hp.deficient_pow (m := 2)
    rw [pow_two] at hd
    omega
  · have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
    have hsum := Nat.Coprime.sum_divisors_mul hcop
    rw [Nat.sum_divisors_eq_sum_properDivisors_add_self, hp.sum_divisors, hq.sum_divisors] at hsum
    have h2p := hp.two_le
    have h2q := hq.two_le
    have hlt : p * q < p + q + 1 := by nlinarith
    rcases Nat.lt_or_gt_of_ne hpq with hl | hl
    · have : 3 ≤ q := by omega
      nlinarith [Nat.mul_le_mul (show 1 ≤ p - 1 by omega) (show 2 ≤ q - 1 by omega), Nat.sub_add_cancel (show 1 ≤ p by omega), Nat.sub_add_cancel (show 1 ≤ q by omega)]
    · have : 3 ≤ p := by omega
      nlinarith [Nat.mul_le_mul (show 2 ≤ p - 1 by omega) (show 1 ≤ q - 1 by omega), Nat.sub_add_cancel (show 1 ≤ p by omega), Nat.sub_add_cancel (show 1 ≤ q by omega)]
end

-- forge:entry ab_six_le_of_perfect kind=proved origin=paper
section
/- 6 is the smallest perfect number. -/
theorem ab_six_le_of_perfect (n : ℕ) (hn : Nat.Perfect n) : 6 ≤ n := by
  have h : ∀ m < 6, ¬ (∑ i ∈ Nat.properDivisors m, i = m ∧ 0 < m) := by decide
  by_contra hlt
  exact h n (by omega) hn
end

-- forge:entry ab_sqrt_three_add_sqrt_five kind=proved origin=paper
section
/- sqrt 3 + sqrt 5 < 4. -/
theorem ab_sqrt_three_add_sqrt_five : Real.sqrt 3 + Real.sqrt 5 < 4 := by
  have h3 : Real.sqrt 3 < 7 / 4 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have h5 : Real.sqrt 5 < 9 / 4 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith
end

-- forge:entry ab_t2_mul_mem_divisors kind=proved origin=paper
section
/- Table 2 step 5: if d divides n then k d is a divisor of k n. -/
theorem ab_t2_mul_mem_divisors (n k d : ℕ) (hk : 0 < k) (hd : d ∈ Nat.divisors n) : k * d ∈ Nat.divisors (k * n) := by
  rw [Nat.mem_divisors] at hd ⊢
  exact ⟨Nat.mul_dvd_mul_left k hd.1, Nat.mul_ne_zero hk.ne' hd.2⟩
end

-- forge:entry ab_t2_one_mem_divisors kind=proved origin=paper
section
/- Table 2 step 7: 1 is a divisor of kn. -/
theorem ab_t2_one_mem_divisors (n k : ℕ) (hn : Nat.Perfect n) (hk : 1 < k) : 1 ∈ Nat.divisors (k * n) := by
  rw [Nat.mem_divisors]
  exact ⟨one_dvd _, Nat.mul_ne_zero (by omega) hn.2.ne'⟩
end

-- forge:entry ab_t2_sum_divisors_ge kind=proved origin=paper
section
/- Table 2 step 9: sum of divisors of kn is at least 2kn + 1 (the k d_i together with 1). -/
theorem ab_t2_sum_divisors_ge (n k : ℕ) (hn : Nat.Perfect n) (hk : 1 < k) : 2 * (k * n) + 1 ≤ ∑ d ∈ Nat.divisors (k * n), d := by
  have hn0 : 0 < n := hn.2
  have hs : ∑ d ∈ Nat.divisors n, d = 2 * n := (Nat.perfect_iff_sum_divisors_eq_two_mul hn0).mp hn
  have hsub : insert 1 ((Nat.divisors n).image (fun d => k * d)) ⊆ Nat.divisors (k * n) := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_image] at hx
    rw [Nat.mem_divisors]
    refine ⟨?_, Nat.mul_ne_zero (by omega) hn0.ne'⟩
    rcases hx with rfl | ⟨d, hd, rfl⟩
    · exact one_dvd _
    · exact Nat.mul_dvd_mul_left k (Nat.dvd_of_mem_divisors hd)
  have h1 : (1 : ℕ) ∉ (Nat.divisors n).image (fun d => k * d) := by
    intro h
    rw [Finset.mem_image] at h
    obtain ⟨d, _, hd⟩ := h
    have hk1 : k ∣ 1 := Dvd.intro d hd
    have := Nat.le_of_dvd one_pos hk1
    omega
  have heq : ∑ x ∈ insert 1 ((Nat.divisors n).image (fun d => k * d)), x = 2 * (k * n) + 1 := by
    rw [Finset.sum_insert h1, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (by omega) h), ← Finset.mul_sum, hs]
    ring
  rw [← heq]
  exact Finset.sum_le_sum_of_subset hsub
end

-- forge:entry ab_t2_sum_mul_divisors kind=proved origin=paper
section
/- Table 2 step 8: sum of k d_i over divisors d_i of perfect n equals 2kn. -/
theorem ab_t2_sum_mul_divisors (n k : ℕ) (hn : Nat.Perfect n) : ∑ d ∈ Nat.divisors n, k * d = 2 * (k * n) := by
  rw [← Finset.mul_sum, (Nat.perfect_iff_sum_divisors_eq_two_mul hn.2).1 hn]
  ring
end

-- forge:entry ab_perfect_mul_abundant kind=proved origin=paper
section
/- Corrected task: a proper multiple (k > 1) of a perfect number is abundant. -/
theorem ab_perfect_mul_abundant (n k : ℕ) (hn : Nat.Perfect n) (hk : 1 < k) : Nat.Abundant (k * n) := by
  have h := ab_t2_sum_divisors_ge n k hn hk
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self] at h
  show k * n < ∑ i ∈ Nat.properDivisors (k * n), i
  omega
end

-- forge:entry is_sophie_germain_prime kind=definition origin=definition
section
/- Sophie Germain 素数：p 与 2p+1 都是素数 -/
def is_sophie_germain_prime (p : ℕ) : Prop := Nat.Prime p ∧ Nat.Prime (2 * p + 1)
end

-- forge:entry r3_imo1988_vieta_jumping_s1h1 kind=proved origin=decomposition
section
/- r3_imo1988_vieta_jumping 的证明骨架中第 1 个空洞 -/
theorem r3_imo1988_vieta_jumping_s1h1 : ∀ (q a b : ℕ), 0 < b → a ^ 2 + b ^ 2 = q * (a * b + 1) → a ≤ q * b := by
  intro q a b hb e
  by_contra hlt
  push_neg at hlt
  obtain ⟨d, rfl⟩ : ∃ d, a = q * b + d + 1 := ⟨a - q * b - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  nlinarith [Nat.zero_le (q * c * d), Nat.zero_le (q * c), Nat.zero_le (q * d), Nat.zero_le (d ^ 2), Nat.zero_le (c ^ 2)]
end

-- forge:entry r3_imo1988_vieta_jumping_s1h2 kind=proved origin=decomposition
section
/- r3_imo1988_vieta_jumping 的证明骨架中第 2 个空洞 -/
theorem r3_imo1988_vieta_jumping_s1h2 : (∀ (q a b : ℕ), 0 < b → a ^ 2 + b ^ 2 = q * (a * b + 1) → a ≤ q * b) → ∀ (q a b : ℕ), a ≤ q * b → a ^ 2 + b ^ 2 = q * (a * b + 1) → (q * b - a) ^ 2 + b ^ 2 = q * ((q * b - a) * b + 1) := by
  intro _ q a b h e
  have e' : (a : ℤ) ^ 2 + b ^ 2 = q * (a * b + 1) := by exact_mod_cast e
  zify [h]
  linear_combination e'
end

-- forge:entry r3_mordell_y_sq_eq_x_cube_add_seven_s1h2 kind=proved origin=decomposition
section
/- r3_mordell_y_sq_eq_x_cube_add_seven 的证明骨架中第 2 个空洞 -/
theorem r3_mordell_y_sq_eq_x_cube_add_seven_s1h2 : ∀ (a b : ℤ), b ^ 2 = a ^ 3 + 7 → a % 2 = 1 := by
  intro a b h
  by_contra hne
  obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
  have e : (2 * k) ^ 3 + 7 = 8 * k ^ 3 + 7 := by ring
  have h8 : b ^ 2 % 8 = 7 := by
    rw [h, e]
    generalize k ^ 3 = m
    omega
  have hb : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by omega
  rcases hb with h' | h' | h' | h' | h' | h' | h' | h' <;> simp [pow_two, Int.mul_emod, h'] at h8
end

-- forge:entry r3_imo1988_vieta_jumping_s1h3 kind=proved origin=decomposition
section
/- r3_imo1988_vieta_jumping 的证明骨架中第 3 个空洞 -/
theorem r3_imo1988_vieta_jumping_s1h3 : (∀ (q a b : ℕ), 0 < b → a ^ 2 + b ^ 2 = q * (a * b + 1) → a ≤ q * b) → (∀ (q a b : ℕ), a ≤ q * b → a ^ 2 + b ^ 2 = q * (a * b + 1) → (q * b - a) ^ 2 + b ^ 2 = q * ((q * b - a) * b + 1)) → ∀ (q a b : ℕ), 0 < b → b ≤ a → a ^ 2 + b ^ 2 = q * (a * b + 1) → q * b - a < a := by
  intro _ _ q a b hb hba e
  by_contra hcon
  have h2 : 2 * a ≤ q * b := by omega
  have h3 : 2 * a * a ≤ q * b * a := Nat.mul_le_mul_right a h2
  have h4 : b * b ≤ a * a := Nat.mul_le_mul hba hba
  have hq : q = 0 := by nlinarith
  subst hq
  omega
end

-- forge:entry r3_mordell_y_sq_eq_x_cube_add_seven_s1h3 kind=proved origin=decomposition
section
/- r3_mordell_y_sq_eq_x_cube_add_seven 的证明骨架中第 3 个空洞 -/
theorem r3_mordell_y_sq_eq_x_cube_add_seven_s1h3 : ∀ (a : ℤ), a % 2 = 1 → (a ^ 2 - 2 * a + 4).natAbs % 4 = 3 := by
  intro a ha
  obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k + 1 := ⟨a / 2, by omega⟩
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (sq_nonneg k)
  have e : (2 * k + 1) ^ 2 - 2 * (2 * k + 1) + 4 = ((4 * n + 3 : ℕ) : ℤ) := by
    push_cast; rw [← hn]; ring
  rw [e, Int.natAbs_natCast]; omega
end

-- forge:entry r3_imo1988_vieta_jumping kind=proved origin=conjecture
section
/- IMO 1988 Q6: if ab+1 divides a^2+b^2 then the quotient is a perfect square. Proof idea: Vieta jumping — fix the quotient q, take a solution with a+b minimal and a ≥ b, the other root a' = q b - a = (b^2 - q)/a of the quadratic satisfies 0 ≤ a' < a (needs a' ≥ 0 from positivity of a'b+1), so minimality forces a' = 0 and q = b^2. -/
theorem r3_imo1988_vieta_jumping (a b : ℕ) (h : a * b + 1 ∣ a ^ 2 + b ^ 2) : ∃ k : ℕ, a ^ 2 + b ^ 2 = k ^ 2 * (a * b + 1) := by
  revert a b
  have h_nonneg : ∀ q a b : ℕ, 0 < b → a ^ 2 + b ^ 2 = q * (a * b + 1) → a ≤ q * b := by
    (first | exact Mathlib2.r3_imo1988_vieta_jumping_s1h1 | apply Mathlib2.r3_imo1988_vieta_jumping_s1h1 <;> assumption | simpa using Mathlib2.r3_imo1988_vieta_jumping_s1h1)
  have h_root : ∀ q a b : ℕ, a ≤ q * b → a ^ 2 + b ^ 2 = q * (a * b + 1) →
      (q * b - a) ^ 2 + b ^ 2 = q * ((q * b - a) * b + 1) := by
    (first | exact Mathlib2.r3_imo1988_vieta_jumping_s1h2 | apply Mathlib2.r3_imo1988_vieta_jumping_s1h2 <;> assumption | simpa using Mathlib2.r3_imo1988_vieta_jumping_s1h2)
  have h_lt : ∀ q a b : ℕ, 0 < b → b ≤ a → a ^ 2 + b ^ 2 = q * (a * b + 1) → q * b - a < a := by
    (first | exact Mathlib2.r3_imo1988_vieta_jumping_s1h3 | apply Mathlib2.r3_imo1988_vieta_jumping_s1h3 <;> assumption | simpa using Mathlib2.r3_imo1988_vieta_jumping_s1h3)
  have key : ∀ q n a b : ℕ, a + b ≤ n → b ≤ a → a ^ 2 + b ^ 2 = q * (a * b + 1) → ∃ k : ℕ, q = k ^ 2 := by
    intro q n
    induction n with
    | zero =>
      intro a b hn hba e
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha hb
      simp at e
      exact ⟨0, by simp [← e]⟩
    | succ n ih =>
      intro a b hn hba e
      rcases Nat.eq_zero_or_pos b with hb | hb
      · subst hb
        simp at e
        exact ⟨a, e.symm⟩
      · have h1 := h_nonneg q a b hb e
        have h2 := h_root q a b h1 e
        have h3 := h_lt q a b hb hba e
        rcases le_total b (q * b - a) with hbc | hcb
        · exact ih (q * b - a) b (by omega) hbc h2
        · refine ih b (q * b - a) (by omega) hcb ?_
          rw [add_comm, mul_comm b (q * b - a)]
          exact h2
  intro a b h
  obtain ⟨q, hq⟩ := h
  rcases le_total b a with hba | hab
  · obtain ⟨k, hk⟩ := key q (a + b) a b le_rfl hba (by rw [hq, mul_comm])
    exact ⟨k, by rw [hq, hk, mul_comm]⟩
  · obtain ⟨k, hk⟩ := key q (b + a) b a le_rfl hab (by rw [add_comm, mul_comm b a, hq, mul_comm])
    exact ⟨k, by rw [hq, hk, mul_comm]⟩
end

-- forge:entry r3_ramsey_three_three_s1h1 kind=proved origin=decomposition
section
/- r3_ramsey_three_three 的证明骨架中第 1 个空洞 -/
theorem r3_ramsey_three_three_s1h1 : ∀ (V : Type) [inst : Fintype V], 6 ≤ Fintype.card V → ∀ (G H : SimpleGraph V) (x y z : V), H.Adj x y → H.Adj x z → H.Adj y z → ¬H.CliqueFree 3 := by
  intro V _ _ _ H x y z hxy hxz hyz hfree
  classical
  exact hfree {x, y, z} (SimpleGraph.is3Clique_triple_iff.2 ⟨hxy, hxz, hyz⟩)
end

-- forge:entry r3_mordell_y_sq_eq_x_cube_add_seven_s1h1 kind=proved origin=decomposition
section
/- r3_mordell_y_sq_eq_x_cube_add_seven 的证明骨架中第 1 个空洞 -/
theorem r3_mordell_y_sq_eq_x_cube_add_seven_s1h1 : ∀ (N : ℕ), N % 4 = 3 → ∃ p, Nat.Prime p ∧ p % 4 = 3 ∧ p ∣ N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    by_cases hp : N.Prime
    · exact ⟨N, hp, hN, dvd_rfl⟩
    · have h2 : 2 ≤ N := by omega
      obtain ⟨a, ha, ha1, haN⟩ := Nat.exists_dvd_of_not_prime h2 hp
      obtain ⟨b, rfl⟩ := ha
      have ha2 : 2 ≤ a := by
        rcases a with _ | _ | a
        · simp at h2
        · simp at ha1
        · omega
      have hb2 : 2 ≤ b := by
        rcases b with _ | _ | b
        · simp at h2
        · simp at haN
        · omega
      have hmm := Nat.mul_mod a b 4
      rw [hN] at hmm
      have hr := Nat.mod_lt a (show 0 < 4 by norm_num)
      have hs := Nat.mod_lt b (show 0 < 4 by norm_num)
      have hgen : ∀ r s : ℕ, r < 4 → s < 4 → 3 = r * s % 4 → r = 3 ∨ s = 3 := by
        intro r s hr hs
        interval_cases r <;> interval_cases s <;> omega
      have hcase : a % 4 = 3 ∨ b % 4 = 3 := hgen _ _ hr hs hmm
      rcases hcase with h | h
      · obtain ⟨p, hp, hp3, hpd⟩ := ih a (by nlinarith) h
        exact ⟨p, hp, hp3, hpd.mul_right b⟩
      · obtain ⟨p, hp, hp3, hpd⟩ := ih b (by nlinarith) h
        exact ⟨p, hp, hp3, hpd.mul_left a⟩
end

-- forge:entry r3_mordell_y_sq_eq_x_cube_add_seven kind=proved origin=conjecture
section
/- V. A. Lebesgue: the Mordell equation y^2 = x^3 + 7 has no integer solutions. Builds on Mathlib2.nt2_prime_three_mod_four_dvd_sq_add_sq (a prime p ≡ 3 mod 4 dividing y^2+1^2 would divide 1). Proof idea: x even gives y^2 ≡ 7 mod 8, impossible; for x odd write y^2 + 1 = (x+2)(x^2-2x+4), where x^2-2x+4 = (x-1)^2+3 is positive and ≡ 3 mod 4, hence has a prime factor p ≡ 3 mod 4 (lemma: a product of primes each ≡ 1 mod 4 is ≡ 1 mod 4), and p | y^2+1 contradicts the catalog theorem. -/
theorem r3_mordell_y_sq_eq_x_cube_add_seven (x y : ℤ) : y ^ 2 ≠ x ^ 3 + 7 := by
  have key : ∀ N : ℕ, N % 4 = 3 → ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ p ∣ N := by
    clear x y
    (first | exact Mathlib2.r3_mordell_y_sq_eq_x_cube_add_seven_s1h1 | apply Mathlib2.r3_mordell_y_sq_eq_x_cube_add_seven_s1h1 <;> assumption | simpa using Mathlib2.r3_mordell_y_sq_eq_x_cube_add_seven_s1h1)
  have hodd : ∀ a b : ℤ, b ^ 2 = a ^ 3 + 7 → a % 2 = 1 := by
    clear x y key
    (first | exact Mathlib2.r3_mordell_y_sq_eq_x_cube_add_seven_s1h2 | apply Mathlib2.r3_mordell_y_sq_eq_x_cube_add_seven_s1h2 <;> assumption | simpa using Mathlib2.r3_mordell_y_sq_eq_x_cube_add_seven_s1h2)
  have hmod : ∀ a : ℤ, a % 2 = 1 → (a ^ 2 - 2 * a + 4).natAbs % 4 = 3 := by
    clear x y key hodd
    (first | exact Mathlib2.r3_mordell_y_sq_eq_x_cube_add_seven_s1h3 | apply Mathlib2.r3_mordell_y_sq_eq_x_cube_add_seven_s1h3 <;> assumption | simpa using Mathlib2.r3_mordell_y_sq_eq_x_cube_add_seven_s1h3)
  intro h
  obtain ⟨p, hp, hp3, hpd⟩ := key _ (hmod x (hodd x y h))
  have hd : (p : ℤ) ∣ y ^ 2 + 1 ^ 2 := by
    have h1 : (p : ℤ) ∣ x ^ 2 - 2 * x + 4 := Int.natCast_dvd.mpr hpd
    have e : y ^ 2 + 1 ^ 2 = (x + 2) * (x ^ 2 - 2 * x + 4) := by rw [h]; ring
    rw [e]; exact Dvd.dvd.mul_left h1 _
  have h2 := (nt2_prime_three_mod_four_dvd_sq_add_sq p hp hp3 y 1 hd).2
  have h1 : p ∣ 1 := by exact_mod_cast h2
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
end

-- forge:entry r3_ramsey_three_three_pigeonhole kind=proved origin=conjecture
section
/- Pigeonhole step of R(3,3)<=6 (hole 2 of the r3_ramsey_three_three skeleton; proposed by hand because sketch left an orphan child that blocks re-sketching): in a graph on >= 6 vertices some vertex v has three distinct neighbours or three distinct non-neighbours. -/
theorem r3_ramsey_three_three_pigeonhole (V : Type) [Fintype V] (h : 6 ≤ Fintype.card V) (G : SimpleGraph V) : ∃ v x y z : V, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ ((G.Adj v x ∧ G.Adj v y ∧ G.Adj v z) ∨ (Gᶜ.Adj v x ∧ Gᶜ.Adj v y ∧ Gᶜ.Adj v z)) := by
  classical
  have hpos : 0 < Fintype.card V := by omega
  obtain ⟨v⟩ := Fintype.card_pos_iff.1 hpos
  have hcov : (Finset.univ.erase v) ⊆ Finset.univ.filter (G.Adj v) ∪ Finset.univ.filter (Gᶜ.Adj v) := by
    intro w hw
    have hne : v ≠ w := fun e => (Finset.mem_erase.1 hw).1 e.symm
    by_cases hA : G.Adj v w
    · exact Finset.mem_union_left _ (by simp [hA])
    · exact Finset.mem_union_right _ (by simp [SimpleGraph.compl_adj, hne, hA])
  have hc := (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
  rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ] at hc
  rcases (by omega : 2 < (Finset.univ.filter (G.Adj v)).card ∨ 2 < (Finset.univ.filter (Gᶜ.Adj v)).card) with h1 | h1
  · obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.1 h1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy hz
    exact ⟨v, x, y, z, hxy, hxz, hyz, Or.inl ⟨hx, hy, hz⟩⟩
  · obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.1 h1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy hz
    exact ⟨v, x, y, z, hxy, hxz, hyz, Or.inr ⟨hx, hy, hz⟩⟩
end

-- forge:entry r3_ramsey_three_three kind=proved origin=conjecture
section
/- R(3,3) ≤ 6: every graph on at least 6 vertices contains a triangle or its complement does. Proof idea: pick a vertex v; among the ≥ 5 other vertices, pigeonhole gives 3 neighbours or 3 non-neighbours; if two of the 3 neighbours are adjacent we get a triangle in G with v, otherwise they form a triangle in the complement (and symmetrically). -/
theorem r3_ramsey_three_three (V : Type) [Fintype V] (h : 6 ≤ Fintype.card V) (G : SimpleGraph V) : ¬ G.CliqueFree 3 ∨ ¬ Gᶜ.CliqueFree 3 := by
  classical
  have tri := Mathlib2.r3_ramsey_three_three_s1h1 V h G
  have pig := Mathlib2.r3_ramsey_three_three_pigeonhole V h G
  have key : ∀ (H : SimpleGraph V) (v x y z : V), x ≠ y → x ≠ z → y ≠ z →
      H.Adj v x → H.Adj v y → H.Adj v z → ¬ H.CliqueFree 3 ∨ ¬ Hᶜ.CliqueFree 3 := by
    intro H v x y z hxy hxz hyz hx hy hz
    by_cases h1 : H.Adj x y
    · exact Or.inl (tri H v x y hx hy h1)
    by_cases h2 : H.Adj x z
    · exact Or.inl (tri H v x z hx hz h2)
    by_cases h3 : H.Adj y z
    · exact Or.inl (tri H v y z hy hz h3)
    · exact Or.inr (tri Hᶜ x y z ((SimpleGraph.compl_adj _ _ _).2 ⟨hxy, h1⟩)
        ((SimpleGraph.compl_adj _ _ _).2 ⟨hxz, h2⟩) ((SimpleGraph.compl_adj _ _ _).2 ⟨hyz, h3⟩))
  obtain ⟨v, x, y, z, hxy, hxz, hyz, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩ := pig
  · exact key G v x y z hxy hxz hyz h1 h2 h3
  · have := key Gᶜ v x y z hxy hxz hyz h1 h2 h3
    rw [compl_compl] at this
    exact this.symm
end

end Mathlib2
