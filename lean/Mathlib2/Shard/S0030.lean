/- Mathlib2 分片 30（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0003
import Mathlib2.Shard.S0004
import Mathlib2.Shard.S0005
import Mathlib2.Shard.S0008
import Mathlib2.Shard.S0009
import Mathlib2.Shard.S0023
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry arith_odd_dvd_sq_add_one_mod_four kind=proved origin=conjecture
section
/- Every odd divisor of n² + 1 is ≡ 1 (mod 4) — Uses Mathlib2.nt2_prime_three_mod_four_dvd_sq_add_sq at step 1 (with b = 1) to show no prime ≡ 3 mod 4 divides n²+1; so all prime factors of d are ≡ 1 mod 4, and a product of such numbers is ≡ 1 mod 4 (induction on d). -/
theorem arith_odd_dvd_sq_add_one_mod_four (n d : ℕ) (hd : d ∣ n ^ 2 + 1) (ho : Odd d) : d % 4 = 1 := by
  induction d using Nat.recOnMul with
  | zero => exact absurd ho (by decide)
  | one => rfl
  | prime p hp =>
    have h3 : p % 4 ≠ 3 := by
      intro h3
      have hd' : (p : ℤ) ∣ (n : ℤ) ^ 2 + 1 ^ 2 := by
        have : ((n ^ 2 + 1 : ℕ) : ℤ) = (n : ℤ) ^ 2 + 1 ^ 2 := by push_cast; ring
        rw [← this]; exact_mod_cast hd
      have := (Mathlib2.nt2_prime_three_mod_four_dvd_sq_add_sq p hp h3 n 1 hd').2
      have h1 : p ∣ 1 := by exact_mod_cast this
      exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
    obtain ⟨c, hc⟩ := ho
    omega
  | mul a b iha ihb =>
    have hoa : Odd a := (Nat.odd_mul.mp ho).1
    have hob : Odd b := (Nat.odd_mul.mp ho).2
    have ha := iha (Dvd.dvd.trans (Dvd.intro _ rfl) hd) hoa
    have hb := ihb (Dvd.dvd.trans (Dvd.intro_left _ rfl) hd) hob
    rw [Nat.mul_mod, ha, hb]
end

-- forge:entry arith_totient_pow_add_sigma_pow kind=proved origin=conjecture
section
/- Power-mean extension of Sandor–Atanassov: φ(n)^k + σ(n)^k ≥ 2n^k for n ≥ 2 — Uses Mathlib2.p5_lemma2 at step 1 (φ + σ ≥ 2n), then convexity of x^k: ((a+b)/2)^k ≤ (a^k+b^k)/2 (inner_le_nnorm_mul_norm / add_pow_le_pow_mul_pow_of_add_eq_one, or induction on k via Chebyshev). -/
theorem arith_totient_pow_add_sigma_pow_aux1 (a b n k : ℕ) (h : 2 * n ≤ a + b) : 2 * n ^ k ≤ a ^ k + b ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have key : a * b ^ k + b * a ^ k ≤ a * a ^ k + b * b ^ k := by
      rcases le_total a b with hab | hab
      · have hxy : a ^ k ≤ b ^ k := Nat.pow_le_pow_left hab k
        obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
        obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hxy
        rw [he]; nlinarith [Nat.zero_le (c * e)]
      · have hxy : b ^ k ≤ a ^ k := Nat.pow_le_pow_left hab k
        obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
        obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hxy
        rw [he]; nlinarith [Nat.zero_le (c * e)]
    have hm := Nat.mul_le_mul h ih
    rw [pow_succ, pow_succ, pow_succ]
    nlinarith

theorem arith_totient_pow_add_sigma_pow (n k : ℕ) (hn : 2 ≤ n) : 2 * n ^ k ≤ n.totient ^ k + ArithmeticFunction.sigma 1 n ^ k :=
  arith_totient_pow_add_sigma_pow_aux1 _ _ n k (Mathlib2.p5_lemma2 n hn)
end

-- forge:entry calc_sum_card_fixed_points_perm kind=proved origin=conjecture
section
/- Total number of fixed points over all permutations of Fin n (n ≥ 1) is n! (expected number of fixed points is 1) — double count pairs (σ,i) with σ i = i: each i has (n−1)! stabiliser elements (MulAction.card stabilizer / Equiv.Perm.decomposeFin), so total n·(n−1)!. -/
theorem calc_sum_card_fixed_points_perm_aux1 {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) :
    ((Finset.univ : Finset (Equiv.Perm α)).filter (fun σ => ∀ a ∈ S, σ a = a)).card
      = (Fintype.card α - S.card).factorial := by
  rw [← Fintype.card_subtype]
  have e : {σ : Equiv.Perm α // ∀ a ∈ S, σ a = a} ≃ Equiv.Perm {a : α // a ∉ S} :=
    (Equiv.subtypeEquivRight (fun σ => by simp only [not_not])).trans (Equiv.Perm.subtypeEquivSubtypePerm (fun a => a ∉ S)).symm
  rw [Fintype.card_congr e, Fintype.card_perm]
  congr 1
  rw [Fintype.card_subtype_compl]
  simp

theorem calc_sum_card_fixed_points_perm (n : ℕ) (hn : 0 < n) : ∑ σ : Equiv.Perm (Fin n), (Finset.univ.filter (fun i => σ i = i)).card = n.factorial := by
  calc ∑ σ : Equiv.Perm (Fin n), (Finset.univ.filter (fun i => σ i = i)).card
      = ∑ σ : Equiv.Perm (Fin n), ∑ i : Fin n, if σ i = i then 1 else 0 := by
        simp only [Finset.card_filter]
    _ = ∑ i : Fin n, ∑ σ : Equiv.Perm (Fin n), if σ i = i then 1 else 0 := Finset.sum_comm
    _ = ∑ i : Fin n, (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ i = i)).card := by
        simp only [Finset.card_filter]
    _ = ∑ i : Fin n, (n - 1).factorial := by
        apply Finset.sum_congr rfl
        intro i _
        have := calc_sum_card_fixed_points_perm_aux1 ({i} : Finset (Fin n))
        simpa using this
    _ = n.factorial := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
        simp [Nat.factorial_succ]
end

-- forge:entry calc_tsum_inv_three_consecutive kind=proved origin=conjecture
section
/- ∑_{n≥1} 1/(n(n+1)(n+2)) = 1/4 — telescoping: term = (1/2)(1/((n+1)(n+2)) − 1/((n+2)(n+3))); HasSum via tendsto of partial sums 1/4 − 1/(2(N+1)(N+2)). -/
theorem calc_tsum_inv_three_consecutive_aux1 (f g : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (h : ∀ n, f n = g n - g (n + 1)) (hg : Filter.Tendsto g Filter.atTop (nhds 0)) : HasSum f (g 0) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg hf]
  have hs : ∀ N, ∑ i ∈ Finset.range N, f i = g 0 - g N := by
    intro N
    induction N with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih, h k]; ring
  simp_rw [hs]
  simpa using (tendsto_const_nhds (x := g 0)).sub hg

theorem calc_tsum_inv_three_consecutive : ∑' n : ℕ, 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) = 1 / 4 := by
  have hg : Filter.Tendsto (fun n : ℕ => 1 / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2))) Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) (tendsto_one_div_add_atTop_nhds_zero_nat : Filter.Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) Filter.atTop (nhds 0))
    apply one_div_le_one_div_of_le (by positivity)
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have h := calc_tsum_inv_three_consecutive_aux1 (fun n : ℕ => 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) _ (fun n => by positivity) (fun n => by push_cast; field_simp; ring) hg
  rw [h.tsum_eq]
  norm_num
end

-- forge:entry calc_tsum_inv_odd_consecutive kind=proved origin=conjecture
section
/- ∑ 1/((2n+1)(2n+3)) = 1/2 — telescoping, partial sums (1/2)(1 − 1/(2N+1)). -/
theorem calc_tsum_inv_odd_consecutive : ∑' n : ℕ, 1 / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) = 1 / 2 := by
  have hg : Filter.Tendsto (fun n : ℕ => 1 / (2 * (2 * (n : ℝ) + 1))) Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) (tendsto_one_div_add_atTop_nhds_zero_nat : Filter.Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) Filter.atTop (nhds 0))
    apply one_div_le_one_div_of_le (by positivity)
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have h := calc_tsum_inv_three_consecutive_aux1 (fun n : ℕ => 1 / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3))) _ (fun n => by positivity) (fun n => by push_cast; field_simp; ring) hg
  rw [h.tsum_eq]
  norm_num
end

-- forge:entry calc_tsum_sq_div_two_pow kind=proved origin=conjecture
section
/- ∑ n²/2ⁿ = 6 — write n² = n(n−1)+n, use hasSum_coe_mul_geometric_of_norm_lt_one and tsum_choose_mul_geometric (or differentiate geometric series twice) at r = 1/2. -/
theorem calc_tsum_sq_div_two_pow : ∑' n : ℕ, (n : ℝ) ^ 2 / 2 ^ n = 6 := by
  have t := fun k : ℕ => tendsto_pow_const_div_const_pow_of_one_lt k (r := (2:ℝ)) (by norm_num)
  have hg : Filter.Tendsto (fun n : ℕ => (2 * (n : ℝ) ^ 2 + 4 * n + 6) / 2 ^ n) Filter.atTop (nhds 0) := by
    have := (((t 2).const_mul 2).add ((t 1).const_mul 4)).add ((t 0).const_mul 6)
    simp only [mul_zero, add_zero] at this
    refine this.congr (fun n => ?_)
    ring
  have h := calc_tsum_inv_three_consecutive_aux1 (fun n : ℕ => (n : ℝ) ^ 2 / 2 ^ n) _ (fun n => by positivity) (fun n => by push_cast; rw [pow_succ]; field_simp; ring) hg
  rw [h.tsum_eq]
  norm_num
end

-- forge:entry arith_prod_properDivisors_eq_self_iff kind=proved origin=conjecture
section
/- The product of the proper divisors of n ≥ 2 equals n iff n has exactly four divisors — with P the proper-divisor product, ∏ divisors = n·P; Uses Mathlib2.nt2_prod_divisors_sq at the key step: (nP)² = n^τ(n), so P = n iff n⁴ = n^τ(n) iff τ(n) = 4 (pow injective for n ≥ 2). -/
theorem arith_prod_properDivisors_eq_self_iff (n : ℕ) (hn : 2 ≤ n) : ∏ d ∈ n.properDivisors, d = n ↔ n.divisors.card = 4 := by
  have h := Mathlib2.nt2_prod_divisors_sq n
  have hd : ∏ d ∈ n.divisors, d = n * ∏ d ∈ n.properDivisors, d := by
    rw [← Nat.insert_self_properDivisors (by omega : n ≠ 0), Finset.prod_insert (by simp [Nat.mem_properDivisors])]
  rw [hd] at h
  constructor
  · intro hP
    rw [hP] at h
    have h4 : n ^ 4 = n ^ n.divisors.card := by rw [← h]; ring
    exact (Nat.pow_right_injective hn h4).symm
  · intro h4
    rw [h4] at h
    have h2 : (n * ∏ d ∈ n.properDivisors, d) ^ 2 = (n * n) ^ 2 := by rw [h]; ring
    have h3 := Nat.pow_left_injective (by norm_num : (2:ℕ) ≠ 0) h2
    exact Nat.eq_of_mul_eq_mul_left (by omega) h3
end

-- forge:entry calc_sum_sq_card_fixed_points_perm kind=proved origin=conjecture
section
/- Second moment of fixed-point count: ∑_σ fix(σ)² = 2·n! for n ≥ 2 (variance 1) — count triples (σ,i,j) with both fixed: n·(n−1)! diagonal plus n(n−1)·(n−2)! off-diagonal; equivalently Burnside for the action on ordered pairs (2 orbits). -/
theorem calc_sum_sq_card_fixed_points_perm (n : ℕ) (hn : 2 ≤ n) : ∑ σ : Equiv.Perm (Fin n), (Finset.univ.filter (fun i => σ i = i)).card ^ 2 = 2 * n.factorial := by
  have h : ∀ σ : Equiv.Perm (Fin n), (Finset.univ.filter (fun i => σ i = i)).card ^ 2
      = ∑ i : Fin n, ∑ j : Fin n, if (σ i = i ∧ σ j = j) then 1 else 0 := by
    intro σ
    rw [sq, Finset.card_filter, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h1 : σ i = i <;> by_cases h2 : σ j = j <;> simp [h1, h2]
  have hc : ∀ i j : Fin n, (∑ σ : Equiv.Perm (Fin n), if (σ i = i ∧ σ j = j) then 1 else 0)
      = (n - ({i, j} : Finset (Fin n)).card).factorial := by
    intro i j
    have := calc_sum_card_fixed_points_perm_aux1 ({i, j} : Finset (Fin n))
    rw [Fintype.card_fin] at this
    rw [← this, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro σ _
    simp
  have hi : ∀ i : Fin n, (∑ j : Fin n, (n - ({i, j} : Finset (Fin n)).card).factorial)
      = (n - 1).factorial + (n - 1) * (n - 2).factorial := by
    intro i
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · simp
    · rw [Finset.sum_congr rfl (g := fun _ => (n - 2).factorial)]
      · simp
      · intro j hj
        have hne : i ≠ j := fun h => (Finset.mem_erase.mp hj).1 h.symm
        rw [Finset.card_pair hne]
  simp only [h]
  rw [Finset.sum_comm]
  simp only [Finset.sum_comm (s := (Finset.univ : Finset (Equiv.Perm (Fin n)))), hc, hi]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp [Nat.factorial_succ]
  ring
end

-- forge:entry calc_tsum_cube_div_two_pow kind=proved origin=conjecture
section
/- ∑ n³/2ⁿ = 26 — expand n³ in binomials C(n,1)+6C(n,2)+6C(n,3) and use ∑ C(n,k) rⁿ = rᵏ/(1−r)^(k+1) at r = 1/2; or telescoping with S(n)= -(n³+3n²+9n+13)/2^(n-1). -/
theorem calc_tsum_cube_div_two_pow : ∑' n : ℕ, (n : ℝ) ^ 3 / 2 ^ n = 26 := by
  have t := fun k : ℕ => tendsto_pow_const_div_const_pow_of_one_lt k (r := (2:ℝ)) (by norm_num)
  have hg : Filter.Tendsto (fun n : ℕ => (2 * (n : ℝ) ^ 3 + 6 * (n : ℝ) ^ 2 + 18 * n + 26) / 2 ^ n) Filter.atTop (nhds 0) := by
    have := ((((t 3).const_mul 2).add ((t 2).const_mul 6)).add ((t 1).const_mul 18)).add ((t 0).const_mul 26)
    simp only [mul_zero, add_zero] at this
    refine this.congr (fun n => ?_)
    ring
  have h := calc_tsum_inv_three_consecutive_aux1 (fun n : ℕ => (n : ℝ) ^ 3 / 2 ^ n) _ (fun n => by positivity) (fun n => by push_cast; rw [pow_succ]; field_simp; ring) hg
  rw [h.tsum_eq]
  norm_num
end

-- forge:entry arith_mul_sigma_le_sigma_mul kind=proved origin=conjecture
section
/- If every prime factor of m divides n then mσ(n) ≤ σ(mn) — induct on m by peeling off a prime p | m: Uses Mathlib2.p5_sigma_prime_mul_of_dvd at each step (p | (m/p)·n since p | n) to get σ(p·(m/p)n) > pσ((m/p)n). -/
theorem arith_mul_sigma_le_sigma_mul (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (h : m.primeFactors ⊆ n.primeFactors) : m * ArithmeticFunction.sigma 1 n ≤ ArithmeticFunction.sigma 1 (m * n) := by
  have hk : 0 < m := Nat.pos_of_ne_zero hm
  rw [ArithmeticFunction.sigma_one_apply, ArithmeticFunction.sigma_one_apply]
  have hsub : n.divisors.image (fun d => m * d) ⊆ (m * n).divisors := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    exact Mathlib2.ab_t2_mul_mem_divisors n m d hk hd
  have h1 : ∑ d ∈ n.divisors.image (fun d => m * d), d ≤ ∑ d ∈ (m * n).divisors, d :=
    Finset.sum_le_sum_of_subset hsub
  rw [Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hk hab), ← Finset.mul_sum] at h1
  exact h1
end

-- forge:entry calc_tsum_fib_div_two_pow kind=proved origin=conjecture
section
/- ∑ Fₙ/2ⁿ = 2 — summability by Fₙ ≤ φⁿ-type bound (fib n ≤ (7/4)^n or 2^n·(geometric)), then S = 1/2 + S/2 + S/4 from the recurrence; or closed partial sums 2 − F_{N+3}/2^N… -/
theorem calc_tsum_fib_div_two_pow_aux1 (n : ℕ) : (Nat.fib n : ℝ) ≤ (7/4) ^ n ∧ (Nat.fib (n + 1) : ℝ) ≤ (7/4) ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [Nat.fib_add_two]
    push_cast
    have hp : (0:ℝ) < (7/4) ^ k := by positivity
    have e1 : ((7:ℝ)/4) ^ (k + 1) = (7/4) ^ k * (7/4) := pow_succ _ _
    have e2 : ((7:ℝ)/4) ^ (k + 1 + 1) = (7/4) ^ k * (7/4) * (7/4) := by rw [pow_succ, pow_succ]
    nlinarith [ih.1, ih.2]

theorem calc_tsum_fib_div_two_pow : ∑' n : ℕ, (Nat.fib n : ℝ) / 2 ^ n = 2 := by
  have hg : Filter.Tendsto (fun n : ℕ => 2 * (Nat.fib (n + 2) : ℝ) / 2 ^ n) Filter.atTop (nhds 0) := by
    have t : Filter.Tendsto (fun n : ℕ => 2 * (49/16 : ℝ) * (7/8) ^ n) Filter.atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (7/8:ℝ)) (by norm_num) (by norm_num)).const_mul (2 * (49/16 : ℝ))
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) t
    have hb := (calc_tsum_fib_div_two_pow_aux1 (n + 1)).2
    have e : (2 * (49/16 : ℝ) * (7/8) ^ n) = 2 * (7/4) ^ (n + 1 + 1) / 2 ^ n := by
      rw [show (7/8 : ℝ) = (7/4) / 2 by norm_num, div_pow, pow_succ, pow_succ]
      ring
    rw [e]
    gcongr
  have h := calc_tsum_inv_three_consecutive_aux1 (fun n : ℕ => (Nat.fib n : ℝ) / 2 ^ n) _ (fun n => by positivity) (fun n => by rw [Nat.fib_add_two, show n + 1 + 2 = (n + 1) + 2 from rfl, Nat.fib_add_two, Nat.fib_add_two]; push_cast; rw [pow_succ]; field_simp; ring) hg
  rw [h.tsum_eq]
  norm_num
end

-- forge:entry arith_sum_natAbs_moebius kind=proved origin=conjecture
section
/- Σ_{d|n} |μ(d)| = 2^ω(n) — |μ(d)| is the indicator of squarefree d; squarefree divisors of n biject with subsets of n.primeFactors. -/
theorem arith_sum_natAbs_moebius (n : ℕ) (hn : 0 < n) : ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d).natAbs = 2 ^ ArithmeticFunction.cardDistinctFactors n := by
  have h1 : ∀ d, (ArithmeticFunction.moebius d).natAbs = if Squarefree d then 1 else 0 := by
    intro d
    apply Int.ofNat_inj.mp
    rw [Int.natCast_natAbs, ArithmeticFunction.abs_moebius]
    split_ifs <;> simp
  simp_rw [h1]
  rw [← Finset.sum_filter, Nat.sum_divisors_filter_squarefree hn.ne']
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_powerset]
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset, Nat.factors_eq]
  simp
end

-- forge:entry arith_sum_moebius_mul_totient kind=proved origin=conjecture
section
/- Σ_{d|n} μ(d)φ(d) = ∏_{p|n} (2 - p) — sum over squarefree divisors of a multiplicative function expands as ∏_{p|n}(1 + μ(p)φ(p)) = ∏(1 - (p-1)). -/
lemma arith_sum_moebius_mul_totient_aux1 (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) : ArithmeticFunction.moebius (∏ p ∈ s, p) * ((∏ p ∈ s, p).totient : ℤ) = ∏ p ∈ s, (1 - (p : ℤ)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hpa := hs a (Finset.mem_insert_self a s)
    have hs' : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have hcop : Nat.Coprime a (∏ p ∈ s, p) := Nat.Coprime.prod_right fun i hi => (Nat.coprime_primes hpa (hs' i hi)).2 (fun h => ha (h ▸ hi))
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop, Nat.totient_mul hcop, ArithmeticFunction.moebius_apply_prime hpa, Nat.totient_prime hpa, ← ih hs']
    have : 1 ≤ a := hpa.pos
    push_cast [Nat.cast_sub this]
    ring

theorem arith_sum_moebius_mul_totient (n : ℕ) (hn : 0 < n) : ∑ d ∈ n.divisors, ArithmeticFunction.moebius d * (d.totient : ℤ) = ∏ p ∈ n.primeFactors, (2 - (p : ℤ)) := by
  have h0 : ∑ d ∈ n.divisors, ArithmeticFunction.moebius d * (d.totient : ℤ) = ∑ d ∈ n.divisors.filter Squarefree, ArithmeticFunction.moebius d * (d.totient : ℤ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    split_ifs with h
    · rfl
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h, zero_mul]
  rw [h0, Nat.sum_divisors_filter_squarefree hn.ne']
  have h2 : ∀ p ∈ n.primeFactors, (2 - (p:ℤ)) = 1 + (1 - (p:ℤ)) := fun p _ => by ring
  rw [Finset.prod_congr rfl h2, Finset.prod_one_add]
  have hF : (UniqueFactorizationMonoid.normalizedFactors n).toFinset = n.primeFactors := by
    rw [Nat.factors_eq]; simp
  rw [hF]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.prod_val]
  simp only [id]
  exact arith_sum_moebius_mul_totient_aux1 t (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp ht hp))
end

-- forge:entry calc_card_perm_one_fixed_point kind=proved origin=conjecture
section
/- Permutations of an (n+1)-set with exactly one fixed point number (n+1)·D(n) — choose the fixed point, derange the remaining n points (card_derangements_eq_numDerangements, Equiv.Perm.subtypeEquivSubtypePerm / derangements.atMostOneFixedPointEquivSum_derangements). -/
theorem calc_card_perm_one_fixed_point_aux1 {α : Type*} [Fintype α] [DecidableEq α] (i : α) :
    ((Finset.univ : Finset (Equiv.Perm α)).filter (fun σ => ∀ a, σ a = a ↔ a = i)).card
      = numDerangements (Fintype.card α - 1) := by
  rw [← Fintype.card_subtype]
  have e : {σ : Equiv.Perm α // ∀ a, σ a = a ↔ a = i} ≃ derangements {a : α // a ≠ i} :=
    (Equiv.subtypeEquivRight (fun σ => forall_congr' fun a => by
      simp only [ne_eq, not_not, Function.mem_fixedPoints_iff]
      exact iff_comm)).trans (derangements.subtypeEquiv (fun a => a ≠ i)).symm
  rw [Fintype.card_congr e, ← card_derangements_fin_eq_numDerangements]
  apply card_derangements_invariant
  simp

theorem calc_card_perm_one_fixed_point (n : ℕ) : ((Finset.univ : Finset (Equiv.Perm (Fin (n + 1)))).filter (fun σ => (Finset.univ.filter (fun i => σ i = i)).card = 1)).card = (n + 1) * numDerangements n := by
  have hset : (Finset.univ : Finset (Equiv.Perm (Fin (n + 1)))).filter (fun σ => (Finset.univ.filter (fun i => σ i = i)).card = 1)
      = (Finset.univ : Finset (Fin (n + 1))).biUnion
          (fun i => (Finset.univ : Finset (Equiv.Perm (Fin (n + 1)))).filter (fun σ => ∀ a, σ a = a ↔ a = i)) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.card_eq_one, Finset.ext_iff,
      Finset.mem_singleton]
  rw [hset, Finset.card_biUnion]
  · have hc : ∀ i : Fin (n + 1), ((Finset.univ : Finset (Equiv.Perm (Fin (n + 1)))).filter (fun σ => ∀ a, σ a = a ↔ a = i)).card
        = numDerangements n := by
      intro i
      have := calc_card_perm_one_fixed_point_aux1 i
      rw [Fintype.card_fin, Nat.add_sub_cancel] at this
      rw [← this]
      congr
    rw [Finset.sum_congr rfl (fun i _ => hc i)]
    simp
  · intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro σ hi hj
    have h1 := (Finset.mem_filter.mp hi).2
    have h2 := (Finset.mem_filter.mp hj).2
    exact hij ((h2 i).mp ((h1 i).mpr rfl))
end

-- forge:entry arith_card_divisors_odd_iff_isSquare kind=proved origin=conjecture
section
/- τ(n) is odd iff n is a perfect square — the involution d ↦ n/d on divisors has a fixed point iff n is a square. -/
theorem arith_card_divisors_odd_iff_isSquare_aux1 {ι : Type*} (s : Finset ι) (f : ι → ℕ) : Odd (∏ i ∈ s, f i) ↔ ∀ i ∈ s, Odd (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Nat.odd_mul, ih, Finset.forall_mem_insert]

theorem arith_card_divisors_odd_iff_isSquare (n : ℕ) (hn : 0 < n) : Odd n.divisors.card ↔ IsSquare n := by
  rw [Nat.card_divisors hn.ne', arith_card_divisors_odd_iff_isSquare_aux1]
  have e : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
    rw [← Nat.prod_factorization_eq_prod_primeFactors]
    exact (Nat.factorization_prod_pow_eq_self hn.ne').symm
  constructor
  · intro h
    refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
    rw [← Finset.prod_mul_distrib]
    refine e.trans (Finset.prod_congr rfl fun p hp => ?_)
    rw [← pow_add]
    congr 1
    obtain ⟨c, hc⟩ := h p hp
    omega
  · rintro ⟨m, rfl⟩ p hp
    have hm : m ≠ 0 := by rintro rfl; simp at hn
    rw [Nat.factorization_mul hm hm]
    exact ⟨m.factorization p, by simp only [Finsupp.coe_add, Pi.add_apply]; ring⟩
end

-- forge:entry calc_card_involutions_rec kind=proved origin=conjecture
section
/- Involution numbers satisfy I(n+2) = I(n+1) + (n+1)·I(n) — split involutions of Fin (n+2) by whether the last point is fixed (I(n+1)) or swapped with one of n+1 others (remaining n points carry an involution). -/
theorem calc_card_involutions_rec (n : ℕ) : ((Finset.univ : Finset (Equiv.Perm (Fin (n + 2)))).filter (fun σ => σ * σ = 1)).card = ((Finset.univ : Finset (Equiv.Perm (Fin (n + 1)))).filter (fun σ => σ * σ = 1)).card + (n + 1) * ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun σ => σ * σ = 1)).card := by
  have h := comb_card_involutions_rec n
  simp only [Fintype.card_subtype] at h
  exact h
end

-- forge:entry calc_tsum_nat_div_factorial kind=proved origin=conjecture
section
/- ∑ n/n! = e — drop n = 0 term, n/n! = 1/(n−1)!, reindex and use Real.exp series (NormedSpace.exp / Real.exp_eq_tsum / hasSum_nat_add_iff). -/
theorem calc_tsum_nat_div_factorial : ∑' n : ℕ, (n : ℝ) / (n.factorial : ℝ) = Real.exp 1 := by
  have h := NormedSpace.expSeries_div_hasSum_exp (1:ℝ)
  rw [← Real.exp_eq_exp_ℝ] at h
  have h' : HasSum (fun n : ℕ => 1 / (n.factorial : ℝ)) (Real.exp 1) := by simpa using h
  have h2 : HasSum (fun n : ℕ => (n : ℝ) / (n.factorial : ℝ)) (Real.exp 1) := by
    rw [← hasSum_nat_add_iff' 1]
    convert! h' using 1
    · funext n
      rw [Nat.factorial_succ]
      push_cast
      field_simp
    · simp
  exact h2.tsum_eq
end

-- forge:entry arith_orderOf_two_zmod_three_pow kind=proved origin=conjecture
section
/- 2 is a primitive root modulo every power of 3: its order mod 3^(n+1) is 2·3^n = φ(3^(n+1)) — the order divides φ; Uses Mathlib2.nt2_lte_three_two_pow_three_pow_add_one at the key step: 2^(3^n) ≡ -1 ≠ 1 rules out divisors of 3^n, and the exact valuation v_3(2^(3^(n-1)) + 1) = n (with 3 ∤ 2^(3^(n-1)) - 1) rules out 2·3^(n-1). -/
theorem arith_orderOf_two_zmod_three_pow (n : ℕ) : orderOf (2 : ZMod (3 ^ (n + 1))) = 2 * 3 ^ n := by
  have key : ∀ m : ℕ, (2 : ZMod (3 ^ (m + 1))) ^ 3 ^ m = -1 := by
    intro m
    obtain ⟨k, hk, -⟩ := Mathlib2.nt2_lte_three_two_pow_three_pow_add_one m
    have : ((2 ^ 3 ^ m + 1 : ℕ) : ZMod (3 ^ (m + 1))) = 0 := by
      rw [hk, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have h3 : 3 ≤ 3 ^ (n + 1) := by
    have : 0 < 3 ^ n := by positivity
    rw [pow_succ]; omega
  refine orderOf_eq_of_pow_and_pow_div_prime (by positivity) ?_ ?_
  · rw [mul_comm, pow_mul, key n]; norm_num
  · intro p hp hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
      subst hp2
      rw [Nat.mul_div_cancel_left _ (by norm_num), key n]
      intro h1
      have h2 : ((2 : ℕ) : ZMod (3 ^ (n + 1))) = 0 := by
        have : (1 : ZMod (3 ^ (n + 1))) + 1 = 0 := by
          nth_rewrite 1 [← h1]; ring
        push_cast; rw [← this]; ring
      have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 _).mp h2)
      omega
    · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)
      subst hp3
      obtain _ | m := n
      · norm_num at h
      · have e : 2 * 3 ^ (m + 1) / 3 = 2 * 3 ^ m := by
          rw [pow_succ, ← mul_assoc, Nat.mul_div_cancel _ (by norm_num)]
        rw [e]
        intro h1
        obtain ⟨k, hk, hk3⟩ := Mathlib2.nt2_lte_three_two_pow_three_pow_add_one m
        have hA : 0 < 2 ^ 3 ^ m := by positivity
        obtain ⟨B, hB⟩ : ∃ B, 2 ^ 3 ^ m = B + 1 := ⟨2 ^ 3 ^ m - 1, by omega⟩
        have h2 : ((2 ^ (2 * 3 ^ m) : ℕ) : ZMod (3 ^ (m + 1 + 1))) = ((1 : ℕ) : ZMod (3 ^ (m + 1 + 1))) := by
          push_cast; exact h1
        rw [ZMod.natCast_eq_natCast_iff] at h2
        have h4 := (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mp h2.symm
        have h5 : 2 ^ (2 * 3 ^ m) - 1 = 3 ^ (m + 1) * (k * B) := by
          rw [Nat.sub_eq_iff_eq_add Nat.one_le_two_pow, mul_comm 2, pow_mul, hB, ← mul_assoc, ← hk, hB]
          ring
        rw [h5, pow_succ 3 (m + 1)] at h4
        have h6 : 3 ∣ k * B := Nat.dvd_of_mul_dvd_mul_left (by positivity) h4
        rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h6 with h7 | h7
        · exact hk3 h7
        · have h8 : 3 ∣ B + 1 + 1 := by
            rw [← hB, hk]; exact Dvd.dvd.mul_right (dvd_pow_self 3 (by omega)) k
          omega
end

-- forge:entry calc_cos_le_quartic kind=proved origin=conjecture
section
/- cos x ≤ 1 − x²/2 + x⁴/24 for all real x — even function so WLOG x ≥ 0; derivative of RHS − LHS is sin x − x + x³/6 ≥ 0 (previous Taylor bound), value 0 at 0. -/
theorem calc_cos_le_quartic_aux1 (x : ℝ) (hx : 0 ≤ x) : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have hk : ∀ y : ℝ, HasDerivAt (fun y : ℝ => 1 - y ^ 2 / 2 + y ^ 4 / 24 - Real.cos y)
      (Real.sin y - y + y ^ 3 / 6) y := by
    intro y
    have := (((hasDerivAt_const y (1:ℝ)).sub ((hasDerivAt_pow 2 y).div_const 2)).add
      ((hasDerivAt_pow 4 y).div_const 24)).sub (Real.hasDerivAt_cos y)
    convert! this using 1
    norm_num
    ring
  have hmono : MonotoneOn (fun y : ℝ => 1 - y ^ 2 / 2 + y ^ 4 / 24 - Real.cos y) (Set.Ici (0:ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · exact fun y _ => (hk y).continuousAt.continuousWithinAt
    · exact fun y _ => (hk y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hk y).deriv]
      linarith [ana_sin_ge_cubic_of_nonneg y (le_of_lt hy)]
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  simp at this
  linarith

theorem calc_cos_le_quartic (x : ℝ) : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  rcases le_total 0 x with h | h
  · exact calc_cos_le_quartic_aux1 x h
  · have := calc_cos_le_quartic_aux1 (-x) (by linarith)
    rw [Real.cos_neg] at this
    have e2 : (-x) ^ 2 = x ^ 2 := by ring
    have e4 : (-x) ^ 4 = x ^ 4 := by ring
    rw [e2, e4] at this
    exact this
end

-- forge:entry calc_tan_ge_cubic kind=proved origin=conjecture
section
/- tan x ≥ x + x³/3 on [0, π/2) — derivative of tan x − x − x³/3 is tan²x − x² ≥ 0 since tan x ≥ x (Real.lt_tan); monotonicity on [0,π/2). -/
theorem calc_tan_ge_cubic (x : ℝ) (hx0 : 0 ≤ x) (hx : x < Real.pi / 2) : x + x ^ 3 / 3 ≤ Real.tan x := by
  have hk : ∀ y ∈ Set.Ico (0:ℝ) (Real.pi / 2), HasDerivAt (fun y : ℝ => Real.tan y - y - y ^ 3 / 3)
      (Real.tan y ^ 2 - y ^ 2) y := by
    intro y hy
    have hc : Real.cos y ≠ 0 := (Real.cos_pos_of_mem_Ioo ⟨by linarith [hy.1, Real.pi_pos], hy.2⟩).ne'
    have := ((Real.hasDerivAt_tan hc).sub (hasDerivAt_id' y)).sub
      ((hasDerivAt_pow 3 y).div_const 3)
    convert! this using 1
    rw [← Real.inv_one_add_tan_sq hc]
    norm_num
  have hmono : MonotoneOn (fun y : ℝ => Real.tan y - y - y ^ 3 / 3) (Set.Ico (0:ℝ) (Real.pi / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico _ _)
    · intro y hy
      exact (hk y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ico] at hy
      exact (hk y ⟨hy.1.le, hy.2⟩).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ico] at hy
      rw [(hk y ⟨hy.1.le, hy.2⟩).deriv]
      have := Real.lt_tan hy.1 hy.2
      nlinarith [hy.1]
  have := hmono (Set.left_mem_Ico.mpr (by positivity)) ⟨hx0, hx⟩ hx0
  simp at this
  linarith
end

end Mathlib2
