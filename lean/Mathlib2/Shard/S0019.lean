/- Mathlib2 分片 19（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0018
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry p4_rem1_lower kind=proved origin=paper
section
/- Remark 1: for 2^s < n <= 2^(s+1), r(n)=s+1 and x(n) >= z(2^s)-(s+2)m(2^(s+1)). -/
theorem p4_rem1_lower (s n : ℕ) (h1 : 2 ^ s < n) (h2 : n ≤ 2 ^ (s + 1)) : p4_r n = s + 1 ∧ p4_z (2 ^ s) - ((s : ℤ) + 2) * (p4_m (2 ^ (s + 1)) : ℤ) ≤ p4_x n := by
  have hn : 0 < n := by omega
  constructor
  · exact ((p4_ex1_levels n (s + 1) hn).2.2 (by omega)).2 ⟨by simpa using h1, h2⟩
  · have h := (p4_lem1_i (2 ^ s) (2 ^ (s + 1)) n (by positivity) h1.le h2).1
    have hr : p4_r (2 ^ (s + 1)) = s + 1 := by
      unfold p4_r
      exact Nat.clog_pow 2 (s + 1) one_lt_two
    rw [hr] at h
    push_cast at h
    linarith
end

-- forge:entry p4_rem1_even kind=proved origin=paper
section
/- Remark 1, s=2k: 2^k <= m(2^s) < 2^(k+1) and z(2^s)=p where 2^(2k+1)=3p+2. -/
theorem p4_rem1_even (k : ℕ) : 2 ^ k ≤ p4_m (2 ^ (2 * k)) ∧ p4_m (2 ^ (2 * k)) < 2 ^ (k + 1) ∧ (2 : ℤ) ^ (2 * k + 1) = 3 * p4_z (2 ^ (2 * k)) + 2 := by
  have h : ∃ c : ℤ, (2 : ℤ) ^ (2 * k) = 3 * c + 1 := by
    induction k with
    | zero => exact ⟨0, by norm_num⟩
    | succ j ih =>
      obtain ⟨c, hc⟩ := ih
      exact ⟨4 * c + 1, by rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add, hc]; ring⟩
  have e : (2 : ℕ) ^ (2 * k) = (2 ^ k) ^ 2 := by rw [← pow_mul, mul_comm]
  have e2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
  have hy : 0 < 2 ^ k := by positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold p4_m
    rw [Nat.le_sqrt', e]
    nlinarith
  · unfold p4_m
    rw [Nat.sqrt_lt', e, e2]
    nlinarith
  · obtain ⟨c, hc⟩ := h
    have e1 : (2 : ℤ) ^ (2 * k + 1) = 2 * (3 * c + 1) := by rw [pow_succ, hc]; ring
    unfold p4_z
    push_cast
    rw [e1, hc]
    omega
end

-- forge:entry p4_rem1_odd kind=proved origin=paper
section
/- Remark 1, s=2k+1: m(2^s)=2^(k+1) and z(2^s)=q where 2^(2k+2)=3q+1. -/
theorem p4_rem1_odd (k : ℕ) : p4_m (2 ^ (2 * k + 1)) = 2 ^ (k + 1) ∧ (2 : ℤ) ^ (2 * k + 2) = 3 * p4_z (2 ^ (2 * k + 1)) + 1 := by
  constructor
  · unfold p4_m
    have e : 2 * 2 ^ (2 * k + 1) = (2 ^ (k + 1)) ^ 2 := by ring
    rw [e, Nat.sqrt_eq']
  · have h : ∃ c : ℤ, (2 : ℤ) ^ (2 * k) = 3 * c + 1 := by
      induction k with
      | zero => exact ⟨0, by norm_num⟩
      | succ j ih =>
        obtain ⟨c, hc⟩ := ih
        exact ⟨4 * c + 1, by rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add, hc]; ring⟩
    obtain ⟨c, hc⟩ := h
    have e1 : (2 : ℤ) ^ (2 * k + 2) = 4 * (3 * c + 1) := by rw [pow_add, hc]; ring
    have e2 : (2 : ℤ) ^ (2 * k + 1) = 2 * (3 * c + 1) := by rw [pow_succ, hc]; ring
    unfold p4_z
    push_cast
    rw [e1, e2]
    omega
end

-- forge:entry bld2_card_conjClasses_of_card_prime_cube kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_center_card_of_card_prime_cube: |Z(G)| = p gives p singleton classes; a non-central x has centralizer containing Z(G) and x, proper in G, hence of order p^2, so its class has p elements; the p^3 - p non-central elements form p^2 - 1 classes (class equation). -/
lemma bld2_card_conjClasses_of_card_prime_cube_aux1 (p : ℕ) (hp : p.Prime) (G : Type*) [Group G] (hG : Nat.card G = p ^ 3) (hnc : ∃ a b : G, a * b ≠ b * a) (a : G) [Decidable (a ∈ Subgroup.center G)] :
    Nat.card {b : G // Commute a b} = if a ∈ Subgroup.center G then p ^ 3 else p ^ 2 := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact pow_ne_zero _ hp.ne_zero)
  have hZ := Mathlib2.bld_center_card_of_card_prime_cube p hp G hG hnc
  have hcard : Nat.card {b : G // Commute a b} = Nat.card (Subgroup.centralizer ({a} : Set G)) := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro b
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => h.eq.symm, fun h => h.symm⟩
  rw [hcard]
  split_ifs with ha
  · have : Subgroup.centralizer ({a} : Set G) = ⊤ := by
      rw [Subgroup.centralizer_eq_top_iff_subset]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact ha
    rw [this, Subgroup.card_top, hG]
  · have hle : Subgroup.center G ≤ Subgroup.centralizer ({a} : Set G) := Subgroup.center_le_centralizer _
    have hamem : a ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
    have hdvd : Nat.card (Subgroup.centralizer ({a} : Set G)) ∣ p ^ 3 := hG ▸ Subgroup.card_subgroup_dvd_card _
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hk3' : k ≠ 3 := by
      rintro rfl
      have htop : Subgroup.centralizer ({a} : Set G) = ⊤ := by
        rw [← Subgroup.card_eq_iff_eq_top, hk, hG]
      rw [Subgroup.centralizer_eq_top_iff_subset] at htop
      exact ha (htop (Set.mem_singleton a))
    have hk1 : 2 ≤ k := by
      by_contra hlt
      have hk1 : k ≤ 1 := by omega
      have hge : Nat.card (Subgroup.centralizer ({a} : Set G)) ≤ Nat.card (Subgroup.center G) := by
        rw [hk, hZ]
        calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
          _ = p := pow_one p
      have heq := Subgroup.eq_of_le_of_card_ge hle hge
      exact ha (heq ▸ hamem)
    have : k = 2 := by omega
    rw [hk, this]

theorem bld2_card_conjClasses_of_card_prime_cube (p : ℕ) (hp : p.Prime) (G : Type*) [Group G] (hG : Nat.card G = p ^ 3) (hnc : ∃ a b : G, a * b ≠ b * a) : Nat.card (ConjClasses G) = p ^ 2 + p - 1 := by
  classical
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact pow_ne_zero _ hp.ne_zero)
  haveI : Fintype G := Fintype.ofFinite G
  have hZ := Mathlib2.bld_center_card_of_card_prime_cube p hp G hG hnc
  have h1 := card_comm_eq_card_conjClasses_mul_card G
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun a b : G => Commute a b)), Nat.card_sigma, hG] at h1
  simp_rw [bld2_card_conjClasses_of_card_prime_cube_aux1 p hp G hG hnc] at h1
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul] at h1
  have hcA : (Finset.univ.filter (fun a : G => a ∈ Subgroup.center G)).card = p := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact hZ
  have hcB := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset G)) (fun a : G => a ∈ Subgroup.center G)
  rw [hcA, Finset.card_univ, ← Nat.card_eq_fintype_card, hG] at hcB
  rw [hcA] at h1
  set K := Nat.card (ConjClasses G)
  set cB := (Finset.univ.filter (fun a : G => ¬ a ∈ Subgroup.center G)).card
  have hp3 : 0 < p ^ 3 := pow_pos hp.pos 3
  have hfin : (K + 1) * p ^ 3 = (p ^ 2 + p) * p ^ 3 := by
    linear_combination (p ^ 2) * hcB - h1
  have := Nat.eq_of_mul_eq_mul_right hp3 hfin
  omega
end

-- forge:entry p4_rem1_bound_even kind=proved origin=paper
section
/- Remark 1: for s=2k, k>=6 and 2^s<n<=2^(s+1): 3x(n) >= 2^(k+1)(2^k-6k-6)-2 >= 2^(k+1)-2 > 0. -/
theorem p4_rem1_bound_even_aux1 (k : ℕ) (hk : 6 ≤ k) : (6 * (k : ℤ) + 7) ≤ (2 : ℤ) ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    rw [pow_succ]
    push_cast
    linarith

theorem p4_rem1_bound_even (k n : ℕ) (hk : 6 ≤ k) (h1 : 2 ^ (2 * k) < n) (h2 : n ≤ 2 ^ (2 * k + 1)) : (2 : ℤ) ^ (k + 1) - 2 ≤ 3 * p4_x n ∧ 0 < p4_x n := by
  have hy := p4_rem1_bound_even_aux1 k hk
  have hl := (p4_rem1_lower (2 * k) n h1 h2).2
  have hz := (p4_rem1_even k).2.2
  have hm := (p4_rem1_odd k).1
  rw [hm] at hl
  push_cast at hl
  have e1 : (2 : ℤ) ^ (2 * k + 1) = 2 * ((2 : ℤ) ^ k) ^ 2 := by ring
  have e2 : (2 : ℤ) ^ (k + 1) = 2 * (2 : ℤ) ^ k := by ring
  rw [e1] at hz
  rw [e2] at hl ⊢
  have hpos : (0 : ℤ) < (2 : ℤ) ^ k := by positivity
  have key : 2 * (2 : ℤ) ^ k - 2 ≤ 3 * p4_x n := by nlinarith
  constructor
  · exact key
  · nlinarith
end

-- forge:entry p4_rem1_bound_odd kind=proved origin=paper
section
/- Remark 1: for s=2k+1, k>=6 and 2^s<n<=2^(s+1): 3x(n) > 2^(k+2)(2^k-6k-9)-1 >= 2^(k+2)-1 > 0. -/
theorem p4_rem1_bound_odd_aux1 (k : ℕ) (hk : 6 ≤ k) : (6 * (k : ℤ) + 10) ≤ (2 : ℤ) ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    rw [pow_succ]
    push_cast
    linarith

theorem p4_rem1_bound_odd (k n : ℕ) (hk : 6 ≤ k) (h1 : 2 ^ (2 * k + 1) < n) (h2 : n ≤ 2 ^ (2 * k + 2)) : (2 : ℤ) ^ (k + 2) - 1 < 3 * p4_x n ∧ 0 < p4_x n := by
  have hy := p4_rem1_bound_odd_aux1 k hk
  have hl := (p4_rem1_lower (2 * k + 1) n h1 h2).2
  have hz := (p4_rem1_odd k).2
  have hm := (p4_rem1_even (k + 1)).2.1
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring] at hm
  have hm' : (p4_m (2 ^ (2 * k + 1 + 1)) : ℤ) + 1 ≤ 4 * (2 : ℤ) ^ k := by
    have : p4_m (2 ^ (2 * k + 1 + 1)) + 1 ≤ 4 * 2 ^ k := by
      have e : 2 ^ (k + 1 + 1) = 4 * 2 ^ k := by ring
      omega
    exact_mod_cast this
  push_cast at hl
  have e1 : (2 : ℤ) ^ (2 * k + 2) = 4 * ((2 : ℤ) ^ k) ^ 2 := by ring
  have e2 : (2 : ℤ) ^ (k + 2) = 4 * (2 : ℤ) ^ k := by ring
  rw [e1] at hz
  rw [e2]
  have hpos : (0 : ℤ) < (2 : ℤ) ^ k := by positivity
  have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
  have hmm : ((2 * (k : ℤ) + 1) + 2) * (p4_m (2 ^ (2 * k + 1 + 1)) : ℤ) ≤ ((2 * (k : ℤ) + 1) + 2) * (4 * (2 : ℤ) ^ k - 1) := by
    apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have key : 4 * (2 : ℤ) ^ k - 1 < 3 * p4_x n := by nlinarith
  constructor
  · exact key
  · nlinarith
end

-- forge:entry p4_rem1_large kind=proved origin=paper
section
/- Remark 1 conclusion: x(n) > 0 for every n > 2^12 = 4096. -/
theorem p4_rem1_large (n : ℕ) (h : 4096 < n) : 0 < p4_x n := by
  have hc : 13 ≤ Nat.clog 2 n := by
    by_contra hc
    push_neg at hc
    have h5 : Nat.clog 2 n ≤ 12 := by omega
    have h6 := (Nat.clog_le_iff_le_pow one_lt_two).1 h5
    have e : (2 : ℕ) ^ 12 = 4096 := by norm_num
    omega
  obtain ⟨s, hs⟩ : ∃ s, Nat.clog 2 n = s + 1 := ⟨Nat.clog 2 n - 1, by omega⟩
  have hup : n ≤ 2 ^ (s + 1) := by
    rw [← hs]
    exact Nat.le_pow_clog one_lt_two n
  have hlo : 2 ^ s < n := by
    by_contra hc2
    push_neg at hc2
    have := (Nat.clog_le_iff_le_pow one_lt_two).2 hc2
    omega
  rcases Nat.even_or_odd' s with ⟨k, hk | hk⟩
  · subst hk
    exact (p4_rem1_bound_even k n (by omega) hlo hup).2
  · subst hk
    exact (p4_rem1_bound_odd k n (by omega) hlo hup).2
end

-- forge:entry p4_thm1_i kind=proved origin=paper
section
/- Theorem 1(i): x(n)=0 iff n is one of 436, 451, 529, 545, 546. -/
theorem p4_thm1_i (n : ℕ) (hn : 0 < n) : p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546 := by
  by_cases h : n ≤ 4096
  · exact (p4_small_classify n hn h).1
  · have := p4_rem1_large n (by omega)
    constructor
    · intro e
      omega
    · intro e
      omega
end

-- forge:entry p4_thm1_ii kind=proved origin=paper
section
/- Theorem 1(ii): x(n)<0 iff n <= 435 or n = 450 or 513 <= n <= 528. -/
theorem p4_thm1_ii (n : ℕ) (hn : 0 < n) : p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528) := by
  by_cases h : n ≤ 4096
  · exact (p4_small_classify n hn h).2.1
  · have := p4_rem1_large n (by omega)
    constructor
    · intro e
      omega
    · intro e
      omega
end

-- forge:entry lib_matrix_rank_smul kind=proved origin=conjecture
section
/- Scaling a (rectangular) matrix over a field by a nonzero scalar does not change its rank: rank (c • M) = rank M. Promoted from Mathlib2.bld_involution_trace_rank_aux1 (also re-proved as bld2_tripotent_rank_split_aux1 and bld2_involution_iff_rank_add_rank_aux1); generalised from square to rectangular matrices. -/
theorem lib_matrix_rank_smul (K : Type*) [Field K] (m n : Type*) [Fintype m] [Fintype n] (c : K) (hc : c ≠ 0) (M : Matrix m n K) : Matrix.rank (c • M) = Matrix.rank M := by
  classical
  apply le_antisymm
  · have : c • M = M * (c • (1 : Matrix n n K)) := by rw [Matrix.mul_smul, Matrix.mul_one]
    rw [this]; exact Matrix.rank_mul_le_left _ _
  · have : M = (c • M) * (c⁻¹ • (1 : Matrix n n K)) := by
      rw [Matrix.mul_smul, Matrix.mul_one, smul_smul, inv_mul_cancel₀ hc, one_smul]
    conv_lhs => rw [this]
    exact Matrix.rank_mul_le_left _ _
end

-- forge:entry p4_thm1_iii kind=proved origin=paper
section
/- Theorem 1(iii): x(n)>0 iff 437 <= n <= 512 with n not 450, 451, or n >= 530 with n not 545, 546. -/
theorem p4_thm1_iii (n : ℕ) (hn : 0 < n) : 0 < p4_x n ↔ (437 ≤ n ∧ n ≤ 512 ∧ n ≠ 450 ∧ n ≠ 451) ∨ (530 ≤ n ∧ n ≠ 545 ∧ n ≠ 546) := by
  by_cases h : n ≤ 4096
  · obtain ⟨c1, c2, -⟩ := p4_small_classify n hn h
    constructor
    · intro hp
      have n0 : ¬ (n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) := fun e => by
        have := c1.2 e
        omega
      have n1 : ¬ (n ≤ 435 ∨ n = 450 ∨ (513 ≤ n ∧ n ≤ 528)) := fun e => by
        have := c2.2 e
        omega
      omega
    · intro hp
      by_contra hneg
      have hh : p4_x n = 0 ∨ p4_x n < 0 := by omega
      rcases hh with e | e
      · have := c1.1 e
        omega
      · have := c2.1 e
        omega
  · have := p4_rem1_large n (by omega)
    constructor
    · intro e
      omega
    · intro e
      exact this
end

-- forge:entry lib_matrix_rank_eq_zero_iff kind=proved origin=conjecture
section
/- A matrix over a field has rank zero iff it is the zero matrix (Matrix.rank A = 0 ↔ A = 0). Promoted from inline derivations (Submodule.finrank_eq_zero + LinearMap.range_eq_bot) inside two bld2 rank proofs in shard S0017. -/
theorem lib_matrix_rank_eq_zero_iff (K : Type*) [Field K] (m n : Type*) [Fintype m] [Fintype n] (A : Matrix m n K) : Matrix.rank A = 0 ↔ A = 0 := by
  constructor
  · intro hr
    unfold Matrix.rank at hr
    rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at hr
    ext i j
    classical
    have := congrArg (fun f => f (Pi.single j 1) i) hr
    simpa using this
  · rintro rfl
    exact Matrix.rank_zero
end

-- forge:entry p4_thm1_iv kind=proved origin=paper
section
/- Theorem 1(iv): x(n) > 0 for every n >= 547. -/
theorem p4_thm1_iv (n : ℕ) (hn : 547 ≤ n) : 0 < p4_x n := by
  exact (p4_thm1_iii n (by omega)).2 (by omega)
end

-- forge:entry p4_thm1_vi kind=proved origin=paper
section
/- Theorem 1(vi): x(129) = -59 and x(n) >= -58 for every positive n other than 129. -/
theorem p4_thm1_vi : p4_x 129 = -59 ∧ ∀ n : ℕ, 0 < n → n ≠ 129 → -58 ≤ p4_x n := by
  constructor
  · rw [p4_x_block 129 8 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  · intro n hn hne
    by_cases h : n ≤ 4096
    · exact (p4_small_classify n hn h).2.2 hne
    · have := p4_rem1_large n (by omega)
      omega
end

-- forge:entry p4_thm1_v_step_fixed kind=proved origin=conjecture
section
/- Auditor's correction, not the paper's wording: the claim in the proof of Theorem 1(v) holds once k >= 4: if 2^(k+2) > 3B+1 and k >= 4 then x(2^(2k+2)) > B. -/
theorem p4_thm1_v_step_fixed_aux1 (k : ℕ) (hk : 4 ≤ k) : 18 * (k : ℤ) + 31 ≤ 8 * (2 : ℤ) ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    rw [pow_succ]
    push_cast
    linarith

theorem p4_thm1_v_step_fixed (B k : ℕ) (hk4 : 4 ≤ k) (hk : 3 * B + 1 < 2 ^ (k + 2)) : (B : ℤ) < p4_x (2 ^ (2 * k + 2)) := by
  have hy := p4_thm1_v_step_fixed_aux1 k hk4
  have hr : p4_r (2 ^ (2 * k + 2)) = 2 * k + 2 := by
    unfold p4_r
    exact Nat.clog_pow 2 _ one_lt_two
  have hm : p4_m (2 ^ (2 * k + 2)) + 1 ≤ 3 * 2 ^ k := by
    have : p4_m (2 ^ (2 * k + 2)) < 3 * 2 ^ k := by
      unfold p4_m
      rw [Nat.sqrt_lt']
      have e : 2 ^ (2 * k + 2) = 4 * (2 ^ k) ^ 2 := by ring
      rw [e]
      have : 0 < 2 ^ k := by positivity
      nlinarith
    omega
  have hm' : (p4_m (2 ^ (2 * k + 2)) : ℤ) + 1 ≤ 3 * (2 : ℤ) ^ k := by exact_mod_cast hm
  have hz := (p4_rem1_even (k + 1)).2.2
  rw [show 2 * (k + 1) = 2 * k + 2 by ring] at hz
  have e1 : (2 : ℤ) ^ (2 * k + 2 + 1) = 8 * ((2 : ℤ) ^ k) ^ 2 := by ring
  rw [e1] at hz
  have hB : 3 * (B : ℤ) + 2 ≤ 4 * (2 : ℤ) ^ k := by
    have : 3 * B + 2 ≤ 4 * 2 ^ k := by
      have e : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
      omega
    exact_mod_cast this
  have hpos : (0 : ℤ) < (2 : ℤ) ^ k := by positivity
  have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
  have hmm : (2 * (k : ℤ) + 2 + 1) * (p4_m (2 ^ (2 * k + 2)) : ℤ) ≤ (2 * (k : ℤ) + 2 + 1) * (3 * (2 : ℤ) ^ k - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hprod := mul_nonneg hpos.le (sub_nonneg.2 hy)
  unfold p4_x
  rw [hr]
  push_cast
  nlinarith
end

-- forge:entry p4_thm1_v kind=proved origin=paper
section
/- Theorem 1(v): x(n) has no maximal value (over positive integers n). -/
theorem p4_thm1_v : ¬ ∃ n0 : ℕ, 0 < n0 ∧ ∀ n : ℕ, 0 < n → p4_x n ≤ p4_x n0 := by
  rintro ⟨n0, -, hmax⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ, B = (p4_x n0).toNat := ⟨_, rfl⟩
  have h1 : 3 * B + 1 < 2 ^ (B + 4 + 2) := by
    have := Nat.lt_two_pow_self (n := B)
    have e : 2 ^ (B + 4 + 2) = 64 * 2 ^ B := by ring
    omega
  have h2 := p4_thm1_v_step_fixed B (B + 4) (by omega) h1
  have h3 := hmax (2 ^ (2 * (B + 4) + 2)) (by positivity)
  have h4 : p4_x n0 ≤ (B : ℤ) := by
    rw [hB]
    exact Int.self_le_toNat _
  linarith
end

-- forge:entry p4_rem2 kind=proved origin=paper
section
/- Remark 2: 547 is the least positive integer N such that x(m) > 0 for all m >= N. -/
theorem p4_rem2 : IsLeast {N : ℕ | 0 < N ∧ ∀ m : ℕ, N ≤ m → 0 < p4_x m} 547 := by
  constructor
  · exact ⟨by norm_num, fun m hm => p4_thm1_iv m hm⟩
  · rintro N ⟨hN, hN2⟩
    by_contra hc
    push_neg at hc
    have h1 := hN2 546 (by omega)
    have h2 := (p4_thm1_i 546 (by norm_num)).2 (by norm_num)
    omega
end

-- forge:entry lib_matrix_charpoly_eq_X_pow_of_isNilpotent kind=proved origin=conjecture
section
/- The characteristic polynomial of a nilpotent square matrix over a reduced commutative ring is X^n (n = size). Promoted from the inline first step of Mathlib2.gen_lin_nilpotent_pow_card_reduced (also re-derived in gen_lin_nilpotent_det_one_add_reduced). -/
theorem lib_matrix_charpoly_eq_X_pow_of_isNilpotent (R : Type*) [CommRing R] [IsReduced R] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R) (h : IsNilpotent A) : A.charpoly = Polynomial.X ^ Fintype.card ι := by
  have hn := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h
  have h0 : A.charpoly - Polynomial.X ^ Fintype.card ι = 0 := by
    ext i
    rw [Polynomial.coeff_zero]
    exact (Polynomial.isNilpotent_iff.mp hn i).eq_zero
  exact sub_eq_zero.mp h0
end

-- forge:entry lib_matrix_transpose_mul_self_eq_zero_iff kind=proved origin=conjecture
section
/- Over a linearly ordered ring, Bᵀ * B = 0 iff B = 0, for rectangular B (the Gram matrix vanishes only for the zero matrix; diagonal entries are sums of squares). Promoted from Mathlib2.gen_lin_symm_nilpotent_eq_zero_ordered_aux1 (also inline in lin_symm_nilpotent_eq_zero); generalised to rectangular matrices and to an iff. -/
theorem lib_matrix_transpose_mul_self_eq_zero_iff (R : Type*) [Ring R] [LinearOrder R] [IsStrictOrderedRing R] (m n : Type*) [Fintype m] (B : Matrix m n R) : B.transpose * B = 0 ↔ B = 0 := by
  constructor
  · intro h
    ext i j
    have hjj : (B.transpose * B) j j = 0 := by rw [h]; rfl
    rw [Matrix.mul_apply] at hjj
    simp only [Matrix.transpose_apply] at hjj
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (B i j))).mp hjj i (Finset.mem_univ i)
    rw [Matrix.zero_apply]
    by_contra hne
    have hpos := mul_self_pos.mpr hne
    rw [this] at hpos
    exact lt_irrefl _ hpos
  · rintro rfl
    simp
end

-- forge:entry lib_matrix_rank_le_iff_exists_factorization kind=proved origin=conjecture
section
/- Rank factorisation, as a characterisation of rank: an n×p matrix B over a field has rank ≤ r iff it factors as B = M * N through K^r (M : n×r, N : r×p). The case r = rank B is Mathlib2.bld_frobenius_rank_inequality_aux1, from which this is promoted. -/
theorem lib_matrix_rank_le_iff_exists_factorization (K : Type*) [Field K] (n p : Type*) [Fintype n] [Fintype p] (B : Matrix n p K) (r : ℕ) : B.rank ≤ r ↔ ∃ (M : Matrix n (Fin r) K) (N : Matrix (Fin r) p K), B = M * N := by
  constructor
  · intro hr
    obtain ⟨M0, N0, h0⟩ := Mathlib2.bld_frobenius_rank_inequality_aux1 K n p B
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hr
    let e : Fin B.rank ⊕ Fin d ≃ Fin r := finSumFinEquiv.trans (finCongr hd.symm)
    refine ⟨(Matrix.fromCols M0 (0 : Matrix n (Fin d) K)).submatrix id e.symm,
      (Matrix.fromRows N0 (0 : Matrix (Fin d) p K)).submatrix e.symm id, ?_⟩
    rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows, Matrix.zero_mul, add_zero,
      Matrix.submatrix_id_id]
    exact h0
  · rintro ⟨M, N, rfl⟩
    calc (M * N).rank ≤ M.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin r) := Matrix.rank_le_card_width M
      _ = r := Fintype.card_fin r
end

end Mathlib2
