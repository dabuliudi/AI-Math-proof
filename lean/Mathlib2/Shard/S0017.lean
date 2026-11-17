/- Mathlib2 分片 17（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0001
import Mathlib2.Shard.S0003
import Mathlib2.Shard.S0006
import Mathlib2.Shard.S0007
import Mathlib2.Shard.S0010
import Mathlib2.Shard.S0011
import Mathlib2.Shard.S0012
import Mathlib2.Shard.S0014
import Mathlib2.Shard.S0015
import Mathlib2.Shard.S0016
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry bld2_tripotent_rank_split kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_idempotent_sum_rank: P = (1/2)(A*A + A) and Q = (1/2)(A*A - A) are idempotents whose sum A*A is idempotent, so rank (A*A) = rank P + rank Q; scalars 1/2 do not change rank and rank (A*A) = rank A since A = A*(A*A). -/
theorem bld2_tripotent_rank_split_aux1 (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K) (c : K) (hc : c ≠ 0) : Matrix.rank (c • M) = Matrix.rank M := by
  have h1 : ∀ (d : K) (N : Matrix ι ι K), Matrix.rank (d • N) ≤ Matrix.rank N := by
    intro d N
    have : d • N = N * (d • (1 : Matrix ι ι K)) := by simp
    rw [this]
    exact Matrix.rank_mul_le_left _ _
  apply le_antisymm (h1 c M)
  have := h1 c⁻¹ (c • M)
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

theorem bld2_tripotent_rank_split_aux2 (K : Type*) [Field K] [CharZero K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι K) (hAA : A * A = B) (hBA : B * A = A) (hAB : A * B = A) (hBB : B * B = B) : Matrix.rank B = Matrix.rank (B + A) + Matrix.rank (B - A) := by
  have hP : ((1/2 : K) • (B + A)) * ((1/2 : K) • (B + A)) = (1/2 : K) • (B + A) := by
    simp only [smul_mul_smul_comm, add_mul, mul_add, hAA, hBA, hAB, hBB]
    module
  have hQ : ((1/2 : K) • (B - A)) * ((1/2 : K) • (B - A)) = (1/2 : K) • (B - A) := by
    simp only [smul_mul_smul_comm, sub_mul, mul_sub, hAA, hBA, hAB, hBB]
    module
  have hS : (1/2 : K) • (B + A) + (1/2 : K) • (B - A) = B := by
    module
  have key := Mathlib2.bld_idempotent_sum_rank K ι _ _ hP hQ (by rw [hS, hBB])
  have h2 : (1/2 : K) ≠ 0 := by norm_num
  rw [hS, bld2_tripotent_rank_split_aux1 K ι _ _ h2, bld2_tripotent_rank_split_aux1 K ι _ _ h2] at key
  exact key

theorem bld2_tripotent_rank_split (K : Type*) [Field K] [CharZero K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (h : A * A * A = A) : Matrix.rank A = Matrix.rank (A * A + A) + Matrix.rank (A * A - A) := by
  have hr : A.rank = (A * A).rank := by
    apply le_antisymm _ (Matrix.rank_mul_le_left A A)
    calc A.rank = (A * A * A).rank := by rw [h]
      _ ≤ (A * A).rank := Matrix.rank_mul_le_left _ _
  rw [hr]
  exact bld2_tripotent_rank_split_aux2 K ι A (A * A) rfl h (by rw [← Matrix.mul_assoc, h]) (by rw [← Matrix.mul_assoc, h])
end

-- forge:entry bld2_lucas_sq_sub_five_fib_sq kind=proved origin=conjecture
section
/- Uses Mathlib2.an_cassini_int (with the definition Mathlib2.p3_lucas): the cast of p3_lucas n is 2 F(n+1) - F(n) (no truncation since F(n) ≤ 2 F(n+1)); expand (2F(n+1) - F(n))^2 - 5F(n)^2 = 4(F(n+1)^2 - F(n+1)F(n) - F(n)^2) and rewrite with Cassini F(n+2)F(n) - F(n+1)^2 = (-1)^(n+1), F(n+2) = F(n+1) + F(n). -/
theorem bld2_lucas_sq_sub_five_fib_sq (n : ℕ) : (p3_lucas n : ℤ) ^ 2 - 5 * (Nat.fib n : ℤ) ^ 2 = 4 * (-1) ^ n := by
  have hc := Mathlib2.an_cassini_int n
  have hle : Nat.fib n ≤ 2 * Nat.fib (n + 1) := by
    have := @Nat.fib_le_fib_succ n
    omega
  have hL : (p3_lucas n : ℤ) = 2 * (Nat.fib (n + 1) : ℤ) - Nat.fib n := by
    unfold p3_lucas
    rw [Nat.cast_sub hle]; push_cast; ring
  rw [Nat.fib_add_two] at hc
  push_cast at hc
  rw [pow_succ] at hc
  rw [hL]
  linear_combination (-4) * hc
end

-- forge:entry bld2_idempotent_iff_rank_add_rank kind=proved origin=conjecture
section
/- Uses Mathlib2.gen_lin_idempotent_rank_complement_field (and Mathlib2.gen_lin_sylvester_rank_rect): forward direction is the rank-complement theorem; conversely the rank equality forces range A and range (1 - A) to be complementary, and A(1-A)x lies in both, so A - A*A = 0. -/
theorem bld2_idempotent_iff_rank_add_rank (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) : A * A = A ↔ Matrix.rank A + Matrix.rank (1 - A) = Fintype.card ι := by
  refine ⟨Mathlib2.gen_lin_idempotent_rank_complement_field K ι A, fun h => ?_⟩
  have h0 := Mathlib2.bld2_rank_add_rank_one_sub K ι A
  have hr : Matrix.rank (A - A * A) = 0 := by omega
  unfold Matrix.rank at hr
  rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at hr
  have hz : A - A * A = 0 := by
    ext i j
    have := congrFun (LinearMap.congr_fun hr (Pi.single j 1)) i
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply,
      LinearMap.zero_apply, Pi.zero_apply, Matrix.zero_apply] using this
  exact (sub_eq_zero.mp hz).symm
end

-- forge:entry bld2_triangle_free_min_degree_le_half kind=proved origin=conjecture
section
/- Uses Mathlib2.comb_degree_add_degree_le_of_triangle_free: if d = 0 trivial; otherwise a vertex v has a neighbour u and 2d ≤ deg u + deg v ≤ card V. -/
theorem bld2_triangle_free_min_degree_le_half (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] (h : G.CliqueFree 3) (d : ℕ) (hd : ∀ v : V, d ≤ G.degree v) : 2 * d ≤ Fintype.card V := by
  rcases Nat.eq_zero_or_pos d with rfl | hpos
  · simp
  obtain ⟨v⟩ := ‹Nonempty V›
  have hv : 0 < G.degree v := lt_of_lt_of_le hpos (hd v)
  obtain ⟨u, hu⟩ := (G.degree_pos_iff_exists_adj v).mp hv
  have := Mathlib2.comb_degree_add_degree_le_of_triangle_free V G h v u hu
  have := hd v
  have := hd u
  omega
end

-- forge:entry bld2_nonexpanding_left_inverse_isometry kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_surjective_nonexpanding_compact_isometry: f is surjective (right inverse g) and non-expanding, hence an isometry, hence injective; so g (f x) = x from f (g (f x)) = f x, and dist (g x) (g y) = dist (f (g x)) (f (g y)) = dist x y. -/
theorem bld2_nonexpanding_left_inverse_isometry {X : Type*} [MetricSpace X] [CompactSpace X] (f g : X → X) (hf : ∀ x y : X, dist (f x) (f y) ≤ dist x y) (hfg : ∀ x : X, f (g x) = x) : Isometry g ∧ ∀ x : X, g (f x) = x := by
  have hiso : Isometry f :=
    Mathlib2.bld_surjective_nonexpanding_compact_isometry f (fun x => ⟨g x, hfg x⟩) hf
  refine ⟨Isometry.of_dist_eq (fun x y => ?_), fun x => hiso.injective (hfg (f x))⟩
  rw [← hiso.dist_eq (g x) (g y), hfg, hfg]
end

-- forge:entry bld2_sqrt_two_rec_viete_prod_gt kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_sqrt_two_rec_viete_prod: the partial product equals 1 / (2^n * sin (π / 2^(n+1))), and sin x < x for x > 0 gives 2^n * sin (π / 2^(n+1)) < π / 2. -/
theorem bld2_sqrt_two_rec_viete_prod_gt (a : ℕ → ℝ) (h0 : a 0 = 0) (hrec : ∀ n : ℕ, a (n + 1) = Real.sqrt (2 + a n)) (n : ℕ) : 2 / Real.pi < ∏ i ∈ Finset.range n, a (i + 1) / 2 := by
  have key := Mathlib2.bld_sqrt_two_rec_viete_prod a h0 hrec n
  have hpi := Real.pi_pos
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hx : 0 < Real.pi / 2 ^ (n + 1) := by positivity
  have hxle : Real.pi / 2 ^ (n + 1) < Real.pi := by
    apply div_lt_self hpi
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hsin_pos : 0 < Real.sin (Real.pi / 2 ^ (n + 1)) := Real.sin_pos_of_pos_of_lt_pi hx hxle
  have hsin_lt : Real.sin (Real.pi / 2 ^ (n + 1)) < Real.pi / 2 ^ (n + 1) := Real.sin_lt hx
  have hS_pos : 0 < 2 ^ n * Real.sin (Real.pi / 2 ^ (n + 1)) := mul_pos h2n hsin_pos
  have hS_lt : 2 ^ n * Real.sin (Real.pi / 2 ^ (n + 1)) < Real.pi / 2 := by
    calc 2 ^ n * Real.sin (Real.pi / 2 ^ (n + 1)) < 2 ^ n * (Real.pi / 2 ^ (n + 1)) :=
          mul_lt_mul_of_pos_left hsin_lt h2n
      _ = Real.pi / 2 := by rw [pow_succ]; field_simp
  have hP : ∏ i ∈ Finset.range n, a (i + 1) / 2 = 1 / (2 ^ n * Real.sin (Real.pi / 2 ^ (n + 1))) :=
    eq_div_of_mul_eq hS_pos.ne' key
  rw [hP]
  have : 2 / Real.pi = 1 / (Real.pi / 2) := by field_simp
  rw [this]
  exact one_div_lt_one_div_of_lt hS_pos hS_lt
end

-- forge:entry bld2_sqrt_two_rec_defect_summable kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_sqrt_two_rec_rate and Mathlib2.ana_sqrt_two_rec_lt_two: 0 ≤ 2 - a n ≤ π^2 / 4^(n+1), and the geometric series on the right is summable, so comparison applies. -/
theorem bld2_sqrt_two_rec_defect_summable (a : ℕ → ℝ) (h0 : a 0 = 0) (hrec : ∀ n : ℕ, a (n + 1) = Real.sqrt (2 + a n)) : Summable (fun n : ℕ => 2 - a n) := by
  have hg : Summable (fun n : ℕ => Real.pi ^ 2 / 4 * (1 / 4 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hg
  · have := (Mathlib2.ana_sqrt_two_rec_lt_two a h0 hrec n).2
    linarith
  · have := Mathlib2.bld_sqrt_two_rec_rate a h0 hrec n
    calc 2 - a n ≤ Real.pi ^ 2 / 4 ^ (n + 1) := this
      _ = Real.pi ^ 2 / 4 * (1 / 4 : ℝ) ^ n := by
        rw [one_div, inv_pow]; field_simp; ring
end

-- forge:entry bld2_involution_iff_rank_add_rank kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_involution_rank_add_rank and Mathlib2.gen_lin_idempotent_rank_complement_field: forward is the involution rank identity; conversely put P = (1/2)(1 + A), so 1 - P = (1/2)(1 - A) and rank P + rank (1 - P) = n, which forces P idempotent (converse of rank complement), i.e. A*A = 1. -/
lemma bld2_involution_iff_rank_add_rank_aux1 (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (c : K) (hc : c ≠ 0) (M : Matrix ι ι K) : Matrix.rank (c • M) = Matrix.rank M := by
  unfold Matrix.rank
  have : (c • M).mulVecLin = c • M.mulVecLin := by
    ext x
    simp [Matrix.smul_mulVec]
  rw [this, LinearMap.range_smul _ _ hc]

theorem bld2_involution_iff_rank_add_rank (K : Type*) [Field K] [CharZero K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) : A * A = 1 ↔ Matrix.rank (1 + A) + Matrix.rank (1 - A) = Fintype.card ι := by
  refine ⟨Mathlib2.bld_involution_rank_add_rank K ι A, fun h => ?_⟩
  have h2 : (2⁻¹ : K) ≠ 0 := by norm_num
  have hQ : (1 : Matrix ι ι K) - (2⁻¹ : K) • (1 + A) = (2⁻¹ : K) • (1 - A) := by
    match_scalars <;> ring
  have hP : ((2⁻¹ : K) • (1 + A)) * ((2⁻¹ : K) • (1 + A)) = (2⁻¹ : K) • (1 + A) := by
    rw [Mathlib2.bld2_idempotent_iff_rank_add_rank, hQ,
      bld2_involution_iff_rank_add_rank_aux1 K ι _ h2, bld2_involution_iff_rank_add_rank_aux1 K ι _ h2]
    exact h
  have key : A * A - 1 = (4 : K) • (((2⁻¹ : K) • (1 + A)) * ((2⁻¹ : K) • (1 + A)) - (2⁻¹ : K) • (1 + A)) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, add_mul, mul_add, one_mul, mul_one, smul_add, smul_sub]
    module
  rw [hP, sub_self, smul_zero] at key
  exact sub_eq_zero.mp key
end

-- forge:entry bld2_involution_trace_eq_card kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_involution_trace_rank and Mathlib2.bld_involution_rank_add_rank: the trace formula gives 2 * rank (1 + A) = 2 * card ι in K, hence (CharZero) rank (1 + A) = card ι; the rank identity then gives rank (1 - A) = 0, so 1 - A = 0. -/
theorem bld2_involution_trace_eq_card (K : Type*) [Field K] [CharZero K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (h : A * A = 1) (ht : Matrix.trace A = (Fintype.card ι : K)) : A = 1 := by
  have h1 := Mathlib2.bld_involution_trace_rank K ι A h
  have h2 := Mathlib2.bld_involution_rank_add_rank K ι A h
  rw [ht] at h1
  have h3 : (Fintype.card ι : K) = ((1 + A).rank : K) := by linear_combination h1 / 2
  have h4 : Fintype.card ι = (1 + A).rank := by exact_mod_cast h3
  have h5 : (1 - A).rank = 0 := by omega
  unfold Matrix.rank at h5
  rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h5
  have h6 : 1 - A = 0 := by
    ext i j
    have := congrFun (LinearMap.congr_fun h5 (Pi.single j 1)) i
    simpa [Matrix.one_apply, Pi.single_apply] using this
  exact (sub_eq_zero.1 h6).symm
end

-- forge:entry bld2_sqrt_two_rec_defect_asymptotic kind=proved origin=conjecture
section
/- Uses Mathlib2.ana_sqrt_two_rec_closed_form (sharpening Mathlib2.bld_sqrt_two_rec_rate): 2 - a n = 2 - 2 cos (π/2^(n+1)) = 4 sin^2 (π/2^(n+2)), so 4^n * (2 - a n) = (2^(n+1) * sin (π/2^(n+2)))^2, which tends to (π/2)^2 since sin x / x → 1. -/
theorem bld2_sqrt_two_rec_defect_asymptotic (a : ℕ → ℝ) (h0 : a 0 = 0) (hrec : ∀ n : ℕ, a (n + 1) = Real.sqrt (2 + a n)) : Filter.Tendsto (fun n : ℕ => 4 ^ n * (2 - a n)) Filter.atTop (nhds (Real.pi ^ 2 / 4)) := by
  have hpi := Real.pi_pos
  have hS : ∀ n : ℕ, 2 ^ n * Real.sin (Real.pi / 2 ^ (n + 1)) = (∏ i ∈ Finset.range n, a (i + 1) / 2)⁻¹ :=
    fun n => eq_inv_of_mul_eq_one_right (Mathlib2.bld_sqrt_two_rec_viete_prod a h0 hrec n)
  have hT : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ n * Real.sin (Real.pi / 2 ^ (n + 1))) Filter.atTop (nhds (2 / Real.pi)⁻¹) := by
    simp only [hS]
    exact (Mathlib2.bld_sqrt_two_rec_viete_tendsto a h0 hrec).inv₀ (by positivity)
  have hT2 := ((Filter.tendsto_add_atTop_iff_nat 1).mpr hT).pow 2
  have hlim : ((2 / Real.pi)⁻¹) ^ 2 = Real.pi ^ 2 / 4 := by
    rw [inv_div]; ring
  rw [hlim] at hT2
  refine hT2.congr (fun n => ?_)
  have hy : Real.pi / 2 ^ (n + 1) = 2 * (Real.pi / 2 ^ (n + 1 + 1)) := by
    field_simp; ring
  have hsc := Real.sin_sq_add_cos_sq (Real.pi / 2 ^ (n + 1 + 1))
  have h4 : (4 : ℝ) ^ n = (2 ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [Mathlib2.ana_sqrt_two_rec_closed_form a h0 hrec n, hy, Real.cos_two_mul, h4, pow_succ 2 n]
  linear_combination (4 * (2 ^ n) ^ 2) * hsc
end

-- forge:entry bld2_rank_pow_convex kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_frobenius_rank_inequality: apply Frobenius to the triple (A, A^k, A): rank (A * A^k) + rank (A^k * A) ≤ rank (A^k) + rank (A * A^k * A). -/
theorem bld2_rank_pow_convex (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (k : ℕ) : 2 * Matrix.rank (A ^ (k + 1)) ≤ Matrix.rank (A ^ k) + Matrix.rank (A ^ (k + 2)) := by
  have h := Mathlib2.bld_frobenius_rank_inequality K ι ι ι ι A (A ^ k) A
  have e1 : A * A ^ k = A ^ (k + 1) := (pow_succ' A k).symm
  have e2 : A ^ k * A = A ^ (k + 1) := (pow_succ A k).symm
  have e3 : A ^ (k + 1) * A = A ^ (k + 2) := (pow_succ A (k + 1)).symm
  rw [e1, e2, e3] at h
  omega
end

-- forge:entry bld2_hardy_inequality_tsum kind=proved origin=conjecture
section
/- Uses Mathlib2.r3_hardy_inequality_finite: the partial sums of the nonnegative left series are bounded by 4 * ∑_{k<n} a k^2 ≤ 4 * ∑' a k^2, so the series is summable (summable_of_sum_range_le) and its tsum obeys the same bound. -/
theorem bld2_hardy_inequality_tsum (a : ℕ → ℝ) (h : Summable (fun k : ℕ => a k ^ 2)) : Summable (fun k : ℕ => ((∑ i ∈ Finset.range (k + 1), a i) / ((k : ℝ) + 1)) ^ 2) ∧ ∑' k : ℕ, ((∑ i ∈ Finset.range (k + 1), a i) / ((k : ℝ) + 1)) ^ 2 ≤ 4 * ∑' k : ℕ, a k ^ 2 := by
  have hb : ∀ n : ℕ, ∑ k ∈ Finset.range n, ((∑ i ∈ Finset.range (k + 1), a i) / ((k : ℝ) + 1)) ^ 2 ≤ 4 * ∑' k : ℕ, a k ^ 2 := by
    intro n
    have h1 := Mathlib2.r3_hardy_inequality_finite a n
    have h2 : ∑ k ∈ Finset.range n, a k ^ 2 ≤ ∑' k : ℕ, a k ^ 2 :=
      h.sum_le_tsum (Finset.range n) (fun i _ => sq_nonneg _)
    linarith
  exact ⟨summable_of_sum_range_le (fun n => sq_nonneg _) hb,
    Real.tsum_le_of_sum_range_le (fun n => sq_nonneg _) hb⟩
end

-- forge:entry p4_x_block kind=proved origin=conjecture
section
/- Auditor's helper lemma (not a statement of the paper): if 2^(s-1) < n <= 2^s and t^2 <= 2n < (t+1)^2 then r(n)=s, m(n)=t and x(n) = floor((2n-1)/3) - (s+1)t. -/
theorem p4_x_block (n s t : ℕ) (h1 : n ≤ 2 ^ s) (h2 : 2 ^ s < 2 * n) (h3 : t * t ≤ 2 * n) (h4 : 2 * n < (t + 1) * (t + 1)) : p4_x n = (2 * (n : ℤ) - 1) / 3 - ((s : ℤ) + 1) * (t : ℤ) := by
  have hm : p4_m n = t := by
    unfold p4_m
    exact (Nat.eq_sqrt.2 ⟨h3, h4⟩).symm
  have hr : p4_r n = s := by
    unfold p4_r
    apply le_antisymm
    · exact (Nat.clog_le_iff_le_pow one_lt_two).2 h1
    · by_contra hlt
      push_neg at hlt
      cases s with
      | zero => omega
      | succ s' =>
        have h5 : Nat.clog 2 n ≤ s' := by omega
        have h6 : n ≤ 2 ^ s' := (Nat.clog_le_iff_le_pow one_lt_two).1 h5
        rw [pow_succ] at h2
        omega
  unfold p4_x p4_z
  rw [hm, hr]
end

-- forge:entry bld2_commuting_idempotents_rank_join kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_idempotent_sum_rank twice: A and B - A*B are idempotents with idempotent sum A + B - A*B, so rank (A + B - A*B) = rank A + rank (B - A*B); A*B and B - A*B are idempotents with sum B, so rank B = rank (A*B) + rank (B - A*B). -/
theorem bld2_commuting_idempotents_rank_join (K : Type*) [Field K] [CharZero K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι K) (hA : A * A = A) (hB : B * B = B) (hAB : A * B = B * A) : Matrix.rank (A + B - A * B) + Matrix.rank (A * B) = Matrix.rank A + Matrix.rank B := by
  have hBA : B * A = A * B := hAB.symm
  have hA' : ∀ X : Matrix ι ι K, A * (A * X) = A * X := fun X => by rw [← mul_assoc, hA]
  have hB' : ∀ X : Matrix ι ι K, B * (B * X) = B * X := fun X => by rw [← mul_assoc, hB]
  have hBA' : ∀ X : Matrix ι ι K, B * (A * X) = A * (B * X) := fun X => by
    rw [← mul_assoc, hBA, mul_assoc]
  have hC : (B - A * B) * (B - A * B) = B - A * B := by
    simp only [mul_sub, sub_mul, mul_assoc, hA, hB, hBA, hA', hB', hBA']
    abel
  have hP : (A * B) * (A * B) = A * B := by
    simp only [mul_assoc, hA, hB, hBA, hA', hB', hBA']
  have e1 : A + (B - A * B) = A + B - A * B := by abel
  have e2 : A * B + (B - A * B) = B := by abel
  have h1 := Mathlib2.bld_idempotent_sum_rank K ι A (B - A * B) hA hC (by
    simp only [mul_sub, sub_mul, mul_add, add_mul, mul_assoc, hA, hB, hBA, hA', hB', hBA']
    abel)
  have h2 := Mathlib2.bld_idempotent_sum_rank K ι (A * B) (B - A * B) hP hC (by
    rw [e2]; exact hB)
  rw [e1] at h1
  rw [e2] at h2
  omega
end

-- forge:entry bld2_two_pow_mul_factorial_le_succ_pow kind=proved origin=conjecture
section
/- Uses Mathlib2.gen_an_amgm_finset_ordered_ring (or Mathlib2.an2_amgm_range_pow): apply AM-GM to a i = i + 1 on Finset.range n: n^n * n! ≤ (n(n+1)/2)^n, i.e. 2^n * n^n * n! ≤ n^n * (n+1)^n; cancel n^n for n > 0. -/
theorem bld2_two_pow_mul_factorial_le_succ_pow (n : ℕ) : 2 ^ n * n.factorial ≤ (n + 1) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hs : ∀ m : ℕ, 2 * ∑ i ∈ Finset.range m, ((i : ℤ) + 1) = m * (m + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, mul_add, ih]; push_cast; ring
  have hp : ∏ i ∈ Finset.range n, ((i : ℤ) + 1) = (n.factorial : ℤ) := by
    rw [← Finset.prod_range_add_one_eq_factorial]; push_cast; rfl
  have key := Mathlib2.gen_an_amgm_finset_ordered_ring ℤ ℕ (Finset.range n) (fun i => (i : ℤ) + 1)
    (fun i _ => by positivity)
  simp only [Finset.card_range] at key
  rw [hp] at key
  have h2 : (2 : ℤ) ^ n * ((n : ℤ) ^ n * (n.factorial : ℤ)) ≤ (n : ℤ) ^ n * ((n : ℤ) + 1) ^ n := by
    calc (2 : ℤ) ^ n * ((n : ℤ) ^ n * (n.factorial : ℤ))
        ≤ 2 ^ n * (∑ i ∈ Finset.range n, ((i : ℤ) + 1)) ^ n :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = (n : ℤ) ^ n * ((n : ℤ) + 1) ^ n := by rw [← mul_pow, hs, mul_pow]
  have hnpos : (0 : ℤ) < (n : ℤ) ^ n := by positivity
  have h3 : (2 : ℤ) ^ n * (n.factorial : ℤ) ≤ ((n : ℤ) + 1) ^ n := by
    apply le_of_mul_le_mul_left _ hnpos
    linarith [h2, mul_left_comm ((2 : ℤ) ^ n) ((n : ℤ) ^ n) (n.factorial : ℤ)]
  exact_mod_cast h3
end

-- forge:entry bld2_fibsum_sum kind=proved origin=conjecture
section
/- Uses Mathlib2.p3_prop1 twice: p3_fibsum i = fib (i+2) - 1, so the sum is (p3_fibsum (n+2) - fib 1 - fib 2) - n = fib (n+4) - 1 - 2 - n; or induct on n using p3_prop1 in the step. -/
theorem bld2_fibsum_sum (n : ℕ) : ∑ i ∈ Finset.Icc 1 n, p3_fibsum i + n + 3 = Nat.fib (n + 4) := by
  induction n with
  | zero => simp [Nat.fib]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Mathlib2.p3_prop1 (n + 1)]
    have hpos : 0 < Nat.fib (n + 1 + 2) := Nat.fib_pos.2 (by omega)
    have hf : Nat.fib (n + 1 + 4) = Nat.fib (n + 1 + 2) + Nat.fib (n + 4) := Nat.fib_add_two
    omega
end

-- forge:entry bld2_expanding_compact_isometryEquiv kind=proved origin=conjecture
section
/- Uses Mathlib2.top_expanding_compact_isometry and Mathlib2.top_isometry_compact_surjective: an expanding self-map of a compact metric space is an isometry, hence surjective; with injectivity of isometries this gives a bijective isometry, packaged as an IsometryEquiv. -/
theorem bld2_expanding_compact_isometryEquiv {X : Type*} [MetricSpace X] [CompactSpace X] (f : X → X) (hf : ∀ x y : X, dist x y ≤ dist (f x) (f y)) : ∃ e : X ≃ᵢ X, ∀ x : X, e x = f x := by
  have hi : Isometry f := Mathlib2.top_expanding_compact_isometry f hf
  have hs : Function.Surjective f := Mathlib2.top_isometry_compact_surjective f hi
  exact ⟨⟨Equiv.ofBijective f ⟨hi.injective, hs⟩, hi⟩, fun x => rfl⟩
end

-- forge:entry bld2_fib_odd_index_iff_five_sq_sub_four kind=proved origin=conjecture
section
/- Uses Mathlib2.r3_fib_iff_five_sq_pm_four_is_square and Mathlib2.bld_fib_even_index_iff_five_sq_add_four: y is Fibonacci iff one of the two Pell conditions holds, and the +4 condition characterises even indices; the two conditions hold simultaneously only for y = 1 = fib 1 = fib 2 (x'^2 - x^2 = 8), which settles the overlap, using strict monotonicity of fib from index 2. -/
theorem bld2_fib_odd_index_iff_five_sq_sub_four (y : ℕ) : (∃ n : ℕ, y = Nat.fib (2 * n + 1)) ↔ ∃ x : ℕ, x ^ 2 + 4 = 5 * y ^ 2 := by
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨p3_lucas (2 * n + 1), ?_⟩
    have h := Mathlib2.bld2_lucas_sq_sub_five_fib_sq (2 * n + 1)
    have e : ((-1 : ℤ)) ^ (2 * n + 1) = -1 := by
      rw [pow_succ, pow_mul]; norm_num
    rw [e] at h
    have h' : ((p3_lucas (2 * n + 1) : ℤ)) ^ 2 + 4 = 5 * (Nat.fib (2 * n + 1) : ℤ) ^ 2 := by linarith
    exact_mod_cast h'
  · rintro ⟨x, hx⟩
    obtain ⟨m, hm⟩ := (Mathlib2.r3_fib_iff_five_sq_pm_four_is_square y).2 ⟨x, Or.inr hx⟩
    rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
    · obtain ⟨x', hx'⟩ := (Mathlib2.bld_fib_even_index_iff_five_sq_add_four y).1 ⟨k, hm⟩
      have h8 : x' ^ 2 = x ^ 2 + 8 := by omega
      have hlt : x < x' := by nlinarith
      have hx3 : x ≤ 3 := by nlinarith
      have hx4 : x' ≤ 4 := by nlinarith
      have hy : y = 1 := by
        interval_cases x <;> interval_cases x' <;> first | omega | nlinarith
      exact ⟨0, by rw [hy]; rfl⟩
    · exact ⟨k, hm⟩
end

-- forge:entry bld2_edelstein_no_periodic_points kind=proved origin=conjecture
section
/- Uses Mathlib2.top_edelstein_unique_fixed_point and Mathlib2.bld_edelstein_iterates_tendsto: X is nonempty, so there is a fixed point p and f^[m] x → p; along the subsequence m = n * k the iterates are constantly x, so x = p by uniqueness of limits. -/
theorem bld2_edelstein_no_periodic_points {X : Type*} [MetricSpace X] [CompactSpace X] (f : X → X) (hf : ∀ x y : X, x ≠ y → dist (f x) (f y) < dist x y) (x : X) (n : ℕ) (hn : 0 < n) (hx : f^[n] x = x) : f x = x := by
  haveI : Nonempty X := ⟨x⟩
  obtain ⟨p, hp, -⟩ := Mathlib2.top_edelstein_unique_fixed_point f hf
  have ht := Mathlib2.bld_edelstein_iterates_tendsto f hf p hp x
  have hm : Filter.Tendsto (fun k : ℕ => n * k) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop' hn
  have hc := ht.comp hm
  have he : ((fun m => f^[m] x) ∘ fun k : ℕ => n * k) = fun _ => x := by
    funext k
    simp only [Function.comp_apply]
    rw [Function.iterate_mul]
    exact Function.iterate_fixed hx k
  rw [he] at hc
  have hxp : x = p := tendsto_nhds_unique tendsto_const_nhds hc
  rw [hxp]; exact hp
end

-- forge:entry bld2_rat_sq_add_sq_ne_prime_mul_coprime kind=proved origin=conjecture
section
/- Uses Mathlib2.nt2_prime_three_mod_four_dvd_sq_add_sq (generalising Mathlib2.bld_rat_sq_add_sq_ne_prime_three_mod_four): clear denominators to a^2 + b^2 = p * m * d^2 in ℤ with d ≠ 0; by strong induction on |d| (or on the p-adic valuation), p ∣ a and p ∣ b, so p^2 ∣ p * m * d^2, so p ∣ d (as p ∤ m), and dividing a, b, d by p gives a smaller solution. -/
theorem bld2_rat_sq_add_sq_ne_prime_mul_coprime_aux1 (p m : ℕ) (hp : p.Prime) (h3 : p % 4 = 3) (hm : ¬ p ∣ m) (d : ℕ) : ∀ a b : ℤ, a ^ 2 + b ^ 2 = (p : ℤ) * (m : ℤ) * (d : ℤ) ^ 2 → d = 0 := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro a b h
    have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := Mathlib2.nt2_prime_three_mod_four_dvd_sq_add_sq p hp h3 a b
      ⟨(m : ℤ) * (d : ℤ) ^ 2, by rw [h]; ring⟩
    have h1 : (p : ℤ) * (a' ^ 2 + b' ^ 2) = (m : ℤ) * (d : ℤ) ^ 2 :=
      mul_left_cancel₀ hpZ (by linear_combination h)
    have hdvd : (p : ℤ) ∣ ((m * d ^ 2 : ℕ) : ℤ) := ⟨a' ^ 2 + b' ^ 2, by push_cast; rw [h1]⟩
    rw [Int.natCast_dvd_natCast] at hdvd
    have hpd : p ∣ d := by
      rcases hp.dvd_mul.mp hdvd with h' | h'
      · exact absurd h' hm
      · exact hp.dvd_of_dvd_pow h'
    obtain ⟨d', rfl⟩ := hpd
    have h2 : a' ^ 2 + b' ^ 2 = (p : ℤ) * (m : ℤ) * (d' : ℤ) ^ 2 := by
      apply mul_left_cancel₀ hpZ
      push_cast at h1
      linear_combination h1
    rcases Nat.eq_zero_or_pos d' with rfl | hd'
    · simp
    · have hlt : d' < p * d' := by
        have := hp.two_le
        nlinarith
      have := ih d' hlt a' b' h2
      omega

theorem bld2_rat_sq_add_sq_ne_prime_mul_coprime (p m : ℕ) (hp : p.Prime) (h3 : p % 4 = 3) (hm : ¬ p ∣ m) (x y : ℚ) : x ^ 2 + y ^ 2 ≠ (p : ℚ) * (m : ℚ) := by
  intro h
  have hxn : (x.num : ℚ) = x * (x.den : ℚ) := (Rat.mul_den_eq_num x).symm
  have hyn : (y.num : ℚ) = y * (y.den : ℚ) := (Rat.mul_den_eq_num y).symm
  have hQ : ((x.num : ℚ) * (y.den : ℚ)) ^ 2 + ((y.num : ℚ) * (x.den : ℚ)) ^ 2
      = (p : ℚ) * (m : ℚ) * ((x.den : ℚ) * (y.den : ℚ)) ^ 2 := by
    rw [hxn, hyn]
    linear_combination ((x.den : ℚ) * (y.den : ℚ)) ^ 2 * h
  have hZ : (x.num * (y.den : ℤ)) ^ 2 + (y.num * (x.den : ℤ)) ^ 2
      = (p : ℤ) * (m : ℤ) * ((x.den * y.den : ℕ) : ℤ) ^ 2 := by
    exact_mod_cast hQ
  have := bld2_rat_sq_add_sq_ne_prime_mul_coprime_aux1 p m hp h3 hm _ _ _ hZ
  have hx := x.den_pos
  have hy := y.den_pos
  have := Nat.mul_pos hx hy
  omega
end

end Mathlib2
