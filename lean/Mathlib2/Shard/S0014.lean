/- Mathlib2 分片 14（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0013
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry geo_cos_pi_div_seven_prod kind=proved origin=conjecture
section
/- cos(π/7)cos(2π/7)cos(4π/7) = −1/8 — multiply by 8 sin(π/7) ≠ 0 and apply sin 2x = 2 sin x cos x three times to get sin(8π/7) = −sin(π/7). -/
theorem geo_cos_pi_div_seven_prod : Real.cos (Real.pi / 7) * Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7) = -1 / 8 := by
  have hs : 0 < Real.sin (Real.pi / 7) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have h1 := Real.sin_two_mul (Real.pi / 7)
  have h2 := Real.sin_two_mul (2 * Real.pi / 7)
  have h3 := Real.sin_two_mul (4 * Real.pi / 7)
  have h4 := Real.sin_add_pi (Real.pi / 7)
  rw [show 2 * (Real.pi / 7) = 2 * Real.pi / 7 by ring] at h1
  rw [show 2 * (2 * Real.pi / 7) = 4 * Real.pi / 7 by ring] at h2
  rw [show 2 * (4 * Real.pi / 7) = 8 * Real.pi / 7 by ring] at h3
  rw [show Real.pi / 7 + Real.pi = 8 * Real.pi / 7 by ring] at h4
  apply mul_left_cancel₀ hs.ne'
  linear_combination (1 / 8) * h4 - (1 / 8) * h3 - (1 / 4) * Real.cos (4 * Real.pi / 7) * h2
    - (1 / 2) * Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7) * h1
end

-- forge:entry geo_centroid_sum_sq_dist kind=proved origin=conjecture
section
/- For the centroid g of triangle abc, |ag|² + |bg|² + |cg|² = (|ab|² + |bc|² + |ca|²)/3 — a − g = ((a−b) + (a−c))/3 etc., expand all squared norms into inner products. -/
theorem geo_centroid_sum_sq_dist {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a b c : V) : ‖a - (1 / 3 : ℝ) • (a + b + c)‖ ^ 2 + ‖b - (1 / 3 : ℝ) • (a + b + c)‖ ^ 2 + ‖c - (1 / 3 : ℝ) • (a + b + c)‖ ^ 2 = (‖a - b‖ ^ 2 + ‖b - c‖ ^ 2 + ‖c - a‖ ^ 2) / 3 := by
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  have h1 := real_inner_comm a b
  have h2 := real_inner_comm a c
  have h3 := real_inner_comm b c
  rw [h1, h2, h3]
  ring
end

-- forge:entry top_finite_monotone_iterate_bot_fixed kind=proved origin=conjecture
section
/- On a finite poset with bottom, iterating a monotone map from ⊥ reaches a fixed point — n ↦ f^[n] ⊥ is monotone; if never stationary it would be strictly monotone hence injective ℕ → α, contradicting finiteness. -/
theorem top_finite_monotone_iterate_bot_fixed {α : Type*} [PartialOrder α] [OrderBot α] [Finite α] (f : α → α) (hf : Monotone f) : ∃ n : ℕ, f (f^[n] ⊥) = f^[n] ⊥ := by
  by_contra hcon
  push_neg at hcon
  have hmono : Monotone fun n => f^[n] ⊥ := hf.monotone_iterate_of_le_map bot_le
  have hs : StrictMono fun n => f^[n] ⊥ := by
    apply strictMono_nat_of_lt_succ
    intro n
    refine lt_of_le_of_ne (hmono (Nat.le_succ n)) ?_
    intro heq
    apply hcon n
    rw [← Function.iterate_succ_apply' f n ⊥]
    exact heq.symm
  exact not_injective_infinite_finite _ hs.injective
end

-- forge:entry p3_prop1 kind=proved origin=paper
section
/- S_n = F_{n+2} - 1 -/
theorem p3_prop1_aux1 (n : ℕ) : p3_fibsum n + 1 = Nat.fib (n + 2) := by
  unfold p3_fibsum
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), add_right_comm, ih, Nat.fib_add_two (n := n + 1)]
    have e : n + 1 + 1 = n + 2 := rfl
    rw [e]
    omega
theorem p3_prop1 (n : ℕ) : p3_fibsum n = Nat.fib (n + 2) - 1 := by
  have := p3_prop1_aux1 n
  omega
end

-- forge:entry geo_euler_quadrilateral kind=proved origin=conjecture
section
/- Euler's quadrilateral theorem: the sum of the squared sides equals the sum of the squared diagonals plus four times the squared distance between the midpoints of the diagonals — expand every squared norm into inner products. -/
theorem geo_euler_quadrilateral {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a b c d : V) : ‖a - b‖ ^ 2 + ‖b - c‖ ^ 2 + ‖c - d‖ ^ 2 + ‖d - a‖ ^ 2 = ‖a - c‖ ^ 2 + ‖b - d‖ ^ 2 + 4 * ‖(1 / 2 : ℝ) • (a + c) - (1 / 2 : ℝ) • (b + d)‖ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  have h1 := real_inner_comm a b
  have h2 := real_inner_comm a c
  have h3 := real_inner_comm a d
  have h4 := real_inner_comm b c
  have h5 := real_inner_comm b d
  have h6 := real_inner_comm c d
  rw [h1, h2, h3, h4, h5, h6]
  ring
end

-- forge:entry p3_remark2 kind=proved origin=paper
section
/- k is self-summable iff F_k divides F_{F_k+2} - 1 -/
theorem p3_remark2 (k : ℕ) : p3_self_summable k ↔ Nat.fib k ∣ Nat.fib (Nat.fib k + 2) - 1 := by
  rw [← p3_prop1]
  rfl
end

-- forge:entry geo_sum_sq_dist_roots_of_unity kind=proved origin=conjecture
section
/- The sum of squared distances from a point of the unit circle to the vertices of the regular n-gon inscribed in it is 2n — ‖z − ζ^k‖² = 2 − 2 Re(z · conj ζ^k), and Σ ζ^k = 0 for the primitive root ζ = exp(2πi/n), n ≥ 2. -/
theorem geo_sum_sq_dist_roots_of_unity (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : ‖z‖ = 1) : ∑ k ∈ Finset.range n, ‖z - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / (n : ℂ))‖ ^ 2 = 2 * (n : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have hζ := Complex.isPrimitiveRoot_exp n hn0
  have hζ1 := hζ.norm'_eq_one hn0
  have hsum := hζ.geom_sum_eq_zero (by omega : 1 < n)
  have each : ∀ k ∈ Finset.range n,
      ‖z - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / (n : ℂ))‖ ^ 2
        = 2 - 2 * (z * (starRingEnd ℂ) (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) ^ k)).re := by
    intro k _
    have e : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / (n : ℂ))
        = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) ^ k := by
      rw [← Complex.exp_nat_mul]; congr 1; ring
    rw [e, Complex.sq_norm, Complex.normSq_sub, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
      hz, norm_pow, hζ1]
    norm_num
  rw [Finset.sum_congr rfl each, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    ← Finset.mul_sum, ← Complex.re_sum, ← Finset.mul_sum, ← map_sum, hsum]
  simp [mul_comm]
end

-- forge:entry top_compact_closed_disjoint_dist_pos kind=proved origin=conjecture
section
/- A compact set and a disjoint closed set in a metric space are a positive distance apart — transfer EMetric.exists_pos_forall_lt_edist to dist, or minimize infDist · C over K. -/
theorem top_compact_closed_disjoint_dist_pos {X : Type*} [MetricSpace X] (K C : Set X) (hK : IsCompact K) (hC : IsClosed C) (hd : Disjoint K C) : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ C, δ ≤ dist x y := by
  obtain ⟨r, hr, h⟩ := EMetric.exists_pos_forall_lt_edist hK hC hd
  refine ⟨r, by exact_mod_cast hr, fun x hx y hy => ?_⟩
  have h1 := h x hx y hy
  rw [edist_nndist, ENNReal.coe_lt_coe] at h1
  have h2 : (r : ℝ) < nndist x y := by exact_mod_cast h1
  rw [coe_nndist] at h2
  exact h2.le
end

-- forge:entry geo_sum_cos_two_pi_mul_div kind=proved origin=conjecture
section
/- The real parts of the n-th roots of unity sum to zero for n ≥ 2 — take the real part of the geometric sum Σ ζ^k = 0 for ζ = exp(2πi/n) (a primitive n-th root, IsPrimitiveRoot.geom_sum_eq_zero). -/
theorem geo_sum_cos_two_pi_mul_div (n : ℕ) (hn : 2 ≤ n) : ∑ k ∈ Finset.range n, Real.cos (2 * Real.pi * (k : ℝ) / (n : ℝ)) = 0 := by
  have hn0 : n ≠ 0 := by omega
  have hζ := Complex.isPrimitiveRoot_exp n hn0
  have hsum := hζ.geom_sum_eq_zero (by omega : 1 < n)
  have each : ∀ k ∈ Finset.range n, Real.cos (2 * Real.pi * (k : ℝ) / (n : ℝ))
      = (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) ^ k).re := by
    intro k _
    rw [← Complex.exp_nat_mul,
      show (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))
        = ((2 * Real.pi * (k : ℝ) / (n : ℝ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re]
  rw [Finset.sum_congr rfl each, ← Complex.re_sum, hsum]
  simp
end

-- forge:entry p3_remark3 kind=proved origin=paper
section
/- F_a - F_b = F_u L_v if a = b mod 4, = F_v L_u if a = b+2 mod 4, where u=(a-b)/2, v=(a+b)/2 -/
theorem p3_remark3_aux0 (m : ℕ) : (Nat.fib (m + 2) : ℤ) = Nat.fib m + Nat.fib (m + 1) := by
  rw [Nat.fib_add_two]; push_cast; ring
theorem p3_remark3_aux1 (n : ℕ) : (p3_lucas n : ℤ) = 2 * Nat.fib (n + 1) - Nat.fib n := by
  unfold p3_lucas
  have := Nat.fib_le_fib_succ (n := n)
  rw [Nat.cast_sub (by omega)]
  push_cast; ring
theorem p3_remark3_aux2 (t b : ℕ) : (Nat.fib (b + 4 * t) : ℤ) - Nat.fib b = Nat.fib (2 * t) * (2 * Nat.fib (b + 2 * t + 1) - Nat.fib (b + 2 * t)) := by
  have hc := p3_aux_period_aux1 (2 * t)
  rw [Even.neg_one_pow (even_two_mul t), p3_remark3_aux0] at hc
  induction b using Nat.twoStepInduction with
  | zero =>
    have h1 := congrArg (Nat.cast : ℕ → ℤ) (Nat.fib_two_mul (2 * t))
    have := Nat.fib_le_fib_succ (n := 2 * t)
    rw [Nat.cast_mul, Nat.cast_sub (by omega)] at h1
    push_cast at h1
    rw [show 0 + 4 * t = 2 * (2 * t) by ring, h1]
    simp
  | one =>
    have h1 := congrArg (Nat.cast : ℕ → ℤ) (Nat.fib_two_mul_add_one (2 * t))
    push_cast at h1
    rw [show 1 + 4 * t = 2 * (2 * t) + 1 by ring, h1, show 1 + 2 * t + 1 = 2 * t + 2 by ring, show 1 + 2 * t = 2 * t + 1 by ring, p3_remark3_aux0]
    simp
    linear_combination hc
  | more b ih0 ih1 =>
    have e1 := p3_remark3_aux0 (b + 4 * t)
    have e2 := p3_remark3_aux0 b
    have e3 := p3_remark3_aux0 (b + 2 * t + 1)
    have e4 := p3_remark3_aux0 (b + 2 * t)
    rw [show b + 2 + 4 * t = b + 4 * t + 2 by ring, show b + 2 + 2 * t + 1 = b + 2 * t + 1 + 2 by ring, show b + 2 + 2 * t = b + 2 * t + 2 by ring]
    rw [show b + 1 + 4 * t = b + 4 * t + 1 by ring, show b + 1 + 2 * t + 1 = b + 2 * t + 1 + 1 by ring, show b + 1 + 2 * t = b + 2 * t + 1 by ring] at ih1
    linear_combination ih0 + ih1 + e1 - e2 - 2 * (Nat.fib (2 * t) : ℤ) * e3 + (Nat.fib (2 * t) : ℤ) * e4
theorem p3_remark3_aux3 (t b : ℕ) : (Nat.fib (b + 2 + 4 * t) : ℤ) - Nat.fib b = Nat.fib (b + 2 * t + 1) * (2 * Nat.fib (2 * t + 1 + 1) - Nat.fib (2 * t + 1)) := by
  have hc := p3_aux_period_aux1 (2 * t + 1)
  rw [Odd.neg_one_pow (odd_two_mul_add_one t), p3_remark3_aux0 (2 * t + 1)] at hc
  induction b using Nat.twoStepInduction with
  | zero =>
    have h1 := congrArg (Nat.cast : ℕ → ℤ) (Nat.fib_two_mul (2 * t + 1))
    have := Nat.fib_le_fib_succ (n := 2 * t + 1)
    rw [Nat.cast_mul, Nat.cast_sub (by omega)] at h1
    push_cast at h1
    rw [show 0 + 2 + 4 * t = 2 * (2 * t + 1) by ring, h1]
    simp
  | one =>
    have h1 := congrArg (Nat.cast : ℕ → ℤ) (Nat.fib_two_mul_add_one (2 * t + 1))
    push_cast at h1
    rw [show 1 + 2 + 4 * t = 2 * (2 * t + 1) + 1 by ring, h1, show 1 + 2 * t + 1 = 2 * t + 1 + 1 by ring]
    simp
    linear_combination -hc
  | more b ih0 ih1 =>
    have e1 := p3_remark3_aux0 (b + 2 + 4 * t)
    have e2 := p3_remark3_aux0 b
    have e3 := p3_remark3_aux0 (b + 2 * t + 1)
    rw [show b + 2 + 2 + 4 * t = b + 2 + 4 * t + 2 by ring, show b + 2 + 2 * t + 1 = b + 2 * t + 1 + 2 by ring]
    rw [show b + 1 + 2 + 4 * t = b + 2 + 4 * t + 1 by ring, show b + 1 + 2 * t + 1 = b + 2 * t + 1 + 1 by ring] at ih1
    linear_combination ih0 + ih1 + e1 - e2 - (2 * (Nat.fib (2 * t + 1 + 1) : ℤ) - Nat.fib (2 * t + 1)) * e3
theorem p3_remark3 (a b : ℕ) (hba : b ≤ a) : (a ≡ b [MOD 4] → (Nat.fib a : ℤ) - Nat.fib b = Nat.fib ((a - b) / 2) * p3_lucas ((a + b) / 2)) ∧ (a ≡ b + 2 [MOD 4] → (Nat.fib a : ℤ) - Nat.fib b = Nat.fib ((a + b) / 2) * p3_lucas ((a - b) / 2)) := by
  constructor
  · intro h
    have ha : a = b + 4 * ((a - b) / 4) := by unfold Nat.ModEq at h; omega
    generalize (a - b) / 4 = t at ha
    subst ha
    rw [show (b + 4 * t - b) / 2 = 2 * t by omega, show (b + 4 * t + b) / 2 = b + 2 * t by omega, p3_remark3_aux1]
    exact p3_remark3_aux2 t b
  · intro h
    have ha : a = b + 2 + 4 * ((a - b - 2) / 4) := by unfold Nat.ModEq at h; omega
    generalize (a - b - 2) / 4 = t at ha
    subst ha
    rw [show (b + 2 + 4 * t - b) / 2 = 2 * t + 1 by omega, show (b + 2 + 4 * t + b) / 2 = b + 2 * t + 1 by omega, p3_remark3_aux1]
    exact p3_remark3_aux3 t b
end

-- forge:entry top_connected_metric_sphere_nonempty kind=proved origin=conjecture
section
/- In a connected metric space every radius between 0 and dist x y is attained as a distance from x — intermediate value theorem for the continuous map z ↦ dist x z on a preconnected space, with values 0 at x and dist x y at y. -/
theorem top_connected_metric_sphere_nonempty {X : Type*} [MetricSpace X] [PreconnectedSpace X] (x y : X) (r : ℝ) (h0 : 0 ≤ r) (hr : r ≤ dist x y) : ∃ z : X, dist x z = r := by
  have hc : Continuous fun z : X => dist x z := continuous_const.dist continuous_id
  have h := intermediate_value_univ x y hc
  have hm : r ∈ Set.Icc ((fun z : X => dist x z) x) ((fun z : X => dist x z) y) := by
    simp only [dist_self]
    exact ⟨h0, hr⟩
  obtain ⟨z, hz⟩ := h hm
  exact ⟨z, hz⟩
end

-- forge:entry top_edelstein_unique_fixed_point kind=proved origin=conjecture
section
/- Edelstein: a strictly distance-decreasing self-map of a nonempty compact metric space has exactly one fixed point — f is 1-Lipschitz hence continuous, x ↦ dist x (f x) attains its minimum at some p; if f p ≠ p then dist (f p) (f (f p)) < dist p (f p) contradicts minimality; uniqueness is immediate from strictness. -/
theorem top_edelstein_unique_fixed_point {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X] (f : X → X) (hf : ∀ x y : X, x ≠ y → dist (f x) (f y) < dist x y) : ∃! p : X, f p = p := by
  have hlip : LipschitzWith 1 f := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    by_cases hxy : x = y
    · subst hxy; simp
    · have := hf x y hxy
      simp only [NNReal.coe_one, one_mul]
      exact this.le
  have hc : Continuous f := hlip.continuous
  have hg : Continuous (fun x : X => dist x (f x)) := continuous_id.dist hc
  obtain ⟨p, -, hp⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty (α := X)) hg.continuousOn
  have hfp : f p = p := by
    by_contra hne
    have h1 := hf (f p) p hne
    have h2 : dist p (f p) ≤ dist (f p) (f (f p)) := hp (Set.mem_univ (f p))
    rw [dist_comm (f (f p)) (f p), dist_comm (f p) p] at h1
    linarith
  refine ⟨p, hfp, ?_⟩
  intro q hq
  by_contra hne
  have := hf q p hne
  rw [hq, hfp] at this
  exact lt_irrefl _ this
end

-- forge:entry top_uniformly_discrete_complete kind=proved origin=conjecture
section
/- A metric space whose distinct points are at distance at least 1 is complete — a Cauchy sequence is eventually within 1/2 of itself hence eventually constant, hence convergent (Metric.complete_of_cauchySeq_tendsto). -/
theorem top_uniformly_discrete_complete {X : Type*} [MetricSpace X] (h : ∀ x y : X, x ≠ y → 1 ≤ dist x y) : CompleteSpace X := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hu 1 one_pos
  refine ⟨u N, tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_⟩
  by_contra hne
  exact absurd (hN n hn) (not_lt.mpr (h _ _ hne))
end

-- forge:entry top_connected_metric_uncountable kind=proved origin=conjecture
section
/- A connected metric space with two distinct points is uncountable — the image of z ↦ dist x z contains the interval [0, dist x y] by the intermediate value theorem, a nondegenerate real interval is uncountable, and images of countable sets are countable. -/
theorem top_connected_metric_uncountable {X : Type*} [MetricSpace X] [PreconnectedSpace X] (x y : X) (h : x ≠ y) : ¬ (Set.univ : Set X).Countable := by
  intro hc
  have hcont : Continuous (fun z : X => dist x z) := continuous_const.dist continuous_id
  have hpre : IsPreconnected ((fun z : X => dist x z) '' Set.univ) :=
    isPreconnected_univ.image _ hcont.continuousOn
  have h0 : (0 : ℝ) ∈ (fun z : X => dist x z) '' Set.univ := ⟨x, Set.mem_univ x, dist_self x⟩
  have hd : dist x y ∈ (fun z : X => dist x z) '' Set.univ := ⟨y, Set.mem_univ y, rfl⟩
  have hsub := hpre.Icc_subset h0 hd
  have hcnt : (Set.Icc (0 : ℝ) (dist x y)).Countable := (hc.image _).mono hsub
  have := Cardinal.Real.Icc_countable_iff.mp hcnt
  exact absurd (dist_pos.mpr h) (not_lt.mpr this)
end

-- forge:entry top_tendsto_of_subseq_limits_unique kind=proved origin=conjecture
section
/- In a compact metric space a sequence all of whose convergent subsequences have limit a converges to a — otherwise infinitely many terms stay ε-far from a; extract a subsequence of those, then a convergent sub-subsequence by sequential compactness, whose limit is ≠ a. -/
theorem top_tendsto_of_subseq_limits_unique {X : Type*} [MetricSpace X] [CompactSpace X] (u : ℕ → X) (a : X) (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ b : X, Filter.Tendsto (u ∘ φ) Filter.atTop (nhds b) → b = a) : Filter.Tendsto u Filter.atTop (nhds a) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨φ, hφ, hφ2⟩ := Filter.strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨b, ψ, hψ, hb⟩ := CompactSpace.tendsto_subseq (u ∘ ns ∘ φ)
  have hba : b = a := h ((ns ∘ φ) ∘ ψ) (hφ2.comp hψ) b hb
  subst hba
  exact ⟨φ ∘ ψ, hb⟩
end

-- forge:entry top_galois_u_eq_sSup kind=proved origin=conjecture
section
/- The upper adjoint of a Galois connection between complete lattices is given by u b = sSup {a | l a ≤ b} — the set equals Set.Iic (u b) by the adjunction, whose supremum is u b. -/
theorem top_galois_u_eq_sSup {α β : Type*} [CompleteLattice α] [CompleteLattice β] (l : α → β) (u : β → α) (gc : GaloisConnection l u) (b : β) : u b = sSup {a : α | l a ≤ b} := by
  apply le_antisymm
  · exact le_sSup (gc.l_u_le b)
  · exact sSup_le (fun a ha => (gc a b).mp ha)
end

-- forge:entry top_isometry_compact_surjective kind=proved origin=conjecture
section
/- An isometry of a compact metric space into itself is surjective — if y is not in the (closed) range, pick ε > 0 with ball y ε disjoint from range f; the orbit f^[n] y then satisfies dist (f^[m] y) (f^[n] y) = dist y (f^[n-m] y) ≥ ε, so it has no convergent subsequence, contradicting sequential compactness. -/
theorem top_isometry_compact_surjective {X : Type*} [MetricSpace X] [CompactSpace X] (f : X → X) (hf : Isometry f) : Function.Surjective f := by
  by_contra hns
  have hex : ∃ y, y ∉ Set.range f := by
    by_contra h
    push_neg at h
    exact hns (fun y => h y)
  obtain ⟨y, hy⟩ := hex
  have hclosed : IsClosed (Set.range f) := (isCompact_range hf.continuous).isClosed
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hclosed.isOpen_compl y hy
  obtain ⟨a, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq (fun n : ℕ => f^[n] y)
  have hcau := hlim.cauchySeq
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hcau ε hε
  have h1 := hN N le_rfl (N + 1) (Nat.le_succ N)
  have hlt : φ N < φ (N + 1) := hφ (Nat.lt_succ_self N)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
  have hit : ∀ (n : ℕ) (x z : X), dist (f^[n] x) (f^[n] z) = dist x z := by
    intro n
    induction n with
    | zero => intro x z; rfl
    | succ n ih => intro x z; rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hf.dist_eq]
  simp only [Function.comp_apply] at h1
  rw [hk, show φ N + k + 1 = φ N + (k + 1) by ring, Function.iterate_add_apply, hit] at h1
  have hmem : f^[k + 1] y ∈ Metric.ball y ε := by
    rw [Metric.mem_ball, dist_comm]; exact h1
  exact hball hmem ⟨f^[k] y, (Function.iterate_succ_apply' f k y).symm⟩
end

-- forge:entry top_distrib_lattice_median kind=proved origin=conjecture
section
/- The median identity in a distributive lattice — ≤ holds in every lattice (each meet is below each join); for ≥ expand the right side using distributivity and absorb. -/
theorem top_distrib_lattice_median {α : Type*} [DistribLattice α] (a b c : α) : (a ⊓ b) ⊔ (b ⊓ c) ⊔ (c ⊓ a) = (a ⊔ b) ⊓ (b ⊔ c) ⊓ (c ⊔ a) := by
  apply le_antisymm
  · refine sup_le (sup_le ?_ ?_) ?_ <;> refine le_inf (le_inf ?_ ?_) ?_ <;>
      first
        | exact inf_le_left.trans le_sup_left
        | exact inf_le_left.trans le_sup_right
        | exact inf_le_right.trans le_sup_left
        | exact inf_le_right.trans le_sup_right
  · have e1 : (a ⊔ b) ⊓ (b ⊔ c) = b ⊔ (a ⊓ c) := by rw [sup_comm a b, ← sup_inf_left]
    rw [e1, inf_sup_right, inf_sup_left]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact le_sup_of_le_left le_sup_right
    · exact le_sup_of_le_left (le_sup_of_le_left (le_of_eq (inf_comm _ _)))
    · exact le_sup_of_le_right (inf_le_left.trans (le_of_eq (inf_comm _ _)))
end

-- forge:entry p3_thm1_corrected kind=proved origin=paper
section
/- CORRECTED Theorem 1 (auditor's correction, not the paper's wording): S_p = 1 mod p if p = 1,4 mod 5 and S_p = -2 mod p if p = 2,3 mod 5 -/
theorem p3_thm1_corrected_aux0 : ((1:ℕ):ZMod 5) ≠ 0 ∧ ((4:ℕ):ZMod 5) ≠ 0 ∧ IsSquare ((1:ℕ):ZMod 5) ∧ IsSquare ((4:ℕ):ZMod 5) ∧ ¬ IsSquare ((2:ℕ):ZMod 5) ∧ ¬ IsSquare ((3:ℕ):ZMod 5) := by decide
theorem p3_thm1_corrected_aux1 (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) :
    ((p % 5 = 1 ∨ p % 5 = 4) → (Nat.fib p : ZMod p) = 1 ∧ (Nat.fib (p + 1) : ZMod p) = 1) ∧
    ((p % 5 = 2 ∨ p % 5 = 3) → (Nat.fib p : ZMod p) = -1 ∧ (Nat.fib (p + 1) : ZMod p) = 0) := by
  haveI := Fact.mk hp
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hL, hF⟩ := p3_aux_fib_prime p hp h2
  have e := legendreSym.eq_pow p ((5 : ℕ) : ℤ)
  have qr := legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p) (by norm_num) h2
  have cast5 : (((p : ℕ) : ℤ) : ZMod 5) = ((p % 5 : ℕ) : ZMod 5) := by
    rw [Int.cast_natCast, ZMod.natCast_mod]
  have hF' : (Nat.fib p : ZMod p) = ((legendreSym p ((5 : ℕ) : ℤ) : ℤ) : ZMod p) := by
    rw [e]
    have := (ZMod.intCast_eq_intCast_iff _ _ _).mpr hF
    push_cast at this ⊢
    exact this
  have hL' : 2 * (Nat.fib (p + 1) : ZMod p) - Nat.fib p = 1 := by
    have := (ZMod.intCast_eq_intCast_iff _ _ _).mpr hL
    push_cast at this
    exact this
  have two_ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    have := hp.two_le
    omega
  constructor
  · intro h
    have hl : legendreSym 5 (p : ℤ) = 1 := by
      rw [legendreSym.eq_one_iff 5 (by rw [cast5]; rcases h with h | h <;> rw [h] <;> [exact p3_thm1_corrected_aux0.1; exact p3_thm1_corrected_aux0.2.1]), cast5]
      rcases h with h | h <;> rw [h] <;> [exact p3_thm1_corrected_aux0.2.2.1; exact p3_thm1_corrected_aux0.2.2.2.1]
    rw [qr, hl] at hF'
    have h1 : (Nat.fib p : ZMod p) = 1 := by simpa using hF'
    refine ⟨h1, ?_⟩
    rw [h1] at hL'
    apply mul_left_cancel₀ two_ne
    linear_combination hL'
  · intro h
    have hl : legendreSym 5 (p : ℤ) = -1 := by
      rw [legendreSym.eq_neg_one_iff 5, cast5]
      rcases h with h | h <;> rw [h] <;> [exact p3_thm1_corrected_aux0.2.2.2.2.1; exact p3_thm1_corrected_aux0.2.2.2.2.2]
    rw [qr, hl] at hF'
    have h1 : (Nat.fib p : ZMod p) = -1 := by simpa using hF'
    refine ⟨h1, ?_⟩
    rw [h1] at hL'
    apply mul_left_cancel₀ two_ne
    linear_combination hL'
theorem p3_thm1_corrected (p : ℕ) (hp : p.Prime) (h5 : 5 < p) : ((p % 5 = 1 ∨ p % 5 = 4) → (p3_fibsum p : ℤ) ≡ 1 [ZMOD p]) ∧ ((p % 5 = 2 ∨ p % 5 = 3) → (p3_fibsum p : ℤ) ≡ -2 [ZMOD p]) := by
  obtain ⟨hA, hB⟩ := p3_thm1_corrected_aux1 p hp (by omega)
  have hs : (p3_fibsum p : ℤ) = Nat.fib p + Nat.fib (p + 1) - 1 := by
    have := p3_prop1_aux1 p
    rw [Nat.fib_add_two] at this
    have : (p3_fibsum p : ℤ) + 1 = Nat.fib p + Nat.fib (p + 1) := by exact_mod_cast this
    linarith
  constructor
  · intro h
    obtain ⟨a, b⟩ := hA h
    rw [← ZMod.intCast_eq_intCast_iff, hs]
    push_cast
    rw [a, b]; ring
  · intro h
    obtain ⟨a, b⟩ := hB h
    rw [← ZMod.intCast_eq_intCast_iff, hs]
    push_cast
    rw [a, b]; ring
end

-- forge:entry top_countable_compact_t2_isolated_point kind=proved origin=conjecture
section
/- A nonempty countable compact Hausdorff space has an isolated point — compact Hausdorff spaces are Baire; if no singleton were open, each complement {x}ᶜ would be open and dense, so their countable intersection (which is empty) would be dense, contradicting nonemptiness. -/
theorem top_countable_compact_t2_isolated_point {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [Countable X] [Nonempty X] : ∃ x : X, IsOpen ({x} : Set X) := by
  by_contra h
  push_neg at h
  have hd : Dense (⋂ x : X, ({x}ᶜ : Set X)) :=
    dense_iInter_of_isOpen (fun x => isOpen_compl_singleton)
      (fun x => dense_compl_singleton_iff_not_open.2 (h x))
  obtain ⟨z, hz⟩ := hd.nonempty
  exact (Set.mem_iInter.1 hz z) rfl
end

end Mathlib2
