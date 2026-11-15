/- Mathlib2 分片 16（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0015
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry bld_sum_inv_sqrt_div_sqrt_tendsto kind=proved origin=conjecture
section
/- Uses Mathlib2.an2_sum_inv_sqrt_bounds: squeeze between 2(sqrt(n+1) - 1)/sqrt n and 2, both tending to 2. -/
open Filter Topology

theorem bld_sum_inv_sqrt_div_sqrt_tendsto : Filter.Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, 1 / Real.sqrt ((i : ℝ) + 1)) / Real.sqrt (n : ℝ)) Filter.atTop (nhds 2) := by
  have hsq : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop := by
    refine tendsto_atTop_atTop.2 (fun b => ⟨⌈b ^ 2⌉₊, fun n hn => ?_⟩)
    have h1 : b ^ 2 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    calc b ≤ |b| := le_abs_self b
      _ = Real.sqrt (b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
      _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt h1
  have hlow : Tendsto (fun n : ℕ => (2:ℝ) - 2 / Real.sqrt (n : ℝ)) atTop (𝓝 2) := by
    have := (tendsto_const_nhds (x := (2:ℝ))).sub (hsq.const_div_atTop 2)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have h1 := (Mathlib2.an2_sum_inv_sqrt_bounds n).1
    have h2 : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    rw [le_div_iff₀ hpos, sub_mul, div_mul_cancel₀ _ hpos.ne']
    linarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    rw [div_le_iff₀ hpos]
    exact (Mathlib2.an2_sum_inv_sqrt_bounds n).2
end

-- forge:entry bld_exists_bipartite_subgraph_half_edges kind=proved origin=conjecture
section
/- Uses Mathlib2.comb_exists_cut_half_edges: take the cut s from the library theorem and let H be the subgraph of G consisting of edges between s and sᶜ; it is 2-coloured by membership in s, and its edges biject with the ordered pairs counted in the cut. -/
theorem bld_exists_bipartite_subgraph_half_edges (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : ∃ H : SimpleGraph V, H ≤ G ∧ H.Colorable 2 ∧ G.edgeSet.ncard ≤ 2 * H.edgeSet.ncard := by
  obtain ⟨s, hs⟩ := Mathlib2.comb_exists_cut_half_edges V G
  let H : SimpleGraph V :=
    { Adj := fun u v => G.Adj u v ∧ (u ∈ s ↔ v ∉ s)
      symm := by
        intro u v ⟨h1, h2⟩
        exact ⟨h1.symm, by tauto⟩
      loopless := by
        intro u ⟨h1, _⟩
        exact G.loopless u h1 }
  refine ⟨H, fun u v h => h.1, ?_, ?_⟩
  · refine ⟨SimpleGraph.Coloring.mk (fun v => if v ∈ s then (0 : Fin 2) else 1) ?_⟩
    intro u v ⟨_, h2⟩
    by_cases hu : u ∈ s
    · have hv : v ∉ s := h2.1 hu
      simp [hu, hv]
    · have hv : v ∈ s := by tauto
      simp [hu, hv]
  · have e1 : G.edgeSet.ncard = G.edgeFinset.card := by
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    have e2 : (Finset.filter (fun p : V × V => G.Adj p.1 p.2) (s ×ˢ sᶜ)).card ≤ H.edgeSet.ncard := by
      rw [← Set.ncard_coe_finset]
      refine Set.ncard_le_ncard_of_injOn (fun p : V × V => s(p.1, p.2)) ?_ ?_ (Set.toFinite _)
      · intro p hp
        simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_compl, Set.mem_setOf_eq] at hp
        show H.Adj p.1 p.2
        exact ⟨hp.2, by tauto⟩
      · intro p hp q hq hpq
        simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_compl, Set.mem_setOf_eq] at hp hq
        rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Prod.ext h1 h2
        · exfalso
          apply hq.1.2
          rw [← h1]; exact hp.1.1
    rw [e1]
    omega
end

-- forge:entry bld_frobenius_rank_inequality kind=proved origin=conjecture
section
/- Uses Mathlib2.gen_lin_sylvester_rank_rect: take a rank factorisation B = M * N with M : n × Fin r, N : Fin r × p, r = rank B; apply the rectangular Sylvester inequality to (A*M) and (N*C) to get rank(AM) + rank(NC) ≤ r + rank(ABC), then rank(AB) ≤ rank(AM) and rank(BC) ≤ rank(NC). -/
theorem bld_frobenius_rank_inequality_aux1 (K : Type*) [Field K] (n p : Type*) [Fintype n] [Fintype p] (B : Matrix n p K) : ∃ (M : Matrix n (Fin B.rank) K) (N : Matrix (Fin B.rank) p K), B = M * N := by
  classical
  let f : (p → K) →ₗ[K] (n → K) := Matrix.toLin' B
  have hr : Module.finrank K (LinearMap.range f) = B.rank := by
    simp only [f, Matrix.toLin'_apply']
    rfl
  let b := Module.finBasisOfFinrankEq K (LinearMap.range f) hr
  let e := b.equivFun
  refine ⟨LinearMap.toMatrix' ((LinearMap.range f).subtype ∘ₗ e.symm.toLinearMap),
    LinearMap.toMatrix' (e.toLinearMap ∘ₗ f.rangeRestrict), ?_⟩
  rw [← LinearMap.toMatrix'_comp]
  have : ((LinearMap.range f).subtype ∘ₗ e.symm.toLinearMap) ∘ₗ (e.toLinearMap ∘ₗ f.rangeRestrict) = f := by
    ext x
    simp
  rw [this]
  simp [f]

theorem bld_frobenius_rank_inequality (K : Type*) [Field K] (m n p q : Type*) [Fintype m] [Fintype n] [Fintype p] [Fintype q] (A : Matrix m n K) (B : Matrix n p K) (C : Matrix p q K) : Matrix.rank (A * B) + Matrix.rank (B * C) ≤ Matrix.rank B + Matrix.rank (A * B * C) := by
  obtain ⟨M, N, hB⟩ := bld_frobenius_rank_inequality_aux1 K n p B
  have hs := Mathlib2.gen_lin_sylvester_rank_rect K m (Fin B.rank) q (A * M) (N * C)
  rw [Fintype.card_fin] at hs
  have e1 : A * M * (N * C) = A * (M * N) * C := by
    simp only [Matrix.mul_assoc]
  rw [← hB] at e1
  have h1 : (A * B).rank ≤ (A * M).rank := by
    have : (A * M) * N = A * (M * N) := by rw [Matrix.mul_assoc]
    rw [← hB] at this
    rw [← this]; exact Matrix.rank_mul_le_left _ _
  have h2 : (B * C).rank ≤ (N * C).rank := by
    have : M * (N * C) = (M * N) * C := by rw [Matrix.mul_assoc]
    rw [← hB] at this
    rw [← this]; exact Matrix.rank_mul_le_right _ _
  rw [e1] at hs
  omega
end

-- forge:entry bld_one_add_div_pow_mono kind=proved origin=conjecture
section
/- Uses Mathlib2.an2_amgm_range_pow: apply AM-GM to the n+1 numbers consisting of n copies of 1 + x/n and one copy of 1; their mean is 1 + x/(n+1). Generalises Mathlib2.ana_one_add_inv_pow_mono (x = 1). -/
theorem bld_one_add_div_pow_mono (n : ℕ) (x : ℝ) (hx : 0 ≤ x) : (1 + x / (n : ℝ)) ^ n ≤ (1 + x / ((n : ℝ) + 1)) ^ (n + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hx
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have key := Mathlib2.an2_amgm_range_pow n (fun i => if i < n then 1 + x / (n : ℝ) else 1)
    (fun i => by dsimp only; split_ifs <;> positivity)
  have hp : ∏ i ∈ Finset.range n, (if i < n then 1 + x / (n : ℝ) else 1) = (1 + x / (n : ℝ)) ^ n := by
    rw [Finset.prod_congr rfl (fun i hi => if_pos (Finset.mem_range.1 hi))]; simp
  have hs : ∑ i ∈ Finset.range n, (if i < n then 1 + x / (n : ℝ) else 1) = n * (1 + x / (n : ℝ)) := by
    rw [Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.1 hi))]; simp; ring
  simp only [] at key
  rw [Finset.prod_range_succ, Finset.sum_range_succ, hp, hs] at key
  simp only [lt_irrefl, if_false, mul_one] at key
  have e : ((n : ℝ) * (1 + x / (n : ℝ)) + 1) / ((n : ℝ) + 1) = 1 + x / ((n : ℝ) + 1) := by
    field_simp; ring
  rwa [e] at key
end

-- forge:entry bld_hardy_cross_term kind=proved origin=conjecture
section
/- Uses Mathlib2.r3_hardy_inequality_finite: by Cauchy–Schwarz the left side is at most sqrt(∑ σ_k^2) * sqrt(∑ a_k^2), and Hardy bounds ∑ σ_k^2 by 4 ∑ a_k^2. -/
theorem bld_hardy_cross_term (a : ℕ → ℝ) (n : ℕ) : ∑ k ∈ Finset.range n, ((∑ i ∈ Finset.range (k + 1), a i) / ((k : ℝ) + 1)) * a k ≤ 2 * ∑ k ∈ Finset.range n, a k ^ 2 := by
  have hH := Mathlib2.r3_hardy_inequality_finite a n
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n)
    (fun k => (∑ i ∈ Finset.range (k + 1), a i) / ((k : ℝ) + 1)) a
  have hA : 0 ≤ ∑ k ∈ Finset.range n, a k ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  simp only [] at hCS
  refine (abs_le_of_sq_le_sq' ?_ (by linarith)).2
  calc _ ≤ _ := hCS
    _ ≤ (4 * ∑ k ∈ Finset.range n, a k ^ 2) * ∑ k ∈ Finset.range n, a k ^ 2 :=
        mul_le_mul_of_nonneg_right hH hA
    _ = _ := by ring
end

-- forge:entry bld_zmod_diag_quadratic_form_surjective kind=proved origin=conjecture
section
/- Uses Mathlib2.alg_card_range_sq_zmod_prime: for odd p the sets {a x^2} and {c - b y^2} each have (p+1)/2 elements, so they intersect by pigeonhole in ZMod p; p = 2 by direct check. -/
theorem bld_zmod_diag_quadratic_form_surjective_aux1 : ∀ a b c : ZMod 2, a ≠ 0 → b ≠ 0 → ∃ x y : ZMod 2, a * x ^ 2 + b * y ^ 2 = c := by
  decide

theorem bld_zmod_diag_quadratic_form_surjective (p : ℕ) [Fact p.Prime] (a b c : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) : ∃ x y : ZMod p, a * x ^ 2 + b * y ^ 2 = c := by
  by_cases hp2 : p = 2
  · subst hp2
    exact bld_zmod_diag_quadratic_form_surjective_aux1 a b c ha hb
  have hcard := Mathlib2.alg_card_range_sq_zmod_prime p hp2
  have hodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hS : (Finset.image (fun x : ZMod p => x ^ 2) Finset.univ).card = (p + 1) / 2 := by
    rw [← hcard, Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
    congr 1
    ext t
    simp
  have hA : (Finset.image (fun t : ZMod p => a * t)
      (Finset.image (fun x : ZMod p => x ^ 2) Finset.univ)).card = (p + 1) / 2 := by
    rw [Finset.card_image_of_injective _ (mul_right_injective₀ ha), hS]
  have hB : (Finset.image (fun t : ZMod p => c - b * t)
      (Finset.image (fun x : ZMod p => x ^ 2) Finset.univ)).card = (p + 1) / 2 := by
    rw [Finset.card_image_of_injective _ ?_, hS]
    intro t t' htt
    have : b * t = b * t' := by
      have := congrArg (fun z => c - z) htt
      simpa using this
    exact mul_right_injective₀ hb this
  by_contra hne
  have hdisj : Disjoint (Finset.image (fun t : ZMod p => a * t)
      (Finset.image (fun x : ZMod p => x ^ 2) Finset.univ))
      (Finset.image (fun t : ZMod p => c - b * t)
      (Finset.image (fun x : ZMod p => x ^ 2) Finset.univ)) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    simp only [Finset.mem_image, Finset.mem_univ, true_and, exists_exists_eq_and] at hz hz'
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨y, hy⟩ := hz'
    exact hne ⟨x, y, by rw [← hy]; ring⟩
  have hle := Finset.card_le_univ ((Finset.image (fun t : ZMod p => a * t)
      (Finset.image (fun x : ZMod p => x ^ 2) Finset.univ)) ∪
      (Finset.image (fun t : ZMod p => c - b * t)
      (Finset.image (fun x : ZMod p => x ^ 2) Finset.univ)))
  rw [Finset.card_union_of_disjoint hdisj, hA, hB, ZMod.card] at hle
  omega
end

-- forge:entry bld_nilpotent_commute_det_add kind=proved origin=conjecture
section
/- Uses Mathlib2.gen_lin_nilpotent_det_one_add_reduced: if B is invertible then B⁻¹A is nilpotent (A, B commute) and det(B + A) = det B * det(1 + B⁻¹A) = det B. For general B apply this to B + t • 1 for the cofinitely many t with det(B + t • 1) ≠ 0 and conclude by the polynomial identity (two polynomials in t agreeing at infinitely many points), then set t = 0. -/
theorem bld_nilpotent_commute_det_add_aux1 (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) (hA : IsNilpotent A) (hAB : A * B = B * A) (hB : IsUnit B.det) : Matrix.det (B + A) = Matrix.det B := by
  have hc : B⁻¹ * A = A * B⁻¹ := by
    calc B⁻¹ * A = B⁻¹ * A * (B * B⁻¹) := by rw [Matrix.mul_nonsing_inv B hB, mul_one]
      _ = B⁻¹ * (A * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (B⁻¹ * B) * A * B⁻¹ := by rw [hAB]; simp only [Matrix.mul_assoc]
      _ = A * B⁻¹ := by rw [Matrix.nonsing_inv_mul B hB, one_mul]
  have hn : IsNilpotent (B⁻¹ * A) := by
    obtain ⟨k, hk⟩ := hA
    refine ⟨k, ?_⟩
    have hcomm : Commute B⁻¹ A := hc
    rw [hcomm.mul_pow, hk, mul_zero]
  have hd := Mathlib2.gen_lin_nilpotent_det_one_add_reduced ℝ (Fin n) (B⁻¹ * A) hn
  have e : B + A = B * (1 + B⁻¹ * A) := by
    rw [Matrix.mul_add, mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv B hB, one_mul]
  rw [e, Matrix.det_mul, hd, mul_one]

theorem bld_nilpotent_commute_det_add (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) (hA : IsNilpotent A) (hAB : A * B = B * A) : Matrix.det (B + A) = Matrix.det B := by
  have hPQ : (-(B + A)).charpoly = (-B).charpoly := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hQ : (-B).charpoly ≠ 0 := (Matrix.charpoly_monic (-B)).ne_zero
    refine Set.Infinite.mono ?_ ((-B).charpoly.roots.toFinset.finite_toSet.infinite_compl)
    intro t ht
    have ht' : Polynomial.eval t (-B).charpoly ≠ 0 := by
      intro h0
      apply ht
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_roots hQ).2 h0
    rw [Matrix.eval_charpoly] at ht'
    show Polynomial.eval t (-(B + A)).charpoly = Polynomial.eval t (-B).charpoly
    rw [Matrix.eval_charpoly, Matrix.eval_charpoly]
    have hcomm : A * (Matrix.scalar (Fin n) t - -B) = (Matrix.scalar (Fin n) t - -B) * A := by
      rw [mul_sub, sub_mul, mul_neg, neg_mul, hAB]
      congr 1
      exact ((Matrix.scalar_commute t (fun r => mul_comm t r) A).eq).symm
    have := bld_nilpotent_commute_det_add_aux1 n A _ hA hcomm (isUnit_iff_ne_zero.2 ht')
    rw [← this]
    congr 1
    abel
  have h0 := congrArg (Polynomial.eval 0) hPQ
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly] at h0
  simpa using h0
end

-- forge:entry bld_prod_sin_pi_div_odd kind=proved origin=conjecture
section
/- Uses Mathlib2.geo_prod_sin_pi_mul_div with 2n factors: the reflection k ↦ 2n+1-k pairs the factors (sin(π - t) = sin t), so the square of the half product equals (2n+1)/2^(2n); take the positive square root since every factor is positive. -/
theorem bld_prod_sin_pi_div_odd (n : ℕ) : ∏ k ∈ Finset.range n, Real.sin (((k : ℝ) + 1) * Real.pi / (2 * (n : ℝ) + 1)) = Real.sqrt (2 * (n : ℝ) + 1) / 2 ^ n := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hd : (0:ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hL := Mathlib2.geo_prod_sin_pi_mul_div (n + n)
  rw [Finset.prod_range_add] at hL
  push_cast at hL
  have hrefl : ∏ x ∈ Finset.range n, Real.sin (((n : ℝ) + (x : ℝ) + 1) * Real.pi / ((n : ℝ) + (n : ℝ) + 1))
      = ∏ k ∈ Finset.range n, Real.sin (((k : ℝ) + 1) * Real.pi / ((n : ℝ) + (n : ℝ) + 1)) := by
    rw [← Finset.prod_range_reflect (fun k : ℕ => Real.sin (((k : ℝ) + 1) * Real.pi / ((n : ℝ) + (n : ℝ) + 1))) n]
    refine Finset.prod_congr rfl (fun j hj => ?_)
    have hj' : j + 1 ≤ n := Finset.mem_range.1 hj
    have hc : ((n - 1 - j : ℕ) : ℝ) = (n : ℝ) - 1 - j := by
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
    rw [hc, ← Real.sin_pi_sub]
    congr 1
    field_simp
    ring
  rw [hrefl] at hL
  have e2 : (n : ℝ) + (n : ℝ) + 1 = 2 * (n : ℝ) + 1 := by ring
  rw [e2] at hL
  set P := ∏ k ∈ Finset.range n, Real.sin (((k : ℝ) + 1) * Real.pi / (2 * (n : ℝ) + 1)) with hP
  have hP0 : 0 ≤ P := by
    refine Finset.prod_nonneg (fun k hk => Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) ?_)
    have hk' : ((k : ℝ) + 1) ≤ n := by exact_mod_cast Finset.mem_range.1 hk
    rw [div_le_iff₀ hd]
    nlinarith
  have hsq : P ^ 2 = (2 * (n : ℝ) + 1) / (2 ^ n) ^ 2 := by
    rw [sq, hL, ← pow_mul, ← two_mul, mul_comm n 2]
  rw [← Real.sqrt_sq hP0, hsq, Real.sqrt_div hd.le, Real.sqrt_sq (by positivity)]
end

-- forge:entry bld_fib_even_index_iff_five_sq_add_four kind=proved origin=conjecture
section
/- Uses Mathlib2.r3_fib_iff_five_sq_pm_four_is_square and Mathlib2.an_cassini_int: solutions of the Pell-type equation x^2 - 5y^2 = 4 are exactly even-indexed Fibonacci numbers. (⇐) the library iff gives y = fib m; if m is odd then Cassini gives 5y^2-4 a square as well, and two squares differing by 8 force y = 1 = fib 2. (⇒) L_{2n}^2 = 5 F_{2n}^2 + 4 from Cassini. -/
theorem bld_fib_even_index_iff_five_sq_add_four_aux1 (n : ℕ) : ∃ x : ℕ, x ^ 2 = 5 * Nat.fib (2 * n) ^ 2 + 4 := by
  have hc := Mathlib2.an_cassini_int (2 * n)
  have hr : (Nat.fib (2 * n + 2) : ℤ) = Nat.fib (2 * n) + Nat.fib (2 * n + 1) := by
    exact_mod_cast Nat.fib_add_two
  have hle : (Nat.fib (2 * n) : ℤ) ≤ Nat.fib (2 * n + 1) := by
    exact_mod_cast Nat.fib_le_fib_succ
  have hp : (-1 : ℤ) ^ (2 * n + 1) = -1 := by rw [pow_succ, pow_mul]; simp
  rw [hr, hp] at hc
  have h0 : (0 : ℤ) ≤ Nat.fib (2 * n) := by positivity
  obtain ⟨x, hx⟩ := Int.eq_ofNat_of_zero_le
    (show (0 : ℤ) ≤ 2 * Nat.fib (2 * n + 1) - Nat.fib (2 * n) by linarith)
  refine ⟨x, ?_⟩
  have : (x : ℤ) ^ 2 = 5 * (Nat.fib (2 * n) : ℤ) ^ 2 + 4 := by
    rw [← hx]; linear_combination (-4) * hc
  exact_mod_cast this

theorem bld_fib_even_index_iff_five_sq_add_four (y : ℕ) : (∃ n : ℕ, y = Nat.fib (2 * n)) ↔ ∃ x : ℕ, x ^ 2 = 5 * y ^ 2 + 4 := by
  constructor
  · rintro ⟨n, rfl⟩
    exact bld_fib_even_index_iff_five_sq_add_four_aux1 n
  · rintro ⟨x, hx⟩
    obtain ⟨m, hm⟩ := (Mathlib2.r3_fib_iff_five_sq_pm_four_is_square y).2 ⟨x, Or.inl hx⟩
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
    · exact ⟨k, hm⟩
    · have hc := Mathlib2.an_cassini_int (2 * k + 1)
      have hr : (Nat.fib (2 * k + 1 + 2) : ℤ) = Nat.fib (2 * k + 1) + Nat.fib (2 * k + 1 + 1) := by
        exact_mod_cast Nat.fib_add_two
      have hp : (-1 : ℤ) ^ (2 * k + 1 + 1) = 1 := by
        rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]; simp
      rw [hr, hp, ← hm] at hc
      have hz : (2 * (Nat.fib (2 * k + 1 + 1) : ℤ) - y) ^ 2 + 8 = (x : ℤ) ^ 2 := by
        have hx' : (x : ℤ) ^ 2 = 5 * (y : ℤ) ^ 2 + 4 := by exact_mod_cast hx
        rw [hx']; linear_combination (-4) * hc
      have hw : (2 * (Nat.fib (2 * k + 1 + 1) : ℤ) - y).natAbs ^ 2 + 8 = x ^ 2 := by
        zify
        rw [sq_abs]; exact hz
      generalize (2 * (Nat.fib (2 * k + 1 + 1) : ℤ) - y).natAbs = w at hw
      have hxw : w < x := by
        by_contra hcon
        push_neg at hcon
        nlinarith
      have hw3 : w ≤ 3 := by nlinarith
      have hx4 : x ≤ 4 := by nlinarith
      have hx3 : x = 3 := by
        interval_cases w <;> interval_cases x <;> omega
      subst hx3
      have hy : y = 1 := by
        rcases y with _ | _ | y
        · omega
        · rfl
        · exfalso; nlinarith
      exact ⟨1, by rw [hy]; rfl⟩
end

-- forge:entry bld_rat_sq_add_sq_ne_prime_three_mod_four kind=proved origin=conjecture
section
/- Uses Mathlib2.gen_nt_sq_add_sq_eq_prime_mul_sq: the circle x^2+y^2=p has no rational point when p ≡ 3 mod 4; clear denominators (x = u/w, y = v/w) to get u^2+v^2 = p*w^2 with w ≠ 0, contradicting the library theorem. -/
theorem bld_rat_sq_add_sq_ne_prime_three_mod_four (p : ℕ) (hp : p.Prime) (h3 : p % 4 = 3) (x y : ℚ) : x ^ 2 + y ^ 2 ≠ (p : ℚ) := by
  intro h
  have hx : (x.num : ℚ) = x * x.den := (Rat.mul_den_eq_num x).symm
  have hy : (y.num : ℚ) = y * y.den := (Rat.mul_den_eq_num y).symm
  have key : (x.num * (y.den : ℤ)) ^ 2 + (y.num * (x.den : ℤ)) ^ 2
      = (p : ℤ) * ((x.den : ℤ) * (y.den : ℤ)) ^ 2 := by
    have : (((x.num * (y.den : ℤ)) ^ 2 + (y.num * (x.den : ℤ)) ^ 2 : ℤ) : ℚ)
        = (((p : ℤ) * ((x.den : ℤ) * (y.den : ℤ)) ^ 2 : ℤ) : ℚ) := by
      push_cast
      rw [hx, hy]
      linear_combination ((x.den : ℚ) * (y.den : ℚ)) ^ 2 * h
    exact_mod_cast this
  have hz := (Mathlib2.gen_nt_sq_add_sq_eq_prime_mul_sq p hp h3 _ _ _ key).2.2
  have hxd : (x.den : ℤ) ≠ 0 := by exact_mod_cast x.den_nz
  have hyd : (y.den : ℤ) ≠ 0 := by exact_mod_cast y.den_nz
  exact mul_ne_zero hxd hyd hz
end

-- forge:entry bld_center_card_of_card_prime_cube kind=proved origin=conjecture
section
/- Uses Mathlib2.alg_center_index_not_prime: the centre of a p-group is non-trivial, so |Z| ∈ {p, p^2, p^3}; p^3 is excluded by non-commutativity and p^2 would give prime index p, contradicting the library theorem. -/
theorem bld_center_card_of_card_prime_cube (p : ℕ) (hp : p.Prime) (G : Type*) [Group G] (hG : Nat.card G = p ^ 3) (hnc : ∃ a b : G, a * b ≠ b * a) : Nat.card (Subgroup.center G) = p := by
  have hpos : 0 < p := hp.pos
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; positivity)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, hab⟩ := hnc
  haveI : Nontrivial G := ⟨⟨a * b, b * a, hab⟩⟩
  haveI := (IsPGroup.of_card hG).center_nontrivial
  have h1 : 1 < Nat.card (Subgroup.center G) := Finite.one_lt_card
  have hdvd : Nat.card (Subgroup.center G) ∣ p ^ 3 := hG ▸ Subgroup.card_subgroup_dvd_card _
  have hidx := Subgroup.index_mul_card (Subgroup.center G)
  rw [hG] at hidx
  obtain ⟨i, hi, hc⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hntop : Nat.card (Subgroup.center G) ≠ p ^ 3 := by
    intro h
    have ht := Subgroup.eq_top_of_card_eq (Subgroup.center G) (h.trans hG.symm)
    have hb : b ∈ Subgroup.center G := ht ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.1 hb a)
  have hni := Mathlib2.alg_center_index_not_prime G
  rw [hc] at h1 hntop hidx ⊢
  interval_cases i
  · simp at h1
  · simp
  · exfalso
    apply hni
    have : (Subgroup.center G).index = p := by
      have h3 : p ^ 3 = p * p ^ 2 := by ring
      rw [h3] at hidx
      exact Nat.eq_of_mul_eq_mul_right (by positivity) hidx
    rw [this]; exact hp
  · exact absurd rfl hntop
end

-- forge:entry bld_center_eq_bot_of_card_prime_mul_prime kind=proved origin=conjecture
section
/- Uses Mathlib2.alg_center_index_not_prime: |Z| divides p*q; |Z| = p or q gives prime index, contradicting the library theorem, and |Z| = p*q contradicts non-commutativity, so |Z| = 1. -/
theorem bld_center_eq_bot_of_card_prime_mul_prime (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (G : Type*) [Group G] (hG : Nat.card G = p * q) (hnc : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  have hpos : 0 < p := hp.pos
  have hqpos : 0 < q := hq.pos
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; positivity)
  obtain ⟨a, b, hab⟩ := hnc
  have hdvd : Nat.card (Subgroup.center G) ∣ p * q := hG ▸ Subgroup.card_subgroup_dvd_card _
  have hidx := Subgroup.index_mul_card (Subgroup.center G)
  rw [hG] at hidx
  have hntop : Nat.card (Subgroup.center G) ≠ p * q := by
    intro h
    have ht := Subgroup.eq_top_of_card_eq (Subgroup.center G) (h.trans hG.symm)
    have hb : b ∈ Subgroup.center G := ht ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.1 hb a)
  have hni := Mathlib2.alg_center_index_not_prime G
  obtain ⟨d1, d2, h1, h2, hd⟩ := (Nat.dvd_mul).1 hdvd
  rw [← hd] at hidx hntop
  rcases (Nat.dvd_prime hp).1 h1 with e1 | e1 <;> rcases (Nat.dvd_prime hq).1 h2 with e2 | e2 <;>
    rw [e1, e2] at hidx hntop hd
  · exact Subgroup.eq_bot_of_card_eq _ (by rw [← hd])
  · exfalso
    apply hni
    have : (Subgroup.center G).index = p := by
      rw [one_mul] at hidx
      exact Nat.eq_of_mul_eq_mul_right hqpos hidx
    rw [this]; exact hp
  · exfalso
    apply hni
    have : (Subgroup.center G).index = q := by
      rw [mul_one] at hidx
      exact Nat.eq_of_mul_eq_mul_right hpos (hidx.trans (mul_comm p q))
    rw [this]; exact hq
  · exact absurd rfl hntop
end

-- forge:entry bld_fib_consecutive_of_quadratic_form kind=proved origin=conjecture
section
/- Uses Mathlib2.r3_fib_iff_five_sq_pm_four_is_square and Mathlib2.an_cassini_int: (2x-y)^2 = 5y^2 ± 4, so y = fib n by the library characterisation; Cassini shows fib (n+1) is a root of the same quadratic in x, and positivity of x pins it down (small cases y ≤ 1 by hand). Key lemma of IMO 1981 Q3. -/
theorem bld_fib_consecutive_of_quadratic_form_aux1 (u v Y : ℤ) (hu : u ^ 2 = 5 * Y ^ 2 + 4) (hv : v ^ 2 + 4 = 5 * Y ^ 2) : Y ^ 2 = 1 := by
  have hp : |u| ^ 2 = |v| ^ 2 + 8 := by rw [sq_abs, sq_abs]; linarith
  have hq0 : 0 ≤ |v| := abs_nonneg v
  have hp0 : 0 ≤ |u| := abs_nonneg u
  have hu2 : |u| ^ 2 = u ^ 2 := sq_abs u
  generalize |u| = p at *
  generalize |v| = q at *
  have hqp : q < p := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hq3 : q ≤ 3 := by nlinarith
  have hp4 : p ≤ 4 := by nlinarith
  have hp3 : p = 3 := by
    interval_cases q <;> interval_cases p <;> omega
  subst hp3
  linarith

theorem bld_fib_consecutive_of_quadratic_form_aux2 (x y : ℕ) (hy : (y : ℤ) ^ 2 = 1) (h : ((x : ℤ) ^ 2 - (x : ℤ) * (y : ℤ) - (y : ℤ) ^ 2) ^ 2 = 1) (hx : 0 < x) : ∃ n : ℕ, y = Nat.fib n ∧ x = Nat.fib (n + 1) := by
  have hy1 : y = 1 := by
    have : y ^ 2 = 1 := by exact_mod_cast hy
    exact (pow_eq_one_iff (by norm_num)).1 this
  subst hy1
  have hx2 : (x : ℤ) ≤ 2 := by
    have hx0 : (1 : ℤ) ≤ x := by exact_mod_cast hx
    by_contra hcon
    push_neg at hcon
    have : (x : ℤ) ^ 2 - x * 1 - 1 ^ 2 ≥ 2 := by nlinarith
    push_cast at h
    nlinarith
  have hx2' : x ≤ 2 := by exact_mod_cast hx2
  interval_cases x
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩

theorem bld_fib_consecutive_of_quadratic_form (x y : ℕ) (hx : 0 < x) (h : ((x : ℤ) ^ 2 - (x : ℤ) * (y : ℤ) - (y : ℤ) ^ 2) ^ 2 = 1) : ∃ n : ℕ, y = Nat.fib n ∧ x = Nat.fib (n + 1) := by
  have hs : (x : ℤ) ^ 2 - x * y - (y : ℤ) ^ 2 = 1 ∨ (x : ℤ) ^ 2 - x * y - (y : ℤ) ^ 2 = -1 := by
    have h0 : ((x : ℤ) ^ 2 - x * y - (y : ℤ) ^ 2 - 1) * ((x : ℤ) ^ 2 - x * y - (y : ℤ) ^ 2 + 1) = 0 := by
      linear_combination h
    rcases mul_eq_zero.1 h0 with h1 | h1
    · left; linarith
    · right; linarith
  have hsq : ∃ z : ℕ, z ^ 2 = 5 * y ^ 2 + 4 ∨ z ^ 2 + 4 = 5 * y ^ 2 := by
    refine ⟨(2 * (x : ℤ) - y).natAbs, ?_⟩
    rcases hs with h1 | h1
    · left; zify; rw [sq_abs]; linear_combination 4 * h1
    · right; zify; rw [sq_abs]; linear_combination 4 * h1
  obtain ⟨m, hm⟩ := (Mathlib2.r3_fib_iff_five_sq_pm_four_is_square y).2 hsq
  have hc := Mathlib2.an_cassini_int m
  have hr : (Nat.fib (m + 2) : ℤ) = Nat.fib m + Nat.fib (m + 1) := by
    exact_mod_cast Nat.fib_add_two
  have hle : (Nat.fib m : ℤ) ≤ Nat.fib (m + 1) := by
    exact_mod_cast Nat.fib_le_fib_succ
  rw [hr, ← hm] at hc
  have hx0 : (1 : ℤ) ≤ x := by exact_mod_cast hx
  rw [← hm] at hle
  generalize hB : (Nat.fib (m + 1) : ℤ) = B at hc hle
  have same : (x : ℤ) ^ 2 - x * y - (y : ℤ) ^ 2 = B ^ 2 - B * y - (y : ℤ) ^ 2 →
      ∃ n : ℕ, y = Nat.fib n ∧ x = Nat.fib (n + 1) := by
    intro he
    have h0 : ((x : ℤ) - B) * (x + B - y) = 0 := by linear_combination he
    rcases mul_eq_zero.1 h0 with h1 | h1
    · refine ⟨m, hm, ?_⟩
      have : (x : ℤ) = Nat.fib (m + 1) := by rw [hB]; linarith
      exact_mod_cast this
    · exfalso; linarith
  rcases neg_one_pow_eq_or ℤ (m + 1) with hpw | hpw <;> rw [hpw] at hc <;> rcases hs with h1 | h1
  · refine bld_fib_consecutive_of_quadratic_form_aux2 x y ?_ h hx
    exact bld_fib_consecutive_of_quadratic_form_aux1 (2 * x - y) (2 * B - y) y
      (by linear_combination 4 * h1) (by linear_combination (-4) * hc)
  · exact same (by linarith)
  · exact same (by linarith)
  · refine bld_fib_consecutive_of_quadratic_form_aux2 x y ?_ h hx
    exact bld_fib_consecutive_of_quadratic_form_aux1 (2 * B - y) (2 * x - y) y
      (by linear_combination (-4) * hc) (by linear_combination 4 * h1)
end

-- forge:entry p4_z kind=definition origin=definition
section
/- z(n): the largest integer z with 3z < 2n, i.e. floor((2n-1)/3) (integer floor division) -/
def p4_z (n : ℕ) : ℤ := (2 * (n : ℤ) - 1) / 3
end

-- forge:entry p4_m kind=definition origin=definition
section
/- m(n): the largest integer m with m^2 <= 2n, i.e. floor(sqrt(2n)) -/
def p4_m (n : ℕ) : ℕ := Nat.sqrt (2 * n)
end

-- forge:entry p4_r kind=definition origin=definition
section
/- r(n): the least non-negative integer r with n <= 2^r, i.e. ceil(log2 n) -/
def p4_r (n : ℕ) : ℕ := Nat.clog 2 n
end

-- forge:entry p4_x kind=definition origin=definition
section
/- x(n) = z(n) - (r(n)+1) m(n), the quantity whose sign the paper determines -/
def p4_x (n : ℕ) : ℤ := p4_z n - ((p4_r n : ℤ) + 1) * (p4_m n : ℤ)
end

-- forge:entry bld2_tripotent_trace_sq_eq_rank kind=proved origin=conjecture
section
/- Uses Mathlib2.gen_lin_idempotent_trace_eq_rank_field: A*A is idempotent, so trace (A*A) = rank (A*A); and rank (A*A) = rank A because A = A * (A*A) gives rank A ≤ rank (A*A) ≤ rank A. -/
theorem bld2_tripotent_trace_sq_eq_rank (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (h : A * A * A = A) : Matrix.trace (A * A) = (Matrix.rank A : K) := by
  have hid : (A * A) * (A * A) = A * A := by
    rw [← Matrix.mul_assoc, h]
  rw [Mathlib2.gen_lin_idempotent_trace_eq_rank_field K ι (A * A) hid]
  congr 1
  apply le_antisymm (Matrix.rank_mul_le_left A A)
  calc A.rank = (A * A * A).rank := by rw [h]
    _ ≤ (A * A).rank := Matrix.rank_mul_le_left _ _
end

-- forge:entry bld2_mantel_equality_regular kind=proved origin=conjecture
section
/- Uses Mathlib2.comb_degree_add_degree_le_of_triangle_free (equality case of Mathlib2.bld_mantel_triangle_free): summing deg u + deg v ≤ n over edges gives ∑ deg^2 ≤ n * e; with Cauchy-Schwarz (2e)^2 ≤ n ∑ deg^2 and 4e = n^2 both are equalities, so ∑ (2 deg v - n)^2 = 0 and every degree equals n/2. -/
theorem bld2_mantel_equality_regular_aux1 (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.CliqueFree 3) : ∑ v, G.degree v ^ 2 ≤ Fintype.card V * G.edgeFinset.card := by
  have key : ∑ u, ∑ v ∈ G.neighborFinset u, G.degree v = ∑ v, G.degree v ^ 2 := by
    simp_rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, sq]
    congr 1
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext u
    simp [SimpleGraph.adj_comm]
  have h1 : ∑ u, ∑ v ∈ G.neighborFinset u, (G.degree u + G.degree v)
      ≤ ∑ u, G.degree u * Fintype.card V := by
    refine Finset.sum_le_sum (fun u _ => ?_)
    calc ∑ v ∈ G.neighborFinset u, (G.degree u + G.degree v)
        ≤ ∑ v ∈ G.neighborFinset u, Fintype.card V := by
          refine Finset.sum_le_sum (fun v hv => ?_)
          exact Mathlib2.comb_degree_add_degree_le_of_triangle_free V G h u v
            ((SimpleGraph.mem_neighborFinset _ _ _).1 hv)
      _ = G.degree u * Fintype.card V := by
          rw [Finset.sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree]
  have h2 : ∑ u, ∑ v ∈ G.neighborFinset u, (G.degree u + G.degree v)
      = ∑ v, G.degree v ^ 2 + ∑ v, G.degree v ^ 2 := by
    simp_rw [Finset.sum_add_distrib]
    rw [key]
    congr 1
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree, sq]
  have hs := G.sum_degrees_eq_twice_card_edges
  rw [h2, ← Finset.sum_mul, hs] at h1
  nlinarith

theorem bld2_mantel_equality_regular (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.CliqueFree 3) (he : 4 * G.edgeFinset.card = Fintype.card V ^ 2) (v : V) : 2 * G.degree v = Fintype.card V := by
  have h1 := bld2_mantel_equality_regular_aux1 V G h
  have hs := G.sum_degrees_eq_twice_card_edges
  have h1' : (∑ v, (G.degree v : ℤ) ^ 2) ≤ Fintype.card V * G.edgeFinset.card := by exact_mod_cast h1
  have hs' : (∑ v, (G.degree v : ℤ)) = 2 * G.edgeFinset.card := by exact_mod_cast hs
  have he' : (4 * G.edgeFinset.card : ℤ) = (Fintype.card V : ℤ) ^ 2 := by exact_mod_cast he
  have hexp : ∑ v, (2 * (G.degree v : ℤ) - Fintype.card V) ^ 2
      = 4 * ∑ v, (G.degree v : ℤ) ^ 2 - 4 * Fintype.card V * ∑ v, (G.degree v : ℤ) + (Fintype.card V : ℤ) ^ 3 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    have : (Fintype.card V : ℤ) ^ 3 = ∑ _v : V, (Fintype.card V : ℤ) ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ]; simp; ring
    rw [this, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun u _ => by ring)
  have hle : ∑ v, (2 * (G.degree v : ℤ) - Fintype.card V) ^ 2 ≤ 0 := by
    rw [hexp, hs']
    nlinarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => sq_nonneg _)).1
    (le_antisymm hle (Finset.sum_nonneg (fun u _ => sq_nonneg _))) v (Finset.mem_univ v)
  have := pow_eq_zero_iff (two_ne_zero) |>.1 hz
  omega
end

-- forge:entry bld2_rank_add_rank_one_sub kind=proved origin=conjecture
section
/- Uses Mathlib2.gen_lin_sylvester_rank_rect: the inequality ≤ is Sylvester applied to A and 1 - A (A * (1 - A) = A - A*A); for ≥ show range A ⊓ range (1 - A) = range (A * (1 - A)) and range A ⊔ range (1 - A) = ⊤, then use the dimension formula. -/
theorem bld2_rank_add_rank_one_sub (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) : Matrix.rank A + Matrix.rank (1 - A) = Fintype.card ι + Matrix.rank (A - A * A) := by
  apply le_antisymm
  · have h := Mathlib2.gen_lin_sylvester_rank_rect K ι ι ι A (1 - A)
    rwa [mul_sub, mul_one] at h
  · have h1 : LinearMap.range A.mulVecLin ⊔ LinearMap.range (1 - A).mulVecLin = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Submodule.mem_sup]
      exact ⟨A.mulVec x, ⟨x, rfl⟩, (1 - A).mulVec x, ⟨x, rfl⟩, by simp [Matrix.sub_mulVec]⟩
    have h2 : LinearMap.range (A - A * A).mulVecLin ≤ LinearMap.range A.mulVecLin ⊓ LinearMap.range (1 - A).mulVecLin := by
      rintro _ ⟨x, rfl⟩
      refine ⟨⟨(1 - A).mulVec x, ?_⟩, ⟨A.mulVec x, ?_⟩⟩
      · simp [Matrix.mulVec_mulVec, mul_sub, Matrix.sub_mulVec, Matrix.mulVec_sub]
      · simp [Matrix.mulVec_mulVec, sub_mul, Matrix.sub_mulVec, Matrix.mulVec_sub]
    have h3 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range A.mulVecLin) (LinearMap.range (1 - A).mulVecLin)
    have h4 := Submodule.finrank_mono h2
    rw [h1, finrank_top, Module.finrank_fintype_fun_eq_card] at h3
    unfold Matrix.rank
    omega
end

end Mathlib2
