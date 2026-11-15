/- Mathlib2 分片 10（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0009
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry lin_idempotent_trace_eq_rank kind=proved origin=conjecture
section
/- The trace of an idempotent rational matrix equals its rank — toLin' A is a projection onto its range (LinearMap.IsProj), so LinearMap.IsProj.trace gives trace = finrank(range) = rank; transfer between Matrix.trace and LinearMap.trace. -/
theorem lin_idempotent_trace_eq_rank (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (h : A * A = A) : Matrix.trace A = (Matrix.rank A : ℚ) := by
  have hid : IsIdempotentElem (Matrix.toLin' A) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, h]
  have hp := LinearMap.IsIdempotentElem.isProj_range _ hid
  have := hp.trace
  rw [Matrix.trace_toLin'_eq] at this
  rw [this, Matrix.rank, Matrix.toLin'_apply']
end

-- forge:entry ana_sqrt_two_rec_lt_two kind=proved origin=conjecture
section
/- The nested radical sequence a_0 = 0, a_{n+1} = sqrt(2 + a_n) stays in [0,2) — induction: if 0 ≤ a_n < 2 then 2 + a_n < 4 so sqrt(2 + a_n) < 2. -/
theorem ana_sqrt_two_rec_lt_two (a : ℕ → ℝ) (h0 : a 0 = 0) (hrec : ∀ n : ℕ, a (n + 1) = Real.sqrt (2 + a n)) (n : ℕ) : 0 ≤ a n ∧ a n < 2 := by
  induction n with
  | zero => rw [h0]; norm_num
  | succ k ih =>
    rw [hrec k]
    refine ⟨Real.sqrt_nonneg _, ?_⟩
    rw [Real.sqrt_lt' (by norm_num)]
    linarith [ih.2]
end

-- forge:entry comb_exists_two_dvd_sub kind=proved origin=conjecture
section
/- Among n+1 integers two differ by a multiple of n — pigeonhole on residues: the map i ↦ (f i : ZMod n) from Fin (n+1) to ZMod n cannot be injective. -/
theorem comb_exists_two_dvd_sub (n : ℕ) (hn : 0 < n) (f : Fin (n + 1) → ℤ) : ∃ i j : Fin (n + 1), i ≠ j ∧ (n : ℤ) ∣ f i - f j := by
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨i, j, hij, h⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun i => ((f i : ℤ) : ZMod n)) (by simp)
  refine ⟨i, j, hij, ?_⟩
  have h2 : ((f i - f j : ℤ) : ZMod n) = 0 := by
    push_cast
    simpa [sub_eq_zero] using h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2
end

-- forge:entry alg_ring_comm_of_pow_three_eq_self kind=proved origin=conjecture
section
/- A ring in which x³ = x for all x is commutative — show 6 = 0 and 3(x² + x) = 0, squares are central (via idempotents e = x² and (e y - e y e)² = 0 implies nilpotents vanish), then x = x³ - ... combine 3x(x+1) and 2-torsion parts to get commutativity. -/
theorem alg_ring_comm_of_pow_three_eq_self (R : Type*) [Ring R] (h : ∀ x : R, x ^ 3 = x) : ∀ x y : R, x * y = y * x := by
  have h' : ∀ x : R, x * x * x = x := by
    intro x; rw [← pow_three']; exact h x
  have A : ∀ a : R, a * a = 0 → a = 0 := by
    intro a ha
    have := h' a
    rw [ha, zero_mul] at this
    exact this.symm
  have B : ∀ e x : R, e * e = e → e * x = x * e := by
    intro e x he
    have h1 : e * x - e * x * e = 0 := by
      apply A
      have : (e * x - e * x * e) * (e * x - e * x * e)
          = e * x * (e * x) - e * x * (e * x) * e - e * x * (e * e) * x + e * x * (e * e) * x * e := by
        noncomm_ring
      rw [this, he]; noncomm_ring
    have h2 : x * e - e * x * e = 0 := by
      apply A
      have : (x * e - e * x * e) * (x * e - e * x * e)
          = x * e * x * e - x * (e * e) * x * e - e * x * e * x * e + e * x * (e * e) * x * e := by
        noncomm_ring
      rw [this, he]; noncomm_ring
    rw [sub_eq_zero.mp h1, sub_eq_zero.mp h2]
  have D : ∀ x y : R, x * x * y = y * (x * x) := by
    intro x y
    apply B
    have : x * x * (x * x) = x * x * x * x := by noncomm_ring
    rw [this, h' x]
  have F : ∀ x y : R, (x + x) * y = y * (x + x) := by
    intro x y
    have sq : (x + x * x) * (x + x * x) = x * x + x * x + (x + x) := by
      have : (x + x * x) * (x + x * x) = x * x + x * x * x + x * x * x + x * x * x * x := by
        noncomm_ring
      rw [this]; simp only [h' x]; abel
    have key := D (x + x * x) y
    rw [sq] at key
    simp only [add_mul, mul_add, D x y] at key
    simp only [add_mul, mul_add]
    exact add_left_cancel key
  have E : ∀ x y : R, (x + x + x) * y = y * (x + x + x) := by
    intro x y
    have h3 : (x * x + x * x + x * x) + (x + x + x) = 0 := by
      have e := h' (x + 1)
      have : (x + 1) * (x + 1) * (x + 1)
          = x * x * x + ((x * x + x * x + x * x) + (x + x + x)) + 1 := by
        noncomm_ring
      rw [this, h' x] at e
      have e' : x + ((x * x + x * x + x * x) + (x + x + x)) + 1 = x + 0 + 1 := by
        rw [add_zero]; exact e
      exact add_left_cancel (add_right_cancel e')
    have key : ((x * x + x * x + x * x) + (x + x + x)) * y
        = y * ((x * x + x * x + x * x) + (x + x + x)) := by
      rw [h3]; simp
    simp only [add_mul, mul_add, D x y] at key
    simp only [add_mul, mul_add]
    exact add_left_cancel key
  intro x y
  have e := E x y
  have f := F x y
  simp only [add_mul, mul_add] at e f
  rw [f] at e
  exact add_left_cancel e
end

-- forge:entry ana_sqrt_two_rec_closed_form kind=proved origin=conjecture
section
/- Viète-type closed form: the nested radical sequence equals 2cos(π/2^(n+1)) — induction using the half-angle identity 2 + 2cos(2t) = 4cos^2 t and positivity of cos on (0, π/2]. -/
theorem ana_sqrt_two_rec_closed_form (a : ℕ → ℝ) (h0 : a 0 = 0) (hrec : ∀ n : ℕ, a (n + 1) = Real.sqrt (2 + a n)) (n : ℕ) : a n = 2 * Real.cos (Real.pi / 2 ^ (n + 1)) := by
  induction n with
  | zero => rw [h0]; norm_num
  | succ k ih =>
    rw [hrec k, ih]
    have hpos : (0:ℝ) < 2 ^ (k + 1 + 1) := by positivity
    have h2 : Real.pi / 2 ^ (k + 1) = 2 * (Real.pi / 2 ^ (k + 1 + 1)) := by
      rw [pow_succ 2 (k+1)]; field_simp
    have hle : Real.pi / 2 ^ (k + 1 + 1) ≤ Real.pi / 2 := by
      apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
      calc (2:ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1 + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hc : 0 ≤ Real.cos (Real.pi / 2 ^ (k + 1 + 1)) :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by have : 0 < Real.pi / 2 ^ (k + 1 + 1) := div_pos Real.pi_pos hpos
            linarith [Real.pi_pos]) hle
    rw [h2, Real.cos_two_mul]
    have : 2 + 2 * (2 * Real.cos (Real.pi / 2 ^ (k + 1 + 1)) ^ 2 - 1) = (2 * Real.cos (Real.pi / 2 ^ (k + 1 + 1))) ^ 2 := by ring
    rw [this, Real.sqrt_sq (by linarith)]
end

-- forge:entry comb_catalan_succ_mul kind=proved origin=conjecture
section
/- First-order Catalan recurrence (n+2)·C_{n+1} = 2(2n+1)·C_n — from (n+1)·catalan n = centralBinom n and Nat.succ_mul_centralBinom_succ: (n+1)·centralBinom (n+1) = 2(2n+1)·centralBinom n. -/
theorem comb_catalan_succ_mul (n : ℕ) : (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  have h1 := succ_mul_catalan_eq_centralBinom (n + 1)
  have h2 := succ_mul_catalan_eq_centralBinom n
  have h3 := Nat.succ_mul_centralBinom_succ n
  have : (n + 1) * ((n + 2) * catalan (n + 1)) = (n + 1) * (2 * (2 * n + 1) * catalan n) := by
    calc (n + 1) * ((n + 2) * catalan (n + 1)) = (n + 1) * ((n + 1 + 1) * catalan (n + 1)) := by ring
      _ = (n + 1) * (n + 1).centralBinom := by rw [h1]
      _ = 2 * (2 * n + 1) * n.centralBinom := h3
      _ = 2 * (2 * n + 1) * ((n + 1) * catalan n) := by rw [h2]
      _ = _ := by ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) this
end

-- forge:entry ana_sqrt_two_rec_tendsto kind=proved origin=conjecture
section
/- The nested radical sequence sqrt(2 + sqrt(2 + ...)) converges to 2 — show 0 ≤ a_n < 2 and the contraction 2 - a_{n+1} = (2 - a_n)/(2 + a_{n+1}) ≤ (2 - a_n)/2, so 0 ≤ 2 - a_n ≤ 2/2^n and squeeze. -/
theorem ana_sqrt_two_rec_tendsto (a : ℕ → ℝ) (h0 : a 0 = 0) (hrec : ∀ n : ℕ, a (n + 1) = Real.sqrt (2 + a n)) : Filter.Tendsto a Filter.atTop (nhds 2) := by
  have ha : a = fun n : ℕ => 2 * Real.cos (Real.pi / 2 ^ (n + 1)) :=
    funext (ana_sqrt_two_rec_closed_form a h0 hrec)
  rw [ha]
  have h1 : Filter.Tendsto (fun n : ℕ => (2:ℝ) ^ (n + 1)) Filter.atTop Filter.atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2)).comp (Filter.tendsto_add_atTop_nat 1)
  have h2 : Filter.Tendsto (fun n : ℕ => Real.pi / (2:ℝ) ^ (n + 1)) Filter.atTop (nhds 0) :=
    h1.const_div_atTop Real.pi
  have h3 := ((Real.continuous_cos.tendsto 0).comp h2).const_mul 2
  simp only [Real.cos_zero, mul_one] at h3
  exact h3
end

-- forge:entry comb_degree_add_degree_le_of_triangle_free kind=proved origin=conjecture
section
/- In a triangle-free graph adjacent vertices u, v satisfy deg u + deg v ≤ n (the key step of Mantel's theorem) — the neighbour sets of u and v are disjoint, since a common neighbour w gives the 3-clique {u,v,w}. -/
theorem comb_degree_add_degree_le_of_triangle_free (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.CliqueFree 3) (u v : V) (huv : G.Adj u v) : G.degree u + G.degree v ≤ Fintype.card V := by
  have hd : Disjoint (G.neighborFinset u) (G.neighborFinset v) := by
    rw [Finset.disjoint_left]
    intro w hwu hwv
    rw [SimpleGraph.mem_neighborFinset] at hwu hwv
    exact h {u, v, w} (SimpleGraph.is3Clique_iff.mpr ⟨u, v, w, huv, hwu, hwv, rfl⟩)
  unfold SimpleGraph.degree
  rw [← Finset.card_union_of_disjoint hd]
  exact Finset.card_le_univ _
end

-- forge:entry ana_tsum_inv_cube_le kind=proved origin=conjecture
section
/- zeta(3) ≤ 5/4 — for n ≥ 3, 1/n^3 ≤ 1/((n-1)n(n+1)) = (1/2)(1/((n-1)n) - 1/(n(n+1))), which telescopes to 1/12; so every partial sum is ≤ 1 + 1/8 + 1/12 < 5/4, then use tsum_le_of_sum_le with summability from the p-series test. -/
theorem ana_tsum_inv_cube_le_aux1 (x : ℝ) (hx : 0 ≤ x) :
    1 / (x + 2) ^ 3 ≤ 1 / (2 * (x + 1) * (x + 2)) - 1 / (2 * (x + 2) * (x + 3)) := by
  have h : 1 / (2 * (x + 1) * (x + 2)) - 1 / (2 * (x + 2) * (x + 3)) = 1 / ((x + 1) * (x + 2) * (x + 3)) := by
    field_simp
    ring
  rw [h]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [sq_nonneg (x + 2)]

theorem ana_tsum_inv_cube_le_aux2 (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), 1 / (((n : ℝ) + 1) ^ 3) ≤ 5 / 4 - 1 / (2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
  induction N with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h := ana_tsum_inv_cube_le_aux1 (k : ℝ) (Nat.cast_nonneg k)
    push_cast
    have e1 : (k : ℝ) + 1 + 1 = k + 2 := by ring
    have e2 : (k : ℝ) + 1 + 2 = k + 3 := by ring
    rw [e1, e2]
    linarith

theorem ana_tsum_inv_cube_le : (∑' n : ℕ, 1 / (((n : ℝ) + 1) ^ 3)) ≤ 5 / 4 := by
  apply Real.tsum_le_of_sum_range_le
  · intro n; positivity
  · intro n
    have h1 : ∑ i ∈ Finset.range n, 1 / (((i : ℝ) + 1) ^ 3) ≤ ∑ i ∈ Finset.range (n + 1), 1 / (((i : ℝ) + 1) ^ 3) := by
      rw [Finset.sum_range_succ]
      have : (0:ℝ) ≤ 1 / (((n : ℝ) + 1) ^ 3) := by positivity
      linarith
    have h2 := ana_tsum_inv_cube_le_aux2 n
    have h3 : (0:ℝ) ≤ 1 / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := by positivity
    linarith
end

-- forge:entry comb_card_subset_pairs kind=proved origin=conjecture
section
/- The number of pairs A ⊆ B ⊆ [n] is 3^n — group by B: ∑_B 2^|B| = ∑_k C(n,k)2^k = 3^n; or biject with functions Fin n → Fin 3. -/
theorem comb_card_subset_pairs (n : ℕ) : ((Finset.univ : Finset (Finset (Fin n) × Finset (Fin n))).filter (fun p => p.1 ⊆ p.2)).card = 3 ^ n := by
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have h : ∀ t : Finset (Fin n), (∑ s : Finset (Fin n), if s ⊆ t then 1 else 0) = 2 ^ t.card := by
    intro t
    rw [← Finset.card_filter]
    have : (Finset.univ.filter (fun s : Finset (Fin n) => s ⊆ t)) = t.powerset := by
      ext s; simp
    rw [this, Finset.card_powerset]
  simp only [h]
  have := Fintype.sum_pow_mul_eq_add_pow (Fin n) (2 : ℕ) 1
  simpa using this
end

-- forge:entry ana_one_add_inv_pow_mono kind=proved origin=conjecture
section
/- The sequence (1 + 1/n)^n is nondecreasing — AM-GM on n copies of (1 + 1/n) and one copy of 1, or equivalently Bernoulli's inequality applied to (1 - 1/(n+1)^2)^(n+1) ≥ 1 - 1/(n+1); n = 0 is trivial. -/
theorem ana_one_add_inv_pow_mono (n : ℕ) : (1 + 1 / (n : ℝ)) ^ n ≤ (1 + 1 / ((n : ℝ) + 1)) ^ (n + 1) := by
  cases n with
  | zero => norm_num
  | succ k =>
    have h : (1 + 1 / ((k : ℝ) + 1)) ^ (k + 1) < (1 + 1 / ((k : ℝ) + 2)) ^ (k + 2) :=
      an2_one_add_inv_pow_strict_mono k
    push_cast
    have e : (k : ℝ) + 1 + 1 = k + 2 := by ring
    rw [e]
    exact h.le
end

-- forge:entry ana_fenchel_young_exp kind=proved origin=conjecture
section
/- Fenchel–Young inequality for the conjugate pair exp and b log b - b — apply 1 + t ≤ exp t with t = a - log b and multiply by b = exp(log b). -/
theorem ana_fenchel_young_exp (a b : ℝ) (hb : 0 < b) : a * b ≤ Real.exp a + b * Real.log b - b := by
  have h := Real.add_one_le_exp (a - Real.log b)
  rw [Real.exp_sub, Real.exp_log hb] at h
  have h2 : (a - Real.log b + 1) * b ≤ Real.exp a / b * b := mul_le_mul_of_nonneg_right h hb.le
  rw [div_mul_cancel₀ _ hb.ne'] at h2
  linarith
end

-- forge:entry lin_sylvester_rank kind=proved origin=conjecture
section
/- Sylvester's rank inequality: rank A + rank B ≤ n + rank(AB) — restrict A to range B: rank(AB) = rank B − dim(ker A ∩ range B) ≥ rank B − dim ker A, and dim ker A = n − rank A by rank–nullity. -/
theorem lin_sylvester_rank (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) : Matrix.rank A + Matrix.rank B ≤ n + Matrix.rank (A * B) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker (A.mulVecLin.domRestrict (LinearMap.range B.mulVecLin))
  rw [LinearMap.range_domRestrict, ← LinearMap.range_comp, ← Matrix.mulVecLin_mul, LinearMap.ker_domRestrict] at h2
  have h3 : Module.finrank ℝ (Submodule.comap (LinearMap.range B.mulVecLin).subtype (LinearMap.ker A.mulVecLin)) ≤ Module.finrank ℝ (LinearMap.ker A.mulVecLin) := by
    rw [← Submodule.finrank_map_subtype_eq]
    apply Submodule.finrank_mono
    exact Submodule.map_comap_le _ _
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
  unfold Matrix.rank
  omega
end

-- forge:entry comb_sum_card_fixed_points_perm kind=proved origin=conjecture
section
/- The total number of fixed points over all permutations of an m-set (m ≥ 1) is m!, i.e. the average is 1 — double count pairs (σ, i) with σ i = i: for each i the stabiliser has (m-1)! elements; or Burnside for the transitive action of Perm on Fin m. -/
theorem comb_sum_card_fixed_points_perm (n : ℕ) : ∑ σ : Equiv.Perm (Fin (n + 1)), (Finset.univ.filter (fun i : Fin (n + 1) => σ i = i)).card = (n + 1).factorial := by
  classical
  haveI : Fintype (Quotient (MulAction.orbitRel (Equiv.Perm (Fin (n + 1))) (Fin (n + 1)))) := Fintype.ofFinite _
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (Equiv.Perm (Fin (n + 1))) (Fin (n + 1))
  have hsub : Subsingleton (Quotient (MulAction.orbitRel (Equiv.Perm (Fin (n + 1))) (Fin (n + 1)))) :=
    (MulAction.pretransitive_iff_subsingleton_quotient _ _).mp inferInstance
  have hne : Nonempty (Quotient (MulAction.orbitRel (Equiv.Perm (Fin (n + 1))) (Fin (n + 1)))) :=
    ⟨Quotient.mk _ 0⟩
  have h1 : Fintype.card (Quotient (MulAction.orbitRel (Equiv.Perm (Fin (n + 1))) (Fin (n + 1)))) = 1 :=
    Fintype.card_eq_one_iff_nonempty_unique.mpr ⟨Unique.mk' _⟩
  rw [h1, one_mul, Fintype.card_perm, Fintype.card_fin] at hB
  rw [← hB]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun i => by simp [MulAction.mem_fixedBy]))
end

-- forge:entry ana_sqrt_sub_sqrt_le_sqrt_abs kind=proved origin=conjecture
section
/- The square root is 1/2-Hölder with constant 1 — WLOG y ≤ x; then (sqrt x - sqrt y)^2 ≤ (sqrt x - sqrt y)(sqrt x + sqrt y) = x - y, and take square roots. -/
theorem ana_sqrt_sub_sqrt_le_sqrt_abs (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : |Real.sqrt x - Real.sqrt y| ≤ Real.sqrt |x - y| := by
  apply Real.abs_le_sqrt
  have hs := Real.sqrt_nonneg x
  have ht := Real.sqrt_nonneg y
  have hs2 := Real.sq_sqrt hx
  have ht2 := Real.sq_sqrt hy
  rcases le_total (Real.sqrt y) (Real.sqrt x) with h | h
  · have := le_abs_self (x - y)
    nlinarith [mul_nonneg ht (sub_nonneg.2 h)]
  · have := neg_abs_le (x - y)
    nlinarith [mul_nonneg hs (sub_nonneg.2 h)]
end

-- forge:entry alg_isCyclic_of_card_eq_prime_mul_prime kind=proved origin=conjecture
section
/- A group of order pq with primes p < q and p ∤ q - 1 is cyclic — by Sylow's theorems both the Sylow p- and Sylow q-subgroup are unique hence normal, so G is their internal direct product C_p × C_q, which is cyclic since p, q are coprime. -/
lemma alg_isCyclic_of_card_eq_prime_mul_prime_aux1 (r s : ℕ) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hn : ∀ n : ℕ, n ∣ s → n ≡ 1 [MOD r] → n = 1) (G : Type*) [Group G] (hG : Nat.card G = r * s) :
    ∃ P : Subgroup G, P.Normal ∧ IsPGroup r P ∧ ∀ g : G, orderOf g = r → g ∈ P := by
  haveI := Fact.mk hr
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact (Nat.mul_pos hr.pos hs.pos).ne')
  let P : Sylow r G := default
  have hcP : Nat.card (P : Subgroup G) = r := by
    rw [P.card_eq_multiplicity, hG, Nat.factorization_mul hr.ne_zero hs.ne_zero, Finsupp.add_apply,
      hr.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (fun hd => hrs ((Nat.prime_dvd_prime_iff_eq hr hs).mp hd)),
      pow_one]
  have hidx : (P : Subgroup G).index = s := by
    have := (P : Subgroup G).card_mul_index
    rw [hcP, hG] at this
    exact Nat.eq_of_mul_eq_mul_left hr.pos this
  have h1 : Nat.card (Sylow r G) = 1 := hn _ (hidx ▸ P.card_dvd_index) (card_sylow_modEq_one r G)
  haveI : Subsingleton (Sylow r G) := (Nat.card_eq_one_iff_unique.mp h1).1
  refine ⟨P, P.normal_of_subsingleton, P.isPGroup', ?_⟩
  intro g hg
  have hz : IsPGroup r (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  rw [Subsingleton.elim P Q]
  exact hQ (Subgroup.mem_zpowers g)

theorem alg_isCyclic_of_card_eq_prime_mul_prime (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hndvd : ¬ p ∣ q - 1) (G : Type*) [Group G] (hG : Nat.card G = p * q) : IsCyclic G := by
  haveI := Fact.mk hp
  haveI := Fact.mk hq
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact (Nat.mul_pos hp.pos hq.pos).ne')
  obtain ⟨P, hPn, hPp, hP⟩ := alg_isCyclic_of_card_eq_prime_mul_prime_aux1 p q hp hq hpq.ne (by
    intro n hnq hmod
    rcases (Nat.dvd_prime hq).mp hnq with h | h
    · exact h
    · subst h
      exact absurd ((Nat.modEq_iff_dvd' hq.one_lt.le).mp hmod.symm) hndvd) G hG
  obtain ⟨Q, hQn, hQp, hQ⟩ := alg_isCyclic_of_card_eq_prime_mul_prime_aux1 q p hq hp hpq.ne' (by
    intro n hnp hmod
    rcases (Nat.dvd_prime hp).mp hnp with h | h
    · exact h
    · subst h
      have := hmod
      unfold Nat.ModEq at this
      rw [Nat.mod_eq_of_lt hpq, Nat.mod_eq_of_lt hq.one_lt] at this
      exact this) G (by rw [hG, mul_comm])
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) p (by rw [hG]; exact dvd_mul_right _ _)
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := G) q (by rw [hG]; exact dvd_mul_left _ _)
  have hdis : Disjoint P Q := IsPGroup.disjoint_of_ne p q hpq.ne P Q hPp hQp
  have hc : Commute g k := Subgroup.commute_of_normal_of_disjoint P Q hPn hQn hdis g k (hP g hg) (hQ k hk)
  have ho := hc.orderOf_mul_eq_mul_orderOf_of_coprime
    (by rw [hg, hk]; exact (Nat.coprime_primes hp hq).mpr hpq.ne)
  exact isCyclic_of_orderOf_eq_card (g * k) (by rw [ho, hg, hk, hG])
end

-- forge:entry ana_continuous_additive_linear kind=proved origin=conjecture
section
/- Cauchy's functional equation: a continuous additive function on ℝ is linear — additivity gives f(q) = q f(1) for rational q, and both sides are continuous so they agree on the closure of ℚ (or package f as a continuous AddMonoidHom and use map_real_smul). -/
theorem ana_continuous_additive_linear (f : ℝ → ℝ) (hf : Continuous f) (hadd : ∀ x y : ℝ, f (x + y) = f x + f y) (x : ℝ) : f x = f 1 * x := by
  have h := map_real_smul (AddMonoidHom.mk' f hadd) (by simpa using hf) x (1 : ℝ)
  simp only [AddMonoidHom.mk'_apply, smul_eq_mul, mul_one] at h
  rw [h, mul_comm]
end

-- forge:entry comb_card_edgeFinset_le_of_coloring_bool kind=proved origin=conjecture
section
/- A bipartite (2-colourable) graph on n vertices has at most n²/4 edges — edges inject into (colour class true) × (colour class false), of size a·(n-a), and 4a(n-a) ≤ n². -/
theorem comb_card_edgeFinset_le_of_coloring_bool (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (C : G.Coloring Bool) : 4 * G.edgeFinset.card ≤ Fintype.card V ^ 2 := by
  have hc : G.Colorable 2 := by
    have := C.colorable
    simpa using this
  have hf : G.CliqueFree (2 + 1) := hc.cliqueFree (by norm_num)
  have h := hf.card_edgeFinset_le
  dsimp only at h
  have h0 : (Fintype.card V % 2).choose 2 = 0 := Nat.choose_eq_zero_of_lt (Nat.mod_lt _ (by norm_num))
  rw [h0] at h
  have h2 : 4 * (((Fintype.card V) ^ 2 - (Fintype.card V % 2) ^ 2) * (2 - 1) / (2 * 2)) ≤ ((Fintype.card V) ^ 2 - (Fintype.card V % 2) ^ 2) * (2 - 1) := Nat.mul_div_le _ 4
  have h3 : ((Fintype.card V) ^ 2 - (Fintype.card V % 2) ^ 2) * (2 - 1) ≤ Fintype.card V ^ 2 := by
    simp
  omega
end

-- forge:entry lin_nilpotent_det_one_add kind=proved origin=conjecture
section
/- For a nilpotent real matrix A, det(I + A) = 1 — the characteristic polynomial of a nilpotent matrix over a domain is X^n; evaluate det(tI − A) at t = −1 (and fix signs), or show det(I + tA) is a polynomial unit in t hence constant. -/
theorem lin_nilpotent_det_one_add (n k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (h : A ^ k = 0) : Matrix.det (1 + A) = 1 := by
  have hA : IsNilpotent A := ⟨k, h⟩
  have hn : IsNilpotent (-A) := hA.neg
  have hc := IsNilpotent.charpoly_eq_X_pow_finrank ((Matrix.isNilpotent_toLin'_iff (-A)).mpr hn)
  rw [Matrix.charpoly_toLin'] at hc
  have he := Matrix.eval_charpoly (-A) 1
  rw [hc, map_one, sub_neg_eq_add] at he
  rw [← he]
  simp
end

-- forge:entry comb_compl_connected_of_not_connected kind=proved origin=conjecture
section
/- The complement of a disconnected graph is connected — pick a, b not G-reachable; for any x, y: if not G-reachable from each other they are adjacent in the complement, otherwise one of a, b is G-unreachable from both and is a common complement-neighbour. -/
theorem comb_compl_connected_of_not_connected_aux1 (V : Type) (G : SimpleGraph V) (x y : V) (h : ¬ G.Reachable x y) : Gᶜ.Adj x y := by
  rw [SimpleGraph.compl_adj]
  refine ⟨?_, fun hadj => h hadj.reachable⟩
  rintro rfl
  exact h (SimpleGraph.Reachable.refl _)

theorem comb_compl_connected_of_not_connected (V : Type) [Nonempty V] (G : SimpleGraph V) (h : ¬ G.Connected) : Gᶜ.Connected := by
  rw [SimpleGraph.connected_iff] at h ⊢
  refine ⟨?_, ‹_›⟩
  have hp : ¬ G.Preconnected := fun hp => h ⟨hp, ‹_›⟩
  unfold SimpleGraph.Preconnected at hp
  push_neg at hp
  obtain ⟨u, v, huv⟩ := hp
  intro x y
  by_cases hxy : G.Reachable x y
  · have key : ∃ w, ¬ G.Reachable x w := by
      by_contra hc
      push_neg at hc
      exact huv ((hc u).symm.trans (hc v))
    obtain ⟨w, hw⟩ := key
    have hyw : ¬ G.Reachable w y := fun hwy => hw (hxy.trans hwy.symm)
    exact (comb_compl_connected_of_not_connected_aux1 V G x w hw).reachable.trans
      (comb_compl_connected_of_not_connected_aux1 V G w y hyw).reachable
  · exact (comb_compl_connected_of_not_connected_aux1 V G x y hxy).reachable
end

end Mathlib2
