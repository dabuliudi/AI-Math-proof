/- Mathlib2 分片 21（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0020
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry bld3_mantel_equality_colorable_two kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_mantel_equality_regular and Mathlib2.bld_mantel_triangle_free: if there is no edge then n = 0; otherwise fix an edge u v: N(u) and N(v) are disjoint with |N(u)| + |N(v)| = n by regularity, so they partition V, and each is independent by triangle-freeness; colour by membership in N(u). -/
theorem bld3_mantel_equality_colorable_two (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.CliqueFree 3) (he : 4 * G.edgeFinset.card = Fintype.card V ^ 2) : G.Colorable 2 := by
  rcases isEmpty_or_nonempty V with hV | ⟨⟨u⟩⟩
  · exact ⟨SimpleGraph.Coloring.mk (fun w => isEmptyElim w) (fun {v} _ => isEmptyElim v)⟩
  · have C : G.Coloring Bool := SimpleGraph.Coloring.mk (fun w => decide (G.Adj u w)) (by
      intro a b hab heq
      by_cases hua : G.Adj u a
      · have hub : G.Adj u b := by
          have : decide (G.Adj u a) = decide (G.Adj u b) := heq
          simpa [hua] using this
        exact hG {u, a, b} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hua, hub, hab⟩)
      · have hub : G.Adj u b :=
          (bld3_mantel_equality_same_neighbors V G hG he u a hua b).mpr hab
        have : decide (G.Adj u a) = decide (G.Adj u b) := heq
        simp [hua, hub] at this)
    have := C.colorable
    simpa using this
end

-- forge:entry bld3_sq_card_le_sum_mul_sum_inv kind=proved origin=conjecture
section
/- Uses Mathlib2.gen_an_amgm_finset_ordered_ring and Mathlib2.bld2_card_le_sum_of_prod_eq_one: AM-GM for a and for a⁻¹ gives n^n ∏ a ≤ (∑ a)^n and n^n ∏ a⁻¹ ≤ (∑ a⁻¹)^n; multiply (the products cancel) to get (n^2)^n ≤ ((∑ a)(∑ a⁻¹))^n and take n-th roots by monotonicity of powers. -/
theorem bld3_sq_card_le_sum_mul_sum_inv (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] (ι : Type*) (s : Finset ι) (a : ι → K) (ha : ∀ i ∈ s, 0 < a i) : (s.card : K) ^ 2 ≤ (∑ i ∈ s, a i) * ∑ i ∈ s, (a i)⁻¹ := by
  rcases Finset.eq_empty_or_nonempty s with rfl | hne
  · simp
  have hn : s.card ≠ 0 := Finset.card_ne_zero.mpr hne
  have hA := Mathlib2.gen_an_amgm_finset_ordered_ring K ι s a (fun i hi => (ha i hi).le)
  have hB := Mathlib2.gen_an_amgm_finset_ordered_ring K ι s (fun i => (a i)⁻¹)
    (fun i hi => (inv_pos.mpr (ha i hi)).le)
  have hprod : (∏ i ∈ s, a i) * ∏ i ∈ s, (a i)⁻¹ = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun i hi => mul_inv_cancel₀ (ha i hi).ne')
  have hpa : 0 ≤ ∏ i ∈ s, a i := Finset.prod_nonneg (fun i hi => (ha i hi).le)
  have hpb : 0 ≤ ∏ i ∈ s, (a i)⁻¹ := Finset.prod_nonneg (fun i hi => (inv_pos.mpr (ha i hi)).le)
  have hsa : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg (fun i hi => (ha i hi).le)
  have hsb : 0 ≤ ∑ i ∈ s, (a i)⁻¹ := Finset.sum_nonneg (fun i hi => (inv_pos.mpr (ha i hi)).le)
  have hmul := mul_le_mul hA hB (by positivity) (by positivity)
  have e : ((s.card : K) ^ s.card * ∏ i ∈ s, a i) * ((s.card : K) ^ s.card * ∏ i ∈ s, (a i)⁻¹)
      = ((s.card : K) ^ 2) ^ s.card := by
    rw [mul_mul_mul_comm, hprod, mul_one, ← pow_add, ← two_mul, pow_mul]
  rw [e, ← mul_pow] at hmul
  exact (pow_le_pow_iff_left₀ (by positivity) (mul_nonneg hsa hsb) hn).mp hmul
end

-- forge:entry bld3_iterate_shrinking_iterates_tendsto kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_edelstein_iterates_tendsto and Mathlib2.bld_iterate_shrinking_unique_fixed_point: n = 0 forces X subsingleton; otherwise apply Edelstein convergence to g = f^[n] (which fixes p) at each of the n starting points f^[r] x, r < n, and merge the n residue-class subsequences f^[n k + r] x = g^[k] (f^[r] x). -/
theorem bld3_iterate_shrinking_iterates_tendsto {X : Type*} [MetricSpace X] [CompactSpace X] (f : X → X) (n : ℕ) (hf : ∀ x y : X, x ≠ y → dist (f^[n] x) (f^[n] y) < dist x y) (p : X) (hp : f p = p) (x : X) : Filter.Tendsto (fun k : ℕ => f^[k] x) Filter.atTop (nhds p) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hsub : ∀ a b : X, a = b := by
      intro a b
      by_contra hab
      have := hf a b hab
      simp at this
    have : (fun k : ℕ => f^[k] x) = fun _ => p := by
      funext k; exact hsub _ _
    rw [this]; exact tendsto_const_nhds
  · have hgp : f^[n] p = p := Function.iterate_fixed hp n
    have hconv := fun r : ℕ => bld_edelstein_iterates_tendsto (f^[n]) hf p hgp (f^[r] x)
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hev : ∀ᶠ q : ℕ in Filter.atTop, ∀ r ∈ Finset.range n,
        dist ((f^[n])^[q] (f^[r] x)) p < ε := by
      rw [Filter.eventually_all_finset]
      intro r _
      exact (Metric.tendsto_atTop'.mp (hconv r) ε hε).elim fun N hN =>
        Filter.eventually_atTop.mpr ⟨N + 1, fun q hq => hN q (by omega)⟩
    obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.mp hev
    refine ⟨n * Q, fun k hk => ?_⟩
    have hq : Q ≤ k / n := (Nat.le_div_iff_mul_le hn).mpr (by rw [mul_comm]; exact hk)
    have h1 := hQ (k / n) hq (k % n) (Finset.mem_range.mpr (Nat.mod_lt k hn))
    rw [← Function.iterate_mul, ← Function.iterate_add_apply, Nat.div_add_mod] at h1
    exact h1
end

-- forge:entry bld3_rank_tripotent_defect kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_frobenius_rank_inequality and Mathlib2.bld2_tripotent_rank_split: generalises the tripotent rank split (the case A^3 = A); ≤ is Frobenius for the triple (A + 1, A, A - 1); ≥ by block elimination on diag(A^2 + A, A^2 - A) using 2A = (A^2 + A) - (A^2 - A) and invertibility of 2. -/
theorem bld3_rank_tripotent_defect_aux1 (K : Type*) [Field K] (m n p : Type*) [Fintype m] [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]
    (M : Matrix m n K) (N : Matrix n p K) :
    LinearMap.range (M * N).mulVecLin ≤ LinearMap.range M.mulVecLin := by
  rw [Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

theorem bld3_rank_tripotent_defect (K : Type*) [Field K] [CharZero K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) : Matrix.rank (A * A + A) + Matrix.rank (A * A - A) = Matrix.rank A + Matrix.rank (A * A * A - A) := by
  apply le_antisymm
  · have h := bld_frobenius_rank_inequality K ι ι ι ι (A + 1) A (A - 1)
    have e1 : (A + 1) * A = A * A + A := by rw [add_mul, one_mul]
    have e2 : A * (A - 1) = A * A - A := by rw [mul_sub, mul_one]
    have e3 : (A + 1) * A * (A - 1) = A * A * A - A := by
      simp only [add_mul, one_mul, mul_sub, mul_one]; abel
    rw [e3, e1, e2] at h
    exact h
  · have h2 : (2 : K) ≠ 0 := two_ne_zero
    have hA : A = (A * A + A) * ((2⁻¹ : K) • (1 : Matrix ι ι K)) + (A * A - A) * ((-(2⁻¹ : K)) • (1 : Matrix ι ι K)) := by
      rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_one]
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      field_simp
      ring
    have e1 : A * A * A - A = (A * A + A) * (A - 1) := by
      simp only [add_mul, mul_sub, mul_one, mul_assoc]; abel
    have e2 : A * A * A - A = (A * A - A) * (A + 1) := by
      simp only [sub_mul, mul_add, mul_one, mul_assoc]; abel
    have hsup : LinearMap.range A.mulVecLin ≤ LinearMap.range (A * A + A).mulVecLin ⊔ LinearMap.range (A * A - A).mulVecLin := by
      conv_lhs => rw [hA]
      rw [Matrix.mulVecLin_add]
      refine (LinearMap.range_add_le _ _).trans (sup_le_sup ?_ ?_)
      · exact bld3_rank_tripotent_defect_aux1 K ι ι ι _ _
      · exact bld3_rank_tripotent_defect_aux1 K ι ι ι _ _
    have hinf : LinearMap.range (A * A * A - A).mulVecLin ≤ LinearMap.range (A * A + A).mulVecLin ⊓ LinearMap.range (A * A - A).mulVecLin := by
      refine le_inf ?_ ?_
      · rw [e1]; exact bld3_rank_tripotent_defect_aux1 K ι ι ι _ _
      · rw [e2]; exact bld3_rank_tripotent_defect_aux1 K ι ι ι _ _
    have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (A * A + A).mulVecLin) (LinearMap.range (A * A - A).mulVecLin)
    have s1 := Submodule.finrank_mono hsup
    have s2 := Submodule.finrank_mono hinf
    simp only [Matrix.rank]
    omega
end

-- forge:entry bld3_self_summable_of_two_mul_dvd_fib kind=proved origin=conjecture
section
/- Uses Mathlib2.p3_aux_period and Mathlib2.p3_remark2: write fib n = 2 n k; by the period lemma fib (2 + 2 n k) ≡ fib 2 = 1 mod fib n, so fib n ∣ fib (fib n + 2) - 1, which is self-summability by Remark 2 (e.g. n = 12, 24, 36). -/
theorem bld3_self_summable_of_two_mul_dvd_fib (n : ℕ) (h2 : 2 ∣ n) (h : 2 * n ∣ Nat.fib n) : p3_self_summable n := by
  rw [Mathlib2.p3_remark2]
  obtain ⟨k, hk⟩ := h
  have hp := Mathlib2.p3_aux_period n k 2 h2
  rw [← hk, add_comm 2, Nat.fib_two] at hp
  have h1 : 1 ≤ Nat.fib (Nat.fib n + 2) := Nat.fib_pos.mpr (by omega)
  exact (Nat.modEq_iff_dvd' h1).mp hp.symm
end

-- forge:entry bld3_pisano_pos_and_period kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_pisano_fib_odd_eq: by its auxiliary lemma bld2_pisano_fib_odd_eq_aux1 it suffices to exhibit one positive period N; pigeonhole on the pairs (fib i, fib (i+1)) mod m gives i < j with equal pairs, and the recurrence run backwards (fib (i) = fib (i+2) - fib (i+1)) shows N = j - i is a period. -/
theorem bld3_pisano_pos_and_period (m : ℕ) (hm : 0 < m) : 0 < p3_pisano m ∧ ∀ i : ℕ, Nat.fib (i + p3_pisano m) ≡ Nat.fib i [MOD m] := by
  haveI : NeZero m := ⟨hm.ne'⟩
  let σ : Equiv.Perm (ZMod m × ZMod m) :=
    ⟨fun p => (p.2, p.1 + p.2), fun p => (p.2 - p.1, p.1),
      fun p => by ext <;> simp, fun p => by ext <;> simp⟩
  have key : ∀ k : ℕ, (σ ^ k) (0, 1) = ((Nat.fib k : ZMod m), (Nat.fib (k + 1) : ZMod m)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      show ((Nat.fib (k + 1) : ZMod m), (Nat.fib k : ZMod m) + (Nat.fib (k + 1) : ZMod m)) = _
      rw [Nat.fib_add_two (n := k)]
      push_cast
      rfl
  have hN : 0 < orderOf σ := orderOf_pos σ
  have h1 := key (orderOf σ)
  rw [pow_orderOf_eq_one, Equiv.Perm.one_apply, Prod.mk.injEq] at h1
  refine bld2_pisano_fib_odd_eq_aux1 m (orderOf σ) hN ((lib_fib_period_iff m (orderOf σ)).mpr ⟨?_, ?_⟩)
  · rw [← ZMod.natCast_eq_natCast_iff]; exact_mod_cast h1.1.symm
  · rw [← ZMod.natCast_eq_natCast_iff]; exact_mod_cast h1.2.symm
end

-- forge:entry bld3_rank_involution_defect kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_rank_add_rank_one_sub and Mathlib2.bld2_involution_iff_rank_add_rank: apply the idempotent-defect identity to B = (1/2) • (1 + A): 1 - B = (1/2) • (1 - A) and B - B * B = (1/4) • (1 - A * A), and nonzero scalars do not change rank; this refines the involution criterion. -/
theorem bld3_rank_involution_defect (K : Type*) [Field K] [CharZero K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) : Matrix.rank (1 + A) + Matrix.rank (1 - A) = Fintype.card ι + Matrix.rank (1 - A * A) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hc : (2⁻¹ : K) ≠ 0 := inv_ne_zero h2
  have hcc : (2⁻¹ * 2⁻¹ : K) ≠ 0 := mul_ne_zero hc hc
  have h := bld2_rank_add_rank_one_sub K ι ((2⁻¹ : K) • (1 + A))
  have e1 : 1 - (2⁻¹ : K) • (1 + A) = (2⁻¹ : K) • (1 - A) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    field_simp
    ring
  have e2 : (2⁻¹ : K) • (1 + A) - ((2⁻¹ : K) • (1 + A)) * ((2⁻¹ : K) • (1 + A)) = (2⁻¹ * 2⁻¹ : K) • (1 - A * A) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_add, add_mul, one_mul, mul_one]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    field_simp
    ring
  rw [e1, e2, lib_matrix_rank_smul K ι ι _ hc, lib_matrix_rank_smul K ι ι _ hc,
    lib_matrix_rank_smul K ι ι _ hcc] at h
  exact h
end

-- forge:entry bld3_rat_sq_add_sq_ne_of_odd_padicValNat kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_rat_sq_add_sq_ne_prime_mul_coprime: write n = p^(2k+1) m with p ∤ m; if x^2 + y^2 = n then (x/p^k)^2 + (y/p^k)^2 = p m, contradicting the library theorem (rational form of the two-squares obstruction). -/
theorem bld3_rat_sq_add_sq_ne_of_odd_padicValNat (p n : ℕ) (hp : p.Prime) (hp4 : p % 4 = 3) (hodd : Odd (padicValNat p n)) (x y : ℚ) : x ^ 2 + y ^ 2 ≠ (n : ℚ) := by
  haveI := Fact.mk hp
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hodd
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have he : padicValNat p (p ^ e * m) = e := by
    rw [padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm, add_zero]
  rw [he] at hodd
  obtain ⟨k, rfl⟩ := hodd
  intro hxy
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  apply Mathlib2.bld2_rat_sq_add_sq_ne_prime_mul_coprime p m hp hp4 hm (x / p ^ k) (y / p ^ k)
  rw [div_pow, div_pow, ← add_div, hxy]
  push_cast
  field_simp
  ring
end

-- forge:entry bld3_pisano_dvd_of_period kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_pisano_fib_odd_eq: if k = 0 trivial; otherwise by the auxiliary lemma bld2_pisano_fib_odd_eq_aux1 the Pisano period P is a positive period, and k % P is again a period smaller than P, so by minimality (Nat.sInf_le) k % P = 0. -/
theorem bld3_pisano_dvd_of_period (m k : ℕ) (hk : ∀ i : ℕ, Nat.fib (i + k) ≡ Nat.fib i [MOD m]) : p3_pisano m ∣ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · exact dvd_zero _
  · exact (lib_pisano_dvd_iff_period m k hpos).mpr hk
end

-- forge:entry bld3_dvd_fibsum_of_pisano_dvd kind=proved origin=conjecture
section
/- Uses Mathlib2.p3_prop1 and Mathlib2.bld2_pisano_fib_odd_eq: if p3_pisano m = 0 then m = 0 and p3_fibsum 0 = 0; otherwise m is a multiple of a period (aux1), so fib (m + 2) ≡ fib 2 = 1 mod m and p3_fibsum m = fib (m + 2) - 1 ≡ 0. -/
theorem bld3_dvd_fibsum_of_pisano_dvd (m : ℕ) (h : p3_pisano m ∣ m) : m ∣ p3_fibsum m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [p3_fibsum]
  · have h2 := (lib_pisano_dvd_iff_period m m hm).mp h 2
    have h3 := p3_prop1_aux1 m
    rw [show 2 + m = m + 2 by ring, ← h3] at h2
    have h4 : p3_fibsum m + 1 ≡ 0 + 1 [MOD m] := by simpa using h2
    exact (Nat.modEq_zero_iff_dvd).mp (Nat.ModEq.add_right_cancel' 1 h4)
end

-- forge:entry bld3_pow_prime_mem_center_of_card_prime_cube kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_center_card_of_card_prime_cube and Mathlib2.bld2_commutator_eq_center_of_card_prime_cube: the centre has order p so G/Z has order p^2 and is not cyclic (else G abelian), hence every element of G/Z has order dividing p, i.e. g^p ∈ Z. -/
theorem bld3_pow_prime_mem_center_of_card_prime_cube (p : ℕ) (hp : p.Prime) (G : Type*) [Group G] (hG : Nat.card G = p ^ 3) (hna : ∃ a b : G, a * b ≠ b * a) (g : G) : g ^ p ∈ Subgroup.center G := by
  have hZ := Mathlib2.bld_center_card_of_card_prime_cube p hp G hG hna
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact pow_ne_zero _ hp.ne_zero)
  have hQ : Nat.card (G ⧸ Subgroup.center G) = p ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)
    rw [hG, hZ] at h
    have : p ^ 2 * p = Nat.card (G ⧸ Subgroup.center G) * p := by rw [← h]; ring
    exact (Nat.eq_of_mul_eq_mul_right hp.pos this).symm
  have hd : orderOf (g : G ⧸ Subgroup.center G) ∣ p ^ 2 := hQ ▸ orderOf_dvd_natCard _
  obtain ⟨m, hm, hmo⟩ := (Nat.dvd_prime_pow hp).mp hd
  have hpow : (g : G ⧸ Subgroup.center G) ^ p = 1 := by
    interval_cases m
    · rw [pow_zero, orderOf_eq_one_iff] at hmo
      rw [hmo, one_pow]
    · rw [pow_one] at hmo
      rw [← hmo]; exact pow_orderOf_eq_one _
    · exfalso
      haveI : IsCyclic (G ⧸ Subgroup.center G) := isCyclic_of_orderOf_eq_card _ (hmo.trans hQ.symm)
      obtain ⟨a, b, hab⟩ := hna
      exact hab (commutative_of_cyclic_center_quotient (QuotientGroup.mk' (Subgroup.center G))
        (by rw [QuotientGroup.ker_mk']) a b)
  rw [← QuotientGroup.mk_pow] at hpow
  exact (QuotientGroup.eq_one_iff _).mp hpow
end

-- forge:entry bld3_pisano_even kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_pisano_fib_odd_eq and Mathlib2.r3_fib_iff_five_sq_pm_four_is_square_s1h1: let k be the Pisano period (if it is 0 done; else a period by bld2_pisano_fib_odd_eq_aux1), so fib k ≡ 0 and fib (k+1) ≡ 1 mod m; Cassini fib(k+1)^2 - fib(k+1) fib k - fib k^2 = (-1)^k then gives (-1)^k ≡ 1 mod m, and m ≥ 3 excludes k odd. -/
theorem bld3_pisano_even (m : ℕ) (hm : 3 ≤ m) : Even (p3_pisano m) := by
  rcases Nat.eq_zero_or_pos (p3_pisano m) with h0 | hpos
  · rw [h0]; exact ⟨0, rfl⟩
  have hper := (lib_pisano_dvd_iff_period m (p3_pisano m) hpos).mp dvd_rfl
  set k := p3_pisano m with hk
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have h0 := (Nat.modEq_iff_dvd).mp (hper 0)
  have h1 := (Nat.modEq_iff_dvd).mp (hper 1)
  have hcas := r3_fib_iff_five_sq_pm_four_is_square_s1h1 k
  rw [Odd.neg_one_pow hodd] at hcas
  simp only [zero_add, Nat.fib_zero, Nat.fib_one, Nat.cast_zero, Nat.cast_one] at h0 h1
  rw [add_comm 1 k] at h1
  obtain ⟨b, hb⟩ := h0
  obtain ⟨a, ha⟩ := h1
  have hf0 : (Nat.fib k : ℤ) = -(m * b) := by linarith
  have hf1 : (Nat.fib (k + 1) : ℤ) = 1 - m * a := by linarith
  rw [hf0, hf1] at hcas
  have hd : (m : ℤ) ∣ 2 := ⟨2 * a - m * a ^ 2 - (1 - m * a) * b + m * b ^ 2, by linear_combination hcas⟩
  have := Int.le_of_dvd (by norm_num) hd
  omega
end

-- forge:entry bld3_pisano_dvd_pisano_of_dvd kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_pisano_fib_odd_eq: if p3_pisano n = 0 trivial; otherwise it is a period mod n (aux1 of bld2_pisano_fib_odd_eq), hence a period mod m, and the least period mod m divides every period (remainder argument with minimality). -/
theorem bld3_pisano_dvd_pisano_of_dvd (m n : ℕ) (h : m ∣ n) : p3_pisano m ∣ p3_pisano n := by
  rcases Nat.eq_zero_or_pos (p3_pisano n) with h0 | hpos
  · rw [h0]; exact dvd_zero _
  have hper := (lib_pisano_dvd_iff_period n (p3_pisano n) hpos).mp dvd_rfl
  exact (lib_pisano_dvd_iff_period m (p3_pisano n) hpos).mpr (fun i => (hper i).of_dvd h)
end

-- forge:entry bld3_compact_mutual_expanding_isometry kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_expanding_compact_isometryEquiv and Mathlib2.top_expanding_compact_isometry: g ∘ f is expanding on compact X hence an isometry, which squeezes dist x x' ≤ dist (f x) (f x') ≤ dist (g (f x)) (g (f x')) = dist x x'; f ∘ g is expanding on Y hence a bijective isometry, so f is surjective (Cantor–Bernstein for compact metric spaces). -/
theorem bld3_compact_mutual_expanding_isometry {X : Type*} [MetricSpace X] [CompactSpace X] {Y : Type*} [MetricSpace Y] [CompactSpace Y] (f : X → Y) (g : Y → X) (hf : ∀ x x' : X, dist x x' ≤ dist (f x) (f x')) (hg : ∀ y y' : Y, dist y y' ≤ dist (g y) (g y')) : Isometry f ∧ Function.Surjective f := by
  constructor
  · have hgf : Isometry (g ∘ f) :=
      top_expanding_compact_isometry (g ∘ f) (fun x y => (hf x y).trans (hg _ _))
    refine Isometry.of_dist_eq (fun x y => le_antisymm ?_ (hf x y))
    have := hgf.dist_eq x y
    simp only [Function.comp_apply] at this
    linarith [hg (f x) (f y)]
  · obtain ⟨e, he⟩ := bld2_expanding_compact_isometryEquiv (f ∘ g)
      (fun x y => (hg x y).trans (hf _ _))
    intro y
    refine ⟨g (e.symm y), ?_⟩
    have := he (e.symm y)
    simp only [Function.comp_apply] at this
    rw [← this]
    exact e.apply_symm_apply y
end

-- forge:entry bld3_compact_mutual_nonexpanding_surjections_isometry kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_surjective_nonexpanding_compact_isometry: g ∘ f is a non-expanding surjection of compact X, hence an isometry, so dist x x' = dist (g (f x)) (g (f x')) ≤ dist (f x) (f x') ≤ dist x x'. -/
theorem bld3_compact_mutual_nonexpanding_surjections_isometry {X : Type*} [MetricSpace X] [CompactSpace X] {Y : Type*} [MetricSpace Y] [CompactSpace Y] (f : X → Y) (g : Y → X) (hf : Function.Surjective f) (hf' : ∀ x x' : X, dist (f x) (f x') ≤ dist x x') (hg : Function.Surjective g) (hg' : ∀ y y' : Y, dist (g y) (g y') ≤ dist y y') : Isometry f := by
  have h := Mathlib2.bld_surjective_nonexpanding_compact_isometry (g ∘ f) (hg.comp hf)
    (fun x y => (hg' _ _).trans (hf' x y))
  refine Isometry.of_dist_eq fun x x' => le_antisymm (hf' x x') ?_
  have := h.dist_eq x x'
  simp only [Function.comp_apply] at this
  linarith [hg' (f x) (f x')]
end

-- forge:entry bld3_pisano_fib_div_fib_tendsto_zero kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_pisano_fib_dvd_four_mul: the Pisano period of fib n divides 4n so is at most 4n, while fib n grows at least like n^2 (e.g. fib (n+2) ≥ n^2/4 or exponentially), so the ratio is squeezed to 0; strengthens the liminf statement p3_cor1. -/
theorem bld3_pisano_fib_div_fib_tendsto_zero_aux1 (n : ℕ) : n ^ 2 ≤ 6 * Nat.fib n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simp
    | 2 => simp
    | 3 => simp [Nat.fib_add_two]
    | 4 => simp [Nat.fib_add_two]
    | k + 5 =>
      have h1 := ih (k + 3) (by omega)
      have h2 := ih (k + 3 + 1) (by omega)
      rw [show k + 5 = (k + 3) + 2 by ring, Nat.fib_add_two]
      have h3 : (k + 3 + 2) ^ 2 ≤ (k + 3) ^ 2 + (k + 3 + 1) ^ 2 := by
        ring_nf
        linarith [Nat.zero_le (k ^ 2), Nat.zero_le k]
      linarith

theorem bld3_pisano_fib_div_fib_tendsto_zero : Filter.Tendsto (fun n : ℕ => (p3_pisano (Nat.fib n) : ℝ) / (Nat.fib n : ℝ)) Filter.atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat 24) (Filter.Eventually.of_forall fun n => by positivity) ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hdvd := Mathlib2.bld2_pisano_fib_dvd_four_mul n hn
  have hle : p3_pisano (Nat.fib n) ≤ 4 * n := Nat.le_of_dvd (by omega) hdvd
  have hfib : 0 < Nat.fib n := Nat.fib_pos.mpr hn
  have hsq := bld3_pisano_fib_div_fib_tendsto_zero_aux1 n
  have hle' : (p3_pisano (Nat.fib n) : ℝ) ≤ 4 * n := by exact_mod_cast hle
  have hsq' : (n : ℝ) ^ 2 ≤ 6 * Nat.fib n := by exact_mod_cast hsq
  have hf : (0 : ℝ) < Nat.fib n := by exact_mod_cast hfib
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_div_iff₀ hf hn']
  nlinarith
end

-- forge:entry bld3_edelstein_iterates_tendsto_uniformly kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_edelstein_iterates_tendsto: the continuous functions x ↦ dist (f^[n] x) p decrease in n and tend to 0 pointwise by the library theorem; Dini's argument (the open sets {x | dist (f^[n] x) p < ε} increase and cover the compact X) gives uniformity. -/
theorem bld3_edelstein_iterates_tendsto_uniformly {X : Type*} [MetricSpace X] [CompactSpace X] (f : X → X) (hf : ∀ x y : X, x ≠ y → dist (f x) (f y) < dist x y) (p : X) (hp : f p = p) (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x : X, dist (f^[n] x) p < ε := by
  have hne : ∀ x y : X, dist (f x) (f y) ≤ dist x y := by
    intro x y
    by_cases hxy : x = y
    · subst hxy; simp
    · exact (hf x y hxy).le
  have hcont : Continuous f := (LipschitzWith.mk_one hne).continuous
  have hanti : ∀ (x : X) (k n : ℕ), k ≤ n → dist (f^[n] x) p ≤ dist (f^[k] x) p := by
    intro x k n hkn
    induction n, hkn using Nat.le_induction with
    | base => exact le_rfl
    | succ n _ ih =>
      rw [Function.iterate_succ_apply']
      calc dist (f (f^[n] x)) p = dist (f (f^[n] x)) (f p) := by rw [hp]
        _ ≤ dist (f^[n] x) p := hne _ _
        _ ≤ _ := ih
  have hopen : ∀ n : ℕ, IsOpen {x : X | dist (f^[n] x) p < ε} := fun n =>
    isOpen_lt ((hcont.iterate n).dist continuous_const) continuous_const
  have hcover : (Set.univ : Set X) ⊆ ⋃ n : ℕ, {x : X | dist (f^[n] x) p < ε} := by
    intro x _
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (bld_edelstein_iterates_tendsto f hf p hp x) ε hε
    exact Set.mem_iUnion.mpr ⟨N, hN N le_rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hopen hcover
  refine ⟨t.sup id, fun n hn x => ?_⟩
  have hx := ht (Set.mem_univ x)
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx
  obtain ⟨k, hkt, hk⟩ := hx
  have hkn : k ≤ n := (Finset.le_sup (f := id) hkt).trans hn
  exact (hanti x k n hkn).trans_lt hk
end

-- forge:entry bld3_mul_pow_prime_of_card_prime_cube kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_commutator_eq_center_of_card_prime_cube and Mathlib2.bld_center_card_of_card_prime_cube: commutators are central of order dividing p, so by induction (a b)^k = a^k b^k c^(k(k-1)/2) with c the central commutator of b and a; for odd p, p ∣ p(p-1)/2 and c^p = 1 (false for p = 2, e.g. the dihedral group of order 8). -/
theorem bld3_mul_pow_prime_of_card_prime_cube_aux1 {M : Type*} [Monoid M] (a b c : M)
    (hca : Commute c a) (hcb : Commute c b) (h : b * a = c * a * b) (k : ℕ) :
    b ^ k * a = c ^ k * a * b ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc b ^ (k + 1) * a = b ^ k * (b * a) := by rw [pow_succ, mul_assoc]
      _ = (b ^ k * c) * a * b := by rw [h]; simp only [mul_assoc]
      _ = c * (b ^ k * a) * b := by rw [← (hcb.pow_right k).eq]; simp only [mul_assoc]
      _ = c * (c ^ k * a * b ^ k) * b := by rw [ih]
      _ = (c * c ^ k) * a * (b ^ k * b) := by simp only [mul_assoc]
      _ = c ^ (k + 1) * a * b ^ (k + 1) := by rw [← pow_succ', ← pow_succ]

theorem bld3_mul_pow_prime_of_card_prime_cube_aux2 {M : Type*} [Monoid M] (a b c : M)
    (hca : Commute c a) (hcb : Commute c b) (h : b * a = c * a * b) (k : ℕ) :
    (a * b) ^ k = a ^ k * b ^ k * c ^ (k.choose 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hT : Commute (c ^ (k.choose 2)) (a * b) := (hca.mul_right hcb).pow_left _
    have hK : Commute (c ^ k) (a ^ (k + 1) * b ^ (k + 1)) :=
      ((hca.pow_right _).mul_right (hcb.pow_right _)).pow_left _
    have hck : a ^ k * c ^ k = c ^ k * a ^ k := ((hca.pow_left k).pow_right k).eq.symm
    have hch : (k + 1).choose 2 = k + k.choose 2 := by
      rw [show 2 = 1 + 1 from rfl, Nat.choose_succ_succ', Nat.choose_one_right]
    calc (a * b) ^ (k + 1) = (a * b) ^ k * (a * b) := pow_succ _ _
      _ = a ^ k * b ^ k * c ^ (k.choose 2) * (a * b) := by rw [ih]
      _ = a ^ k * b ^ k * (a * b) * c ^ (k.choose 2) := by rw [mul_assoc, hT.eq, ← mul_assoc]
      _ = a ^ k * (b ^ k * a) * b * c ^ (k.choose 2) := by simp only [mul_assoc]
      _ = a ^ k * (c ^ k * a * b ^ k) * b * c ^ (k.choose 2) := by
        rw [bld3_mul_pow_prime_of_card_prime_cube_aux1 a b c hca hcb h k]
      _ = (a ^ k * c ^ k) * (a * (b ^ k * b)) * c ^ (k.choose 2) := by simp only [mul_assoc]
      _ = (c ^ k * a ^ k) * (a * b ^ (k + 1)) * c ^ (k.choose 2) := by rw [← pow_succ, hck]
      _ = c ^ k * (a ^ (k + 1) * b ^ (k + 1)) * c ^ (k.choose 2) := by
        rw [pow_succ a]; simp only [mul_assoc]
      _ = a ^ (k + 1) * b ^ (k + 1) * c ^ k * c ^ (k.choose 2) := by rw [hK.eq]
      _ = a ^ (k + 1) * b ^ (k + 1) * c ^ ((k + 1).choose 2) := by
        rw [mul_assoc, ← pow_add, hch]

theorem bld3_mul_pow_prime_of_card_prime_cube (p : ℕ) (hp : p.Prime) (G : Type*) [Group G] (hG : Nat.card G = p ^ 3) (hna : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (a b : G) : (a * b) ^ p = a ^ p * b ^ p := by
  letI : Bracket G G := commutatorElement
  have hZ := Mathlib2.bld_center_card_of_card_prime_cube p hp G hG hna
  have hC := Mathlib2.bld2_commutator_eq_center_of_card_prime_cube p hp G hG hna
  have hc : ⁅b, a⁆ ∈ Subgroup.center G := by
    rw [← hC, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top b) (Subgroup.mem_top a)
  have hcp : ⁅b, a⁆ ^ p = 1 := by
    have h1 : (⟨⁅b, a⁆, hc⟩ : Subgroup.center G) ^ Nat.card (Subgroup.center G) = 1 :=
      pow_card_eq_one'
    rw [hZ] at h1
    exact congrArg Subtype.val h1
  have hcomm : ∀ x : G, Commute ⁅b, a⁆ x := fun x => ((Subgroup.mem_center_iff.mp hc) x).symm
  have h : b * a = ⁅b, a⁆ * a * b := by
    rw [commutatorElement_def]; group
  rw [bld3_mul_pow_prime_of_card_prime_cube_aux2 a b ⁅b, a⁆ (hcomm a) (hcomm b) h p]
  have h2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  obtain ⟨m, hm⟩ := hp.dvd_choose_self (by norm_num : (2 : ℕ) ≠ 0) h2
  rw [hm, pow_mul, hcp, one_pow, mul_one]
end

-- forge:entry bld3_card_sylow_of_card_prime_mul_prime kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_center_eq_bot_of_card_prime_mul_prime: the number of Sylow p-subgroups divides q, so is 1 or q; if 1 the Sylow p-subgroup P is normal of order p, G acts on it by conjugation through Aut(P) of order p - 1 coprime to pq, so P is central, contradicting the trivial centre. -/
lemma bld3_card_sylow_of_card_prime_mul_prime_aux1 (r s : ℕ) [Fact r.Prime] (hs : s.Prime) (hrs : r ≠ s)
    (G : Type*) [Group G] (hG : Nat.card G = r * s) (P : Sylow r G) :
    Nat.card (P : Subgroup G) = r ∧ (P : Subgroup G).index = s := by
  have hr : r.Prime := Fact.out
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact mul_ne_zero hr.ne_zero hs.ne_zero)
  have h1 : Nat.card (P : Subgroup G) = r := by
    rw [Sylow.card_eq_multiplicity, hG, Nat.factorization_mul hr.ne_zero hs.ne_zero]
    have : s.factorization r = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun h => hrs ((Nat.prime_dvd_prime_iff_eq hr hs).1 h))
    simp [this, hr.factorization_self]
  refine ⟨h1, ?_⟩
  have := Subgroup.index_mul_card (P : Subgroup G)
  rw [h1, hG, mul_comm] at this
  exact Nat.eq_of_mul_eq_mul_left hr.pos this

theorem bld3_card_sylow_of_card_prime_mul_prime (p q : ℕ) [Fact p.Prime] (hq : q.Prime) (hpq : p < q) (G : Type*) [Group G] (hG : Nat.card G = p * q) (hna : ∃ a b : G, a * b ≠ b * a) : Nat.card (Sylow p G) = q := by
  have hp : p.Prime := Fact.out
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact mul_ne_zero hp.ne_zero hq.ne_zero)
  have hZ := Mathlib2.bld_center_eq_bot_of_card_prime_mul_prime p q hp hq G hG hna
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  obtain ⟨Q⟩ : Nonempty (Sylow q G) := inferInstance
  obtain ⟨hP, hPi⟩ := bld3_card_sylow_of_card_prime_mul_prime_aux1 p q hq hpq.ne G hG P
  obtain ⟨hQ, hQi⟩ := bld3_card_sylow_of_card_prime_mul_prime_aux1 q p hp hpq.ne' G (by rw [hG, mul_comm]) Q
  have hd : Nat.card (Sylow p G) ∣ q := hPi ▸ Sylow.card_dvd_index P
  rcases (Nat.dvd_prime hq).1 hd with h1 | h1
  swap
  · exact h1
  exfalso
  haveI : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.1 h1).1
  have hPn : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
  have hQn : (Q : Subgroup G).Normal := by
    have hd' : Nat.card (Sylow q G) ∣ p := hQi ▸ Sylow.card_dvd_index Q
    have hm := card_sylow_modEq_one q G
    rcases (Nat.dvd_prime hp).1 hd' with h2 | h2
    · haveI : Subsingleton (Sylow q G) := (Nat.card_eq_one_iff_unique.1 h2).1
      exact Sylow.normal_of_subsingleton Q
    · exfalso
      rw [h2] at hm
      unfold Nat.ModEq at hm
      rw [Nat.mod_eq_of_lt hpq, Nat.mod_eq_of_lt hq.one_lt] at hm
      exact hp.one_lt.ne' hm
  have hcop : (Nat.card (P : Subgroup G)).Coprime (Nat.card (Q : Subgroup G)) := by
    rw [hP, hQ]; exact (Nat.coprime_primes hp hq).2 hpq.ne
  have hdisj : Disjoint (P : Subgroup G) (Q : Subgroup G) :=
    disjoint_iff.2 (Subgroup.inf_eq_bot_of_coprime hcop)
  have hcomm := Subgroup.commute_of_normal_of_disjoint _ _ hPn hQn hdisj
  haveI : IsCyclic (P : Subgroup G) := isCyclic_of_prime_card hP
  have hPC : (P : Subgroup G) ≤ Subgroup.centralizer ((P : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have := (IsCyclic.isMulCommutative (α := (P : Subgroup G))).is_comm.comm ⟨h, hh⟩ ⟨g, hg⟩
    exact congrArg Subtype.val this
  have hQC : (Q : Subgroup G) ≤ Subgroup.centralizer ((P : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hcomm h g hh hg).eq
  have hdvd : p * q ∣ Nat.card (Subgroup.centralizer ((P : Subgroup G) : Set G)) := by
    have a1 := Subgroup.card_dvd_of_le hPC
    have a2 := Subgroup.card_dvd_of_le hQC
    rw [hP] at a1; rw [hQ] at a2
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hp hq).2 hpq.ne) a1 a2
  have htop : Subgroup.centralizer ((P : Subgroup G) : Set G) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    apply Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card _)
    rw [hG]; exact hdvd
  have hsub := Subgroup.centralizer_eq_top_iff_subset.1 htop
  have hle : (P : Subgroup G) ≤ ⊥ := hZ ▸ hsub
  have := Subgroup.card_dvd_of_le hle
  rw [hP, Subgroup.card_bot] at this
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)
end

-- forge:entry bld3_card_conjClasses_of_card_prime_mul_prime kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_center_eq_bot_of_card_prime_mul_prime and Mathlib2.alg_isCyclic_of_card_eq_prime_mul_prime: the centre is trivial, so every non-identity class has size p or q; the normal Sylow q-subgroup contributes (q-1)/p classes of size p (centralizer of order q), the remaining q(p-1) elements of order p have centralizer of order p and form p - 1 classes of size q; total 1 + (q-1)/p + (p-1). -/
lemma bld3_card_conjClasses_of_card_prime_mul_prime_aux1 (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (G : Type*) [Group G] (hG : Nat.card G = p * q) (hna : ∃ a b : G, a * b ≠ b * a) (a : G) (ha : a ≠ 1) :
    Nat.card {b : G // Commute a b} = orderOf a ∧ (orderOf a = p ∨ orderOf a = q) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact mul_ne_zero hp.ne_zero hq.ne_zero)
  have hZ := Mathlib2.bld_center_eq_bot_of_card_prime_mul_prime p q hp hq G hG hna
  have hcard : Nat.card {b : G // Commute a b} = Nat.card (Subgroup.centralizer ({a} : Set G)) := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro b
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => h.eq.symm, fun h => h.symm⟩
  rw [hcard]
  have hamem : a ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
  have hord : orderOf a ∣ Nat.card (Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.orderOf_dvd_natCard _ hamem
  have ho1 : orderOf a ≠ 1 := fun h => ha (orderOf_eq_one_iff.1 h)
  have hdvd : Nat.card (Subgroup.centralizer ({a} : Set G)) ∣ p * q := hG ▸ Subgroup.card_subgroup_dvd_card _
  have hntop : Nat.card (Subgroup.centralizer ({a} : Set G)) ≠ p * q := by
    intro h
    have htop : Subgroup.centralizer ({a} : Set G) = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (h.trans hG.symm)
    rw [Subgroup.centralizer_eq_top_iff_subset] at htop
    have : a ∈ Subgroup.center G := htop (Set.mem_singleton a)
    rw [hZ, Subgroup.mem_bot] at this
    exact ha this
  obtain ⟨d1, d2, h1, h2, hd⟩ := (Nat.dvd_mul).1 hdvd
  rw [← hd] at hord hntop ⊢
  rcases (Nat.dvd_prime hp).1 h1 with e1 | e1 <;> rcases (Nat.dvd_prime hq).1 h2 with e2 | e2 <;>
    rw [e1, e2] at hord hntop ⊢
  · exact absurd (Nat.dvd_one.1 (by simpa using hord)) ho1
  · rw [one_mul] at hord ⊢
    have := ((Nat.dvd_prime hq).1 hord).resolve_left ho1
    exact ⟨this.symm, Or.inr this⟩
  · rw [mul_one] at hord ⊢
    have := ((Nat.dvd_prime hp).1 hord).resolve_left ho1
    exact ⟨this.symm, Or.inl this⟩
  · exact absurd rfl hntop

theorem bld3_card_conjClasses_of_card_prime_mul_prime (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (G : Type*) [Group G] (hG : Nat.card G = p * q) (hna : ∃ a b : G, a * b ≠ b * a) : Nat.card (ConjClasses G) = p + (q - 1) / p := by
  classical
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact mul_ne_zero hp.ne_zero hq.ne_zero)
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fact q.Prime := ⟨hq⟩
  -- p ∣ q - 1, else G is cyclic
  have hdiv : p ∣ q - 1 := by
    by_contra hnd
    haveI := Mathlib2.alg_isCyclic_of_card_eq_prime_mul_prime p q hp hq hpq hnd G hG
    obtain ⟨a, b, hab⟩ := hna
    exact hab ((IsCyclic.isMulCommutative (α := G)).is_comm.comm a b)
  obtain ⟨m, hm⟩ := hdiv
  -- the normal Sylow q-subgroup containing all elements of order q
  obtain ⟨P, -, hPq, hPmem⟩ := Mathlib2.alg_isCyclic_of_card_eq_prime_mul_prime_aux1 q p hq hp hpq.ne'
    (by
      intro n hn hmod
      rcases (Nat.dvd_prime hp).1 hn with h | h
      · exact h
      · exfalso
        rw [h] at hmod
        unfold Nat.ModEq at hmod
        rw [Nat.mod_eq_of_lt hpq, Nat.mod_eq_of_lt hq.one_lt] at hmod
        exact hp.one_lt.ne' hmod) G (by rw [hG, mul_comm])
  have hPc : Nat.card P = q := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hPq
    have hdvd : Nat.card P ∣ q * p := by
      rw [mul_comm, ← hG]; exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) q (by rw [hG]; exact dvd_mul_left q p)
    have hgP := hPmem g hg
    have hgd : q ∣ Nat.card P := hg ▸ Subgroup.orderOf_dvd_natCard _ hgP
    rw [hk] at hdvd hgd ⊢
    rcases k with _ | _ | k
    · simp at hgd; exact absurd hgd hq.one_lt.ne'
    · simp
    · exfalso
      have h2 : q ^ 2 ∣ q * p := (pow_dvd_pow q (by omega)).trans hdvd
      rw [pow_two] at h2
      have h3 : q ∣ p := Nat.dvd_of_mul_dvd_mul_left hq.pos h2
      exact hpq.ne' ((Nat.prime_dvd_prime_iff_eq hq hp).1 h3)
  have hqpq : q ≤ p * q := Nat.le_mul_of_pos_left q hp.pos
  have key : ∀ a : G, Nat.card {b : G // Commute a b} =
      p + (if a ∈ P then q - p else 0) + (if a = 1 then p * q - q else 0) := by
    intro a
    by_cases ha : a = 1
    · subst ha
      have : Nat.card {b : G // Commute (1 : G) b} = Nat.card G :=
        Nat.card_congr (Equiv.subtypeUnivEquiv (fun b => Commute.one_left b))
      rw [this, hG, if_pos P.one_mem, if_pos rfl]
      omega
    · obtain ⟨h1, h2⟩ := bld3_card_conjClasses_of_card_prime_mul_prime_aux1 p q hp hq G hG hna a ha
      rw [h1, if_neg ha, add_zero]
      by_cases haP : a ∈ P
      · rw [if_pos haP]
        have hd : orderOf a ∣ q := hPc ▸ Subgroup.orderOf_dvd_natCard _ haP
        have : orderOf a = q :=
          ((Nat.dvd_prime hq).1 hd).resolve_left (fun h => ha (orderOf_eq_one_iff.1 h))
        omega
      · rw [if_neg haP]
        rcases h2 with h | h
        · omega
        · exact absurd (hPmem a h) haP
  have h1 := card_comm_eq_card_conjClasses_mul_card G
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun a b : G => Commute a b)), Nat.card_sigma, hG] at h1
  simp_rw [key] at h1
  have hsP : ∑ a : G, (if a ∈ P then q - p else 0) = q * (q - p) := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul,
      ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact congrArg (· * (q - p)) hPc
  have hs1 : ∑ a : G, (if a = 1 then p * q - q else 0) = p * q - q := by
    simp
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsP, hs1, Finset.sum_const, smul_eq_mul,
    Finset.card_univ, ← Nat.card_eq_fintype_card, hG] at h1
  obtain ⟨d, hd⟩ : ∃ d, q = p + d := ⟨q - p, by omega⟩
  obtain ⟨e, he⟩ : ∃ e, p * q = q + e := ⟨p * q - q, by omega⟩
  have hd' : q - p = d := by omega
  have he' : p * q - q = e := by omega
  rw [hd', he'] at h1
  have hq1 : q = p * m + 1 := by have := hq.one_lt; omega
  have hfin : Nat.card (ConjClasses G) * (p * q) = (p + m) * (p * q) := by
    zify at h1 hd he hq1 ⊢
    linear_combination (-1 : ℤ) * h1 - (q : ℤ) * hd - he + (q : ℤ) * hq1
  have hK := Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hp.pos hq.pos) hfin
  rw [hK, hm, Nat.mul_div_cancel_left m hp.pos]
end

end Mathlib2
