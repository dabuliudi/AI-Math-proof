/- Mathlib2 分片 8（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0007
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry alg_center_index_not_prime kind=proved origin=conjecture
section
/- The index of the center of a group is never a prime — if [G : Z(G)] = p then G/Z(G) is cyclic, so G is abelian and the index is 1. -/
theorem alg_center_index_not_prime (G : Type*) [Group G] : ¬ (Subgroup.center G).index.Prime := by
  intro hp
  haveI : Fact (Subgroup.center G).index.Prime := ⟨hp⟩
  haveI : IsCyclic (G ⧸ Subgroup.center G) := isCyclic_of_prime_card (p := (Subgroup.center G).index) rfl
  have hc : ∀ a b : G, a * b = b * a :=
    commutative_of_cyclic_center_quotient (QuotientGroup.mk' (Subgroup.center G)) (by simp)
  have ht : Subgroup.center G = ⊤ := by
    ext x
    simp only [Subgroup.mem_center_iff, Subgroup.mem_top, iff_true]
    intro g
    exact hc g x
  rw [ht, Subgroup.index_top] at hp
  exact Nat.not_prime_one hp
end

-- forge:entry lin_involution_eigenvalue kind=proved origin=conjecture
section
/- Every eigenvalue of a linear involution is 1 or -1 — take an eigenvector v; v = f (f v) = μ² v with v ≠ 0 gives μ² = 1. -/
theorem lin_involution_eigenvalue (V : Type) [AddCommGroup V] [Module ℝ V] (f : Module.End ℝ V) (hf : f * f = 1) (μ : ℝ) (h : Module.End.HasEigenvalue f μ) : μ = 1 ∨ μ = -1 := by
  obtain ⟨v, hv⟩ := h.exists_hasEigenvector
  have h1 : f v = μ • v := hv.apply_eq_smul
  have h2 : (f * f) v = v := by rw [hf]; rfl
  have h3 : (μ * μ - 1) • v = 0 := by
    rw [sub_smul, one_smul, mul_smul]
    have : f (f v) = v := h2
    rw [h1, map_smul, h1] at this
    rw [this, sub_self]
  have h4 : μ * μ - 1 = 0 := by
    rcases smul_eq_zero.mp h3 with h | h
    · exact h
    · exact absurd h hv.2
  have h5 : (μ - 1) * (μ + 1) = 0 := by ring_nf; ring_nf at h4; linarith
  rcases mul_eq_zero.mp h5 with h | h
  · left; linarith
  · right; linarith
end

-- forge:entry comb_exists_two_vertices_same_degree kind=proved origin=conjecture
section
/- Every finite simple graph on at least two vertices has two distinct vertices of equal degree — degrees lie in {0..n-1}; if injective, degree is a bijection onto range n, so some vertex has degree 0 and another degree n-1, contradiction since the latter is adjacent to the former. -/
theorem comb_exists_two_vertices_same_degree (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (h : 2 ≤ Fintype.card V) : ∃ u v : V, u ≠ v ∧ G.degree u = G.degree v := by
  by_contra hcon
  push_neg at hcon
  have hinj : Function.Injective (fun v : V => (⟨G.degree v, G.degree_lt_card_verts v⟩ : Fin (Fintype.card V))) := by
    intro a b hab
    by_contra hne
    exact hcon a b hne (congrArg Fin.val hab)
  have hbij := (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, by simp⟩
  obtain ⟨u, hu⟩ := hbij.2 ⟨0, by omega⟩
  obtain ⟨v, hv⟩ := hbij.2 ⟨Fintype.card V - 1, by omega⟩
  have hu0 : G.degree u = 0 := congrArg Fin.val hu
  have hv1 : G.degree v = Fintype.card V - 1 := congrArg Fin.val hv
  have huv : u ≠ v := by
    rintro rfl
    omega
  have hsub : G.neighborFinset v = Finset.univ.erase v := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      simp only [SimpleGraph.mem_neighborFinset] at hw
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      rintro rfl
      exact G.irrefl hw
    · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, G.card_neighborFinset_eq_degree, hv1]
  have hmem : u ∈ G.neighborFinset v := by
    rw [hsub]
    simp [huv]
  have hadj : G.Adj u v := ((G.mem_neighborFinset _ _).1 hmem).symm
  have hpos : 0 < G.degree u := (G.degree_pos_iff_exists_adj u).2 ⟨v, hadj⟩
  omega
end

-- forge:entry ana_exp_ge_cubic_taylor kind=proved origin=conjecture
section
/- The cubic Taylor polynomial of exp is a lower bound on all of ℝ (odd degree) — g = exp - T3 has g' = exp - T2 ≥ ... ; iterate: exp - (1+x) ≥ 0 everywhere, so exp - T2 is increasing with zero at 0, so exp - T3 has a minimum 0 at 0. -/
theorem ana_exp_ge_cubic_taylor (x : ℝ) : 1 + x + x ^ 2 / 2 + x ^ 3 / 6 ≤ Real.exp x := by
  have hk : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Real.exp (-y) * (1 + y + y ^ 2 / 2 + y ^ 3 / 6))
      (-(Real.exp (-y) * (y ^ 3 / 6))) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => 1 + y + y ^ 2 / 2 + y ^ 3 / 6) (1 + y + y ^ 2 / 2) y := by
      have := (((hasDerivAt_id' y).const_add 1).add ((hasDerivAt_pow 2 y).div_const 2)).add
        ((hasDerivAt_pow 3 y).div_const 6)
      convert! this using 1
      norm_num
      ring
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (Real.exp (-y) * -1) y := (hasDerivAt_neg y).exp
    convert! h2.mul h1 using 1
    ring
  have hd : Differentiable ℝ (fun y : ℝ => Real.exp (-y) * (1 + y + y ^ 2 / 2 + y ^ 3 / 6)) :=
    fun y => (hk y).differentiableAt
  have hmono : MonotoneOn (fun y : ℝ => Real.exp (-y) * (1 + y + y ^ 2 / 2 + y ^ 3 / 6)) (Set.Iic 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iic 0) hd.continuous.continuousOn hd.differentiableOn
    intro y hy
    rw [interior_Iic, Set.mem_Iio] at hy
    rw [(hk y).deriv]
    have : y ^ 3 < 0 := by
      have : 0 < (-y) ^ 3 := pow_pos (neg_pos.mpr hy) 3
      nlinarith
    nlinarith [Real.exp_pos (-y), mul_pos (Real.exp_pos (-y)) (neg_pos.mpr this)]
  have hanti : AntitoneOn (fun y : ℝ => Real.exp (-y) * (1 + y + y ^ 2 / 2 + y ^ 3 / 6)) (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hd.continuous.continuousOn hd.differentiableOn
    intro y hy
    rw [interior_Ici, Set.mem_Ioi] at hy
    rw [(hk y).deriv]
    have : 0 < Real.exp (-y) * (y ^ 3 / 6) := by positivity
    linarith
  have hle : Real.exp (-x) * (1 + x + x ^ 2 / 2 + x ^ 3 / 6) ≤ 1 := by
    rcases le_total x 0 with h | h
    · have := hmono (Set.mem_Iic.mpr h) (Set.mem_Iic.mpr le_rfl) h
      simpa using this
    · have := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h) h
      simpa using this
  have he : 1 + x + x ^ 2 / 2 + x ^ 3 / 6 = Real.exp x * (Real.exp (-x) * (1 + x + x ^ 2 / 2 + x ^ 3 / 6)) := by
    rw [← mul_assoc, ← Real.exp_add]; simp
  rw [he]
  calc Real.exp x * (Real.exp (-x) * (1 + x + x ^ 2 / 2 + x ^ 3 / 6)) ≤ Real.exp x * 1 :=
        mul_le_mul_of_nonneg_left hle (Real.exp_pos x).le
    _ = Real.exp x := mul_one _
end

-- forge:entry lin_gram_det_nonneg kind=proved origin=conjecture
section
/- The 2×2 Gram determinant of two vectors in a real inner product space is nonnegative — expand with det_fin_two; it is Cauchy–Schwarz ⟨x,y⟩² ≤ ⟨x,x⟩⟨y,y⟩ plus symmetry of the inner product. -/
theorem lin_gram_det_nonneg (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (x y : V) : 0 ≤ Matrix.det !![inner ℝ x x, inner ℝ x y; inner ℝ y x, inner ℝ y y] := by
  rw [Matrix.det_fin_two_of]
  have h := real_inner_mul_inner_self_le x y
  rw [real_inner_comm x y]
  linarith
end

-- forge:entry comb_connected_of_min_degree_half kind=proved origin=conjecture
section
/- A graph on n vertices with every degree ≥ (n-1)/2 is connected — two non-adjacent vertices u ≠ v have neighbourhoods inside V \ {u,v} (n-2 elements) of total size ≥ n-1, so they share a neighbour; hence any two vertices are at distance ≤ 2. -/
theorem comb_connected_of_min_degree_half (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (h : ∀ v : V, Fintype.card V ≤ 2 * G.degree v + 1) : G.Connected := by
  refine ⟨fun u v => ?_⟩
  by_cases huv : u = v
  · subst huv
    exact SimpleGraph.Reachable.refl _
  by_cases hadj : G.Adj u v
  · exact hadj.reachable
  by_contra hnr
  have hdisj : Disjoint (G.neighborFinset u) (G.neighborFinset v) := by
    rw [Finset.disjoint_left]
    intro w hwu hwv
    rw [SimpleGraph.mem_neighborFinset] at hwu hwv
    exact hnr (hwu.reachable.trans hwv.symm.reachable)
  have hsub : G.neighborFinset u ∪ G.neighborFinset v ⊆ (Finset.univ.erase u).erase v := by
    intro w hw
    rw [Finset.mem_union, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset] at hw
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    rcases hw with hw | hw
    · refine ⟨?_, ?_⟩
      · rintro rfl
        exact hadj hw
      · rintro rfl
        exact G.irrefl hw
    · refine ⟨?_, ?_⟩
      · rintro rfl
        exact G.irrefl hw
      · rintro rfl
        exact hadj hw.symm
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree,
    Finset.card_erase_of_mem (by simp [Ne.symm huv]), Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at hcard
  have h1 := h u
  have h2 := h v
  have h3 : 2 ≤ Fintype.card V := by
    have := Fintype.one_lt_card_iff.2 ⟨u, v, huv⟩
    omega
  omega
end

-- forge:entry ana_log_one_add_ge_quadratic kind=proved origin=conjecture
section
/- log(1+x) ≥ x - x^2/2 for x ≥ 0 — the difference vanishes at 0 and has derivative 1/(1+x) - 1 + x = x^2/(1+x) ≥ 0, so it is monotone on [0,∞). -/
theorem ana_log_one_add_ge_quadratic (x : ℝ) (hx : 0 ≤ x) : x - x ^ 2 / 2 ≤ Real.log (1 + x) := by
  have hk : ∀ y : ℝ, 0 ≤ y → HasDerivAt (fun y : ℝ => Real.log (1 + y) - y + y ^ 2 / 2)
      (y ^ 2 / (1 + y)) y := by
    intro y hy
    have hne : (1 + y) ≠ 0 := by positivity
    have := ((((hasDerivAt_id' y).const_add 1).log hne).sub (hasDerivAt_id' y)).add
      ((hasDerivAt_pow 2 y).div_const 2)
    convert! this using 1
    field_simp
    ring
  have hmono : MonotoneOn (fun y : ℝ => Real.log (1 + y) - y + y ^ 2 / 2) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun y hy => (hk y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact (hk y (le_of_lt hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici, Set.mem_Ioi] at hy
      rw [(hk y hy.le).deriv]
      positivity
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  simp at this
  linarith
end

-- forge:entry alg_odd_card_order_two_of_even_card kind=proved origin=conjecture
section
/- In a finite group of even order the number of elements of order exactly 2 is odd — pair g with g⁻¹: the elements with g ≠ g⁻¹ come in pairs, so |{g : g² = 1}| is even, and removing the identity leaves an odd number. -/
theorem alg_odd_card_order_two_of_even_card (G : Type*) [Group G] [Finite G] (h : Even (Nat.card G)) : Odd (Nat.card {g : G // orderOf g = 2}) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : Function.End G := fun g => g⁻¹
  have hf : f ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    funext g
    exact inv_inv g
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hf
  have hset : Function.fixedPoints f = insert 1 {g : G | orderOf g = 2} := by
    ext g
    simp only [Function.mem_fixedPoints, Function.IsFixedPt, Set.mem_insert_iff, Set.mem_setOf_eq]
    show g⁻¹ = g ↔ _
    rw [orderOf_eq_prime_iff, inv_eq_iff_mul_eq_one, pow_two]
    by_cases hg : g = 1
    · simp [hg]
    · simp [hg]
  have hcard : Nat.card (Function.fixedPoints f) = Nat.card {g : G // orderOf g = 2} + 1 := by
    rw [hset]
    have h1 : (1 : G) ∉ {g : G | orderOf g = 2} := by simp
    have := Set.ncard_insert_of_notMem h1 (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at this
    exact this
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard] at hmod
  have h2 : Nat.card G % 2 = 0 := Nat.even_iff.mp h
  unfold Nat.ModEq at hmod
  rw [Nat.odd_iff]
  omega
end

-- forge:entry lin_commutator_ne_one kind=proved origin=conjecture
section
/- A commutator of real square matrices of positive size is never the identity — take traces: tr(AB − BA) = 0 by trace_mul_comm while tr I = n + 1 ≠ 0. -/
theorem lin_commutator_ne_one (n : ℕ) (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : A * B - B * A ≠ 1 := by
  intro h
  have h1 := congrArg Matrix.trace h
  rw [Matrix.trace_sub, Matrix.trace_mul_comm A B, sub_self, Matrix.trace_one] at h1
  simp at h1
  have : (0:ℝ) < (n:ℝ) + 1 := by positivity
  linarith
end

-- forge:entry comb_card_even_card_powerset kind=proved origin=conjecture
section
/- A nonempty (n+1)-set has exactly 2^n subsets of even size — toggling membership of a fixed element is an involution of the powerset swapping even-size and odd-size subsets; alternatively use Finset.sum_powerset_neg_one_pow_card or Nat.sum_range_choose with the alternating sum. -/
theorem comb_card_even_card_powerset (n : ℕ) : ((Finset.range (n + 1)).powerset.filter (fun s => Even s.card)).card = 2 ^ n := by
  have hsum : ∑ m ∈ (Finset.range (n + 1)).powerset, (-1 : ℤ) ^ m.card = 0 := by
    rw [Finset.sum_powerset_neg_one_pow_card]
    simp
  have htot := Finset.card_filter_add_card_filter_not (s := (Finset.range (n + 1)).powerset) (fun s => Even s.card)
  rw [Finset.card_powerset, Finset.card_range] at htot
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun s => Even s.card)] at hsum
  have h1 : ∑ m ∈ (Finset.range (n + 1)).powerset.filter (fun s => Even s.card), (-1 : ℤ) ^ m.card
      = (((Finset.range (n + 1)).powerset.filter (fun s => Even s.card)).card : ℤ) := by
    rw [Finset.sum_congr rfl (fun m hm => (Finset.mem_filter.1 hm).2.neg_one_pow)]
    simp
  have h2 : ∑ m ∈ (Finset.range (n + 1)).powerset.filter (fun s => ¬ Even s.card), (-1 : ℤ) ^ m.card
      = -(((Finset.range (n + 1)).powerset.filter (fun s => ¬ Even s.card)).card : ℤ) := by
    rw [Finset.sum_congr rfl (fun m hm => (Nat.not_even_iff_odd.1 (Finset.mem_filter.1 hm).2).neg_one_pow)]
    simp
  rw [h1, h2] at hsum
  have h3 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
  omega
end

-- forge:entry ana_sin_ge_cubic_of_nonneg kind=proved origin=conjecture
section
/- sin x ≥ x - x^3/6 for every x ≥ 0 (Mathlib only has it for x ≤ 1) — differentiate twice: the derivative cos x - 1 + x^2/2 is nonnegative by Real.one_sub_sq_div_two_le_cos, so the difference is monotone from value 0 at 0. -/
theorem ana_sin_ge_cubic_of_nonneg (x : ℝ) (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x := by
  have hk : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Real.sin y - y + y ^ 3 / 6)
      (Real.cos y - 1 + y ^ 2 / 2) y := by
    intro y
    have := ((Real.hasDerivAt_sin y).sub (hasDerivAt_id' y)).add
      ((hasDerivAt_pow 3 y).div_const 6)
    convert! this using 1
    norm_num
    ring
  have hmono : Monotone (fun y : ℝ => Real.sin y - y + y ^ 3 / 6) := by
    apply monotone_of_deriv_nonneg (fun y => (hk y).differentiableAt)
    intro y
    rw [(hk y).deriv]
    linarith [Real.one_sub_sq_div_two_le_cos (x := y)]
  have := hmono hx
  simp at this
  linarith
end

-- forge:entry r3_wolstenholme_harmonic_s1h1 kind=proved origin=decomposition
section
/- r3_wolstenholme_harmonic 的证明骨架中第 1 个空洞 -/
theorem r3_wolstenholme_harmonic_s1h1_aux1 (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : k ∈ Finset.Icc 1 (p - 1)) :
    ∃ m c : ℕ, p = k + m ∧ 0 < k ∧ 0 < m ∧ (p - 1).factorial = k * m * c := by
  rw [Finset.mem_Icc] at hk
  have hp2 := hp.two_le
  obtain ⟨m, hm⟩ : ∃ m, p = k + m := ⟨p - k, by omega⟩
  have hkN : k ∣ (p - 1).factorial := Nat.dvd_factorial (by omega) (by omega)
  have hmN : m ∣ (p - 1).factorial := Nat.dvd_factorial (by omega) (by omega)
  have hkp : Nat.Coprime k p :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)))
  have cop : Nat.Coprime k m := by
    rw [hm] at hkp
    exact Nat.coprime_self_add_right.mp hkp
  obtain ⟨c, hc⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd cop hkN hmN
  exact ⟨m, c, hm, by omega, by omega, hc⟩

theorem r3_wolstenholme_harmonic_s1h1 : ∀ (p : ℕ), Nat.Prime p → 5 ≤ p → ∀ k ∈ Finset.Icc 1 (p - 1), (p - 1).factorial / k + (p - 1).factorial / (p - k) = p * ((p - 1).factorial / (k * (p - k))) := by
  intro p hp h5 k hk
  obtain ⟨m, c, hm, hk0, hm0, hc⟩ := r3_wolstenholme_harmonic_s1h1_aux1 p hp k hk
  have hpk : p - k = m := by omega
  have e1 : k * m * c / k = m * c := by rw [mul_assoc]; exact Nat.mul_div_cancel_left _ hk0
  have e2 : k * m * c / m = k * c := by rw [mul_comm k m, mul_assoc]; exact Nat.mul_div_cancel_left _ hm0
  have e3 : k * m * c / (k * m) = c := Nat.mul_div_cancel_left _ (Nat.mul_pos hk0 hm0)
  rw [hpk, hc, e1, e2, e3, hm]; ring
end

-- forge:entry alg_card_eq_two_of_two_conj_classes kind=proved origin=conjecture
section
/- A finite group with exactly two conjugacy classes has order 2 — the classes are {1} and G \ {1}, whose size |G| - 1 divides |G| by orbit-stabilizer, forcing |G| = 2. -/
theorem alg_card_eq_two_of_two_conj_classes (G : Type*) [Group G] [Finite G] (h : Nat.card (ConjClasses G) = 2) : Nat.card G = 2 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (ConjClasses.mk (1 : G))).mp h
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective y
  have hcar : (ConjClasses.mk g).carrier = ({1} : Set G)ᶜ := by
    ext x
    rw [ConjClasses.mem_carrier_iff_mk_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro hx rfl
      exact hy hx.symm
    · intro hx
      apply huniq
      intro hx1
      rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left] at hx1
      exact hx hx1
  have hc := ConjClasses.card_carrier g
  have hdvd : Fintype.card (MulAction.stabilizer (ConjAct G) g) ∣ Fintype.card G := by
    have := Subgroup.card_subgroup_dvd_card (MulAction.stabilizer (ConjAct G) g)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this
    exact this
  have hn : Fintype.card (ConjClasses.mk g).carrier + 1 = Nat.card G := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hcar]
    have := Set.ncard_add_ncard_compl ({1} : Set G)
    rw [Set.ncard_singleton] at this
    omega
  rw [Nat.card_eq_fintype_card] at hn ⊢
  have h1 : Fintype.card (ConjClasses.mk g).carrier ∣ Fintype.card G := by
    rw [hc]; exact Nat.div_dvd_of_dvd hdvd
  have h2 : Fintype.card (ConjClasses.mk g).carrier ∣ 1 := by
    have := (Nat.dvd_add_right (dvd_refl (Fintype.card (ConjClasses.mk g).carrier))).mp (hn ▸ h1)
    exact this
  have h3 := Nat.dvd_one.mp h2
  omega
end

-- forge:entry r3_wolstenholme_harmonic_s1h2 kind=proved origin=decomposition
section
/- r3_wolstenholme_harmonic 的证明骨架中第 2 个空洞 -/
theorem r3_wolstenholme_harmonic_s1h2 : ∀ (p : ℕ), Nat.Prime p → 5 ≤ p → ∑ k ∈ Finset.Icc 1 (p - 1), (p - 1).factorial / (p - k) = ∑ k ∈ Finset.Icc 1 (p - 1), (p - 1).factorial / k := by
  intro p hp h5
  refine Finset.sum_nbij' (fun k => p - k) (fun k => p - k) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; rfl
end

-- forge:entry lin_nilpotent_det_zero kind=proved origin=conjecture
section
/- A nilpotent real matrix of positive size has determinant 0 — det(A)^k = det(A^k) = det 0 = 0 (size positive), and ℝ has no nilpotents. -/
theorem lin_nilpotent_det_zero (n k : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (h : A ^ k = 0) : Matrix.det A = 0 := by
  have h1 : Matrix.det A ^ k = 0 := by
    rw [← Matrix.det_pow, h, Matrix.det_zero]
  exact pow_eq_zero_iff (M₀ := ℝ) (by rintro rfl; simp at h1) |>.mp h1
end

-- forge:entry comb_card_surjective_bool kind=proved origin=conjecture
section
/- The number of surjections from an n-set onto a 2-set is 2^n - 2 (truncated subtraction covers n = 0) — a function to Bool is non-surjective iff it is one of the two constant functions (for n ≥ 1), count the complement. -/
theorem comb_card_surjective_bool (n : ℕ) : Fintype.card {f : Fin n → Bool // Function.Surjective f} = 2 ^ n - 2 := by
  classical
  rcases n with _ | n
  · show _ = 0
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨f, hf⟩ => ?_⟩
    obtain ⟨i, _⟩ := hf true
    exact i.elim0
  · rw [Fintype.card_of_subtype ((Finset.univ.erase (fun _ : Fin (n + 1) => true)).erase (fun _ => false))]
    · rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      · simp
        omega
      · rw [Finset.mem_erase]
        refine ⟨fun hc => ?_, Finset.mem_univ _⟩
        have := congrFun hc 0
        simp at this
    · intro f
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · rintro ⟨hF, hT⟩ b
        have h1 : ∃ i, f i = false := by
          by_contra hc
          push_neg at hc
          exact hT (funext fun i => by simpa using hc i)
        have h2 : ∃ i, f i = true := by
          by_contra hc
          push_neg at hc
          exact hF (funext fun i => by simpa using hc i)
        cases b
        · exact h1
        · exact h2
      · intro hs
        refine ⟨?_, ?_⟩
        · rintro rfl
          obtain ⟨i, hi⟩ := hs true
          simp at hi
        · rintro rfl
          obtain ⟨i, hi⟩ := hs false
          simp at hi
end

-- forge:entry lin_cayley_hamilton_two kind=proved origin=conjecture
section
/- Cayley–Hamilton for 2×2 matrices over a commutative ring: A² − (tr A)A + (det A)I = 0 — entrywise check after expanding mul, trace and det on Fin 2, then ring. -/
theorem lin_cayley_hamilton_two (R : Type) [CommRing R] (A : Matrix (Fin 2) (Fin 2) R) : A * A - Matrix.trace A • A + Matrix.det A • (1 : Matrix (Fin 2) (Fin 2) R) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring
end

-- forge:entry r3_wolstenholme_harmonic_s1h4 kind=proved origin=decomposition
section
/- r3_wolstenholme_harmonic 的证明骨架中第 4 个空洞 -/
theorem r3_wolstenholme_harmonic_s1h4 : ∀ (p : ℕ), Nat.Prime p → 5 ≤ p → ∑ k ∈ Finset.Icc 1 (p - 1), (↑k : ZMod p)⁻¹ ^ 2 = 0 := by
  intro p hp h5
  haveI := Fact.mk hp
  have h0 : ∑ x : ZMod p, x ^ 2 = 0 :=
    FiniteField.sum_pow_lt_card_sub_one (ZMod p) 2 (by rw [ZMod.card]; omega)
  have h1 : ∑ x : ZMod p, (x⁻¹) ^ 2 = 0 := by
    rw [← h0]; exact Equiv.sum_comp (Equiv.inv (ZMod p)) (fun x => x ^ 2)
  have h2 : ∑ k ∈ Finset.range p, ((k : ZMod p))⁻¹ ^ 2 = ∑ x : ZMod p, (x⁻¹) ^ 2 := by
    refine Finset.sum_nbij' (fun k => (k : ZMod p)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
    · intro a _; exact Finset.mem_univ _
    · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt x)
    · intro a ha; exact ZMod.val_natCast_of_lt (Finset.mem_range.mp ha)
    · intro x _; exact ZMod.natCast_zmod_val x
    · intro a _; rfl
  rw [← h1, ← h2]
  apply Finset.sum_subset
  · intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
  · intro k hk hk'
    rw [Finset.mem_range] at hk; rw [Finset.mem_Icc] at hk'
    have : k = 0 := by omega
    subst this; simp
end

-- forge:entry lin_skew_odd_det_zero kind=proved origin=conjecture
section
/- A real skew-symmetric matrix of odd size is singular — det A = det Aᵀ = det(−A) = (−1)^(2n+1) det A = −det A, so 2 det A = 0. -/
theorem lin_skew_odd_det_zero (n : ℕ) (A : Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1)) ℝ) (h : A.transpose = -A) : Matrix.det A = 0 := by
  have h1 := Matrix.det_transpose A
  rw [h, Matrix.det_neg, Fintype.card_fin, pow_succ, pow_mul] at h1
  norm_num at h1
  linarith
end

-- forge:entry alg_card_prime_of_subgroups_trivial kind=proved origin=conjecture
section
/- A group whose only subgroups are ⊥ and ⊤ is trivial or (finite) of prime order — any g ≠ 1 generates G so G is cyclic; ℤ has proper subgroups so G is finite, and a cyclic group of composite order has a proper subgroup. -/
theorem alg_card_prime_of_subgroups_trivial (G : Type*) [Group G] (h : ∀ H : Subgroup G, H = ⊥ ∨ H = ⊤) : Nat.card G = 1 ∨ (Nat.card G).Prime := by
  by_cases hs : ∀ x : G, x = 1
  · left
    haveI : Subsingleton G := ⟨fun a b => (hs a).trans (hs b).symm⟩
    exact Nat.card_unique
  right
  push_neg at hs
  obtain ⟨g, hg⟩ := hs
  have htop : Subgroup.zpowers g = ⊤ := by
    rcases h (Subgroup.zpowers g) with h1 | h1
    · exact absurd (Subgroup.zpowers_eq_bot.mp h1) hg
    · exact h1
  have hmem : ∀ x : G, ∃ k : ℤ, g ^ k = x := fun x =>
    Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top x)
  have hcomm : ∀ a b : G, a * b = b * a := by
    intro a b
    obtain ⟨m, rfl⟩ := hmem a
    obtain ⟨n, rfl⟩ := hmem b
    exact ((Commute.refl g).zpow_zpow m n).eq
  have hfo : IsOfFinOrder g := by
    rw [isOfFinOrder_iff_zpow_eq_one]
    rcases h (Subgroup.zpowers (g ^ 2)) with h1 | h1
    · refine ⟨2, by norm_num, ?_⟩
      have := Subgroup.zpowers_eq_bot.mp h1
      exact_mod_cast this
    · have : g ∈ Subgroup.zpowers (g ^ 2) := h1 ▸ Subgroup.mem_top g
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp this
      refine ⟨2 * k - 1, by omega, ?_⟩
      have hk' : g ^ (2 * k) = g := by
        rw [zpow_mul]; exact_mod_cast hk
      rw [zpow_sub, hk', zpow_one, mul_inv_cancel]
  haveI : Finite G := by
    have hf : (Set.univ : Set G).Finite := by
      have := hfo.finite_zpowers
      rw [htop] at this
      simpa using this
    exact Set.finite_univ_iff.mp hf
  letI : CommGroup G := { (inferInstance : Group G) with mul_comm := hcomm }
  haveI : IsSimpleGroup G :=
    { exists_pair_ne := ⟨g, 1, hg⟩, eq_bot_or_eq_top_of_normal := fun H _ => h H }
  exact IsSimpleGroup.prime_card
end

end Mathlib2
