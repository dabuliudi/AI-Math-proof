/- Mathlib2 分片 11（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0010
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry lin_idempotent_rank_complement kind=proved origin=conjecture
section
/- For an idempotent matrix, rank A + rank(I − A) = n — ≤ from A(I − A) = 0 (Matrix.rank_add_rank_le_card_of_mul_eq_zero), ≥ from subadditivity of rank applied to A + (I − A) = I. -/
theorem lin_idempotent_rank_complement_aux1 (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (h : A * A = A) : Matrix.trace A = (Matrix.rank A : ℝ) := by
  have hid : IsIdempotentElem (Matrix.toLin' A) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, h]
  have hp := LinearMap.IsIdempotentElem.isProj_range _ hid
  have := hp.trace
  rw [Matrix.trace_toLin'_eq] at this
  rw [this, Matrix.rank, Matrix.toLin'_apply']

theorem lin_idempotent_rank_complement (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (h : A * A = A) : Matrix.rank A + Matrix.rank (1 - A) = n := by
  have h1 := lin_idempotent_rank_complement_aux1 n A h
  have hA : IsIdempotentElem A := h
  have h2 := lin_idempotent_rank_complement_aux1 n (1 - A) hA.one_sub.eq
  rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, h1] at h2
  have : ((Matrix.rank A + Matrix.rank (1 - A) : ℕ) : ℝ) = (n : ℝ) := by
    push_cast
    linarith
  exact_mod_cast this
end

-- forge:entry lin_nilpotent_pow_card kind=proved origin=conjecture
section
/- A nilpotent n×n real matrix satisfies Aⁿ = 0 — its characteristic polynomial is Xⁿ (nilpotent over a domain), then Cayley–Hamilton (Matrix.aeval_self_charpoly). -/
theorem lin_nilpotent_pow_card (n k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (h : A ^ k = 0) : A ^ n = 0 := by
  have hA : IsNilpotent A := ⟨k, h⟩
  have hc := IsNilpotent.charpoly_eq_X_pow_finrank ((Matrix.isNilpotent_toLin'_iff A).mpr hA)
  rw [Matrix.charpoly_toLin'] at hc
  have he := Matrix.aeval_self_charpoly A
  rw [hc] at he
  simpa using he
end

-- forge:entry comb_not_acyclic_of_two_le_degree kind=proved origin=conjecture
section
/- A nonempty finite graph with minimum degree ≥ 2 contains a cycle — take a longest path; its end vertex has a second neighbour which must lie on the path, closing a cycle. Alternatively count: an acyclic graph has fewer than n edges while the handshake lemma gives ≥ n. -/
theorem comb_not_acyclic_of_two_le_degree (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (h : ∀ v : V, 2 ≤ G.degree v) : ¬ G.IsAcyclic := by
  intro hac
  obtain ⟨v0⟩ := ‹Nonempty V›
  have ht := hac.isTree_connectedComponent (G.connectedComponentMk v0)
  generalize G.connectedComponentMk v0 = c at ht
  haveI : Fintype ↥c := Fintype.ofFinite _
  haveI : DecidableRel c.toSimpleGraph.Adj := Classical.decRel _
  have key : ∀ x : ↥c, 2 ≤ c.toSimpleGraph.degree x := by
    rintro ⟨x, hx⟩
    have hx2 := h x
    unfold SimpleGraph.degree at hx2 ⊢
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hx2
    rw [SimpleGraph.mem_neighborFinset] at ha hb
    have ha' : a ∈ c := c.mem_supp_of_adj_mem_supp hx ha
    have hb' : b ∈ c := c.mem_supp_of_adj_mem_supp hx hb
    refine Finset.one_lt_card.mpr ⟨⟨a, ha'⟩, ?_, ⟨b, hb'⟩, ?_, ?_⟩
    · rw [SimpleGraph.mem_neighborFinset]; exact (c.toSimpleGraph_adj hx ha').mpr ha
    · rw [SimpleGraph.mem_neighborFinset]; exact (c.toSimpleGraph_adj hx hb').mpr hb
    · intro heq; exact hab (congrArg Subtype.val heq)
  haveI : Nontrivial ↥c := by
    obtain ⟨x⟩ := ht.isConnected.nonempty
    have hx2 := key x
    unfold SimpleGraph.degree at hx2
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hx2
    exact ⟨⟨a, b, hab⟩⟩
  obtain ⟨v, hv⟩ := ht.exists_vert_degree_one_of_nontrivial
  have := key v
  omega
end

-- forge:entry alg_card_sq_eq_one_zmod_two_pow kind=proved origin=conjecture
section
/- For k ≥ 3 the congruence x² = 1 mod 2^k has exactly four solutions (±1 and 2^(k-1) ± 1) — 2^k | (x-1)(x+1) with gcd(x-1, x+1) = 2 forces 2^(k-1) | x - 1 or 2^(k-1) | x + 1. -/
lemma alg_card_sq_eq_one_zmod_two_pow_aux1 (n : ℕ) (a : ℤ) (h : (2 : ℤ) ^ (n + 2) ∣ a ^ 2 - 1) :
    ∃ c : ℤ, a = 2 ^ (n + 1) * c + 1 ∨ a = 2 ^ (n + 1) * c - 1 := by
  obtain ⟨b, hb | hb⟩ := Int.even_or_odd' a
  · exfalso
    have h2 : (2 : ℤ) ∣ a ^ 2 - 1 := dvd_trans (dvd_pow_self 2 (by omega)) h
    obtain ⟨e, he⟩ := h2
    rw [hb] at he
    have : (2 * b) ^ 2 - 1 = 2 * (2 * (b * b)) - 1 := by ring
    rw [this] at he
    generalize b * b = y at he
    omega
  · have h4 : (2 : ℤ) ^ (n + 2) = 4 * 2 ^ n := by ring
    have h5 : a ^ 2 - 1 = 4 * (b * (b + 1)) := by rw [hb]; ring
    rw [h4, h5] at h
    have hd : (2 : ℤ) ^ n ∣ b * (b + 1) := (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp h
    obtain ⟨c, hc | hc⟩ := Int.even_or_odd' b
    · have cop : IsCoprime ((2 : ℤ) ^ n) (b + 1) := IsCoprime.pow_left ⟨-c, 1, by rw [hc]; ring⟩
      obtain ⟨d, hd'⟩ := cop.dvd_of_dvd_mul_right hd
      exact ⟨d, Or.inl (by linear_combination hb + 2 * hd')⟩
    · have cop : IsCoprime ((2 : ℤ) ^ n) b := IsCoprime.pow_left ⟨-c, 1, by rw [hc]; ring⟩
      obtain ⟨d, hd'⟩ := cop.dvd_of_dvd_mul_left hd
      exact ⟨d, Or.inr (by linear_combination hb + 2 * hd')⟩

theorem alg_card_sq_eq_one_zmod_two_pow (k : ℕ) (hk : 3 ≤ k) : Nat.card {x : ZMod (2 ^ k) // x ^ 2 = 1} = 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  classical
  have hP : 4 ≤ 2 ^ (m + 2) := by
    have h1 := Nat.one_le_two_pow (n := m)
    have h2 : 2 ^ (m + 2) = 4 * 2 ^ m := by ring
    omega
  have hN : 2 ^ (m + 3) = 2 * 2 ^ (m + 2) := by ring
  have hinj : ∀ a b : ℕ, a < 2 ^ (m + 3) → b < 2 ^ (m + 3) →
      ((a : ℕ) : ZMod (2 ^ (m + 3))) = b → a = b := by
    intro a b ha hb h
    have := (ZMod.natCast_eq_natCast_iff' a b (2 ^ (m + 3))).mp h
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  have ht2 : (2 : ZMod (2 ^ (m + 3))) ^ (m + 2) * 2 = 0 := by
    have := ZMod.natCast_self (2 ^ (m + 3))
    push_cast at this
    rw [← pow_succ]; exact this
  have htt : (2 : ZMod (2 ^ (m + 3))) ^ (m + 2) * 2 ^ (m + 2) = 0 := by
    have : (2 : ZMod (2 ^ (m + 3))) ^ (m + 2) * 2 ^ (m + 2) = (2 ^ (m + 2) * 2) * 2 ^ (m + 1) := by
      ring
    rw [this, ht2, zero_mul]
  have char : ∀ x : ZMod (2 ^ (m + 3)), x ^ 2 = 1 ↔
      x ∈ ({1, -1, 2 ^ (m + 2) + 1, 2 ^ (m + 2) - 1} : Finset (ZMod (2 ^ (m + 3)))) := by
    intro x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
      have h0 : ((a ^ 2 - 1 : ℤ) : ZMod (2 ^ (m + 3))) = 0 := by push_cast; rw [h]; ring
      have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
      push_cast at hd
      obtain ⟨c, hc | hc⟩ := alg_card_sq_eq_one_zmod_two_pow_aux1 (m + 1) a hd
      · obtain ⟨d, hd' | hd'⟩ := Int.even_or_odd' c
        · left; rw [hc, hd']; push_cast
          linear_combination (d : ZMod (2 ^ (m + 3))) * ht2
        · right; right; left; rw [hc, hd']; push_cast
          linear_combination (d : ZMod (2 ^ (m + 3))) * ht2
      · obtain ⟨d, hd' | hd'⟩ := Int.even_or_odd' c
        · right; left; rw [hc, hd']; push_cast
          linear_combination (d : ZMod (2 ^ (m + 3))) * ht2
        · right; right; right; rw [hc, hd']; push_cast
          linear_combination (d : ZMod (2 ^ (m + 3))) * ht2
    · rintro (rfl | rfl | rfl | rfl)
      · ring
      · ring
      · linear_combination htt + ht2
      · linear_combination htt - ht2
  have h12 : (1 : ZMod (2 ^ (m + 3))) ≠ -1 := by
    intro h
    have := hinj 2 0 (by omega) (by omega) (by push_cast; linear_combination h)
    omega
  have h13 : (1 : ZMod (2 ^ (m + 3))) ≠ 2 ^ (m + 2) + 1 := by
    intro h
    have := hinj (2 ^ (m + 2)) 0 (by omega) (by omega) (by push_cast; linear_combination -h)
    omega
  have h14 : (1 : ZMod (2 ^ (m + 3))) ≠ 2 ^ (m + 2) - 1 := by
    intro h
    have := hinj (2 ^ (m + 2)) 2 (by omega) (by omega) (by push_cast; linear_combination -h)
    omega
  have h23 : (-1 : ZMod (2 ^ (m + 3))) ≠ 2 ^ (m + 2) + 1 := by
    intro h
    have := hinj (2 ^ (m + 2) + 2) 0 (by omega) (by omega) (by push_cast; linear_combination -h)
    omega
  have h24 : (-1 : ZMod (2 ^ (m + 3))) ≠ 2 ^ (m + 2) - 1 := by
    intro h
    have := hinj (2 ^ (m + 2)) 0 (by omega) (by omega) (by push_cast; linear_combination -h)
    omega
  have h34 : (2 ^ (m + 2) + 1 : ZMod (2 ^ (m + 3))) ≠ 2 ^ (m + 2) - 1 := by
    intro h
    have := hinj 2 0 (by omega) (by omega) (by push_cast; linear_combination h)
    omega
  have e : {x : ZMod (2 ^ (m + 3)) | x ^ 2 = 1}
      = ↑({1, -1, 2 ^ (m + 2) + 1, 2 ^ (m + 2) - 1} : Finset (ZMod (2 ^ (m + 3)))) :=
    Set.ext fun x => (char x).trans Finset.mem_coe.symm
  calc Nat.card {x : ZMod (2 ^ (m + 3)) // x ^ 2 = 1}
      = Set.ncard {x : ZMod (2 ^ (m + 3)) | x ^ 2 = 1} := Nat.card_coe_set_eq _
    _ = ({1, -1, 2 ^ (m + 2) + 1, 2 ^ (m + 2) - 1} : Finset (ZMod (2 ^ (m + 3)))).card := by
        rw [e, Set.ncard_coe_finset]
    _ = 4 := by
        rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h12, h13, h14⟩),
          Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h23, h24⟩),
          Finset.card_pair h34]
end

-- forge:entry ana_monotone_additive_linear kind=proved origin=conjecture
section
/- A monotone additive function on ℝ is linear — f(q) = q f(1) on rationals; for real x squeeze between rationals p < x < q: p f(1) ≤ f(x) ≤ q f(1) (f(1) ≥ 0 by monotonicity), and let p, q → x. -/
theorem ana_monotone_additive_linear (f : ℝ → ℝ) (hf : Monotone f) (hadd : ∀ x y : ℝ, f (x + y) = f x + f y) (x : ℝ) : f x = f 1 * x := by
  have h0 : f 0 = 0 := by
    have := hadd 0 0
    simp at this
    exact this
  have hq : ∀ q : ℚ, f q = f 1 * q := by
    intro q
    have h := map_rat_smul (AddMonoidHom.mk' f hadd) q (1:ℝ)
    simp only [AddMonoidHom.mk'_apply, Rat.smul_def, mul_one] at h
    rw [h, mul_comm]
  have h1 : 0 ≤ f 1 := by
    have := hf (zero_le_one : (0:ℝ) ≤ 1)
    rw [h0] at this
    exact this
  rcases h1.eq_or_lt with h1 | h1
  · obtain ⟨p, hp⟩ := exists_rat_lt x
    obtain ⟨q, hq'⟩ := exists_rat_gt x
    have a := hf hp.le
    have b := hf hq'.le
    rw [hq, ← h1] at a b
    rw [← h1]
    linarith
  · rcases lt_trichotomy (f x) (f 1 * x) with h | h | h
    · exfalso
      have h2 : f x / f 1 < x := by
        rw [div_lt_iff₀ h1]; linarith
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h2
      have a := hf hq2.le
      rw [hq] at a
      rw [div_lt_iff₀ h1] at hq1
      linarith
    · exact h
    · exfalso
      have h2 : x < f x / f 1 := by
        rw [lt_div_iff₀ h1]; linarith
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h2
      have a := hf hq1.le
      rw [hq] at a
      rw [lt_div_iff₀ h1] at hq2
      linarith
end

-- forge:entry ana_convex_bddAbove_const kind=proved origin=conjecture
section
/- A convex function on ℝ that is bounded above is constant — if f x < f y, write y as a convex combination of x and the far point z_t = x + t(y - x), t > 1: f y ≤ (1 - 1/t) f x + (1/t) f z_t gives f z_t ≥ f x + t (f y - f x) → ∞, contradicting the bound; symmetric for f y < f x. -/
theorem ana_convex_bddAbove_const_aux1 (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) (M : ℝ) (hM : ∀ x : ℝ, f x ≤ M) (x y : ℝ) : f y ≤ f x := by
  by_contra hlt
  push_neg at hlt
  have hd : 0 < f y - f x := by linarith
  have hD : 0 < M - f x + (f y - f x) := by linarith [hM x]
  have hs0 : 0 ≤ (f y - f x) / (M - f x + (f y - f x)) := (div_pos hd hD).le
  have hs1 : (f y - f x) / (M - f x + (f y - f x)) ≤ 1 := by
    rw [div_le_one hD]; linarith [hM x]
  have hsD : (f y - f x) / (M - f x + (f y - f x)) * (M - f x + (f y - f x)) = f y - f x :=
    div_mul_cancel₀ _ hD.ne'
  have hst : (f y - f x) / (M - f x + (f y - f x)) * ((M - f x + (f y - f x)) / (f y - f x)) = 1 := by
    field_simp
  have key := hf.2 (Set.mem_univ x) (Set.mem_univ (x + (M - f x + (f y - f x)) / (f y - f x) * (y - x)))
    (sub_nonneg.mpr hs1) hs0 (by ring)
  simp only [smul_eq_mul] at key
  have harg : (1 - (f y - f x) / (M - f x + (f y - f x))) * x + (f y - f x) / (M - f x + (f y - f x)) * (x + (M - f x + (f y - f x)) / (f y - f x) * (y - x)) = y := by
    linear_combination (y - x) * hst
  rw [harg] at key
  have hz := hM (x + (M - f x + (f y - f x)) / (f y - f x) * (y - x))
  have hspos : 0 < (f y - f x) / (M - f x + (f y - f x)) := div_pos hd hD
  nlinarith [mul_le_mul_of_nonneg_left hz hs0, mul_pos hspos hd]

theorem ana_convex_bddAbove_const (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) (M : ℝ) (hM : ∀ x : ℝ, f x ≤ M) (x y : ℝ) : f x = f y :=
  le_antisymm (ana_convex_bddAbove_const_aux1 f hf M hM y x) (ana_convex_bddAbove_const_aux1 f hf M hM x y)
end

-- forge:entry comb_colorable_of_degree_le kind=proved origin=conjecture
section
/- Greedy bound χ(G) ≤ Δ(G) + 1 — induction on the number of vertices: remove a vertex, colour the rest with d+1 colours, and give the removed vertex a colour not used on its ≤ d neighbours. -/
theorem comb_colorable_of_degree_le (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (h : ∀ v : V, G.degree v ≤ d) : G.Colorable (d + 1) := by
  have key : ∀ S : Finset V, ∃ c : V → Fin (d + 1), ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨fun _ => 0, by simp⟩
    | insert a S ha ih =>
      obtain ⟨c, hc⟩ := ih
      have hcard : ((G.neighborFinset a).image c).card < (Finset.univ : Finset (Fin (d + 1))).card := by
        have h1 := Finset.card_image_le (s := G.neighborFinset a) (f := c)
        have h2 := G.card_neighborFinset_eq_degree a
        have h3 := h a
        simp only [Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
      have hk' : ∀ v, G.Adj a v → k ≠ c v := by
        intro v hv hkv
        apply hk
        rw [hkv]
        exact Finset.mem_image_of_mem c ((G.mem_neighborFinset a v).mpr hv)
      refine ⟨Function.update c a k, ?_⟩
      intro u hu v hv huv
      rw [Finset.mem_insert] at hu hv
      by_cases hua : u = a
      · subst hua
        have hvu : v ≠ u := fun e => G.loopless u (e ▸ huv)
        rw [Function.update_self, Function.update_of_ne hvu]
        exact hk' v huv
      · by_cases hva : v = a
        · subst hva
          rw [Function.update_self, Function.update_of_ne hua]
          exact (hk' u huv.symm).symm
        · rw [Function.update_of_ne hua, Function.update_of_ne hva]
          exact hc u (hu.resolve_left hua) v (hv.resolve_left hva) huv
  obtain ⟨c, hc⟩ := key Finset.univ
  exact ⟨SimpleGraph.Coloring.mk c (fun {u v} huv => hc u (Finset.mem_univ _) v (Finset.mem_univ _) huv)⟩
end

-- forge:entry alg_card_le_two_of_mulAut_trivial kind=proved origin=conjecture
section
/- A finite group with trivial automorphism group has at most 2 elements — inner automorphisms trivial gives G abelian; inversion trivial gives exponent 2; so G is an F_2-vector space, and if its dimension is ≥ 2 swapping two basis vectors is a nontrivial automorphism. -/
theorem alg_card_le_two_of_mulAut_trivial (G : Type*) [Group G] [Finite G] (h : ∀ f : MulAut G, f = 1) : Nat.card G ≤ 2 := by
  classical
  have comm : ∀ x y : G, x * y = y * x := by
    intro x y
    have := congrArg (fun f : MulAut G => f y) (h (MulAut.conj x))
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [this]
  have sq : ∀ x : G, x * x = 1 := by
    intro x
    have := congrArg (fun f : MulAut G => f x) (h
      { toFun := fun g => g⁻¹, invFun := fun g => g⁻¹, left_inv := fun g => inv_inv g,
        right_inv := fun g => inv_inv g, map_mul' := fun g k => by rw [mul_inv_rev, comm] })
    have hx : x⁻¹ = x := this
    calc x * x = x⁻¹ * x := by rw [hx]
      _ = 1 := inv_mul_cancel x
  have inv_eq : ∀ g : G, g⁻¹ = g := fun g => inv_eq_of_mul_eq_one_left (sq g)
  by_contra hcard
  push_neg at hcard
  obtain ⟨a, ha⟩ : ∃ a : G, a ≠ 1 := by
    by_contra hall
    push_neg at hall
    haveI : Subsingleton G := ⟨fun x y => by rw [hall x, hall y]⟩
    have := Finite.card_le_one_iff_subsingleton.mpr this
    omega
  obtain ⟨c, hc1, hca⟩ : ∃ c : G, c ≠ 1 ∧ c ≠ a := by
    by_contra hall
    push_neg at hall
    haveI := Fintype.ofFinite G
    have h1 : (Finset.univ : Finset G) ⊆ {1, a} := by
      intro x _
      by_cases hx : x = 1
      · simp [hx]
      · simp [hall x hx]
    have h2 := Finset.card_le_card h1
    have h3 : ({1, a} : Finset G).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h2
    omega
  obtain ⟨H, haH, hmax⟩ : ∃ H : Subgroup G, a ∉ H ∧ ∀ K : Subgroup G, H ≤ K → a ∉ K → K = H := by
    haveI : Finite (Subgroup G) :=
      Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
    obtain ⟨H, -, hH⟩ := Finite.exists_le_maximal (p := fun K : Subgroup G => a ∉ K) (a := ⊥)
      (fun hmem => ha (Subgroup.mem_bot.mp hmem))
    exact ⟨H, hH.1, fun K hHK haK => le_antisymm (hH.2 haK hHK) hHK⟩
  have key : ∀ x, x ∉ H → a * x ∈ H := by
    intro x hx
    let K : Subgroup G :=
      { carrier := {g | g ∈ H ∨ g * x ∈ H}
        mul_mem' := by
          intro g k hg hk
          rcases hg with hg | hg <;> rcases hk with hk | hk
          · exact Or.inl (H.mul_mem hg hk)
          · right; rw [mul_assoc]; exact H.mul_mem hg hk
          · right
            have : g * k * x = (g * x) * k := by rw [mul_assoc, comm k x, ← mul_assoc]
            rw [this]; exact H.mul_mem hg hk
          · left
            have : g * k = (g * x) * (k * x) := by
              rw [mul_assoc g x, ← mul_assoc x k x, comm x k, mul_assoc k x x, sq x, mul_one]
            rw [this]; exact H.mul_mem hg hk
        one_mem' := Or.inl H.one_mem
        inv_mem' := by
          intro g hg
          rw [inv_eq g]; exact hg }
    have hHK : H ≤ K := fun g hg => Or.inl hg
    have hxK : x ∈ K := Or.inr (by rw [sq x]; exact H.one_mem)
    have haK : a ∈ K := by
      by_contra haK
      have := hmax K hHK haK
      rw [this] at hxK
      exact hx hxK
    rcases haK with h1 | h1
    · exact absurd h1 haH
    · exact h1
  obtain ⟨b, hbH, hb1⟩ : ∃ b ∈ H, b ≠ 1 := by
    by_cases hcH : c ∈ H
    · exact ⟨c, hcH, hc1⟩
    · refine ⟨a * c, key c hcH, ?_⟩
      intro h0
      apply hca
      calc c = a * (a * c) := by rw [← mul_assoc, sq a, one_mul]
        _ = a := by rw [h0, mul_one]
  have prod : ∀ x y, x ∉ H → y ∉ H → x * y ∈ H := by
    intro x y hx hy
    have : x * y = (a * x) * (a * y) := by
      rw [comm a x, mul_assoc x a, ← mul_assoc a a y, sq a, one_mul]
    rw [this]; exact H.mul_mem (key x hx) (key y hy)
  obtain ⟨f, hf⟩ : ∃ f : G → G, ∀ x, f x = if x ∈ H then x else x * b := ⟨_, fun _ => rfl⟩
  have fmul : ∀ x y, f (x * y) = f x * f y := by
    intro x y
    by_cases hx : x ∈ H <;> by_cases hy : y ∈ H
    · simp only [hf, if_pos hx, if_pos hy, if_pos (H.mul_mem hx hy)]
    · have : x * y ∉ H := fun hxy => hy ((H.mul_mem_cancel_left hx).mp hxy)
      simp only [hf, if_pos hx, if_neg hy, if_neg this, mul_assoc]
    · have : x * y ∉ H := fun hxy => hx ((H.mul_mem_cancel_right hy).mp hxy)
      simp only [hf, if_neg hx, if_pos hy, if_neg this]
      rw [mul_assoc, mul_assoc, comm y b]
    · simp only [hf, if_neg hx, if_neg hy, if_pos (prod x y hx hy)]
      rw [mul_assoc x b, ← mul_assoc b y b, comm b y, mul_assoc y b b, sq b, mul_one]
  have finv : ∀ x, f (f x) = x := by
    intro x
    by_cases hx : x ∈ H
    · simp only [hf, if_pos hx]
    · have : x * b ∉ H := fun hxb => hx ((H.mul_mem_cancel_right hbH).mp hxb)
      simp only [hf, if_neg hx, if_neg this, mul_assoc, sq b, mul_one]
  have := congrArg (fun φ : MulAut G => φ a) (h ⟨⟨f, f, finv, finv⟩, fmul⟩)
  have hfa : f a = a := this
  rw [hf, if_neg haH] at hfa
  exact hb1 (mul_left_cancel (hfa.trans (mul_one a).symm))
end

-- forge:entry comb_tournament_hamiltonian_path kind=proved origin=conjecture
section
/- Rédei: every tournament (indeed every semicomplete digraph) on n vertices has a directed Hamiltonian path — induction on n: given a path through the first n vertices, insert the new vertex v before the first path vertex that v beats (or at the end if none). -/
theorem comb_tournament_hamiltonian_path_aux1 {α : Type} (r : α → α → Prop) (a : α) (l : List α)
    (hl : ∀ b ∈ l, r a b ∨ r b a) (hc : List.IsChain r l) :
    ∃ l' : List α, l'.Perm (a :: l) ∧ List.IsChain r l' ∧ (∀ x ∈ l'.head?, x = a ∨ x ∈ l.head?) := by
  induction l with
  | nil => exact ⟨[a], List.Perm.refl _, List.isChain_singleton a, by simp⟩
  | cons b t ih =>
    by_cases hab : r a b
    · exact ⟨a :: b :: t, List.Perm.refl _, List.chain'_cons.2 ⟨hab, hc⟩, by simp⟩
    · have hba : r b a := (hl b List.mem_cons_self).resolve_left hab
      have hc2 := List.chain'_cons'.1 hc
      obtain ⟨t', hp, hc', hh⟩ := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) hc2.2
      refine ⟨b :: t', (hp.cons b).trans (List.Perm.swap a b t), List.chain'_cons'.2 ⟨?_, hc'⟩, by simp⟩
      intro y hy
      rcases hh y hy with h1 | h1
      · rw [h1]; exact hba
      · exact hc2.1 y h1

theorem comb_tournament_hamiltonian_path_aux2 {α : Type} (r : α → α → Prop) (l : List α)
    (hnd : l.Nodup) (hl : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b ∨ r b a) :
    ∃ l' : List α, l'.Perm l ∧ List.IsChain r l' := by
  induction l with
  | nil => exact ⟨[], List.Perm.refl _, List.isChain_nil⟩
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨t', hp, hc⟩ := ih hnd.2 (fun x hx y hy => hl x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
    obtain ⟨l', hp', hc', -⟩ := comb_tournament_hamiltonian_path_aux1 r a t' (fun b hb => by
      have hbt : b ∈ t := hp.mem_iff.1 hb
      exact hl a List.mem_cons_self b (List.mem_cons_of_mem _ hbt) (fun e => hnd.1 (e ▸ hbt))) hc
    exact ⟨l', hp'.trans (hp.cons a), hc'⟩

theorem comb_tournament_hamiltonian_path (n : ℕ) (r : Fin n → Fin n → Prop) (h : ∀ i j : Fin n, i ≠ j → r i j ∨ r j i) : ∃ σ : Equiv.Perm (Fin n), ∀ (i : Fin n) (hi : i.val + 1 < n), r (σ i) (σ ⟨i.val + 1, hi⟩) := by
  obtain ⟨l, hp, hc⟩ := comb_tournament_hamiltonian_path_aux2 r (List.finRange n) (List.nodup_finRange n)
    (fun a _ b _ hab => h a b hab)
  have hlen : l.length = n := by rw [hp.length_eq, List.length_finRange]
  have hnd : l.Nodup := hp.nodup_iff.2 (List.nodup_finRange n)
  have hinj : Function.Injective (fun i : Fin n => l[i.val]'(by rw [hlen]; exact i.isLt)) := by
    intro i j hij
    exact Fin.ext (hnd.getElem_inj_iff.1 hij)
  refine ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj), ?_⟩
  intro i hi
  exact (List.isChain_iff_getElem.1 hc) i.val (by rw [hlen]; exact hi)
end

-- forge:entry comb_exists_cut_half_edges kind=proved origin=conjecture
section
/- Every finite graph has a cut containing at least half of its edges — take s maximising the cut size: every vertex then has at least half of its neighbours on the other side (else moving it increases the cut); sum over vertices. Or average over all 2^n subsets. -/
theorem comb_exists_cut_half_edges_aux1 (V : Type) [DecidableEq V] (f : V → V → ℕ)
    (hsym : ∀ u v, f u v = f v u) (hirr : ∀ u, f u u = 0) (S : Finset V) :
    ∃ s : Finset V, s ⊆ S ∧ (∑ u ∈ S, ∑ v ∈ S, f u v) ≤ 4 * ∑ u ∈ s, ∑ v ∈ S \ s, f u v := by
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simp⟩
  | insert a S ha ih =>
    obtain ⟨s, hs, hle⟩ := ih
    have has : a ∉ s := fun h => ha (hs h)
    have hasd : a ∉ S \ s := fun h => ha (Finset.mem_sdiff.1 h).1
    have hsplit : ∑ v ∈ S, f a v = ∑ v ∈ S \ s, f a v + ∑ v ∈ s, f a v := (Finset.sum_sdiff hs).symm
    have hD' : ∑ u ∈ S, f u a = ∑ v ∈ S, f a v := Finset.sum_congr rfl (fun u _ => hsym u a)
    have htot : (∑ u ∈ insert a S, ∑ v ∈ insert a S, f u v)
        = 2 * (∑ v ∈ S, f a v) + ∑ u ∈ S, ∑ v ∈ S, f u v := by
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hirr]
      have : ∑ u ∈ S, ∑ v ∈ insert a S, f u v = ∑ u ∈ S, f u a + ∑ u ∈ S, ∑ v ∈ S, f u v := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun u _ => Finset.sum_insert ha)
      rw [this, hD']; ring
    by_cases hc : ∑ v ∈ S \ s, f a v ≤ ∑ v ∈ s, f a v
    · refine ⟨s, hs.trans (Finset.subset_insert a S), ?_⟩
      have h1 : ∑ u ∈ s, ∑ v ∈ insert a S \ s, f u v
          = ∑ v ∈ s, f a v + ∑ u ∈ s, ∑ v ∈ S \ s, f u v := by
        rw [Finset.insert_sdiff_of_notMem _ has, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun u _ => ?_)
        rw [Finset.sum_insert hasd, hsym u a]
      rw [htot, h1]; omega
    · refine ⟨insert a s, Finset.insert_subset_insert a hs, ?_⟩
      have h1 : ∑ u ∈ insert a s, ∑ v ∈ insert a S \ insert a s, f u v
          = ∑ v ∈ S \ s, f a v + ∑ u ∈ s, ∑ v ∈ S \ s, f u v := by
        have e : insert a S \ insert a s = S \ s := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨h1 | h1, h2⟩
            · exact absurd (Or.inl h1) h2
            · exact ⟨h1, fun h => h2 (Or.inr h)⟩
          · rintro ⟨h1, h2⟩
            refine ⟨Or.inr h1, ?_⟩
            rintro (h | h)
            · exact ha (h ▸ h1)
            · exact h2 h
        rw [e, Finset.sum_insert has]
      rw [htot, h1]; omega

theorem comb_exists_cut_half_edges (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : ∃ s : Finset V, G.edgeFinset.card ≤ 2 * ((s ×ˢ sᶜ).filter (fun p : V × V => G.Adj p.1 p.2)).card := by
  obtain ⟨s, -, hle⟩ := comb_exists_cut_half_edges_aux1 V (fun u v => if G.Adj u v then 1 else 0)
    (fun u v => by simp only [G.adj_comm u v]) (fun u => by simp) Finset.univ
  refine ⟨s, ?_⟩
  have h1 : (∑ u : V, ∑ v : V, (if G.Adj u v then 1 else 0)) = 2 * G.edgeFinset.card := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [← Finset.card_filter, ← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]
  have h2 : ((s ×ˢ sᶜ).filter (fun p : V × V => G.Adj p.1 p.2)).card
      = ∑ u ∈ s, ∑ v ∈ Finset.univ \ s, (if G.Adj u v then 1 else 0) := by
    rw [Finset.card_filter, Finset.sum_product, Finset.compl_eq_univ_sdiff]
  rw [h2]
  rw [h1] at hle
  omega
end

-- forge:entry gen_lin_idempotent_trace_eq_rank_field kind=proved origin=conjecture
section
/- Generalizes Mathlib2.lin_idempotent_trace_eq_rank: ℚ → arbitrary field K (any characteristic; the rank is cast into K), Fin n → arbitrary Fintype. Also subsumes lin_idempotent_rank_complement_aux1 (the ℝ copy). Proof idea: the original proof is field-agnostic: toLin' A is idempotent, LinearMap.IsIdempotentElem.isProj_range + LinearMap.IsProj.trace + Matrix.trace_toLin'_eq. -/
theorem gen_lin_idempotent_trace_eq_rank_field (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (h : A * A = A) : Matrix.trace A = (Matrix.rank A : K) := by
  have hid : IsIdempotentElem (Matrix.toLin' A) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, h]
  have hp := LinearMap.IsIdempotentElem.isProj_range _ hid
  have := hp.trace
  rw [Matrix.trace_toLin'_eq] at this
  rw [this, Matrix.rank, Matrix.toLin'_apply']
end

-- forge:entry gen_lin_idempotent_rank_complement_field kind=proved origin=conjecture
section
/- Generalizes Mathlib2.lin_idempotent_rank_complement: ℝ → arbitrary field K, Fin n → arbitrary Fintype. Proof idea: avoid the trace argument (fails to conclude in positive characteristic); instead range(1-A) = ker A for idempotent A and rank-nullity, or Sylvester (A(1-A)=0 gives ≤) plus rank subadditivity for A + (1-A) = 1 (gives ≥). -/
theorem gen_lin_idempotent_rank_complement_field (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (h : A * A = A) : Matrix.rank A + Matrix.rank (1 - A) = Fintype.card ι := by
  have hle : LinearMap.range (1 - A).mulVecLin = LinearMap.ker A.mulVecLin := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
      rw [mul_sub, mul_one, h, sub_self, Matrix.zero_mulVec]
    · intro v hv
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
      refine ⟨v, ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec, hv, sub_zero]
  have h2 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h2
  have h3 : (1 - A).rank = Module.finrank K (LinearMap.range (1 - A).mulVecLin) := rfl
  have h4 : A.rank = Module.finrank K (LinearMap.range A.mulVecLin) := rfl
  rw [hle] at h3
  omega
end

-- forge:entry alg_perm_eq_mul_two_involutions_s1h1 kind=proved origin=decomposition
section
/- alg_perm_eq_mul_two_involutions 的证明骨架中第 1 个空洞 -/
theorem alg_perm_eq_mul_two_involutions_s1h1 (n : ℕ) (τ : Equiv.Perm (Fin n)) : τ.IsCycle → ∃ (a : Equiv.Perm (Fin n)), a * a = 1 ∧ a * τ * a = τ⁻¹ ∧ ∀ (x : Fin n), (τ : Fin n → Fin n) x = x → (a : Fin n → Fin n) x = x := by
  intro hτ
  classical
  obtain ⟨x, hx, hall⟩ := hτ
  let f : Fin n → Fin n := fun y =>
    if h : τ.SameCycle x y then (τ ^ (-(Classical.choose h))) x else y
  have hf : ∀ i : ℤ, f ((τ ^ i) x) = (τ ^ (-i)) x := by
    intro i
    have h : τ.SameCycle x ((τ ^ i) x) := ⟨i, rfl⟩
    have hk : (τ ^ (Classical.choose h)) x = (τ ^ i) x := Classical.choose_spec h
    simp only [f, dif_pos h]
    generalize Classical.choose h = k at hk
    rw [zpow_neg, zpow_neg, Equiv.Perm.inv_eq_iff_eq]
    have c : τ ^ k * (τ ^ i)⁻¹ = (τ ^ i)⁻¹ * τ ^ k := by group
    calc x = (τ ^ i)⁻¹ ((τ ^ i) x) := by simp
      _ = (τ ^ i)⁻¹ ((τ ^ k) x) := by rw [hk]
      _ = ((τ ^ i)⁻¹ * τ ^ k) x := rfl
      _ = (τ ^ k * (τ ^ i)⁻¹) x := by rw [c]
      _ = (τ ^ k) ((τ ^ i)⁻¹ x) := rfl
  have hfix : ∀ y : Fin n, ¬ τ.SameCycle x y → f y = y := fun y h => by
    simp only [f, dif_neg h]
  have hnot : ∀ y : Fin n, ¬ τ.SameCycle x y → τ y = y := fun y h => by
    by_contra h'
    exact h (hall h')
  have hinv : Function.Involutive f := by
    intro y
    by_cases h : τ.SameCycle x y
    · obtain ⟨i, rfl⟩ := h
      rw [hf, hf, neg_neg]
    · rw [hfix y h, hfix y h]
  refine ⟨hinv.toPerm f, ?_, ?_, ?_⟩
  · refine Equiv.ext fun y => ?_
    show f (f y) = y
    exact hinv y
  · refine Equiv.ext fun y => ?_
    show f (τ (f y)) = τ⁻¹ y
    by_cases h : τ.SameCycle x y
    · obtain ⟨i, rfl⟩ := h
      rw [hf]
      have e1 : τ ((τ ^ (-i)) x) = (τ ^ (-(i - 1))) x := by
        rw [← Equiv.Perm.mul_apply, ← zpow_one_add]
        congr 2
        ring
      rw [e1, hf, neg_neg, ← Equiv.Perm.mul_apply, ← zpow_neg_one, ← zpow_add]
      congr 2
      ring
    · rw [hfix y h, hnot y h, hfix y h]
      exact (Equiv.Perm.inv_eq_iff_eq.2 (hnot y h).symm).symm
  · intro y hy
    show f y = y
    by_cases h : τ.SameCycle x y
    · exfalso
      obtain ⟨i, rfl⟩ := h
      have e : (τ ^ i) (τ x) = (τ ^ i) x := by
        have c : τ ^ i * τ = τ * τ ^ i := by group
        calc (τ ^ i) (τ x) = (τ ^ i * τ) x := rfl
          _ = (τ * τ ^ i) x := by rw [c]
          _ = (τ ^ i) x := hy
      exact hx ((τ ^ i).injective e)
    · exact hfix y h
end

-- forge:entry gen_lin_sylvester_rank_rect kind=proved origin=conjecture
section
/- Generalizes Mathlib2.lin_sylvester_rank: ℝ → arbitrary field K, square Fin n matrices → rectangular matrices A : m×n, B : n×p over arbitrary Fintypes. Proof idea: the original proof (rank-nullity for A.mulVecLin and for its restriction to range B.mulVecLin) never uses ℝ or squareness. -/
theorem gen_lin_sylvester_rank_rect (K : Type*) [Field K] (m n p : Type*) [Fintype m] [Fintype n] [Fintype p] (A : Matrix m n K) (B : Matrix n p K) : Matrix.rank A + Matrix.rank B ≤ Fintype.card n + Matrix.rank (A * B) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker (A.mulVecLin.domRestrict (LinearMap.range B.mulVecLin))
  rw [LinearMap.range_domRestrict, ← LinearMap.range_comp, ← Matrix.mulVecLin_mul, LinearMap.ker_domRestrict] at h2
  have h3 : Module.finrank K (Submodule.comap (LinearMap.range B.mulVecLin).subtype (LinearMap.ker A.mulVecLin)) ≤ Module.finrank K (LinearMap.ker A.mulVecLin) := by
    rw [← Submodule.finrank_map_subtype_eq]
    apply Submodule.finrank_mono
    exact Submodule.map_comap_le _ _
  rw [Module.finrank_fintype_fun_eq_card] at h1
  unfold Matrix.rank
  omega
end

-- forge:entry alg_perm_eq_mul_two_involutions_s2h2 kind=proved origin=decomposition
section
/- alg_perm_eq_mul_two_involutions 的证明骨架中第 2 个空洞 -/
theorem alg_perm_eq_mul_two_involutions_s2h2 (n : ℕ) (τ ρ : Equiv.Perm (Fin n)) : τ.Disjoint ρ → (∃ (a : Equiv.Perm (Fin n)), a * a = 1 ∧ a * τ * a = τ⁻¹ ∧ ∀ (x : Fin n), (τ : Fin n → Fin n) x = x → (a : Fin n → Fin n) x = x) → (∃ (a : Equiv.Perm (Fin n)), a * a = 1 ∧ a * ρ * a = ρ⁻¹ ∧ ∀ (x : Fin n), (ρ : Fin n → Fin n) x = x → (a : Fin n → Fin n) x = x) → ∃ (a : Equiv.Perm (Fin n)), a * a = 1 ∧ a * (τ * ρ) * a = (τ * ρ)⁻¹ ∧ ∀ (x : Fin n), (τ : Fin n → Fin n) ((ρ : Fin n → Fin n) x) = x → (a : Fin n → Fin n) x = x := by
  rintro hdis ⟨a1, h11, h1c, h1f⟩ ⟨a2, h22, h2c, h2f⟩
  have d12 : a1.Disjoint a2 := fun x => (hdis x).imp (h1f x) (h2f x)
  have d1ρ : a1.Disjoint ρ := fun x => (hdis x).imp (h1f x) id
  have dτ2 : τ.Disjoint a2 := fun x => (hdis x).imp id (h2f x)
  have c12 : a1 * a2 = a2 * a1 := d12.commute.eq
  have c1ρ : a1 * ρ = ρ * a1 := d1ρ.commute.eq
  have cτ2 : τ * a2 = a2 * τ := dτ2.commute.eq
  have cτρ : τ * ρ = ρ * τ := hdis.commute.eq
  refine ⟨a1 * a2, ?_, ?_, ?_⟩
  · calc a1 * a2 * (a1 * a2) = a1 * (a2 * a1) * a2 := by group
      _ = a1 * (a1 * a2) * a2 := by rw [← c12]
      _ = (a1 * a1) * (a2 * a2) := by group
      _ = 1 := by rw [h11, h22, one_mul]
  · calc a1 * a2 * (τ * ρ) * (a1 * a2) = a1 * (a2 * τ) * (ρ * a1) * a2 := by group
      _ = a1 * (τ * a2) * (a1 * ρ) * a2 := by rw [← cτ2, ← c1ρ]
      _ = a1 * τ * (a2 * a1) * ρ * a2 := by group
      _ = a1 * τ * (a1 * a2) * ρ * a2 := by rw [← c12]
      _ = (a1 * τ * a1) * (a2 * ρ * a2) := by group
      _ = τ⁻¹ * ρ⁻¹ := by rw [h1c, h2c]
      _ = (τ * ρ)⁻¹ := by rw [cτρ, mul_inv_rev]
  · intro x hx
    have hx' : τ (ρ x) = x := hx
    have hρ : ρ x = x := by
      rcases hdis x with h | h
      · apply τ.injective; rw [hx', h]
      · exact h
    have hτ : τ x = x := by rw [hρ] at hx'; exact hx'
    show a1 (a2 x) = x
    rw [h2f x hρ, h1f x hτ]
end

-- forge:entry alg_perm_eq_mul_two_involutions kind=proved origin=conjecture
section
/- Every permutation of a finite set is a product of two involutions — on each cycle (x, σx, …, σ^{m-1}x) define a as the reflection σ^i x ↦ σ^{-i} x; then a is an involution and a σ a = σ⁻¹, so b = a σ satisfies b² = 1 and σ = a b. -/
theorem alg_perm_eq_mul_two_involutions (n : ℕ) (σ : Equiv.Perm (Fin n)) : ∃ a b : Equiv.Perm (Fin n), a * a = 1 ∧ b * b = 1 ∧ σ = a * b := by
  have H : (∀ τ : Equiv.Perm (Fin n), τ.IsCycle →
        ∃ a : Equiv.Perm (Fin n), a * a = 1 ∧ a * τ * a = τ⁻¹ ∧ ∀ x : Fin n, τ x = x → a x = x) ∧
      (∀ τ ρ : Equiv.Perm (Fin n), τ.Disjoint ρ →
        (∃ a : Equiv.Perm (Fin n), a * a = 1 ∧ a * τ * a = τ⁻¹ ∧ ∀ x : Fin n, τ x = x → a x = x) →
        (∃ a : Equiv.Perm (Fin n), a * a = 1 ∧ a * ρ * a = ρ⁻¹ ∧ ∀ x : Fin n, ρ x = x → a x = x) →
        (∃ a : Equiv.Perm (Fin n), a * a = 1 ∧ a * (τ * ρ) * a = (τ * ρ)⁻¹ ∧ ∀ x : Fin n, τ (ρ x) = x → a x = x)) := by
    clear σ
    refine ⟨?_, ?_⟩ <;> (first | exact @Mathlib2.alg_perm_eq_mul_two_involutions_s1h1 n | exact Mathlib2.alg_perm_eq_mul_two_involutions_s1h1 | apply Mathlib2.alg_perm_eq_mul_two_involutions_s1h1 <;> assumption | simpa using Mathlib2.alg_perm_eq_mul_two_involutions_s1h1 | exact @Mathlib2.alg_perm_eq_mul_two_involutions_s2h2 n | exact Mathlib2.alg_perm_eq_mul_two_involutions_s2h2 | apply Mathlib2.alg_perm_eq_mul_two_involutions_s2h2 <;> assumption | simpa using Mathlib2.alg_perm_eq_mul_two_involutions_s2h2)
  obtain ⟨hc, hd⟩ := H
  have key : ∃ a : Equiv.Perm (Fin n), a * a = 1 ∧ a * σ * a = σ⁻¹ ∧ ∀ x : Fin n, σ x = x → a x = x := by
    induction σ using Equiv.Perm.cycle_induction_on with
    | base_one => exact ⟨1, by simp, by simp, fun x _ => rfl⟩
    | base_cycles τ hτ => exact hc τ hτ
    | induction_disjoint τ ρ hdis _ h1 h2 => exact hd τ ρ hdis h1 h2
  obtain ⟨a, haa, hconj, -⟩ := key
  refine ⟨a, a * σ, haa, ?_, ?_⟩
  · calc a * σ * (a * σ) = (a * σ * a) * σ := by group
      _ = 1 := by rw [hconj]; simp
  · calc σ = (a * a) * σ := by rw [haa, one_mul]
      _ = a * (a * σ) := by group
end

-- forge:entry gen_nt_sq_add_sq_eq_prime_mul_sq kind=proved origin=conjecture
section
/- Generalizes Mathlib2.nt2_sq_add_sq_eq_seven_mul_sq: 7 → every prime p ≡ 3 (mod 4). Proof idea: infinite descent on |z| (or on x²+y²) using Mathlib2.nt2_prime_three_mod_four_dvd_sq_add_sq: p ∣ x, p ∣ y, hence p ∣ z², p ∣ z, and (x/p, y/p, z/p) is a smaller solution. -/
theorem gen_nt_sq_add_sq_eq_prime_mul_sq_aux1 (p : ℕ) (hp : p.Prime) (hp3 : p % 4 = 3) (n : ℕ) : ∀ x y z : ℤ, z.natAbs < n → x ^ 2 + y ^ 2 = (p : ℤ) * z ^ 2 → z = 0 := by
  induction n with
  | zero => intro x y z hz; omega
  | succ n ih =>
    intro x y z hz h
    by_contra hz0
    obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := Mathlib2.nt2_prime_three_mod_four_dvd_sq_add_sq p hp hp3 x y ⟨z ^ 2, h⟩
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have h7 : (p : ℤ) ∣ z ^ 2 := by
      refine ⟨a ^ 2 + b ^ 2, ?_⟩
      apply mul_left_cancel₀ hp0
      linear_combination -h
    have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    obtain ⟨c, rfl⟩ := hpp.dvd_of_dvd_pow h7
    have hc : c = 0 := by
      apply ih a b c
      · have hc0 : c ≠ 0 := by rintro rfl; simp at hz0
        have hcp : 0 < c.natAbs := Int.natAbs_pos.mpr hc0
        rw [Int.natAbs_mul, Int.natAbs_natCast] at hz
        have : 2 ≤ p := hp.two_le
        nlinarith
      · apply mul_left_cancel₀ (pow_ne_zero 2 hp0)
        linear_combination h
    subst hc
    simp at hz0

theorem gen_nt_sq_add_sq_eq_prime_mul_sq (p : ℕ) (hp : p.Prime) (hp3 : p % 4 = 3) (x y z : ℤ) (h : x ^ 2 + y ^ 2 = (p : ℤ) * z ^ 2) : x = 0 ∧ y = 0 ∧ z = 0 := by
  have hz := gen_nt_sq_add_sq_eq_prime_mul_sq_aux1 p hp hp3 (z.natAbs + 1) x y z (Nat.lt_succ_self _) h
  subst hz
  have hx : x ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hy : y ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  exact ⟨by simpa using hx, by simpa using hy, rfl⟩
end

-- forge:entry gen_lin_nilpotent_pow_card_reduced kind=proved origin=conjecture
section
/- Generalizes Mathlib2.lin_nilpotent_pow_card: ℝ → any reduced commutative ring (false for non-reduced rings: the 1×1 matrix [ε], ε²=0), Fin n → Fintype. Proof idea: Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent gives charpoly − X^card nilpotent in R[X], which is reduced, so charpoly = X^card; then Cayley–Hamilton (Matrix.aeval_self_charpoly). -/
theorem gen_lin_nilpotent_pow_card_reduced (R : Type*) [CommRing R] [IsReduced R] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R) (h : IsNilpotent A) : A ^ Fintype.card ι = 0 := by
  have hn := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h
  have h0 : A.charpoly - Polynomial.X ^ Fintype.card ι = 0 := by
    ext i
    rw [Polynomial.coeff_zero]
    exact (Polynomial.isNilpotent_iff.mp hn i).eq_zero
  have hc : A.charpoly = Polynomial.X ^ Fintype.card ι := sub_eq_zero.mp h0
  have he := Matrix.aeval_self_charpoly A
  rw [hc] at he
  simpa using he
end

-- forge:entry gen_nt_sq_sub_add_one_dvd_pow_sum kind=proved origin=conjecture
section
/- Generalizes Mathlib2.nt_seven_dvd_pow_sum: the constants 3, 2, 7 → a, a−1, a²−a+1 for an arbitrary element a of an arbitrary commutative ring (a = 3 in ℤ gives the original). Proof idea: modulo a²−a+1 one has a² ≡ a−1 and (a−1)² ≡ −a, so a^(2n+1) ≡ a(a−1)^n and (a−1)^(n+2) ≡ −a(a−1)^n; formally induct on n with step a^(2n+3)+(a−1)^(n+3) = (a−1)(a^(2n+1)+(a−1)^(n+2)) + (a²−a+1)·a^(2n+1). -/
theorem gen_nt_sq_sub_add_one_dvd_pow_sum (R : Type*) [CommRing R] (a : R) (n : ℕ) : (a ^ 2 - a + 1) ∣ a ^ (2 * n + 1) + (a - 1) ^ (n + 2) := by
  induction n with
  | zero => exact ⟨1, by ring⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨(a - 1) * c + a ^ (2 * n + 1), ?_⟩
    have e : a ^ (2 * (n + 1) + 1) + (a - 1) ^ (n + 1 + 2) = (a - 1) * (a ^ (2 * n + 1) + (a - 1) ^ (n + 2)) + (a ^ 2 - a + 1) * a ^ (2 * n + 1) := by ring
    rw [e, hc]; ring
end

-- forge:entry gen_lin_nilpotent_det_one_add_reduced kind=proved origin=conjecture
section
/- Generalizes Mathlib2.lin_nilpotent_det_one_add: ℝ → any reduced commutative ring (false in non-reduced rings: det(1+[ε]) = 1+ε), Fin n → Fintype. Proof idea: charpoly(−A) = X^card as for nilpotent matrices over a reduced ring; evaluate at 1: det(1·1 − (−A)) = 1. -/
theorem gen_lin_nilpotent_det_one_add_reduced (R : Type*) [CommRing R] [IsReduced R] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R) (h : IsNilpotent A) : Matrix.det (1 + A) = 1 := by
  have hn := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h.neg
  have h0 : (-A).charpoly - Polynomial.X ^ Fintype.card ι = 0 := by
    ext i
    rw [Polynomial.coeff_zero]
    exact (Polynomial.isNilpotent_iff.mp hn i).eq_zero
  have hc : (-A).charpoly = Polynomial.X ^ Fintype.card ι := sub_eq_zero.mp h0
  have he := Matrix.eval_charpoly (-A) 1
  rw [hc, map_one, sub_neg_eq_add] at he
  rw [← he]
  simp
end

end Mathlib2
