/- Mathlib2 分片 37（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0036
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry gr_five_no_mono_triangle_degree_two kind=proved origin=conjecture
section
/- In a 2-colouring of K₅ without monochromatic triangle every vertex has red degree 2 (so the colouring is the pentagon) — if deg v ≥ 3 then three neighbours are pairwise non-adjacent (G triangle-free) hence a triangle of Gᶜ; if deg v ≤ 1 then v has ≥ 3 non-neighbours, pairwise adjacent in G (Gᶜ triangle-free), a triangle of G. -/
theorem gr_five_no_mono_triangle_degree_two_aux1
    (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 3) (v : V) :
    G.degree v ≤ 2 := by
  classical
  by_contra hn
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq
    (show 3 ≤ (G.neighborFinset v).card by
      rw [G.card_neighborFinset_eq_degree]
      omega)
  have hi : Gᶜ.IsClique (G.neighborSet v) :=
    (SimpleGraph.isClique_compl G).mpr
      (G.isIndepSet_neighborSet_of_triangleFree h v)
  apply hc s
  refine ⟨hi.subset ?_, hcard⟩
  intro x hx
  exact (G.mem_neighborFinset v x).mp (hs hx)

theorem gr_five_no_mono_triangle_degree_two
    (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h5 : Fintype.card V = 5) (h : G.CliqueFree 3)
    (hc : Gᶜ.CliqueFree 3) (v : V) : G.degree v = 2 := by
  classical
  have hd := gr_five_no_mono_triangle_degree_two_aux1 V G h hc v
  have hdc := gr_five_no_mono_triangle_degree_two_aux1 V Gᶜ hc (by simpa using h) v
  rw [G.degree_compl, h5] at hdc
  omega
end

-- forge:entry gr_nordhaus_gaddum_mul kind=proved origin=conjecture
section
/- Nordhaus–Gaddum product bound χ(G)·χ(Gᶜ) ≥ n — with colourings c₁ : V → Fin a of G and c₂ : V → Fin b of Gᶜ the map v ↦ (c₁ v, c₂ v) is injective, since distinct u,v are adjacent in G or in Gᶜ; compare cardinalities. -/
theorem gr_nordhaus_gaddum_mul (V : Type) [Fintype V] (G : SimpleGraph V)
    (a b : ℕ) (ha : G.Colorable a) (hb : Gᶜ.Colorable b) :
    Fintype.card V ≤ a * b := by
  classical
  obtain ⟨c₁⟩ := ha
  obtain ⟨c₂⟩ := hb
  have hinj : Function.Injective (fun v : V => (c₁ v, c₂ v)) := by
    intro u v huv
    by_contra hne
    by_cases hadj : G.Adj u v
    · exact c₁.valid hadj (congrArg Prod.fst huv)
    · have hcompl : Gᶜ.Adj u v := (G.compl_adj u v).2 ⟨hne, hadj⟩
      exact c₂.valid hcompl (congrArg Prod.snd huv)
  simpa using Fintype.card_le_of_injective (fun v : V => (c₁ v, c₂ v)) hinj
end

-- forge:entry p6_coprime kind=proved origin=paper
section
/- After Lemma 2.3 (unnumbered): gcd(f_n, f_{n+1}) = 1 -/
theorem p6_coprime (k n : ℤ) : IsCoprime (p6_kfib k n) (p6_kfib k (n + 1)) := by
  refine ⟨p6_kfib k (-n), p6_kfib k (-n + 1), ?_⟩
  have h := (p6_addition k (-n) n).2
  rw [neg_add_cancel, zero_add, (p6_kfib_def k 0).2.1] at h
  linarith
end

-- forge:entry p6_odd_pos kind=proved origin=paper
section
/- Sec 3 (unnumbered): Note that f_{2n+1} > 0, since it is a sum of squares -/
theorem p6_odd_pos (k n : ℤ) : 0 < p6_kfib k (2 * n + 1) := by
  rw [p6_lem23_eq7]
  by_cases hn : p6_kfib k n = 0
  · have hn1 : p6_kfib k (n + 1) ≠ 0 := by
      intro hzero
      apply Units.ne_zero (Int.negOnePow n)
      simpa [hn, hzero] using (p6_lem23_eq8 k n).symm
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hn1)
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hn) (sq_nonneg _)
end

-- forge:entry gr_card_le_colorable_mul_indep kind=proved origin=conjecture
section
/- n ≤ χ(G)·α(G) — the k colour classes are independent sets, each of size ≤ a, and they partition V (Finset.card_eq_sum_card_fiberwise). -/
theorem gr_card_le_colorable_mul_indep (V : Type) [Fintype V]
    (G : SimpleGraph V) (k a : ℕ) (hk : G.Colorable k)
    (ha : ∀ s : Finset V, G.IsIndepSet (s : Set V) → s.card ≤ a) :
    Fintype.card V ≤ k * a := by
  classical
  obtain ⟨C⟩ := hk
  have hclass (c : Fin k) :
      (Finset.univ.filter (fun v : V => C v = c)).card ≤ a := by
    apply ha
    intro u hu v hv _ hadj
    exact C.valid hadj
      ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm)
  calc
    Fintype.card V =
        ∑ c : Fin k, (Finset.univ.filter (fun v : V => C v = c)).card := by
      simpa only [Finset.card_univ] using
        (Finset.card_eq_sum_card_fiberwise
          (f := fun v : V => C v) (s := Finset.univ) (t := Finset.univ)
          (fun _ _ => Finset.mem_univ _))
    _ ≤ ∑ _c : Fin k, a := Finset.sum_le_sum (fun c _ => hclass c)
    _ = k * a := by simp
end

-- forge:entry gr_regular_odd_degree_even_card kind=proved origin=conjecture
section
/- A regular graph of odd degree has an even number of vertices — handshake lemma: n·d = 2e is even and d is odd. -/
theorem gr_regular_odd_degree_even_card (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (h : G.IsRegularOfDegree d) (hd : Odd d) : Even (Fintype.card V) := by
  have hsum : Fintype.card V * d = 2 * G.edgeFinset.card := by
    simpa only [h.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul]
      using G.sum_degrees_eq_twice_card_edges
  have heven : Even (Fintype.card V * d) := by
    rw [hsum]
    exact ⟨G.edgeFinset.card, by omega⟩
  exact (Nat.even_mul.mp heven).resolve_right (Nat.not_even_iff_odd.mpr hd)
end

-- forge:entry p6_prop21_tangent kind=proved origin=paper
section
/- Proposition 2.1 (Ford), first half: If det [[p,r],[q,s]] = ±1 then K[p,q] and K[r,s] are tangent [Tangent = externally tangent: distance of centres equals sum of radii; stated as an iff (stronger than printed). Finite circles only (q,s>0); the K[1,0] line convention is not formalised. Cited result (Ford 1938).] -/
theorem p6_prop21_tangent (p q r s : ℤ) (hq : 0 < q) (hs : 0 < s) :
    ((p : ℝ) / q - (r : ℝ) / s) ^ 2 +
        (1 / (2 * (q : ℝ) ^ 2) - 1 / (2 * (s : ℝ) ^ 2)) ^ 2 =
      (1 / (2 * (q : ℝ) ^ 2) + 1 / (2 * (s : ℝ) ^ 2)) ^ 2 ↔
      (p * s - q * r = 1 ∨ p * s - q * r = -1) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hs)
  have hidentity :
      ((p : ℝ) / q - (r : ℝ) / s) ^ 2 +
          (1 / (2 * (q : ℝ) ^ 2) - 1 / (2 * (s : ℝ) ^ 2)) ^ 2 -
          (1 / (2 * (q : ℝ) ^ 2) + 1 / (2 * (s : ℝ) ^ 2)) ^ 2 =
        (((p : ℝ) * s - (q : ℝ) * r) ^ 2 - 1) / ((q : ℝ) * s) ^ 2 := by
    field_simp [hq0, hs0] <;> ring
  have hreal :
      ((p : ℝ) / q - (r : ℝ) / s) ^ 2 +
          (1 / (2 * (q : ℝ) ^ 2) - 1 / (2 * (s : ℝ) ^ 2)) ^ 2 =
        (1 / (2 * (q : ℝ) ^ 2) + 1 / (2 * (s : ℝ) ^ 2)) ^ 2 ↔
        ((p : ℝ) * s - (q : ℝ) * r) ^ 2 = 1 := by
    rw [← sub_eq_zero, hidentity, div_eq_zero_iff]
    simp [sub_eq_zero, hq0, hs0]
  rw [hreal, sq_eq_one_iff]
  norm_cast
end

-- forge:entry gr_tree_two_leaves kind=proved origin=conjecture
section
/- A tree on at least two vertices has at least two leaves — ∑deg = 2e = 2(n−1) by the handshake lemma and SimpleGraph.IsTree.card_edgeFinset; every degree is ≥ 1 by connectedness; if at most one vertex had degree 1 the sum would be ≥ 2(n−1) + 1. -/
theorem gr_tree_two_leaves (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.IsTree)
    (hn : 2 ≤ Fintype.card V) :
    ∃ u v, u ≠ v ∧ G.degree u = 1 ∧ G.degree v = 1 := by
  classical
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨u, hu⟩ := h.exists_vert_degree_one_of_nontrivial
  refine ⟨u, ?_⟩
  by_contra hnot
  have hdeg : ∀ v ∈ (Finset.univ : Finset V).erase u, 2 ≤ G.degree v := by
    intro v hv
    have hne : u ≠ v := (Finset.mem_erase.mp hv).1.symm
    have hpos := h.isConnected.preconnected.degree_pos_of_nontrivial v
    by_contra htwo
    have hone : G.degree v = 1 := by omega
    exact hnot ⟨v, hne, hu, hone⟩
  have hsum :
      (∑ _v ∈ (Finset.univ : Finset V).erase u, (2 : ℕ)) ≤
        ∑ v ∈ (Finset.univ : Finset V).erase u, G.degree v :=
    Finset.sum_le_sum hdeg
  simp only [Finset.sum_const, smul_eq_mul] at hsum
  have hsplit :
      (∑ v ∈ (Finset.univ : Finset V).erase u, G.degree v) + 1 =
        2 * G.edgeFinset.card := by
    simpa only [hu, G.sum_degrees_eq_twice_card_edges] using
      Finset.sum_erase_add (Finset.univ : Finset V) (fun v => G.degree v)
        (Finset.mem_univ u)
  have hcard := Finset.card_erase_add_one
    (s := (Finset.univ : Finset V)) (Finset.mem_univ u)
  simp only [Finset.card_univ] at hcard
  have htree := h.card_edgeFinset
  omega
end

-- forge:entry p6_prop21_disjoint kind=proved origin=paper
section
/- Proposition 2.1 (Ford), second half: two distinct Ford circles ... otherwise, they are disjoint [Distinct circles read as p/q ≠ r/s i.e. ps-qr ≠ 0; disjoint = distance of centres exceeds sum of radii. Reducedness of the fractions is not needed.] -/
theorem p6_prop21_disjoint (p q r s : ℤ) (hq : 0 < q) (hs : 0 < s)
    (hne : p * s - q * r ≠ 0) (h1 : p * s - q * r ≠ 1)
    (h2 : p * s - q * r ≠ -1) :
    (1 / (2 * (q : ℝ) ^ 2) + 1 / (2 * (s : ℝ) ^ 2)) ^ 2 <
      ((p : ℝ) / q - (r : ℝ) / s) ^ 2 +
        (1 / (2 * (q : ℝ) ^ 2) - 1 / (2 * (s : ℝ) ^ 2)) ^ 2 := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hs)
  have hdet_cases : (2 : ℤ) ≤ p * s - q * r ∨ p * s - q * r ≤ -2 := by
    omega
  have hdet : 1 < ((p : ℝ) * s - (q : ℝ) * r) ^ 2 := by
    rcases hdet_cases with hd | hd
    · have hd' : (2 : ℝ) ≤ (p : ℝ) * s - (q : ℝ) * r := by
        exact_mod_cast hd
      nlinarith
    · have hd' : (p : ℝ) * s - (q : ℝ) * r ≤ -2 := by
        exact_mod_cast hd
      nlinarith
  have hidentity :
      ((p : ℝ) / q - (r : ℝ) / s) ^ 2 +
          (1 / (2 * (q : ℝ) ^ 2) - 1 / (2 * (s : ℝ) ^ 2)) ^ 2 -
          (1 / (2 * (q : ℝ) ^ 2) + 1 / (2 * (s : ℝ) ^ 2)) ^ 2 =
        (((p : ℝ) * s - (q : ℝ) * r) ^ 2 - 1) / ((q : ℝ) * s) ^ 2 := by
    field_simp [hq0, hs0] <;> ring
  have hgap : 0 <
      ((p : ℝ) / q - (r : ℝ) / s) ^ 2 +
          (1 / (2 * (q : ℝ) ^ 2) - 1 / (2 * (s : ℝ) ^ 2)) ^ 2 -
          (1 / (2 * (q : ℝ) ^ 2) + 1 / (2 * (s : ℝ) ^ 2)) ^ 2 := by
    rw [hidentity]
    exact div_pos (sub_pos.mpr hdet) (sq_pos_of_ne_zero (mul_ne_zero hq0 hs0))
  linarith
end

-- forge:entry gr_bipartite_regular_parts_equal kind=proved origin=conjecture
section
/- A regular bipartite graph of positive degree has colour classes of equal size — double count edges (darts from the true class): each edge has exactly one endpoint in each class, so d·|true class| = e = d·|false class|; cancel d. -/
theorem gr_bipartite_regular_parts_equal (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (hd : 0 < d)
    (h : G.IsRegularOfDegree d) (C : G.Coloring Bool) :
    (Finset.univ.filter (fun v => C v = true)).card =
      (Finset.univ.filter (fun v => C v = false)).card := by
  let s : Finset V := Finset.univ.filter (fun v => C v = true)
  let t : Finset V := Finset.univ.filter (fun v => C v = false)
  have hb : G.IsBipartiteWith (s : Set V) (t : Set V) := by
    constructor
    · apply Set.disjoint_left.mpr
      intro v hv ht
      have hv' : C v = true := by simpa [s] using hv
      have ht' : C v = false := by simpa [t] using ht
      exact Bool.false_ne_true (ht'.symm.trans hv')
    · intro v w hvw
      have hc := C.valid hvw
      change (v ∈ s ∧ w ∈ t) ∨ (v ∈ t ∧ w ∈ s)
      simp only [s, t, Finset.mem_filter, Finset.mem_univ, true_and]
      cases hv : C v <;> cases hw : C w <;> simp_all
  apply Nat.mul_right_cancel hd
  simpa [s, t, h.degree_eq] using SimpleGraph.isBipartiteWith_sum_degrees_eq hb
end

-- forge:entry gr_connected_of_ore_condition kind=proved origin=conjecture
section
/- Ore-type connectivity criterion generalising Mathlib2.comb_connected_of_min_degree_half: if deg u + deg v ≥ n − 1 for all non-adjacent u ≠ v then G is connected (indeed of diameter ≤ 2) — for non-adjacent u ≠ v the neighbour sets lie in V \ {u,v} of size n − 2 and have total size ≥ n − 1, so they intersect, giving a walk u-w-v. -/
theorem gr_connected_of_ore_condition (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (h : ∀ u v, u ≠ v → ¬ G.Adj u v →
      Fintype.card V ≤ G.degree u + G.degree v + 1) : G.Connected := by
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
  have hsub : G.neighborFinset u ∪ G.neighborFinset v ⊆
      (Finset.univ.erase u).erase v := by
    intro w hw
    rw [Finset.mem_union, SimpleGraph.mem_neighborFinset,
      SimpleGraph.mem_neighborFinset] at hw
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    rcases hw with hw | hw
    · refine ⟨?_, ?_⟩
      · rintro rfl
        exact hadj hw
      · rintro rfl
        exact G.loopless.irrefl _ hw
    · refine ⟨?_, ?_⟩
      · rintro rfl
        exact G.loopless.irrefl _ hw
      · rintro rfl
        exact hadj hw.symm
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, G.card_neighborFinset_eq_degree,
    G.card_neighborFinset_eq_degree,
    Finset.card_erase_of_mem (by simp [Ne.symm huv]),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at hcard
  have hsum := h u v huv hadj
  have htwo : 2 ≤ Fintype.card V := by
    have := Fintype.one_lt_card_iff.2 ⟨u, v, huv⟩
    omega
  omega
end

-- forge:entry p6_prop22_on_circles kind=proved origin=paper
section
/- Proposition 2.2 (Kocik), formula (1): If K[p,q] and K[r,s] are tangent, their tangency point is ((pq+rs)/(q^2+s^2), 1/(q^2+s^2)) [The point (1) lies on both circles.] -/
lemma p6_prop22_on_circles_aux1 {K : Type*} [Field K] [CharZero K]
    (p q r s : K) (hq : q ≠ 0) (hd : q ^ 2 + s ^ 2 ≠ 0) :
    ((p * q + r * s) / (q ^ 2 + s ^ 2) - p / q) ^ 2 +
        (1 / (q ^ 2 + s ^ 2) - 1 / (2 * q ^ 2)) ^ 2 -
        (1 / (2 * q ^ 2)) ^ 2 =
      s ^ 2 * ((p * s - q * r) ^ 2 - 1) /
        (q ^ 2 * (q ^ 2 + s ^ 2) ^ 2) := by
  field_simp [hq, hd] <;> ring

theorem p6_prop22_on_circles (p q r s : ℤ) (hq : 0 < q) (hs : 0 < s)
    (h : p * s - q * r = 1 ∨ p * s - q * r = -1) :
    ((((p * q + r * s : ℤ) : ℝ) / ((q ^ 2 + s ^ 2 : ℤ) : ℝ) - (p : ℝ) / q) ^ 2 +
      (1 / ((q ^ 2 + s ^ 2 : ℤ) : ℝ) - 1 / (2 * (q : ℝ) ^ 2)) ^ 2 =
      (1 / (2 * (q : ℝ) ^ 2)) ^ 2) ∧
    ((((p * q + r * s : ℤ) : ℝ) / ((q ^ 2 + s ^ 2 : ℤ) : ℝ) - (r : ℝ) / s) ^ 2 +
      (1 / ((q ^ 2 + s ^ 2 : ℤ) : ℝ) - 1 / (2 * (s : ℝ) ^ 2)) ^ 2 =
      (1 / (2 * (s : ℝ) ^ 2)) ^ 2) := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqR
  have hs0 : (s : ℝ) ≠ 0 := ne_of_gt hsR
  have hd : (q : ℝ) ^ 2 + (s : ℝ) ^ 2 ≠ 0 := by positivity
  have hd' : (s : ℝ) ^ 2 + (q : ℝ) ^ 2 ≠ 0 := by positivity
  have hdetZ : (p * s - q * r) ^ 2 = 1 := by
    rcases h with h | h <;> rw [h] <;> norm_num
  have hdet : ((p : ℝ) * s - (q : ℝ) * r) ^ 2 = 1 := by
    exact_mod_cast hdetZ
  have hdet' : ((r : ℝ) * q - (s : ℝ) * p) ^ 2 = 1 := by
    nlinarith [hdet]
  push_cast
  constructor
  · apply sub_eq_zero.mp
    rw [p6_prop22_on_circles_aux1 (p : ℝ) q r s hq0 hd, hdet]
    simp
  · apply sub_eq_zero.mp
    have hi := p6_prop22_on_circles_aux1 (r : ℝ) s p q hs0 hd'
    rw [hdet'] at hi
    simpa [add_comm, mul_comm] using hi
end

-- forge:entry p6_prop22_unique kind=proved origin=paper
section
/- Proposition 2.2 (Kocik), uniqueness: ...their tangency point is (1) [Any common point of the two tangent circles is the point (1).] -/
lemma p6_prop22_unique_aux1 {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (a b c d u v x y : K)
    (h1 : (x - a) ^ 2 + (y - b) ^ 2 = u ^ 2)
    (h2 : (x - c) ^ 2 + (y - d) ^ 2 = v ^ 2)
    (ht : (a - c) ^ 2 + (b - d) ^ 2 = (u + v) ^ 2) :
    v * (x - a) + u * (x - c) = 0 ∧
      v * (y - b) + u * (y - d) = 0 := by
  have hid : (v * (x - a) + u * (x - c)) ^ 2 +
      (v * (y - b) + u * (y - d)) ^ 2 = 0 := by
    linear_combination v * (u + v) * h1 + u * (u + v) * h2 - u * v * ht
  have hx : (v * (x - a) + u * (x - c)) ^ 2 = 0 := by
    have hy := sq_nonneg (v * (y - b) + u * (y - d))
    have hx := sq_nonneg (v * (x - a) + u * (x - c))
    linarith
  have hy : (v * (y - b) + u * (y - d)) ^ 2 = 0 := by
    linarith
  exact ⟨sq_eq_zero_iff.mp hx, sq_eq_zero_iff.mp hy⟩

theorem p6_prop22_unique (p q r s : ℤ) (hq : 0 < q) (hs : 0 < s)
    (h : p * s - q * r = 1 ∨ p * s - q * r = -1) (x y : ℝ)
    (h1 : (x - (p : ℝ) / q) ^ 2 +
      (y - 1 / (2 * (q : ℝ) ^ 2)) ^ 2 = (1 / (2 * (q : ℝ) ^ 2)) ^ 2)
    (h2 : (x - (r : ℝ) / s) ^ 2 +
      (y - 1 / (2 * (s : ℝ) ^ 2)) ^ 2 = (1 / (2 * (s : ℝ) ^ 2)) ^ 2) :
    x = ((p * q + r * s : ℤ) : ℝ) / ((q ^ 2 + s ^ 2 : ℤ) : ℝ) ∧
      y = 1 / ((q ^ 2 + s ^ 2 : ℤ) : ℝ) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hs)
  have hD : (q : ℝ) ^ 2 + (s : ℝ) ^ 2 ≠ 0 := by
    have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq
    positivity
  have ht := (p6_prop21_tangent p q r s hq hs).mpr h
  obtain ⟨hx, hy⟩ := p6_prop22_unique_aux1
    ((p : ℝ) / q) (1 / (2 * (q : ℝ) ^ 2))
    ((r : ℝ) / s) (1 / (2 * (s : ℝ) ^ 2))
    (1 / (2 * (q : ℝ) ^ 2)) (1 / (2 * (s : ℝ) ^ 2)) x y h1 h2 ht
  push_cast
  constructor
  · apply (eq_div_iff hD).mpr
    field_simp [hq0, hs0] at hx
    nlinarith only [hx]
  · apply (eq_div_iff hD).mpr
    field_simp [hq0, hs0] at hy
    nlinarith only [hy]
end

-- forge:entry gr_connected_of_many_edges kind=proved origin=conjecture
section
/- A graph with more than C(n−1,2) edges is connected — otherwise (using Mathlib2.comb_compl_connected_of_not_connected style splitting) V splits into nonempty parts of sizes k and n−k with no edges between, so e ≤ C(k,2) + C(n−k,2) ≤ C(n−1,2) for 1 ≤ k ≤ n−1. -/
theorem gr_connected_of_many_edges (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : (Fintype.card V - 1).choose 2 < G.edgeFinset.card) : G.Connected := by
  classical
  have hn : 0 < Fintype.card V := by
    by_contra hn
    have hz : Fintype.card V = 0 := by omega
    have he : G.edgeFinset.card ≤ 0 := by
      simpa [hz] using G.card_edgeFinset_le_card_choose_two
    have hp : 0 < G.edgeFinset.card := by
      simpa [hz] using h
    omega
  letI : Nonempty V := Fintype.card_pos_iff.mp hn
  by_contra hc
  have hcc := comb_compl_connected_of_not_connected V G hc
  have hbound : Fintype.card V ≤ Gᶜ.edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using
      hcc.card_vert_le_card_edgeSet_add_one
  have hsum : G.edgeFinset.card + Gᶜ.edgeFinset.card = (Fintype.card V).choose 2 := by
    calc
      _ = (G ⊔ Gᶜ).edgeFinset.card := by
        rw [SimpleGraph.edgeFinset_sup,
          Finset.card_union_of_disjoint
            (SimpleGraph.disjoint_edgeFinset.mpr disjoint_compl_right)]
      _ = _ := by
        have ht : (G ⊔ Gᶜ).edgeFinset = (⊤ : SimpleGraph V).edgeFinset :=
          SimpleGraph.edgeFinset_inj.mpr sup_compl_eq_top
        rw [ht, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  have hchoose : (Fintype.card V).choose 2 =
      (Fintype.card V - 1).choose 2 + (Fintype.card V - 1) := by
    have hn' : Fintype.card V = (Fintype.card V - 1) + 1 := by omega
    conv_lhs => rw [hn']
    simpa only [Nat.choose_one_right, Nat.add_comm] using
      (Nat.choose_succ_succ' (Fintype.card V - 1) 1)
  omega
end

-- forge:entry p6_thm31_circle kind=proved origin=paper
section
/- Theorem 3.1 (Metallic circle): the points P_n=(f_{2n}/f_{2n+1}, 1/f_{2n+1}), n in Z, lie on C_k: (x+k/2)^2+y^2=(k^2+4)/4 [Stated for every integer k (paper: k>=1; the hypothesis is not needed).] -/
theorem p6_thm31_circle (k n : ℤ) :
    (((p6_kfib k (2 * n) : ℤ) : ℝ) /
      ((p6_kfib k (2 * n + 1) : ℤ) : ℝ) + (k : ℝ) / 2) ^ 2 +
      (1 / ((p6_kfib k (2 * n + 1) : ℤ) : ℝ)) ^ 2 =
      ((k : ℝ) ^ 2 + 4) / 4 := by
  have hz : p6_kfib k (2 * n + 1) ^ 2 -
      k * p6_kfib k (2 * n) * p6_kfib k (2 * n + 1) -
      p6_kfib k (2 * n) ^ 2 = 1 := by
    simpa only [Int.negOnePow_two_mul, Units.val_one] using p6_lem23_eq9 k (2 * n)
  have hr : ((p6_kfib k (2 * n + 1) : ℤ) : ℝ) ^ 2 -
      (k : ℝ) * ((p6_kfib k (2 * n) : ℤ) : ℝ) *
      ((p6_kfib k (2 * n + 1) : ℤ) : ℝ) -
      ((p6_kfib k (2 * n) : ℤ) : ℝ) ^ 2 = 1 := by
    exact_mod_cast hz
  have hpos : (0 : ℝ) < ((p6_kfib k (2 * n + 1) : ℤ) : ℝ) := by
    exact_mod_cast p6_odd_pos k n
  have hne := ne_of_gt hpos
  field_simp
  nlinarith [hr]
end

-- forge:entry gr_self_compl_card_mod_four kind=proved origin=conjecture
section
/- A self-complementary graph has n ≡ 0 or 1 (mod 4) — an isomorphism gives a bijection of edge sets so e(G) = e(Gᶜ), and e(G) + e(Gᶜ) = n(n−1)/2, hence 4 ∣ n(n−1); as n, n−1 are coprime with one odd, 4 ∣ n or 4 ∣ n−1. -/
theorem gr_self_compl_card_mod_four (V : Type) [Fintype V] (G : SimpleGraph V)
    (h : Nonempty (SimpleGraph.Iso G Gᶜ)) :
    Fintype.card V % 4 = 0 ∨ Fintype.card V % 4 = 1 := by
  classical
  obtain ⟨f⟩ := h
  have he : G.edgeFinset.card = Gᶜ.edgeFinset.card := f.card_edgeFinset_eq
  have hdeg (v : V) : G.degree v + Gᶜ.degree v + 1 = Fintype.card V := by
    rw [SimpleGraph.degree_compl]
    have hv := G.degree_lt_card_verts v
    omega
  have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset V)) rfl
    (fun v _ => hdeg v)
  have hcount : 2 * G.edgeFinset.card + 2 * Gᶜ.edgeFinset.card + Fintype.card V =
      Fintype.card V * Fintype.card V := by
    simpa only [Finset.sum_add_distrib, SimpleGraph.sum_degrees_eq_twice_card_edges,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] using hs
  have hc : 4 * G.edgeFinset.card + Fintype.card V =
      Fintype.card V * Fintype.card V := by omega
  have hm : Fintype.card V % 4 =
      (Fintype.card V % 4 * (Fintype.card V % 4)) % 4 := by
    simpa [Nat.add_mod, Nat.mul_mod] using congrArg (fun x : ℕ => x % 4) hc
  have hr := Nat.mod_lt (Fintype.card V) (by omega : 0 < 4)
  have hres : Fintype.card V % 4 = 0 ∨ Fintype.card V % 4 = 1 ∨
      Fintype.card V % 4 = 2 ∨ Fintype.card V % 4 = 3 := by omega
  rcases hres with h0 | h1 | h2 | h3
  · exact Or.inl h0
  · exact Or.inr h1
  · norm_num [h2] at hm
  · norm_num [h3] at hm
end

-- forge:entry gr_set_union_ne_univ_card_le kind=proved origin=conjecture
section
/- A family of subsets of [n] in which no two members (possibly equal) cover [n] has at most 2^(n−1) members — the family of complements is intersecting (Aᶜ ∩ Bᶜ = (A ∪ B)ᶜ ≠ ∅), has the same cardinality, and Set.Intersecting.card_le applies; alternatively 𝒜 contains at most one of each complementary pair. -/
theorem gr_set_union_ne_univ_card_le (n : ℕ) (𝒜 : Finset (Finset (Fin n)))
    (h : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ∪ B ≠ Finset.univ) : 2 * 𝒜.card ≤ 2 ^ n := by
  let 𝒜' : Finset (OrderDual (Finset (Fin n))) := 𝒜
  have hi : (𝒜' : Set (OrderDual (Finset (Fin n)))).Intersecting := by
    intro A hA B hB hd
    exact h A hA B hB (disjoint_iff.mp hd)
  simpa [𝒜', OrderDual] using hi.card_le
end

-- forge:entry p6_thm31_feet kind=proved origin=paper
section
/- Theorem 3.1, feet: C_k meets the X-axis at (σ_k^{-1},0) and (-σ_k,0) [Read as: the points of C_k on the axis are exactly these two.] -/
theorem p6_thm31_feet (k : ℤ) (x : ℝ) :
    (x + (k : ℝ) / 2) ^ 2 + (0 : ℝ) ^ 2 = ((k : ℝ) ^ 2 + 4) / 4 ↔
      (x = (((k : ℝ) + Real.sqrt ((k : ℝ) ^ 2 + 4)) / 2)⁻¹ ∨
        x = -(((k : ℝ) + Real.sqrt ((k : ℝ) ^ 2 + 4)) / 2)) := by
  have hs : Real.sqrt ((k : ℝ) ^ 2 + 4) ^ 2 = (k : ℝ) ^ 2 + 4 :=
    Real.sq_sqrt (by positivity)
  have hprod :
      (((k : ℝ) + Real.sqrt ((k : ℝ) ^ 2 + 4)) / 2) *
        ((Real.sqrt ((k : ℝ) ^ 2 + 4) - (k : ℝ)) / 2) = 1 := by
    nlinarith [hs]
  have hinv :
      (((k : ℝ) + Real.sqrt ((k : ℝ) ^ 2 + 4)) / 2)⁻¹ =
        (Real.sqrt ((k : ℝ) ^ 2 + 4) - (k : ℝ)) / 2 :=
    (eq_inv_of_mul_eq_one_right hprod).symm
  rw [hinv]
  constructor
  · intro h
    have hf :
        (x - (Real.sqrt ((k : ℝ) ^ 2 + 4) - (k : ℝ)) / 2) *
          (x + ((k : ℝ) + Real.sqrt ((k : ℝ) ^ 2 + 4)) / 2) = 0 := by
      nlinarith [hs]
    rcases mul_eq_zero.mp hf with hroot | hroot
    · left
      linarith
    · right
      linarith
  · rintro (rfl | rfl) <;> nlinarith [hs]
end

-- forge:entry p6_cor32_step kind=proved origin=paper
section
/- Proof of Corollary 3.2: x_{n+1}-x_n = k/(f_{2n+1} f_{2n+3}) -/
lemma p6_cor32_step_aux1 (k n : ℤ) : p6_kfib k (2 * n + 1) ≠ 0 := by
  intro hz
  have h := p6_lem23_eq9 k (2 * n)
  simp [hz, Int.negOnePow_two_mul] at h
  nlinarith [sq_nonneg (p6_kfib k (2 * n))]

theorem p6_cor32_step (k n : ℤ) :
    ((p6_kfib k (2 * (n + 1)) : ℤ) : ℝ) /
        ((p6_kfib k (2 * (n + 1) + 1) : ℤ) : ℝ) -
      ((p6_kfib k (2 * n) : ℤ) : ℝ) /
        ((p6_kfib k (2 * n + 1) : ℤ) : ℝ) =
      (k : ℝ) / (((p6_kfib k (2 * n + 1) : ℤ) : ℝ) *
        ((p6_kfib k (2 * n + 3) : ℤ) : ℝ)) := by
  have htwo : p6_kfib k 2 = k := by
    have h := (p6_kfib_def k 1).2.2
    simpa [(p6_kfib_def k 0).1, (p6_kfib_def k 0).2.1] using h
  have hdet : p6_kfib k (2 * n + 2) * p6_kfib k (2 * n + 1) -
      p6_kfib k (2 * n + 3) * p6_kfib k (2 * n) = k := by
    have h := p6_lem23_eq10 k (2 * n + 2) (2 * n)
    simpa only [Int.negOnePow_two_mul, Units.val_one, one_mul,
      show 2 * n + 2 + 1 = 2 * n + 3 by ring,
      show 2 * n + 2 - 2 * n = 2 by ring, htwo] using h
  have hdetR : (p6_kfib k (2 * n + 2) : ℝ) * (p6_kfib k (2 * n + 1) : ℝ) -
      (p6_kfib k (2 * n + 3) : ℝ) * (p6_kfib k (2 * n) : ℝ) = (k : ℝ) := by
    exact_mod_cast hdet
  have h1 : (p6_kfib k (2 * n + 1) : ℝ) ≠ 0 := by
    exact_mod_cast p6_cor32_step_aux1 k n
  have h3 : (p6_kfib k (2 * n + 3) : ℝ) ≠ 0 := by
    have h := p6_cor32_step_aux1 k (n + 1)
    rw [show 2 * (n + 1) + 1 = 2 * n + 3 by ring] at h
    exact_mod_cast h
  rw [show 2 * (n + 1) = 2 * n + 2 by ring,
    show 2 * n + 2 + 1 = 2 * n + 3 by ring]
  field_simp [h1, h3]
  nlinarith [hdetR]
end

-- forge:entry p6_cor32_mono kind=proved origin=paper
section
/- Corollary 3.2, monotonicity: the abscissa x_n=f_{2n}/f_{2n+1} of P_n is strictly increasing in n in Z -/
lemma p6_cor32_mono_aux1 (k n : ℤ) : 0 < p6_kfib k (2 * n + 1) := by
  have hs := p6_lem23_eq7 k n
  by_contra h
  have hz : p6_kfib k (2 * n + 1) ≤ 0 := le_of_not_gt h
  have h0 : p6_kfib k n = 0 := by
    nlinarith [sq_nonneg (p6_kfib k n), sq_nonneg (p6_kfib k (n + 1))]
  have h1 : p6_kfib k (n + 1) = 0 := by
    nlinarith [sq_nonneg (p6_kfib k n), sq_nonneg (p6_kfib k (n + 1))]
  obtain ⟨a, b, hab⟩ := p6_coprime k n
  simp [h0, h1] at hab

theorem p6_cor32_mono (k : ℤ) (hk : 1 ≤ k) : StrictMono (fun n : ℤ => ((p6_kfib k (2 * n) : ℤ) : ℝ) / ((p6_kfib k (2 * n + 1) : ℤ) : ℝ)) := by
  apply strictMono_int_of_lt_succ
  intro n
  have h0 := p6_cor32_mono_aux1 k n
  have h1 := p6_cor32_mono_aux1 k (n + 1)
  apply (div_lt_div_iff₀ (by exact_mod_cast h0) (by exact_mod_cast h1)).2
  have hf2 : p6_kfib k 2 = k := by
    have hrec := (p6_kfib_def k 1).2.2
    simpa [(p6_kfib_def k 0).1, (p6_kfib_def k 0).2.1] using hrec
  have hid := p6_lem23_eq10 k (2 * (n + 1)) (2 * n)
  have he : 2 * (n + 1) - 2 * n = (2 : ℤ) := by ring
  rw [Int.negOnePow_two_mul, he, hf2] at hid
  simp only [Units.val_one, one_mul] at hid
  have hlt : p6_kfib k (2 * n) * p6_kfib k (2 * (n + 1) + 1) <
      p6_kfib k (2 * (n + 1)) * p6_kfib k (2 * n + 1) := by
    nlinarith
  exact_mod_cast hlt
end

end Mathlib2
