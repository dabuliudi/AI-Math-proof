/- Mathlib2 分片 36（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0035
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry gr_triangle_free_sum_choose_two_le kind=proved origin=conjecture
section
/- In a triangle-free graph the number of 2-paths (cherries) is at most e(n−2)/2 — 2·C(d,2) + d = d², so the left side is ∑ deg² − 2e + 2e... precisely 2∑C(deg,2) + ∑deg = ∑deg²; with the handshake lemma ∑deg = 2e the claim is ∑deg² ≤ n·e, which is exactly: Uses Mathlib2.lib_simpleGraph_sum_degree_sq_le_card_mul_card_edgeFinset at the last step. -/
open scoped BigOperators

lemma gr_triangle_free_sum_choose_two_le_aux1 (n : ℕ) :
    2 * n.choose 2 + n = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ]
    simp only [Nat.choose_one_right, Nat.succ_eq_add_one]
    nlinarith

theorem gr_triangle_free_sum_choose_two_le
    (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : G.CliqueFree 3) :
    2 * ∑ v, (G.degree v).choose 2 + 2 * G.edgeFinset.card ≤
      Fintype.card V * G.edgeFinset.card := by
  calc
    2 * ∑ v, (G.degree v).choose 2 + 2 * G.edgeFinset.card =
        ∑ v, (2 * (G.degree v).choose 2 + G.degree v) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        G.sum_degrees_eq_twice_card_edges]
    _ = ∑ v, G.degree v ^ 2 := by
      apply Finset.sum_congr rfl
      intro v hv
      exact gr_triangle_free_sum_choose_two_le_aux1 (G.degree v)
    _ ≤ Fintype.card V * G.edgeFinset.card :=
      lib_simpleGraph_sum_degree_sq_le_card_mul_card_edgeFinset V G h
end

-- forge:entry gr_triangle_free_exists_degree_le_half kind=proved origin=conjecture
section
/- A triangle-free graph has a vertex of degree at most n/2 — take v of minimum degree (G.exists_minimal_degree_vertex) and d = G.minDegree; Uses Mathlib2.bld2_triangle_free_min_degree_le_half at step 2 with d ≤ deg w for all w. -/
theorem gr_triangle_free_exists_degree_le_half (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] (h : G.CliqueFree 3) : ∃ v, 2 * G.degree v ≤ Fintype.card V := by
  obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  refine ⟨v, ?_⟩
  rw [← hv]
  exact Mathlib2.bld2_triangle_free_min_degree_le_half V G h G.minDegree
    (fun w => G.minDegree_le_degree w)
end

-- forge:entry gr_triangle_free_compl_edges_lower kind=proved origin=conjecture
section
/- The complement of a triangle-free graph has at least n(n−2)/4 edges — e(G) + e(Gᶜ) = C(n,2) (SimpleGraph.card_edgeFinset_compl or a direct count), and Uses Mathlib2.bld_mantel_triangle_free at step 2 for 4e(G) ≤ n²; combine: 4e(Gᶜ) = 2n(n−1) − 4e(G) ≥ n² − 2n. -/
theorem gr_triangle_free_compl_edges_lower (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.CliqueFree 3) :
    Fintype.card V ^ 2 ≤ 4 * Gᶜ.edgeFinset.card + 2 * Fintype.card V := by
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
  have hmantel := Mathlib2.bld_mantel_triangle_free V G h
  nlinarith
end

-- forge:entry gr_self_compl_connected kind=proved origin=conjecture
section
/- A self-complementary graph is connected — by contradiction: if G is not connected then Uses Mathlib2.comb_compl_connected_of_not_connected at step 1 to get Gᶜ connected, and transport connectedness back along the isomorphism (SimpleGraph.Iso.connected_iff), contradiction. -/
theorem gr_self_compl_connected (V : Type) [Nonempty V] (G : SimpleGraph V)
    (h : Nonempty (SimpleGraph.Iso G Gᶜ)) : G.Connected := by
  classical
  by_contra hc
  obtain ⟨e⟩ := h
  exact hc (e.connected_iff.mpr (Mathlib2.comb_compl_connected_of_not_connected V G hc))
end

-- forge:entry gr_exists_clique_or_indep_three kind=proved origin=conjecture
section
/- Among any 6 vertices there is a clique or an independent set of size 3 — Uses Mathlib2.r3_ramsey_three_three at step 1 to get ¬CliqueFree 3 for G or Gᶜ; unfold CliqueFree/IsNClique to extract the 3-set, and translate a clique of Gᶜ into an independent set of G (SimpleGraph.isClique_compl / isIndepSet_iff). -/
theorem gr_exists_clique_or_indep_three (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : 6 ≤ Fintype.card V) :
    ∃ s : Finset V, s.card = 3 ∧
      (G.IsClique (s : Set V) ∨ G.IsIndepSet (s : Set V)) := by
  classical
  rcases Mathlib2.r3_ramsey_three_three V h G with hG | hGc
  · have hex : ∃ s : Finset V, G.IsNClique 3 s := by
      simpa only [SimpleGraph.CliqueFree, not_forall, not_not] using hG
    obtain ⟨s, hs⟩ := hex
    exact ⟨s, hs.card_eq, Or.inl hs.isClique⟩
  · have hex : ∃ s : Finset V, Gᶜ.IsNClique 3 s := by
      simpa only [SimpleGraph.CliqueFree, not_forall, not_not] using hGc
    obtain ⟨s, hs⟩ := hex
    exact ⟨s, hs.card_eq, Or.inr ((SimpleGraph.isClique_compl G).mp hs.isClique)⟩
end

-- forge:entry p6_kfib_def kind=proved origin=paper
section
/- Definition (Sec 2.2): f_0=0, f_1=1, f_{n+1}=k f_n+f_{n-1}; negative indices by f_{n-1}=f_{n+1}-k f_n [Checks that the library definition p6_kfib (entry (0,1) of M^n) satisfies the paper's defining recurrence for every integer n; this characterises it uniquely. Stated for all integers k (paper: k>=1).] -/
theorem p6_kfib_def (k n : ℤ) : p6_kfib k 0 = 0 ∧ p6_kfib k 1 = 1 ∧ p6_kfib k (n + 1) = k * p6_kfib k n + p6_kfib k (n - 1) := by
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![k, 1; 1, 0]
  have hu : IsUnit M.det := by
    simp [M, Matrix.det_fin_two]
  have hnext : M ^ (n + 1) = M * M ^ n := by
    simpa [add_comm] using Matrix.zpow_one_add hu n
  have hprev : M ^ n = M * M ^ (n - 1) := by
    have h := Matrix.zpow_one_add hu (n - 1)
    simpa using h
  have hentry : (M ^ n) 1 1 = (M ^ (n - 1)) 0 1 := by
    rw [hprev]
    simp [Matrix.mul_apply, Fin.sum_univ_two, M]
  refine ⟨?_, ?_, ?_⟩
  · simp [p6_kfib]
  · simp [p6_kfib]
  · change (M ^ (n + 1)) 0 1 = k * (M ^ n) 0 1 + (M ^ (n - 1)) 0 1
    rw [hnext]
    simpa [Matrix.mul_apply, Fin.sum_univ_two, M] using
      congrArg (fun t : ℤ => k * (M ^ n) 0 1 + t) hentry
end

-- forge:entry gr_acyclic_exists_degree_le_one kind=proved origin=conjecture
section
/- A nonempty finite forest has a vertex of degree at most 1 — contrapositive: if every vertex has degree ≥ 2 then Uses Mathlib2.comb_not_acyclic_of_two_le_degree at the only step. -/
theorem gr_acyclic_exists_degree_le_one
    (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [Nonempty V] (h : G.IsAcyclic) :
    ∃ v, G.degree v ≤ 1 := by
  classical
  by_contra hn
  have hdeg : ∀ v : V, 2 ≤ G.degree v := by
    intro v
    have hv : ¬ G.degree v ≤ 1 := by
      intro hv
      exact hn ⟨v, hv⟩
    omega
  exact (Mathlib2.comb_not_acyclic_of_two_le_degree V G hdeg) h
end

-- forge:entry p6_kfib_matrix kind=proved origin=paper
section
/- Eq. (3) (Sec 2.2): M^n = [[f_{n+1}, f_n],[f_n, f_{n-1}]], n in Z [Integer matrix power (zpow, inverse for negative n).] -/
theorem p6_kfib_matrix (k n : ℤ) :
    (!![k, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) ^ n =
      !![p6_kfib k (n + 1), p6_kfib k n;
         p6_kfib k n, p6_kfib k (n - 1)] := by
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![k, 1; 1, 0]
  have hu : IsUnit M.det := by
    norm_num [M, Matrix.det_fin_two]
  have hs : M.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [M]
  have h00 : (M ^ n) 0 0 = (M ^ (n + 1)) 0 1 := by
    simpa [M, Matrix.mul_apply, Fin.sum_univ_two] using
      (congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 0 1)
        (Matrix.zpow_add_one hu n)).symm
  have h10 : (M ^ n) 1 0 = (M ^ n) 0 1 :=
    (hs.zpow n).apply 0 1
  have h11 : (M ^ n) 1 1 = (M ^ (n - 1)) 0 1 := by
    have hn : 1 + (n - 1) = n := by omega
    simpa [hn, M, Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 1 1)
        (Matrix.zpow_one_add hu (n - 1))
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [p6_kfib, M] using h00
  · simp [p6_kfib, M]
  · simpa [p6_kfib, M] using h10
  · simpa [p6_kfib, M] using h11
end

-- forge:entry p6_kfib_neg kind=proved origin=paper
section
/- Sec 2.2 (unnumbered): f_{-m} = (-1)^{m+1} f_m [m taken as a natural number (the paper says 'by induction').] -/
theorem p6_kfib_neg (k : ℤ) (m : ℕ) : p6_kfib k (-(m : ℤ)) = (-1) ^ (m + 1) * p6_kfib k (m : ℤ) := by
  have hzero : p6_kfib k 0 = 0 := (p6_kfib_def k 0).1
  have hone : p6_kfib k 1 = 1 := (p6_kfib_def k 0).2.1
  induction m using Nat.twoStepInduction with
  | zero => simp [hzero]
  | one =>
      have h := (p6_kfib_def k 0).2.2
      norm_num [hzero, hone] at h ⊢
      linarith
  | more m ih0 ih1 =>
      have hp := (p6_kfib_def k ((m + 1 : ℕ) : ℤ)).2.2
      have hn := (p6_kfib_def k (-((m + 1 : ℕ) : ℤ))).2.2
      have ep1 : ((m + 1 : ℕ) : ℤ) + 1 = ((m + 2 : ℕ) : ℤ) := by
        push_cast
        ring
      have ep2 : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by
        push_cast
        ring
      have en1 : -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) := by
        push_cast
        ring
      have en2 : -((m + 1 : ℕ) : ℤ) - 1 = -((m + 2 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [ep1, ep2] at hp
      rw [en1, en2, ih0, ih1] at hn
      simp only [pow_succ] at hn ⊢
      rw [hp]
      nlinarith
end

-- forge:entry gr_acyclic_exists_leaf_of_edge kind=proved origin=conjecture
section
/- A finite forest with at least one edge has a leaf — let W = {v | deg v ≥ 1} (nonempty by he) and H = G.induce W, which is acyclic (map a cycle along the embedding) and has the same degrees as G on W since all neighbours of a vertex lie in W; if no vertex had degree 1 then all degrees in H are ≥ 2 and Uses Mathlib2.comb_not_acyclic_of_two_le_degree at this step on H for a contradiction. -/
theorem gr_acyclic_exists_leaf_of_edge (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.IsAcyclic)
    (he : G.edgeFinset.Nonempty) : ∃ v, G.degree v = 1 := by
  classical
  have hs : G.support.Nonempty := by
    by_contra hs
    apply (SimpleGraph.edgeFinset_nonempty.mp he)
    ext v w
    simp only [SimpleGraph.bot_adj, iff_false]
    intro hvw
    exact hs ⟨v, (G.mem_support).mpr ⟨w, hvw⟩⟩
  letI : Nonempty G.support := hs.to_subtype
  by_contra hn
  push_neg at hn
  apply comb_not_acyclic_of_two_le_degree G.support (G.induce G.support) ?_
    (h.induce G.support)
  intro v
  rw [G.degree_induce_support v]
  have hp : 0 < G.degree v := (G.degree_pos_iff_mem_support v).mpr v.property
  have hne := hn v.val
  omega
end

-- forge:entry gr_exists_indepSet_card_ge kind=proved origin=conjecture
section
/- A graph of maximum degree ≤ d has an independent set of size ≥ n/(d+1) — Uses Mathlib2.comb_colorable_of_degree_le at step 1 to get a colouring C : G.Coloring (Fin (d+1)); by pigeonhole (Finset.exists_lt_card_fiber_of... / sum of fibre sizes = n) some colour class has (d+1)·|class| ≥ n, and colour classes are independent. -/
theorem gr_exists_indepSet_card_ge (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (h : ∀ v, G.degree v ≤ d) :
    ∃ s : Finset V, G.IsIndepSet (s : Set V) ∧
      Fintype.card V ≤ (d + 1) * s.card := by
  classical
  by_cases hn : Fintype.card V = 0
  · refine ⟨∅, ?_, ?_⟩
    · simp [SimpleGraph.IsIndepSet]
    · simp [hn]
  obtain ⟨C⟩ := comb_colorable_of_degree_le V G d h
  have hbound : Fintype.card (Fin (d + 1)) *
      ((Fintype.card V - 1) / (d + 1)) < Fintype.card V := by
    rw [Fintype.card_fin]
    have hdiv := Nat.mul_div_le (Fintype.card V - 1) (d + 1)
    omega
  obtain ⟨c, hc⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card C hbound
  refine ⟨Finset.univ.filter (fun v => C v = c), ?_, ?_⟩
  · intro u hu v hv _ hadj
    exact C.valid hadj
      ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm)
  · have hb := (Nat.div_lt_iff_lt_mul (by omega : 0 < d + 1)).mp hc
    rw [Nat.mul_comm] at hb
    omega
end

-- forge:entry p6_addition kind=proved origin=paper
section
/- Proof of Lemma 2.3 (unnumbered): f_{m+n} = f_m f_{n+1} + f_{m-1} f_n and companion f_{m+n+1} = f_{m+1} f_{n+1} + f_m f_n [All integers m, n.] -/
theorem p6_addition (k m n : ℤ) :
    p6_kfib k (m + n) =
      p6_kfib k m * p6_kfib k (n + 1) + p6_kfib k (m - 1) * p6_kfib k n ∧
    p6_kfib k (m + n + 1) =
      p6_kfib k (m + 1) * p6_kfib k (n + 1) + p6_kfib k m * p6_kfib k n := by
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![k, 1; 1, 0]
  have hu : IsUnit M.det := by
    norm_num [M, Matrix.det_fin_two]
  have h := Matrix.zpow_add hu m n
  dsimp only [M] at h
  rw [p6_kfib_matrix k (m + n), p6_kfib_matrix k m, p6_kfib_matrix k n] at h
  constructor
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 1 0) h
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 0 0) h
end

-- forge:entry p6_lem23_eq6 kind=proved origin=paper
section
/- Lemma 2.3 (6): f_{2n} = f_n (f_{n-1} + f_{n+1}) -/
theorem p6_lem23_eq6 (k n : ℤ) :
    p6_kfib k (2 * n) = p6_kfib k n * (p6_kfib k (n - 1) + p6_kfib k (n + 1)) := by
  calc
    p6_kfib k (2 * n) =
        p6_kfib k n * p6_kfib k (n + 1) + p6_kfib k (n - 1) * p6_kfib k n := by
      simpa only [two_mul] using (p6_addition k n n).1
    _ = p6_kfib k n * (p6_kfib k (n - 1) + p6_kfib k (n + 1)) := by ring
end

-- forge:entry gr_ramsey_three_four_le_nine kind=proved origin=conjecture
section
/- R(3,4) ≤ 9 — reduce to card V = 9 (restrict to a 9-subset) and argue by contradiction: as in the 10-vertex bound every vertex has degree ≤ 3 (4 pairwise non-adjacent neighbours give an independent 4-set) and at most 5 non-neighbours (Uses Mathlib2.r3_ramsey_three_three at this step on 6 non-neighbours), so every degree is exactly 3; then ∑deg = 27 is odd, contradicting the handshake lemma. -/
theorem gr_ramsey_three_four_le_nine (V : Type) [Fintype V]
    (h : 9 ≤ Fintype.card V) (G : SimpleGraph V) :
    ¬ G.CliqueFree 3 ∨ ¬ Gᶜ.CliqueFree 4 := by
  classical
  by_contra! hbad
  obtain ⟨hG, hGc⟩ := hbad
  have hcard : Fintype.card V = 9 := by
    by_contra hn
    have h10 : 10 ≤ Fintype.card V := by omega
    rcases Mathlib2.gr_ramsey_three_four_le_ten V h10 G with ht | hi
    · exact ht hG
    · exact hi hGc
  have hd (v : V) : G.degree v = 3 := by
    have hu : G.degree v ≤ 3 := by
      by_contra hn
      obtain ⟨s, hs, hsize⟩ := Finset.exists_subset_card_eq
        (show 4 ≤ (G.neighborFinset v).card by
          rw [G.card_neighborFinset_eq_degree]
          omega)
      have hi : Gᶜ.IsClique (G.neighborSet v) :=
        (SimpleGraph.isClique_compl G).mpr
          (G.isIndepSet_neighborSet_of_triangleFree hG v)
      apply hGc s
      refine ⟨hi.subset ?_, hsize⟩
      intro x hx
      exact (G.mem_neighborFinset v x).mp (hs hx)
    have hcu : Gᶜ.degree v ≤ 5 := by
      by_contra hn
      let N : Set V := Gᶜ.neighborSet v
      let H : SimpleGraph N := G.induce N
      have hN : 6 ≤ Fintype.card N := by
        change 6 ≤ Fintype.card (Gᶜ.neighborSet v)
        rw [SimpleGraph.card_neighborSet_eq_degree]
        omega
      rcases Mathlib2.r3_ramsey_three_three N hN H with htri | hind
      · exact htri (hG.comap (SimpleGraph.Embedding.induce N).isContained)
      · obtain ⟨s, hs⟩ : ∃ s, Hᶜ.IsNClique 3 s := by
          simpa only [SimpleGraph.CliqueFree, not_forall, Classical.not_not] using hind
        let e : Hᶜ ↪g Gᶜ :=
          SimpleGraph.Embedding.complEquiv (SimpleGraph.Embedding.induce N)
        have hc : Gᶜ.IsNClique 3 (s.map e.toEmbedding) := by
          refine ⟨?_, by simpa only [Finset.card_map] using hs.card_eq⟩
          intro x hx y hy hxy
          obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
          obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
          exact e.map_adj_iff.mpr
            (hs.isClique ha hb (fun hab => hxy (congrArg e hab)))
        apply hGc (insert v (s.map e.toEmbedding))
        apply hc.insert
        intro x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
        exact a.property
    rw [G.degree_compl, hcard] at hcu
    omega
  have hsum : ∑ v : V, G.degree v = 27 := by
    simp [hd, hcard]
  have handshake := G.sum_degrees_eq_twice_card_edges
  omega
end

-- forge:entry p6_lem23_eq7 kind=proved origin=paper
section
/- Lemma 2.3 (7): f_{2n+1} = f_n^2 + f_{n+1}^2 -/
theorem p6_lem23_eq7 (k n : ℤ) :
    p6_kfib k (2 * n + 1) = p6_kfib k n ^ 2 + p6_kfib k (n + 1) ^ 2 := by
  simpa only [two_mul, pow_two, add_comm] using (p6_addition k n n).2
end

-- forge:entry p6_lem23_eq8 kind=proved origin=paper
section
/- Lemma 2.3 (8) Cassini: f_{n-1} f_{n+1} - f_n^2 = (-1)^n [(-1)^n for integer n is Mathlib's Int.negOnePow.] -/
theorem p6_lem23_eq8 (k n : ℤ) :
    p6_kfib k (n - 1) * p6_kfib k (n + 1) - p6_kfib k n ^ 2 =
      ((Int.negOnePow n : ℤˣ) : ℤ) := by
  have hstep (m : ℤ) :
      p6_kfib k (m + 1 - 1) * p6_kfib k (m + 1 + 1) -
          p6_kfib k (m + 1) ^ 2 =
        -(p6_kfib k (m - 1) * p6_kfib k (m + 1) - p6_kfib k m ^ 2) := by
    rw [show m + 1 - 1 = m by omega]
    rw [(p6_kfib_def k (m + 1)).2.2]
    rw [show m + 1 - 1 = m by omega]
    rw [(p6_kfib_def k m).2.2]
    ring
  induction n using Int.induction_on with
  | zero =>
      have h0 := (p6_kfib_def k 0).1
      have h1 := (p6_kfib_def k 0).2.1
      have hm := (p6_kfib_def k 0).2.2
      norm_num at hm ⊢
      rw [h0, h1] at hm ⊢
      norm_num at hm ⊢
      exact hm.symm
  | succ i ih =>
      rw [hstep, ih]
      simp [Int.negOnePow_succ]
  | pred i ih =>
      have hs := hstep (-(i : ℤ) - 1)
      have he : -(i : ℤ) - 1 + 1 = -(i : ℤ) := by omega
      rw [he] at hs
      have hsign :
          ((Int.negOnePow (-(i : ℤ) - 1) : ℤˣ) : ℤ) =
            -((Int.negOnePow (-(i : ℤ)) : ℤˣ) : ℤ) := by
        simp [Int.negOnePow_sub]
      rw [hsign, he]
      linarith
end

-- forge:entry gr_goodman_six_two_mono_triangles kind=proved origin=conjecture
section
/- Goodman: any 2-colouring of the edges of K₆ has at least two monochromatic triangles (strengthens Mathlib2.r3_ramsey_three_three, which gives one) — count non-monochromatic triangles: each has exactly two vertices where its two edges differ in colour, so their number is ½∑_v deg(v)(5 − deg(v)) ≤ ½·6·6 = 18, and 20 − 18 = 2. -/
lemma gr_goodman_six_two_mono_triangles_aux1 {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (s : Finset V) (hs : G.IsNClique 3 s)
    (hu : ∀ t, G.IsNClique 3 t → t = s) (hc : Gᶜ.CliqueFree 3) :
    G.IsClique ((s : Set V)ᶜ) := by
  classical
  intro x hx y hy hxy
  change x ∉ s at hx
  change y ∉ s at hy
  by_contra hnxy
  have one : ∀ v, v ∉ s → ∀ p ∈ s, ∀ q ∈ s, p ≠ q →
      ¬ (G.Adj p v ∧ G.Adj q v) := by
    rintro v hv p hp q hq hpq ⟨hpv, hqv⟩
    have hpqG : G.Adj p q := hs.isClique hp hq hpq
    have ht : G.IsNClique 3 {p, q, v} :=
      SimpleGraph.is3Clique_triple_iff.mpr ⟨hpqG, hpv, hqv⟩
    have heq := hu _ ht
    apply hv
    rw [← heq]
    simp
  have cover : ∀ p ∈ s, G.Adj p x ∨ G.Adj p y := by
    intro p hp
    by_contra hn
    push_neg at hn
    have hpx : p ≠ x := by
      intro heq
      subst p
      exact hx hp
    have hpy : p ≠ y := by
      intro heq
      subst p
      exact hy hp
    apply hc {p, x, y}
    exact SimpleGraph.is3Clique_triple_iff.mpr
      ⟨(SimpleGraph.compl_adj G p x).mpr ⟨hpx, hn.1⟩,
       (SimpleGraph.compl_adj G p y).mpr ⟨hpy, hn.2⟩,
       (SimpleGraph.compl_adj G x y).mpr ⟨hxy, hnxy⟩⟩
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp hs.card_eq
  have ha : a ∈ s := by simp [hset]
  have hb : b ∈ s := by simp [hset]
  have hc' : c ∈ s := by simp [hset]
  have ca := cover a ha
  have cb := cover b hb
  have cc := cover c hc'
  have xab := one x hx a ha b hb hab
  have xac := one x hx a ha c hc' hac
  have xbc := one x hx b hb c hc' hbc
  have yab := one y hy a ha b hb hab
  have yac := one y hy a ha c hc' hac
  have ybc := one y hy b hb c hc' hbc
  tauto

lemma gr_goodman_six_two_mono_triangles_aux2 (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : Fintype.card V = 6)
    (hn : ¬ G.CliqueFree 3)
    (hb : (G.cliqueFinset 3).card + (Gᶜ.cliqueFinset 3).card ≤ 1) : False := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : Finset V, G.IsNClique 3 s := by
    simpa only [SimpleGraph.CliqueFree, not_forall, not_not] using hn
  have hsmem : s ∈ G.cliqueFinset 3 := SimpleGraph.mem_cliqueFinset_iff.mpr hs
  have hpos : 0 < (G.cliqueFinset 3).card := Finset.card_pos.mpr ⟨s, hsmem⟩
  have hle : (G.cliqueFinset 3).card ≤ 1 := by omega
  have hzero : (Gᶜ.cliqueFinset 3).card = 0 := by omega
  have hc : Gᶜ.CliqueFree 3 :=
    SimpleGraph.cliqueFinset_eq_empty_iff.mp (Finset.card_eq_zero.mp hzero)
  have hu : ∀ t, G.IsNClique 3 t → t = s := by
    intro t ht
    exact Finset.card_le_one.mp hle t (SimpleGraph.mem_cliqueFinset_iff.mpr ht) s hsmem
  have hout := gr_goodman_six_two_mono_triangles_aux1 G s hs hu hc
  have hcard : (sᶜ : Finset V).card = 3 := by
    rw [Finset.card_compl, h, hs.card_eq]
  have ht : G.IsNClique 3 (sᶜ : Finset V) := by
    refine ⟨?_, hcard⟩
    simpa only [Finset.coe_compl] using hout
  have heq := hu _ ht
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < s.card by rw [hs.card_eq]; omega)
  have hxc : x ∈ (sᶜ : Finset V) := by rw [heq]; exact hx
  exact (Finset.mem_compl.mp hxc) hx

theorem gr_goodman_six_two_mono_triangles (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : Fintype.card V = 6) :
    2 ≤ (G.cliqueFinset 3).card + (Gᶜ.cliqueFinset 3).card := by
  classical
  by_contra hn
  have hb : (G.cliqueFinset 3).card + (Gᶜ.cliqueFinset 3).card ≤ 1 := by omega
  rcases Mathlib2.r3_ramsey_three_three V (by omega) G with hG | hGc
  · exact gr_goodman_six_two_mono_triangles_aux2 V G h hG hb
  · apply gr_goodman_six_two_mono_triangles_aux2 V Gᶜ h hGc
    simpa only [compl_compl, Nat.add_comm] using hb
end

-- forge:entry gr_triangle_count_lower_bound kind=proved origin=conjecture
section
/- Quantitative Mantel (Moon–Moser/Nordhaus–Stewart): a graph has at least e(4e − n²)/(3n) triangles; for triangle-free G this recovers Mathlib2.bld_mantel_triangle_free — for each edge uv the number of triangles on it is ≥ deg u + deg v − n; summing over edges gives 3t ≥ ∑deg² − n·e, and Cauchy–Schwarz ∑deg² ≥ (2e)²/n finishes. -/
open Finset

lemma gr_triangle_count_lower_bound_aux1 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    G.degree u + G.degree v ≤ Fintype.card V + (G.neighborFinset u ∩ G.neighborFinset v).card := by
  have h := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
  have hle := Finset.card_le_univ (G.neighborFinset u ∪ G.neighborFinset v)
  rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree] at h
  omega

lemma gr_triangle_count_lower_bound_aux2 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ u, ∑ v ∈ G.neighborFinset u, (G.neighborFinset u ∩ G.neighborFinset v).card
      ≤ 6 * (G.cliqueFinset 3).card := by
  classical
  let T : Finset (V × V × V) := Finset.univ.filter
    (fun p => G.Adj p.1 p.2.1 ∧ G.Adj p.1 p.2.2 ∧ G.Adj p.2.1 p.2.2)
  have hT : T.card = ∑ u, ∑ v ∈ G.neighborFinset u,
      (G.neighborFinset u ∩ G.neighborFinset v).card := by
    simp only [T, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type,
      SimpleGraph.neighborFinset_eq_filter, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    refine Finset.sum_congr rfl (fun v _ => ?_)
    by_cases huv : G.Adj u v <;> simp [huv]
    congr 1
    ext w
    simp
  have hmap : (T : Set (V × V × V)).MapsTo
      (fun p => ({p.1, p.2.1, p.2.2} : Finset V)) (G.cliqueFinset 3) := by
    intro p hp
    exact SimpleGraph.mem_cliqueFinset_iff.2
      (SimpleGraph.is3Clique_triple_iff.2 (Finset.mem_filter.1 hp).2)
  have hfiber (s : Finset V) (hs : s ∈ G.cliqueFinset 3) :
      (T.filter (fun p => ({p.1, p.2.1, p.2.2} : Finset V) = s)).card ≤ 6 := by
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ :=
      SimpleGraph.is3Clique_iff.1 (SimpleGraph.mem_cliqueFinset_iff.1 hs)
    let S : Finset (V × V × V) :=
      {(a,b,c), (a,c,b), (b,a,c), (b,c,a), (c,a,b), (c,b,a)}
    have hsub : T.filter (fun p => ({p.1, p.2.1, p.2.2} : Finset V) = {a,b,c}) ⊆ S := by
      rintro ⟨x,y,z⟩ hp
      obtain ⟨hp, he⟩ := Finset.mem_filter.1 hp
      have hx : x ∈ ({a,b,c} : Finset V) := he ▸ (by simp)
      have hy : y ∈ ({a,b,c} : Finset V) := he ▸ (by simp)
      have hz : z ∈ ({a,b,c} : Finset V) := he ▸ (by simp)
      have ha := (Finset.mem_filter.1 hp).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz
      rcases hx with rfl | rfl | rfl <;>
        rcases hy with rfl | rfl | rfl <;>
        rcases hz with rfl | rfl | rfl <;> simp_all [S]
    calc
      _ ≤ S.card := Finset.card_le_card hsub
      _ = 6 := by simp [S, hab.ne, hac.ne, hbc.ne, hab.ne.symm, hac.ne.symm, hbc.ne.symm]
  rw [← hT, Finset.card_eq_sum_card_fiberwise hmap]
  calc
    _ ≤ ∑ s ∈ G.cliqueFinset 3, 6 := Finset.sum_le_sum hfiber
    _ = _ := by simp [mul_comm]

lemma gr_triangle_count_lower_bound_aux3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v, G.degree v ^ 2 ≤ Fintype.card V * G.edgeFinset.card + 3 * (G.cliqueFinset 3).card := by
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
      ≤ ∑ u, ∑ v ∈ G.neighborFinset u,
        (Fintype.card V + (G.neighborFinset u ∩ G.neighborFinset v).card) := by
    exact Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ =>
      gr_triangle_count_lower_bound_aux1 G u v))
  have h2 : ∑ u, ∑ v ∈ G.neighborFinset u, (G.degree u + G.degree v)
      = 2 * ∑ v, G.degree v ^ 2 := by
    simp_rw [Finset.sum_add_distrib]
    rw [key, two_mul]
    congr 1
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree, sq]
  have h3 : ∑ u, ∑ v ∈ G.neighborFinset u,
        (Fintype.card V + (G.neighborFinset u ∩ G.neighborFinset v).card)
      = (2 * G.edgeFinset.card) * Fintype.card V +
        ∑ u, ∑ v ∈ G.neighborFinset u, (G.neighborFinset u ∩ G.neighborFinset v).card := by
    simp_rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
      SimpleGraph.card_neighborFinset_eq_degree]
    rw [← Finset.sum_mul, G.sum_degrees_eq_twice_card_edges]
  rw [h2, h3] at h1
  have h4 := gr_triangle_count_lower_bound_aux2 G
  nlinarith

theorem gr_triangle_count_lower_bound (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    4 * G.edgeFinset.card ^ 2 ≤ Fintype.card V ^ 2 * G.edgeFinset.card +
      3 * Fintype.card V * (G.cliqueFinset 3).card := by
  have hc : (∑ v, G.degree v) ^ 2 ≤ Fintype.card V * ∑ v, G.degree v ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset V))
      (f := fun v => G.degree v))
  rw [G.sum_degrees_eq_twice_card_edges] at hc
  have hb := Nat.mul_le_mul_left (Fintype.card V) (gr_triangle_count_lower_bound_aux3 G)
  nlinarith
end

-- forge:entry p6_lem23_eq9 kind=proved origin=paper
section
/- Lemma 2.3 (9): f_{n+1}^2 - k f_n f_{n+1} - f_n^2 = (-1)^n -/
theorem p6_lem23_eq9 (k n : ℤ) : p6_kfib k (n + 1) ^ 2 - k * p6_kfib k n * p6_kfib k (n + 1) - p6_kfib k n ^ 2 = ((Int.negOnePow n : ℤˣ) : ℤ) := by
  have hrec : p6_kfib k (n + 1) - k * p6_kfib k n = p6_kfib k (n - 1) := by
    linarith [(p6_kfib_def k n).2.2]
  calc
    p6_kfib k (n + 1) ^ 2 - k * p6_kfib k n * p6_kfib k (n + 1) - p6_kfib k n ^ 2 =
        (p6_kfib k (n + 1) - k * p6_kfib k n) * p6_kfib k (n + 1) - p6_kfib k n ^ 2 := by ring
    _ = p6_kfib k (n - 1) * p6_kfib k (n + 1) - p6_kfib k n ^ 2 := by rw [hrec]
    _ = ((Int.negOnePow n : ℤˣ) : ℤ) := p6_lem23_eq8 k n
end

-- forge:entry p6_lem23_eq10 kind=proved origin=paper
section
/- Lemma 2.3 (10) d'Ocagne: f_a f_{b+1} - f_{a+1} f_b = (-1)^b f_{a-b} -/
theorem p6_lem23_eq10 (k a b : ℤ) :
    p6_kfib k a * p6_kfib k (b + 1) - p6_kfib k (a + 1) * p6_kfib k b =
      ((Int.negOnePow b : ℤˣ) : ℤ) * p6_kfib k (a - b) := by
  obtain ⟨ha, ha1⟩ := p6_addition k (a - b) b
  rw [sub_add_cancel] at ha ha1
  rw [ha, ha1, (p6_kfib_def k (a - b)).2.2]
  calc
    _ = (p6_kfib k (b + 1) ^ 2 -
          k * p6_kfib k b * p6_kfib k (b + 1) - p6_kfib k b ^ 2) *
          p6_kfib k (a - b) := by ring
    _ = _ := by rw [p6_lem23_eq9 k b]
end

end Mathlib2
