/- Mathlib2 分片 20（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0019
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry lib_matrix_mul_rank_le_add_rank_pow kind=proved origin=conjecture
section
/- Iterated Sylvester rank inequality for powers of a square matrix over a field: j * rank A ≤ (j - 1) * n + rank (A^j) (so A^j = 0 forces rank A ≤ (j-1)n/j). Promoted from Mathlib2.bld_nilpotent_rank_bound_aux1 (stated there with j+1). -/
theorem lib_matrix_mul_rank_le_add_rank_pow (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (j : ℕ) : j * Matrix.rank A ≤ (j - 1) * Fintype.card ι + Matrix.rank (A ^ j) := by
  cases j with
  | zero => simp
  | succ j => simpa using Mathlib2.bld_nilpotent_rank_bound_aux1 K ι A j
end

-- forge:entry lib_pisano_dvd_iff_period kind=proved origin=conjecture
section
/- The positive periods of the Fibonacci sequence mod m are exactly the positive multiples of the Pisano period p3_pisano m (the least period divides every period, and every multiple of it is a period). Promoted from Mathlib2.bld2_pisano_fib_dvd_four_mul_aux1 and bld2_pisano_fib_odd_eq_aux1 (same argument also inline in p3_prop2). -/
theorem lib_pisano_dvd_iff_period (m N : ℕ) (hN : 0 < N) : p3_pisano m ∣ N ↔ ∀ i : ℕ, Nat.fib (i + N) ≡ Nat.fib i [MOD m] := by
  constructor
  · rintro ⟨k, rfl⟩
    have hp : 0 < p3_pisano m :=
      Nat.pos_of_ne_zero (fun h => by rw [h, zero_mul] at hN; exact lt_irrefl _ hN)
    have hne : {k : ℕ | 0 < k ∧ ∀ i : ℕ, Nat.fib (i + k) ≡ Nat.fib i [MOD m]}.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have h0 : p3_pisano m = 0 := by
        unfold p3_pisano
        rw [h]
        exact Nat.sInf_empty
      omega
    have hP : p3_pisano m ∈ {k : ℕ | 0 < k ∧ ∀ i : ℕ, Nat.fib (i + k) ≡ Nat.fib i [MOD m]} := by
      unfold p3_pisano
      exact Nat.sInf_mem hne
    obtain ⟨-, hPper⟩ := hP
    clear hN
    induction k with
    | zero => intro i; simp [Nat.ModEq.refl]
    | succ q ih =>
      intro i
      have e : i + p3_pisano m * (q + 1) = (i + p3_pisano m * q) + p3_pisano m := by ring
      rw [e]
      exact (hPper _).trans (ih i)
  · exact Mathlib2.bld2_pisano_fib_dvd_four_mul_aux1 m N hN
end

-- forge:entry lib_fib_period_iff kind=proved origin=conjecture
section
/- Fibonacci period criterion: m is a period of the Fibonacci sequence modulo N iff F_m ≡ 0 and F_(m+1) ≡ 1 (mod N). Promoted from Mathlib2.p3_aux_period_aux2 / p3_aux_period_aux3 (the same two-term induction is re-done in p3_cor1_aux3/aux4). -/
theorem lib_fib_period_iff (N m : ℕ) : (∀ i : ℕ, Nat.fib (i + m) ≡ Nat.fib i [MOD N]) ↔ Nat.fib m ≡ 0 [MOD N] ∧ Nat.fib (m + 1) ≡ 1 [MOD N] := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    rw [zero_add, Nat.fib_zero] at h0
    rw [add_comm, Nat.fib_one] at h1
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩ i
    exact Mathlib2.p3_aux_period_aux2 N m h0 h1 i
end

-- forge:entry lib_fib_sq_modEq_neg_one_pow kind=proved origin=conjecture
section
/- Cassini's identity as a congruence: F_n^2 ≡ (-1)^(n+1) modulo F_(n+1); in particular F_n^4 ≡ 1 (mod F_(n+1)). Sharpens Mathlib2.p3_cor1_aux1 / p3_cor1_aux2 (squared Cassini), which re-derive Cassini although Mathlib2.an_cassini_int exists (also re-proved as p3_aux_period_aux1 and r3_fib_iff_five_sq_pm_four_is_square_s1h1). -/
theorem lib_fib_sq_modEq_neg_one_pow (n : ℕ) : (Nat.fib n : ℤ) ^ 2 ≡ (-1) ^ (n + 1) [ZMOD (Nat.fib (n + 1) : ℤ)] := by
  have hc := Mathlib2.an_cassini_int n
  rw [Int.modEq_iff_dvd]
  refine ⟨(Nat.fib n : ℤ) - Nat.fib (n + 1), ?_⟩
  have h2 : (Nat.fib (n + 2) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by
    rw [Nat.fib_add_two]; push_cast; ring
  rw [← hc, h2]; ring
end

-- forge:entry lib_simpleGraph_sum_degree_sq_le_card_mul_card_edgeFinset kind=proved origin=conjecture
section
/- In a triangle-free graph on n vertices with e edges the sum of squared degrees is at most n * e (sum deg u + deg v ≤ n over the edges); this is the key step of Mantel's theorem. Promoted from Mathlib2.bld2_mantel_equality_regular_aux1 (also proved inline in bld_mantel_triangle_free); generalised to an arbitrary universe. -/
theorem lib_simpleGraph_sum_degree_sq_le_card_mul_card_edgeFinset_aux1 (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.CliqueFree 3) (u v : V) (huv : G.Adj u v) : G.degree u + G.degree v ≤ Fintype.card V := by
  have hd : Disjoint (G.neighborFinset u) (G.neighborFinset v) := by
    rw [Finset.disjoint_left]
    intro w hwu hwv
    rw [SimpleGraph.mem_neighborFinset] at hwu hwv
    exact h {u, v, w} (SimpleGraph.is3Clique_iff.mpr ⟨u, v, w, huv, hwu, hwv, rfl⟩)
  unfold SimpleGraph.degree
  rw [← Finset.card_union_of_disjoint hd]
  exact Finset.card_le_univ _

theorem lib_simpleGraph_sum_degree_sq_le_card_mul_card_edgeFinset (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.CliqueFree 3) : ∑ v, G.degree v ^ 2 ≤ Fintype.card V * G.edgeFinset.card := by
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
          exact lib_simpleGraph_sum_degree_sq_le_card_mul_card_edgeFinset_aux1 V G h u v
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
end

-- forge:entry lib_mul_pow_mul_sub_le_pow_succ_sub_pow_succ kind=proved origin=conjecture
section
/- Two-sided tangent-line (generalised Bernoulli / mean-value) inequality for powers in a linearly ordered commutative ring: for a, b ≥ 0, (m+1) a^m (b - a) ≤ b^(m+1) - a^(m+1) ≤ (m+1) b^m (b - a). Promoted from Mathlib2.gen_an_amgm_finset_ordered_ring_aux1 (the left inequality). -/
theorem lib_mul_pow_mul_sub_le_pow_succ_sub_pow_succ (R : Type*) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (a b : R) (ha : 0 ≤ a) (hb : 0 ≤ b) (m : ℕ) : ((m : R) + 1) * a ^ m * (b - a) ≤ b ^ (m + 1) - a ^ (m + 1) ∧ b ^ (m + 1) - a ^ (m + 1) ≤ ((m : R) + 1) * b ^ m * (b - a) := by
  constructor
  · have h := Mathlib2.gen_an_amgm_finset_ordered_ring_aux1 R a b ha hb m
    linarith
  · have h := Mathlib2.gen_an_amgm_finset_ordered_ring_aux1 R b a hb ha m
    have e : ((m : R) + 1) * b ^ m * (a - b) = -(((m : R) + 1) * b ^ m * (b - a)) := by ring
    linarith
end

-- forge:entry lib_expanding_iterate_dist_le kind=proved origin=conjecture
section
/- Iterates of a distance non-decreasing (expanding) self-map of a pseudometric space are again expanding: dist x y ≤ dist (f^[k] x) (f^[k] y). Promoted from Mathlib2.top_expanding_compact_isometry_aux1 (the isometry analogue is re-derived in top_isometry_compact_surjective); generalised from metric to pseudometric spaces. -/
theorem lib_expanding_iterate_dist_le {X : Type*} [PseudoMetricSpace X] (f : X → X) (hf : ∀ x y : X, dist x y ≤ dist (f x) (f y)) (k : ℕ) (x y : X) : dist x y ≤ dist (f^[k] x) (f^[k] y) := by
  induction k generalizing x y with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact (hf x y).trans (ih (f x) (f y))
end

-- forge:entry lib_compactSpace_exists_lt_and_dist_lt kind=proved origin=conjecture
section
/- Pigeonhole principle in a compact pseudometric space: every sequence has two terms u m, u n with m < n at distance < ε (take a convergent subsequence). Promoted from Mathlib2.top_expanding_compact_isometry_aux2 (the same argument is used in top_isometry_compact_surjective); generalised from metric to pseudometric spaces. -/
theorem lib_compactSpace_exists_lt_and_dist_lt {Y : Type*} [PseudoMetricSpace Y] [CompactSpace Y] (u : ℕ → Y) (ε : ℝ) (hε : 0 < ε) : ∃ m n : ℕ, m < n ∧ dist (u m) (u n) < ε := by
  obtain ⟨a, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq u
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) (half_pos hε)
  refine ⟨φ N, φ (N + 1), hφ (Nat.lt_succ_self N), ?_⟩
  have h1 := hN N le_rfl
  have h2 := hN (N + 1) (Nat.le_succ N)
  simp only [Function.comp_apply] at h1 h2
  calc dist (u (φ N)) (u (φ (N + 1))) ≤ dist (u (φ N)) a + dist a (u (φ (N + 1))) := dist_triangle _ _ _
    _ = dist (u (φ N)) a + dist (u (φ (N + 1))) a := by rw [dist_comm a]
    _ < ε := by linarith
end

-- forge:entry lib_list_exists_perm_isChain_of_pairwise_or kind=proved origin=conjecture
section
/- Rédei's theorem in list form (every tournament has a Hamiltonian path): a duplicate-free list whose distinct elements are pairwise r-comparable (r a b ∨ r b a) can be permuted into an r-chain. Promoted from Mathlib2.comb_tournament_hamiltonian_path_aux2; generalised to an arbitrary universe. -/
theorem lib_list_exists_perm_isChain_of_pairwise_or_aux1 {α : Type*} (r : α → α → Prop) (a : α) (l : List α)
    (hl : ∀ b ∈ l, r a b ∨ r b a) (hc : List.IsChain r l) :
    ∃ l' : List α, l'.Perm (a :: l) ∧ List.IsChain r l' ∧ (∀ x ∈ l'.head?, x = a ∨ x ∈ l.head?) := by
  induction l with
  | nil => exact ⟨[a], List.Perm.refl _, List.isChain_singleton a, by simp⟩
  | cons b t ih =>
    by_cases hab : r a b
    · exact ⟨a :: b :: t, List.Perm.refl _, List.isChain_cons_cons.2 ⟨hab, hc⟩, by simp⟩
    · have hba : r b a := (hl b List.mem_cons_self).resolve_left hab
      have hc2 := List.isChain_cons.1 hc
      obtain ⟨t', hp, hc', hh⟩ := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) hc2.2
      refine ⟨b :: t', (hp.cons b).trans (List.Perm.swap a b t), List.isChain_cons.2 ⟨?_, hc'⟩, by simp⟩
      intro y hy
      rcases hh y hy with h1 | h1
      · rw [h1]; exact hba
      · exact hc2.1 y h1

theorem lib_list_exists_perm_isChain_of_pairwise_or {α : Type*} (r : α → α → Prop) (l : List α) (hnd : l.Nodup) (hl : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b ∨ r b a) : ∃ l' : List α, l'.Perm l ∧ List.IsChain r l' := by
  induction l with
  | nil => exact ⟨[], List.Perm.refl _, List.isChain_nil⟩
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨t', hp, hc⟩ := ih hnd.2 (fun x hx y hy => hl x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
    obtain ⟨l', hp', hc', -⟩ := lib_list_exists_perm_isChain_of_pairwise_or_aux1 r a t' (fun b hb => by
      have hbt : b ∈ t := hp.mem_iff.1 hb
      exact hl a List.mem_cons_self b (List.mem_cons_of_mem _ hbt) (fun e => hnd.1 (e ▸ hbt))) hc
    exact ⟨l', hp'.trans (hp.cons a), hc'⟩
end

-- forge:entry lib_finset_exists_cut_sum_le_four_mul kind=proved origin=conjecture
section
/- Weighted max-cut bound: for a symmetric, zero-diagonal weight f : V → V → ℕ on a finset S there is a cut (s, S \ s) carrying at least half of the total weight (the ordered-pair sum over S × S is ≤ 4 × the one-directional cut sum). Promoted from Mathlib2.comb_exists_cut_half_edges_aux1; generalised to an arbitrary universe. -/
theorem lib_finset_exists_cut_sum_le_four_mul (V : Type*) [DecidableEq V] (f : V → V → ℕ) (hsym : ∀ u v, f u v = f v u) (hirr : ∀ u, f u u = 0) (S : Finset V) : ∃ s : Finset V, s ⊆ S ∧ (∑ u ∈ S, ∑ v ∈ S, f u v) ≤ 4 * ∑ u ∈ s, ∑ v ∈ S \ s, f u v := by
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
end

-- forge:entry bld3_pell_five_neg_one_solutions kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_fib_odd_index_iff_five_sq_sub_four and Mathlib2.bld2_lucas_sq_sub_five_fib_sq: (2x)^2 + 4 = 5 (2y)^2, so 2y = fib (2m+1) and 2x = L_(2m+1) by the odd-index description and the Lucas–Fibonacci identity; fib (2m+1) even forces 3 ∣ 2m+1, i.e. 2m+1 = 6n+3. -/
theorem bld3_pell_five_neg_one_solutions (x y : ℕ) (h : x ^ 2 + 1 = 5 * y ^ 2) : ∃ n : ℕ, 2 * y = Nat.fib (6 * n + 3) ∧ 2 * x = p3_lucas (6 * n + 3) := by
  obtain ⟨m, hm⟩ := (bld2_fib_odd_index_iff_five_sq_sub_four (2 * y)).mpr ⟨2 * x, by nlinarith⟩
  have hL := bld2_lucas_sq_sub_five_fib_sq (2 * m + 1)
  rw [← hm] at hL
  have hpow : ((-1 : ℤ)) ^ (2 * m + 1) = -1 := by
    rw [pow_succ, pow_mul]; norm_num
  rw [hpow] at hL
  have hx : 2 * x = p3_lucas (2 * m + 1) := by
    have h1 : ((p3_lucas (2 * m + 1) : ℕ) : ℤ) ^ 2 = ((2 * x : ℕ) : ℤ) ^ 2 := by
      have h' : ((x : ℤ)) ^ 2 + 1 = 5 * (y : ℤ) ^ 2 := by exact_mod_cast h
      push_cast at hL ⊢
      nlinarith
    have h2 : (p3_lucas (2 * m + 1)) ^ 2 = (2 * x) ^ 2 := by exact_mod_cast h1
    exact ((Nat.pow_left_injective (by norm_num : (2:ℕ) ≠ 0)) h2).symm
  have h3 : 3 ∣ 2 * m + 1 := by
    have hg := Nat.fib_gcd 3 (2 * m + 1)
    have h2 : Nat.fib 3 ∣ Nat.fib (2 * m + 1) := by
      rw [← hm]; exact ⟨y, by norm_num [Nat.fib]⟩
    rw [Nat.gcd_eq_left h2] at hg
    rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 (2 * m + 1)) with h1 | h1
    · rw [h1] at hg; norm_num [Nat.fib] at hg
    · rw [← h1]; exact Nat.gcd_dvd_right _ _
  obtain ⟨j, hj⟩ := h3
  obtain ⟨n, rfl⟩ : ∃ n, j = 2 * n + 1 := ⟨j / 2, by omega⟩
  have e : 2 * m + 1 = 6 * n + 3 := by omega
  rw [e] at hm hx
  exact ⟨n, hm, hx⟩
end

-- forge:entry bld3_rank_pow_card_stabilizes kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_rank_pow_convex: Fitting-type stabilisation: the drops d_k = rank A^k - rank A^(k+1) are non-negative and, by convexity, non-increasing; if d_n > 0 with n = card ι then d_0,...,d_n ≥ 1 and rank A^0 = n ≥ n + 1, contradiction. -/
theorem bld3_rank_pow_card_stabilizes_aux1 (f : ℕ → ℕ)
    (hconv : ∀ k, 2 * f (k + 1) ≤ f k + f (k + 2)) (k j : ℕ)
    (h : f (k + j + 1) < f (k + j)) : f (k + 1) < f k := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    apply ih
    have := hconv (k + j)
    have e1 : k + (j + 1) + 1 = k + j + 2 := by ring
    have e2 : k + (j + 1) = k + j + 1 := by ring
    rw [e1, e2] at h
    omega

theorem bld3_rank_pow_card_stabilizes_aux2 (f : ℕ → ℕ)
    (hconv : ∀ k, 2 * f (k + 1) ≤ f k + f (k + 2)) (m : ℕ)
    (h : f (m + 1) < f m) : f (m + 1) + (m + 1) ≤ f 0 := by
  have key : ∀ k, k ≤ m + 1 → f k + k ≤ f 0 := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      obtain ⟨j, rfl⟩ : ∃ j, m = k + j := ⟨m - k, by omega⟩
      have := bld3_rank_pow_card_stabilizes_aux1 f hconv k j h
      omega
  exact key (m + 1) le_rfl

theorem bld3_rank_pow_card_stabilizes (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) : Matrix.rank (A ^ (Fintype.card ι + 1)) = Matrix.rank (A ^ Fintype.card ι) := by
  apply le_antisymm
  · rw [pow_succ]
    exact Matrix.rank_mul_le_left _ _
  · by_contra hlt
    push_neg at hlt
    have := bld3_rank_pow_card_stabilizes_aux2 (fun k => Matrix.rank (A ^ k))
      (fun k => bld2_rank_pow_convex K ι A k) (Fintype.card ι) hlt
    simp only [pow_zero, Matrix.rank_one] at this
    omega
end

-- forge:entry bld3_pell_five_neg_four_solutions_lucas kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_fib_odd_index_iff_five_sq_sub_four and Mathlib2.bld2_lucas_sq_sub_five_fib_sq: the odd-index characterisation gives y = fib (2n+1) (choose n with the right value; fib 1 = fib 2 only matters for y = 1 where n = 0 works), and L^2 = 5 F^2 - 4 at odd index forces x = p3_lucas (2n+1) by injectivity of squaring on ℕ. -/
theorem bld3_pell_five_neg_four_solutions_lucas (x y : ℕ) (h : x ^ 2 + 4 = 5 * y ^ 2) : ∃ n : ℕ, y = Nat.fib (2 * n + 1) ∧ x = p3_lucas (2 * n + 1) := by
  obtain ⟨m, hm⟩ := (bld2_fib_odd_index_iff_five_sq_sub_four y).mpr ⟨x, h⟩
  have hL := bld2_lucas_sq_sub_five_fib_sq (2 * m + 1)
  rw [← hm] at hL
  have hpow : ((-1 : ℤ)) ^ (2 * m + 1) = -1 := by
    rw [pow_succ, pow_mul]; norm_num
  rw [hpow] at hL
  refine ⟨m, hm, ?_⟩
  have h1 : ((p3_lucas (2 * m + 1) : ℕ) : ℤ) ^ 2 = ((x : ℕ) : ℤ) ^ 2 := by
    have h' : ((x : ℤ)) ^ 2 + 4 = 5 * (y : ℤ) ^ 2 := by exact_mod_cast h
    linarith
  have h2 : (p3_lucas (2 * m + 1)) ^ 2 = x ^ 2 := by exact_mod_cast h1
  exact ((Nat.pow_left_injective (by norm_num : (2:ℕ) ≠ 0)) h2).symm
end

-- forge:entry bld3_sqrt_two_rec_viete_prod_le kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_sqrt_two_rec_viete_prod and Mathlib2.bld2_sqrt_two_rec_viete_prod_gt: by the finite Viète product the product equals 1/(2^n sin x) with x = π/2^(n+1); sin x ≥ x - x^3/6 and 1/(1-t) ≤ 1 + 2t for t = x^2/6 ≤ 1/2 give the explicit O(4^-n) upper bound matching the library lower bound 2/π. -/
theorem bld3_sqrt_two_rec_viete_prod_le (a : ℕ → ℝ) (h0 : a 0 = 0) (h : ∀ n : ℕ, a (n + 1) = Real.sqrt (2 + a n)) (n : ℕ) : ∏ i ∈ Finset.range n, a (i + 1) / 2 ≤ 2 / Real.pi + 2 * Real.pi / (3 * 4 ^ (n + 1)) := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_le_four
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Finset.range_zero, Finset.prod_empty]
    rw [show (2:ℝ) / Real.pi + 2 * Real.pi / (3 * 4 ^ (0 + 1)) = (12 + Real.pi ^ 2) / (6 * Real.pi) by
      field_simp; ring]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (Real.pi - 3)]
  have key := Mathlib2.bld_sqrt_two_rec_viete_prod a h0 h n
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have h2n2 : (2 : ℝ) ≤ 2 ^ n := by
    calc (2:ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  set x := Real.pi / 2 ^ (n + 1) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one (by positivity), pow_succ]
    nlinarith
  have hs := Real.sin_gt_sub_cube hx0
  have hspos : 0 < Real.sin x := by
    have : 0 ≤ x - x ^ 3 / 6 := by nlinarith [mul_pos hx0 hx0, pow_le_one₀ hx0.le hx1 (n := 2)]
    linarith
  have hS_pos : 0 < 2 ^ n * Real.sin x := mul_pos h2n hspos
  have e1 : (2 : ℝ) ^ n = Real.pi / (2 * x) := by
    rw [hx, pow_succ]; field_simp
  have e2 : (2:ℝ) / Real.pi + 2 * Real.pi / (3 * 4 ^ (n + 1)) = 2 / Real.pi * (1 + x ^ 2 / 3) := by
    rw [hx, show (4:ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm 2 (n+1), pow_mul]
    field_simp
  have hmain : 1 ≤ (2 / Real.pi + 2 * Real.pi / (3 * 4 ^ (n + 1))) * (2 ^ n * Real.sin x) := by
    rw [e2, e1]
    have : 2 / Real.pi * (1 + x ^ 2 / 3) * (Real.pi / (2 * x) * Real.sin x) = (1 + x ^ 2 / 3) * Real.sin x / x := by
      field_simp
    rw [this, le_div_iff₀ hx0]
    have h5 : x ^ 2 ≤ 1 := pow_le_one₀ hx0.le hx1
    have h6 : 0 ≤ x ^ 3 * (1 - x ^ 2) := mul_nonneg (by positivity) (by linarith)
    nlinarith [mul_lt_mul_of_pos_left hs (show (0:ℝ) < 1 + x ^ 2 / 3 by positivity)]
  rw [← key] at hmain
  exact le_of_mul_le_mul_right hmain hS_pos
end

-- forge:entry bld3_nilpotent_rank_pow_le kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_rank_pow_convex and Mathlib2.bld_nilpotent_rank_bound: by convexity the drops d_k are non-increasing, so once d_k = 0 the rank is constant forever; nilpotency forces that constant to be 0, hence the rank drops by at least 1 at each step until it reaches 0, giving rank A^k ≤ n - k (truncated subtraction). -/
theorem bld3_nilpotent_rank_pow_le (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (hA : IsNilpotent A) (k : ℕ) : Matrix.rank (A ^ k) ≤ Fintype.card ι - k := by
  obtain ⟨N, hN⟩ := hA
  set f : ℕ → ℕ := fun k => Matrix.rank (A ^ k) with hf
  have hconv : ∀ k, 2 * f (k + 1) ≤ f k + f (k + 2) := fun k => bld2_rank_pow_convex K ι A k
  have hzero : ∀ i, f (N + i) = 0 := by
    intro i
    simp only [hf, pow_add, hN, zero_mul, Matrix.rank_zero]
  have h0 : f 0 = Fintype.card ι := by simp [hf]
  change f k ≤ Fintype.card ι - k
  rcases Nat.eq_zero_or_pos (f k) with hk | hk
  · omega
  -- some strict drop at or after k
  have hdrop : ∃ m, k ≤ m ∧ f (m + 1) < f m := by
    by_contra hcon
    push_neg at hcon
    have hmono : ∀ i, f k ≤ f (k + i) := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => exact ih.trans (hcon (k + i) (by omega))
    have h1 := hmono N
    have h2 := hzero k
    rw [add_comm] at h2
    omega
  obtain ⟨m, hkm, hm⟩ := hdrop
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · omega
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = k' + j := ⟨m - k', by omega⟩
  have hstep := bld3_rank_pow_card_stabilizes_aux1 f hconv k' j hm
  have := bld3_rank_pow_card_stabilizes_aux2 f hconv k' hstep
  omega
end

-- forge:entry bld3_pell_five_one_solutions kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_pell_five_solutions_lucas: (2x)^2 = 5 (2y)^2 + 4, so 2y = fib (2m) and 2x = p3_lucas (2m); fib (2m) is even iff 3 ∣ 2m iff 3 ∣ m (fib mod 2 has period 3), so 2m = 6n. -/
theorem bld3_pell_five_one_solutions (x y : ℕ) (h : x ^ 2 = 5 * y ^ 2 + 1) : ∃ n : ℕ, 2 * y = Nat.fib (6 * n) ∧ 2 * x = p3_lucas (6 * n) := by
  obtain ⟨m, hm, hx⟩ := bld2_pell_five_solutions_lucas (2 * x) (2 * y) (by nlinarith)
  have h3 : 3 ∣ 2 * m := by
    have hg := Nat.fib_gcd 3 (2 * m)
    have h2 : Nat.fib 3 ∣ Nat.fib (2 * m) := by
      rw [← hm]; exact ⟨y, by norm_num [Nat.fib]⟩
    rw [Nat.gcd_eq_left h2] at hg
    rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 (2 * m)) with h1 | h1
    · rw [h1] at hg; norm_num [Nat.fib] at hg
    · rw [← h1]; exact Nat.gcd_dvd_right _ _
  obtain ⟨n, hn⟩ : ∃ n, 2 * m = 6 * n := ⟨m / 3, by omega⟩
  rw [hn] at hm hx
  exact ⟨n, hm, hx⟩
end

-- forge:entry bld3_sqrt_two_rec_pi_limit kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_sqrt_two_rec_defect_asymptotic: (2^n √(2 - a n)) = √(4^n (2 - a n)); compose the defect asymptotic 4^n (2 - a n) → π^2/4 with continuity of the square root, √(π^2/4) = π/2 (the classical nested-radical formula for π). -/
theorem bld3_sqrt_two_rec_pi_limit (a : ℕ → ℝ) (h0 : a 0 = 0) (h : ∀ n : ℕ, a (n + 1) = Real.sqrt (2 + a n)) : Filter.Tendsto (fun n : ℕ => 2 ^ n * Real.sqrt (2 - a n)) Filter.atTop (nhds (Real.pi / 2)) := by
  have key := Mathlib2.bld2_sqrt_two_rec_defect_asymptotic a h0 h
  have h2 := (Real.continuous_sqrt.tendsto _).comp key
  have e : Real.sqrt (Real.pi ^ 2 / 4) = Real.pi / 2 := by
    rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  rw [e] at h2
  refine h2.congr (fun n => ?_)
  simp only [Function.comp]
  rw [show (4:ℝ) ^ n = (2 ^ n) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
end

-- forge:entry bld3_mantel_equality_same_neighbors kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_mantel_equality_regular and Mathlib2.comb_degree_add_degree_le_of_triangle_free: all degrees are n/2; for an edge u v the neighbourhoods are disjoint of total size n so they partition V; if z ~ x then y lies in N(x) or N(z), the former is excluded, so y ~ z (the extremal graph is complete bipartite). -/
theorem bld3_mantel_equality_same_neighbors (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.CliqueFree 3) (he : 4 * G.edgeFinset.card = Fintype.card V ^ 2) (x y : V) (hxy : ¬ G.Adj x y) (z : V) : G.Adj x z ↔ G.Adj y z := by
  have hreg := bld2_mantel_equality_regular V G hG he
  have key : ∀ a b : V, ¬ G.Adj a b → G.Adj a z → G.Adj b z := by
    intro a b hab haz
    have hdisj : Disjoint (G.neighborFinset a) (G.neighborFinset z) := by
      rw [Finset.disjoint_left]
      intro w hwa hwz
      rw [SimpleGraph.mem_neighborFinset] at hwa hwz
      exact hG {a, z, w} (SimpleGraph.is3Clique_triple_iff.mpr ⟨haz, hwa, hwz⟩)
    have hcard : (G.neighborFinset a ∪ G.neighborFinset z).card = Fintype.card V := by
      rw [Finset.card_union_of_disjoint hdisj, SimpleGraph.card_neighborFinset_eq_degree,
        SimpleGraph.card_neighborFinset_eq_degree]
      have := hreg a
      have := hreg z
      omega
    have huniv := (Finset.card_eq_iff_eq_univ _).mp hcard
    have hb : b ∈ G.neighborFinset a ∪ G.neighborFinset z := by rw [huniv]; exact Finset.mem_univ b
    rw [Finset.mem_union, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset] at hb
    rcases hb with hb | hb
    · exact absurd hb hab
    · exact hb.symm
  exact ⟨key x y hxy, key y x (fun h => hxy h.symm)⟩
end

-- forge:entry bld3_commuting_idempotents_rank_sub kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_idempotent_sum_rank and Mathlib2.bld2_commuting_idempotents_rank_join: P = A - AB and Q = B - AB are orthogonal idempotents with A = AB + P, B = AB + Q, so rank P = rank A - rank AB and rank Q = rank B - rank AB; (P - Q)^2 = P + Q is idempotent of rank rank P + rank Q, which squeezes rank (A - B) = rank (P - Q) between rank (P + Q) and rank P + rank Q. -/
theorem bld3_commuting_idempotents_rank_sub (K : Type*) [Field K] [CharZero K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι K) (hA : A * A = A) (hB : B * B = B) (hAB : A * B = B * A) : Matrix.rank (A - B) + 2 * Matrix.rank (A * B) = Matrix.rank A + Matrix.rank B := by
  have hAC : A * (A * B) = A * B := by rw [← mul_assoc, hA]
  have hCB : A * B * B = A * B := by rw [mul_assoc, hB]
  have hCA : A * B * A = A * B := by rw [mul_assoc, ← hAB, ← mul_assoc, hA]
  have hBC : B * (A * B) = A * B := by rw [hAB, ← mul_assoc, hB]
  have hCC : A * B * (A * B) = A * B := by rw [← mul_assoc, hCA, hCB]
  have hBA : B * A = A * B := hAB.symm
  obtain ⟨C, hC⟩ : ∃ C, C = A * B := ⟨_, rfl⟩
  rw [← hC] at hAC hCB hCA hBC hCC hBA ⊢
  clear hAB
  have hAB : A * B = C := hC.symm
  clear hC
  have hP : (A - C) * (A - C) = A - C := by
    simp only [mul_sub, sub_mul, hA, hAC, hCA, hCC]; abel
  have hQ : (B - C) * (B - C) = B - C := by
    simp only [mul_sub, sub_mul, hB, hBC, hCB, hCC]; abel
  have hS : ((A - C) + (B - C)) * ((A - C) + (B - C)) = (A - C) + (B - C) := by
    simp only [mul_sub, sub_mul, mul_add, add_mul, hA, hB, hAC, hCA, hBC, hCB, hCC, hBA, hAB]; abel
  have hMM : (A - B) * (A - B) = (A - C) + (B - C) := by
    simp only [mul_sub, sub_mul, hA, hB, hAC, hBA, hAB]; abel
  have hMS : (A - B) * ((A - C) + (B - C)) = A - B := by
    simp only [mul_sub, sub_mul, mul_add, add_mul, hA, hB, hAC, hCA, hBC, hCB, hCC, hBA, hAB]; abel
  have r1 := bld_idempotent_sum_rank K ι (A - C) (B - C) hP hQ hS
  have r2 := bld_idempotent_sum_rank K ι C (A - C) hCC hP (by simpa using hA)
  have r3 := bld_idempotent_sum_rank K ι C (B - C) hCC hQ (by simpa using hB)
  rw [add_sub_cancel] at r2 r3
  have l1 : ((A - C) + (B - C)).rank ≤ (A - B).rank := by
    rw [← hMM]; exact Matrix.rank_mul_le_left _ _
  have l2 : (A - B).rank ≤ ((A - C) + (B - C)).rank := by
    conv_lhs => rw [← hMS]
    exact Matrix.rank_mul_le_right _ _
  omega
end

-- forge:entry bld3_sqrt_two_rec_defect_tsum_bounds kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_sqrt_two_rec_rate and Mathlib2.bld2_sqrt_two_rec_defect_summable: upper bound: compare termwise with the geometric series ∑ π^2/4^(n+1) = π^2/3 using the rate; lower bound: 2 - a (n+1) = (2 - a n)/(2 + a (n+1)) ≥ (2 - a n)/4 gives 2 - a n ≥ 2/4^n, whose sum is 8/3; summability from the library. -/
theorem bld3_sqrt_two_rec_defect_tsum_bounds (a : ℕ → ℝ) (h0 : a 0 = 0) (h : ∀ n : ℕ, a (n + 1) = Real.sqrt (2 + a n)) : 8 / 3 ≤ ∑' n : ℕ, (2 - a n) ∧ ∑' n : ℕ, (2 - a n) ≤ Real.pi ^ 2 / 3 := by
  have hsum := Mathlib2.bld2_sqrt_two_rec_defect_summable a h0 h
  have hrate := Mathlib2.bld_sqrt_two_rec_rate a h0 h
  have hb := Mathlib2.ana_sqrt_two_rec_lt_two a h0 h
  have hg : HasSum (fun n : ℕ => ((1:ℝ) / 4) ^ n) (1 - 1 / 4)⁻¹ :=
    hasSum_geometric_of_lt_one (by norm_num) (by norm_num)
  have hlow : ∀ n : ℕ, 2 * ((1:ℝ) / 4) ^ n ≤ 2 - a n := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ k ih =>
      have hk := hb k
      have hk1 := hb (k + 1)
      have hsq : a (k + 1) ^ 2 = 2 + a k := by
        rw [h k]; exact Real.sq_sqrt (by linarith)
      rw [pow_succ]
      nlinarith
  have hup : ∀ n : ℕ, 2 - a n ≤ Real.pi ^ 2 / 4 * ((1:ℝ) / 4) ^ n := by
    intro n
    refine (hrate n).trans (le_of_eq ?_)
    rw [one_div, inv_pow]; field_simp; ring
  constructor
  · have h1 := (hg.mul_left 2)
    have := hasSum_le hlow h1 hsum.hasSum
    norm_num at this ⊢
    linarith
  · have h1 := (hg.mul_left (Real.pi ^ 2 / 4))
    have := hasSum_le hup hsum.hasSum h1
    refine this.trans (le_of_eq ?_)
    norm_num; ring
end

end Mathlib2
