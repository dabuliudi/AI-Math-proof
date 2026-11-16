/- Mathlib2 分片 60（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0059
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry x2611_16338_balanced_counts kind=proved origin=paper
section
/- Section 3: a=c for a balanced subset -/
open Finset

lemma x2611_16338_balanced_counts_aux1 {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → ℤ) (w : Sym2 V → ℤ)
    (hw : ∀ u v, w s(u, v) = f u + f v) :
    ∑ e ∈ G.edgeFinset, w e = ∑ v, (G.degree v : ℤ) * f v := by
  classical
  have hfst : ∑ d : G.Dart, f d.fst = ∑ v, (G.degree v : ℤ) * f v := by
    rw [← Finset.sum_fiberwise Finset.univ (fun d : G.Dart => d.fst)]
    apply Finset.sum_congr rfl
    intro v hv
    calc
      ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = v), f d.fst =
          ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = v), f v := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [(Finset.mem_filter.mp hd).2]
      _ = (G.degree v : ℤ) * f v := by
        simp [G.dart_fst_fiber_card_eq_degree v]
  rw [← hfst]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := G.edgeFinset) (g := SimpleGraph.Dart.edge)
    (fun d _ => G.mem_edgeFinset.mpr d.edge_mem) (fun d : G.Dart => f d.fst)]
  apply Finset.sum_congr rfl
  intro e he
  obtain ⟨u, v⟩ := e
  have huv : G.Adj u v := G.mem_edgeFinset.mp he
  let d : G.Dart := ⟨(u, v), huv⟩
  have hfiber : (Finset.univ.filter (fun d' : G.Dart => d'.edge = s(u, v))) =
      {d, d.symm} := d.edge_fiber
  rw [hfiber]
  rw [Finset.sum_pair (Ne.symm d.symm_ne)]
  exact hw u v

theorem x2611_16338_balanced_counts (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsRegularOfDegree 3)
    (s : ℕ) (hs : s = Fintype.card V / 2 + 1) (hs3 : 3 ≤ s)
    (U : Finset V) (φ : V → ℕ) (hφ : ∀ v, φ v = if v ∈ U then 1 else s)
    (hU : U.card = Fintype.card V / 2) (a b c : ℕ)
    (ha : a = (x2611_16338_edgeClass G φ 2).ncard)
    (hb : b = (x2611_16338_edgeClass G φ (s + 1)).ncard)
    (hc : c = (x2611_16338_edgeClass G φ (2 * s)).ncard) : a = c := by
  classical
  have hdegree := G.sum_degrees_eq_twice_card_edges
  simp only [hG.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hdegree
  have hn : Fintype.card V = 2 * U.card := by omega
  let f : V → ℤ := fun v => if v ∈ U then 1 else -1
  let w : Sym2 V → ℤ := Sym2.lift ⟨(fun u v => f u + f v), (fun u v => add_comm (f u) (f v))⟩
  have hw : ∀ u v, w s(u, v) = f u + f v := by intros; rfl
  have hsum := x2611_16338_balanced_counts_aux1 G f w hw
  have hright : (∑ v, (G.degree v : ℤ) * f v) = 0 := by
    simp only [hG.degree_eq]
    rw [← Finset.mul_sum]
    have hf : (∑ v, f v) = (U.card : ℤ) - ((Finset.univ \ U).card : ℤ) := by
      simp [f, Finset.sum_ite, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.mpr (Finset.subset_univ U),
        Finset.filter_notMem_eq_sdiff, sub_eq_add_neg]
    rw [hf]
    have hcompl : (Finset.univ \ U).card = U.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ U), Finset.card_univ, hn]
      omega
    rw [hcompl, sub_self, mul_zero]
  have hpoint (e : Sym2 V) : w e =
      (if x2611_16338_vertexSum φ e = 2 then 2 else 0) -
      (if x2611_16338_vertexSum φ e = 2 * s then 2 else 0) := by
    obtain ⟨u, v⟩ := e
    rw [hw]
    simp only [x2611_16338_vertexSum, Sym2.lift_mk, hφ]
    by_cases hu : u ∈ U <;> by_cases hv : v ∈ U <;> simp [f, hu, hv] <;> omega
  have hcard (r : ℕ) :
      (G.edgeFinset.filter (fun e => x2611_16338_vertexSum φ e = r)).card =
      (x2611_16338_edgeClass G φ r).ncard := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext e
    simp [x2611_16338_edgeClass]
  have hleft : (∑ e ∈ G.edgeFinset, w e) = 2 * (a : ℤ) - 2 * (c : ℤ) := by
    simp_rw [hpoint]
    rw [Finset.sum_sub_distrib]
    simp only [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    rw [hcard, hcard, ← ha, ← hc]
    ring
  rw [hleft, hright] at hsum
  omega
end

-- forge:entry x2611_15210_lem4_1 kind=proved origin=paper
section
/- Lemma 4.1 -/
lemma x2611_15210_lem4_1_aux1 (m n : ℕ) (hm : 0 < m) (hn : n ≤ 2*m)
    (hd : m ∣ n) : n = 0 ∨ n = m ∨ n = 2*m := by
  obtain ⟨k, rfl⟩ := hd
  have hk : k ≤ 2 := by nlinarith
  interval_cases k <;> simp_all <;> omega

lemma x2611_15210_lem4_1_aux2 (m : ℕ) (c : Fin 9 → ℕ) :
    (∑ i : Fin 9, c i • (fun j : Fin 5 => (x2611_15210_P i j : ZMod m))) = 0 ↔
    m ∣ (c 6 + c 7 + c 8) ∧
    m ∣ (c 3 + c 4 + c 5) ∧
    m ∣ (c 1 + c 2 + c 4 + c 5 + c 7 + c 8) ∧
    m ∣ (c 1 + c 2 + c 3 + c 5 + c 6 + c 8) ∧
    m ∣ (c 2 + c 5 + c 6) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals apply (ZMod.natCast_eq_zero_iff _ _).mp
    · simpa [Fin.sum_univ_succ, x2611_15210_P, nsmul_eq_mul, add_assoc] using congrFun h (0 : Fin 5)
    · simpa [Fin.sum_univ_succ, x2611_15210_P, nsmul_eq_mul, add_assoc] using congrFun h (1 : Fin 5)
    · simpa [Fin.sum_univ_succ, x2611_15210_P, nsmul_eq_mul, add_assoc] using congrFun h (2 : Fin 5)
    · simpa [Fin.sum_univ_succ, x2611_15210_P, nsmul_eq_mul, add_assoc] using congrFun h (3 : Fin 5)
    · simpa [Fin.sum_univ_succ, x2611_15210_P, nsmul_eq_mul, add_assoc] using congrFun h (4 : Fin 5)
  · rintro ⟨h0,h1,h2,h3,h4⟩
    have h0 := (ZMod.natCast_eq_zero_iff _ _).mpr h0
    have h1 := (ZMod.natCast_eq_zero_iff _ _).mpr h1
    have h2 := (ZMod.natCast_eq_zero_iff _ _).mpr h2
    have h3 := (ZMod.natCast_eq_zero_iff _ _).mpr h3
    have h4 := (ZMod.natCast_eq_zero_iff _ _).mpr h4
    ext j
    fin_cases j
    all_goals simp_all [Fin.sum_univ_succ, x2611_15210_P, nsmul_eq_mul, add_assoc]


lemma x2611_15210_lem4_1_aux3 (m : ℕ) (hm : 0 < m) (c : Fin 9 → ℕ)
    (hc : ∑ i, c i = 2*m)
    (h0 : c 6 + c 7 + c 8 = 0)
    (h1 : c 3 + c 4 + c 5 = 0 ∨ c 3 + c 4 + c 5 = m ∨ c 3 + c 4 + c 5 = 2*m)
    (h2 : c 1 + c 2 + c 4 + c 5 + c 7 + c 8 = 0 ∨ c 1 + c 2 + c 4 + c 5 + c 7 + c 8 = m ∨ c 1 + c 2 + c 4 + c 5 + c 7 + c 8 = 2*m)
    (h3 : c 1 + c 2 + c 3 + c 5 + c 6 + c 8 = 0 ∨ c 1 + c 2 + c 3 + c 5 + c 6 + c 8 = m ∨ c 1 + c 2 + c 3 + c 5 + c 6 + c 8 = 2*m)
    (h4 : c 2 + c 5 + c 6 = 0 ∨ c 2 + c 5 + c 6 = m ∨ c 2 + c 5 + c 6 = 2*m)
    : ((∃ i : Fin 9, c i = 2*m ∧ ∀ j : Fin 9, j ≠ i → c j = 0) ∨
      ∃ i j : Fin 9, i ≠ j ∧ c i = m ∧ c j = m ∧
        ∀ k : Fin 9, k ≠ i → k ≠ j → c k = 0) ∨ (∃ S : Finset (Fin 9),
      (S = {0, 1, 3, 4} ∨ S = {0, 2, 6, 7} ∨ S = {3, 5, 6, 8}) ∧
      ∀ i : Fin 9, 2*c i = if i ∈ S then m else 0) := by
  have hsum : c 0 + c 1 + c 2 + c 3 + c 4 + c 5 + c 6 + c 7 + c 8 = 2*m := by
    simpa [Fin.sum_univ_succ, add_assoc] using hc
  clear hc
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
    rcases h3 with h3 | h3 | h3 <;> rcases h4 with h4 | h4 | h4
  · left
    left
    refine ⟨0, ?_, ?_⟩
    · omega
    · intro k hk
      fin_cases k
      · exact (hk rfl).elim
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · left
    right
    refine ⟨0, 1, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · exact (hki rfl).elim
      · exact (hkj rfl).elim
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · left
    right
    refine ⟨0, 2, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · exact (hki rfl).elim
      · change c 1 = 0
        omega
      · exact (hkj rfl).elim
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · left
    left
    refine ⟨1, ?_, ?_⟩
    · omega
    · intro k hk
      fin_cases k
      · change c 0 = 0
        omega
      · exact (hk rfl).elim
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · left
    right
    refine ⟨1, 2, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · exact (hki rfl).elim
      · exact (hkj rfl).elim
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · left
    left
    refine ⟨2, ?_, ?_⟩
    · omega
    · intro k hk
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · exact (hk rfl).elim
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · omega
  · omega
  · omega
  · left
    right
    refine ⟨0, 3, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · exact (hki rfl).elim
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · exact (hkj rfl).elim
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · left
    right
    refine ⟨0, 4, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · exact (hki rfl).elim
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · exact (hkj rfl).elim
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · omega
  · omega
  · right
    refine ⟨{0, 1, 3, 4}, Or.inl rfl, ?_⟩
    intro i
    fin_cases i
    · change 2*c 0 = m
      omega
    · change 2*c 1 = m
      omega
    · change 2*c 2 = 0
      omega
    · change 2*c 3 = m
      omega
    · change 2*c 4 = m
      omega
    · change 2*c 5 = 0
      omega
    · change 2*c 6 = 0
      omega
    · change 2*c 7 = 0
      omega
    · change 2*c 8 = 0
      omega
  · left
    right
    refine ⟨0, 5, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · exact (hki rfl).elim
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · exact (hkj rfl).elim
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · omega
  · left
    right
    refine ⟨1, 3, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · exact (hki rfl).elim
      · change c 2 = 0
        omega
      · exact (hkj rfl).elim
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · left
    right
    refine ⟨2, 3, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · exact (hki rfl).elim
      · exact (hkj rfl).elim
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · omega
  · omega
  · omega
  · omega
  · left
    right
    refine ⟨1, 4, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · exact (hki rfl).elim
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · exact (hkj rfl).elim
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · left
    right
    refine ⟨2, 4, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · exact (hki rfl).elim
      · change c 3 = 0
        omega
      · exact (hkj rfl).elim
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · omega
  · omega
  · left
    right
    refine ⟨1, 5, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · exact (hki rfl).elim
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · exact (hkj rfl).elim
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · left
    right
    refine ⟨2, 5, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · exact (hki rfl).elim
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · exact (hkj rfl).elim
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · left
    left
    refine ⟨3, ?_, ?_⟩
    · omega
    · intro k hk
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · exact (hk rfl).elim
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · left
    right
    refine ⟨3, 4, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · exact (hki rfl).elim
      · exact (hkj rfl).elim
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · omega
  · omega
  · omega
  · left
    right
    refine ⟨3, 5, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · exact (hki rfl).elim
      · change c 4 = 0
        omega
      · exact (hkj rfl).elim
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · omega
  · left
    left
    refine ⟨4, ?_, ?_⟩
    · omega
    · intro k hk
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · exact (hk rfl).elim
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · omega
  · omega
  · omega
  · left
    right
    refine ⟨4, 5, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · exact (hki rfl).elim
      · exact (hkj rfl).elim
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · omega
  · omega
  · omega
  · left
    left
    refine ⟨5, ?_, ?_⟩
    · omega
    · intro k hk
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · exact (hk rfl).elim
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega

lemma x2611_15210_lem4_1_aux4 (m : ℕ) (hm : 0 < m) (c : Fin 9 → ℕ)
    (hc : ∑ i, c i = 2*m)
    (h0 : c 6 + c 7 + c 8 = m)
    (h1 : c 3 + c 4 + c 5 = 0 ∨ c 3 + c 4 + c 5 = m ∨ c 3 + c 4 + c 5 = 2*m)
    (h2 : c 1 + c 2 + c 4 + c 5 + c 7 + c 8 = 0 ∨ c 1 + c 2 + c 4 + c 5 + c 7 + c 8 = m ∨ c 1 + c 2 + c 4 + c 5 + c 7 + c 8 = 2*m)
    (h3 : c 1 + c 2 + c 3 + c 5 + c 6 + c 8 = 0 ∨ c 1 + c 2 + c 3 + c 5 + c 6 + c 8 = m ∨ c 1 + c 2 + c 3 + c 5 + c 6 + c 8 = 2*m)
    (h4 : c 2 + c 5 + c 6 = 0 ∨ c 2 + c 5 + c 6 = m ∨ c 2 + c 5 + c 6 = 2*m)
    : ((∃ i : Fin 9, c i = 2*m ∧ ∀ j : Fin 9, j ≠ i → c j = 0) ∨
      ∃ i j : Fin 9, i ≠ j ∧ c i = m ∧ c j = m ∧
        ∀ k : Fin 9, k ≠ i → k ≠ j → c k = 0) ∨ (∃ S : Finset (Fin 9),
      (S = {0, 1, 3, 4} ∨ S = {0, 2, 6, 7} ∨ S = {3, 5, 6, 8}) ∧
      ∀ i : Fin 9, 2*c i = if i ∈ S then m else 0) := by
  have hsum : c 0 + c 1 + c 2 + c 3 + c 4 + c 5 + c 6 + c 7 + c 8 = 2*m := by
    simpa [Fin.sum_univ_succ, add_assoc] using hc
  clear hc
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
    rcases h3 with h3 | h3 | h3 <;> rcases h4 with h4 | h4 | h4
  · omega
  · omega
  · omega
  · omega
  · left
    right
    refine ⟨0, 6, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · exact (hki rfl).elim
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · exact (hkj rfl).elim
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · omega
  · omega
  · omega
  · omega
  · left
    right
    refine ⟨0, 7, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · exact (hki rfl).elim
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · exact (hkj rfl).elim
      · change c 8 = 0
        omega
  · omega
  · omega
  · left
    right
    refine ⟨0, 8, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · exact (hki rfl).elim
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · exact (hkj rfl).elim
  · right
    refine ⟨{0, 2, 6, 7}, Or.inr (Or.inl rfl), ?_⟩
    intro i
    fin_cases i
    · change 2*c 0 = m
      omega
    · change 2*c 1 = 0
      omega
    · change 2*c 2 = m
      omega
    · change 2*c 3 = 0
      omega
    · change 2*c 4 = 0
      omega
    · change 2*c 5 = 0
      omega
    · change 2*c 6 = m
      omega
    · change 2*c 7 = m
      omega
    · change 2*c 8 = 0
      omega
  · omega
  · omega
  · left
    right
    refine ⟨1, 6, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · exact (hki rfl).elim
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · exact (hkj rfl).elim
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · left
    right
    refine ⟨2, 6, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · exact (hki rfl).elim
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · exact (hkj rfl).elim
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · omega
  · omega
  · omega
  · left
    right
    refine ⟨1, 7, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · exact (hki rfl).elim
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · exact (hkj rfl).elim
      · change c 8 = 0
        omega
  · left
    right
    refine ⟨2, 7, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · exact (hki rfl).elim
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · exact (hkj rfl).elim
      · change c 8 = 0
        omega
  · omega
  · left
    right
    refine ⟨1, 8, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · exact (hki rfl).elim
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · exact (hkj rfl).elim
  · left
    right
    refine ⟨2, 8, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · exact (hki rfl).elim
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · exact (hkj rfl).elim
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · left
    right
    refine ⟨3, 6, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · exact (hki rfl).elim
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · exact (hkj rfl).elim
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · omega
  · omega
  · omega
  · omega
  · left
    right
    refine ⟨3, 7, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · exact (hki rfl).elim
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · exact (hkj rfl).elim
      · change c 8 = 0
        omega
  · left
    right
    refine ⟨4, 6, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · exact (hki rfl).elim
      · change c 5 = 0
        omega
      · exact (hkj rfl).elim
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · omega
  · left
    right
    refine ⟨3, 8, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · exact (hki rfl).elim
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · exact (hkj rfl).elim
  · right
    refine ⟨{3, 5, 6, 8}, Or.inr (Or.inr rfl), ?_⟩
    intro i
    fin_cases i
    · change 2*c 0 = 0
      omega
    · change 2*c 1 = 0
      omega
    · change 2*c 2 = 0
      omega
    · change 2*c 3 = m
      omega
    · change 2*c 4 = 0
      omega
    · change 2*c 5 = m
      omega
    · change 2*c 6 = m
      omega
    · change 2*c 7 = 0
      omega
    · change 2*c 8 = m
      omega
  · left
    right
    refine ⟨5, 6, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · exact (hki rfl).elim
      · exact (hkj rfl).elim
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · left
    right
    refine ⟨4, 7, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · exact (hki rfl).elim
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · exact (hkj rfl).elim
      · change c 8 = 0
        omega
  · omega
  · omega
  · left
    right
    refine ⟨4, 8, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · exact (hki rfl).elim
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · exact (hkj rfl).elim
  · left
    right
    refine ⟨5, 7, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · exact (hki rfl).elim
      · change c 6 = 0
        omega
      · exact (hkj rfl).elim
      · change c 8 = 0
        omega
  · omega
  · omega
  · left
    right
    refine ⟨5, 8, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · exact (hki rfl).elim
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · exact (hkj rfl).elim
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

lemma x2611_15210_lem4_1_aux5 (m : ℕ) (hm : 0 < m) (c : Fin 9 → ℕ)
    (hc : ∑ i, c i = 2*m)
    (h0 : c 6 + c 7 + c 8 = 2*m)
    (h1 : c 3 + c 4 + c 5 = 0 ∨ c 3 + c 4 + c 5 = m ∨ c 3 + c 4 + c 5 = 2*m)
    (h2 : c 1 + c 2 + c 4 + c 5 + c 7 + c 8 = 0 ∨ c 1 + c 2 + c 4 + c 5 + c 7 + c 8 = m ∨ c 1 + c 2 + c 4 + c 5 + c 7 + c 8 = 2*m)
    (h3 : c 1 + c 2 + c 3 + c 5 + c 6 + c 8 = 0 ∨ c 1 + c 2 + c 3 + c 5 + c 6 + c 8 = m ∨ c 1 + c 2 + c 3 + c 5 + c 6 + c 8 = 2*m)
    (h4 : c 2 + c 5 + c 6 = 0 ∨ c 2 + c 5 + c 6 = m ∨ c 2 + c 5 + c 6 = 2*m)
    : ((∃ i : Fin 9, c i = 2*m ∧ ∀ j : Fin 9, j ≠ i → c j = 0) ∨
      ∃ i j : Fin 9, i ≠ j ∧ c i = m ∧ c j = m ∧
        ∀ k : Fin 9, k ≠ i → k ≠ j → c k = 0) ∨ (∃ S : Finset (Fin 9),
      (S = {0, 1, 3, 4} ∨ S = {0, 2, 6, 7} ∨ S = {3, 5, 6, 8}) ∧
      ∀ i : Fin 9, 2*c i = if i ∈ S then m else 0) := by
  have hsum : c 0 + c 1 + c 2 + c 3 + c 4 + c 5 + c 6 + c 7 + c 8 = 2*m := by
    simpa [Fin.sum_univ_succ, add_assoc] using hc
  clear hc
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
    rcases h3 with h3 | h3 | h3 <;> rcases h4 with h4 | h4 | h4
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · left
    left
    refine ⟨6, ?_, ?_⟩
    · omega
    · intro k hk
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · exact (hk rfl).elim
      · change c 7 = 0
        omega
      · change c 8 = 0
        omega
  · omega
  · omega
  · omega
  · omega
  · left
    right
    refine ⟨6, 7, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · exact (hki rfl).elim
      · exact (hkj rfl).elim
      · change c 8 = 0
        omega
  · omega
  · omega
  · left
    right
    refine ⟨6, 8, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · exact (hki rfl).elim
      · change c 7 = 0
        omega
      · exact (hkj rfl).elim
  · omega
  · left
    left
    refine ⟨7, ?_, ?_⟩
    · omega
    · intro k hk
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · exact (hk rfl).elim
      · change c 8 = 0
        omega
  · omega
  · omega
  · left
    right
    refine ⟨7, 8, by decide, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro k hki hkj
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · exact (hki rfl).elim
      · exact (hkj rfl).elim
  · omega
  · omega
  · left
    left
    refine ⟨8, ?_, ?_⟩
    · omega
    · intro k hk
      fin_cases k
      · change c 0 = 0
        omega
      · change c 1 = 0
        omega
      · change c 2 = 0
        omega
      · change c 3 = 0
        omega
      · change c 4 = 0
        omega
      · change c 5 = 0
        omega
      · change c 6 = 0
        omega
      · change c 7 = 0
        omega
      · exact (hk rfl).elim
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
lemma x2611_15210_lem4_1_aux6 (m : ℕ) (hm : 2 ≤ m) (c : Fin 9 → ℕ)
    (hc : ∑ i, c i = 2*m)
    (hz : (∑ i : Fin 9, c i • (fun j : Fin 5 => (x2611_15210_P i j : ZMod m))) = 0) :
    ((∃ i : Fin 9, c i = 2*m ∧ ∀ j : Fin 9, j ≠ i → c j = 0) ∨
      ∃ i j : Fin 9, i ≠ j ∧ c i = m ∧ c j = m ∧
        ∀ k : Fin 9, k ≠ i → k ≠ j → c k = 0) ∨
    (∃ S : Finset (Fin 9),
      (S = {0, 1, 3, 4} ∨ S = {0, 2, 6, 7} ∨ S = {3, 5, 6, 8}) ∧
      ∀ i : Fin 9, 2*c i = if i ∈ S then m else 0) := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := (x2611_15210_lem4_1_aux2 m c).mp hz
  have hsum : c 0 + c 1 + c 2 + c 3 + c 4 + c 5 + c 6 + c 7 + c 8 = 2*m := by
    simpa [Fin.sum_univ_succ, add_assoc] using hc
  have hm' : 0 < m := by omega
  have h0 := x2611_15210_lem4_1_aux1 m _ hm' (by omega) h0
  have h1 := x2611_15210_lem4_1_aux1 m _ hm' (by omega) h1
  have h2 := x2611_15210_lem4_1_aux1 m _ hm' (by omega) h2
  have h3 := x2611_15210_lem4_1_aux1 m _ hm' (by omega) h3
  have h4 := x2611_15210_lem4_1_aux1 m _ hm' (by omega) h4
  rcases h0 with h0 | h0 | h0
  · exact x2611_15210_lem4_1_aux3 m hm' c hc h0 h1 h2 h3 h4
  · exact x2611_15210_lem4_1_aux4 m hm' c hc h0 h1 h2 h3 h4
  · exact x2611_15210_lem4_1_aux5 m hm' c hc h0 h1 h2 h3 h4

lemma x2611_15210_lem4_1_aux7 (m : ℕ) (c : Fin 9 → ℕ)
    (h : (∃ i : Fin 9, c i = 2*m ∧ ∀ j : Fin 9, j ≠ i → c j = 0) ∨
      ∃ i j : Fin 9, i ≠ j ∧ c i = m ∧ c j = m ∧
        ∀ k : Fin 9, k ≠ i → k ≠ j → c k = 0) : ∀ i, m ∣ c i := by
  rcases h with ⟨i,hi,hs⟩ | ⟨i,j,hij,hi,hj,hs⟩
  · intro k
    by_cases hk : k = i
    · subst k
      simp [hi]
    · simp [hs k hk]
  · intro k
    by_cases hk : k = i
    · subst k
      simp [hi]
    · by_cases hkj : k = j
      · subst k
        simp [hj]
      · simp [hs k hk hkj]

lemma x2611_15210_lem4_1_aux8 (m : ℕ) (c : Fin 9 → ℕ) (h : ∀ i, m ∣ c i) :
    (∑ i : Fin 9, c i • (fun j : Fin 5 => (x2611_15210_P i j : ZMod m))) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  obtain ⟨k,hk⟩ := h i
  ext j
  simp [hk, nsmul_eq_mul, Nat.cast_mul, ZMod.natCast_self]

lemma x2611_15210_lem4_1_aux9 (m : ℕ) (hm : 0 < m) (c : Fin 9 → ℕ)
    (h : ∃ S : Finset (Fin 9),
      (S = {0, 1, 3, 4} ∨ S = {0, 2, 6, 7} ∨ S = {3, 5, 6, 8}) ∧
      ∀ i : Fin 9, 2*c i = if i ∈ S then m else 0) :
    ∃ S : Finset (Fin 9),
      (S = {0, 1, 3, 4} ∨ S = {0, 2, 6, 7} ∨ S = {3, 5, 6, 8}) ∧
      ∀ i : Fin 9, (c i : ℚ) / (m : ℚ) = if i ∈ S then (1/2 : ℚ) else 0 := by
  obtain ⟨S,hS,hc⟩ := h
  refine ⟨S,hS,?_⟩
  intro i
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  by_cases hi : i ∈ S
  · have hci := hc i
    simp only [if_pos hi] at hci ⊢
    have hci' : 2*(c i : ℚ) = (m : ℚ) := by exact_mod_cast hci
    apply (div_eq_iff hm').mpr
    linarith
  · have hci := hc i
    simp only [if_neg hi] at hci ⊢
    have : c i = 0 := by omega
    simp [this]


lemma x2611_15210_lem4_1_aux10 (m : ℕ) (hm : 0 < m) (c : Fin 9 → ℕ)
    (h : ∃ S : Finset (Fin 9),
      (S = {0, 1, 3, 4} ∨ S = {0, 2, 6, 7} ∨ S = {3, 5, 6, 8}) ∧
      ∀ i : Fin 9, 2*c i = if i ∈ S then m else 0) :
    Even m ∧ (0 < c 0 ∨ 0 < c 6) := by
  obtain ⟨S,hS,hc⟩ := h
  rcases hS with rfl | rfl | rfl
  · have he := hc 0
    norm_num at he
    exact ⟨⟨c 0, by omega⟩, Or.inl (by omega)⟩
  · have he := hc 0
    norm_num at he
    exact ⟨⟨c 0, by omega⟩, Or.inl (by omega)⟩
  · have he := hc 6
    norm_num at he
    exact ⟨⟨c 6, by omega⟩, Or.inr (by omega)⟩

theorem x2611_15210_lem4_1 (m : ℕ) (hm : 2 ≤ m) (c : Fin 9 → ℕ)
    (hc : ∑ i, c i = 2 * m) :
    (((∑ i : Fin 9, c i • (fun j : Fin 5 => (x2611_15210_P i j : ZMod m))) = 0) →
      ((∀ i : Fin 9, m ∣ c i) ∨ ∃ S : Finset (Fin 9),
        (S = {0, 1, 3, 4} ∨ S = {0, 2, 6, 7} ∨ S = {3, 5, 6, 8}) ∧
        ∀ i : Fin 9, (c i : ℚ) / (m : ℚ) = if i ∈ S then (1 / 2 : ℚ) else 0)) ∧
    (Odd m → (((∑ i : Fin 9, c i • (fun j : Fin 5 => (x2611_15210_P i j : ZMod m))) = 0) ↔
      ((∃ i : Fin 9, c i = 2 * m ∧ ∀ j : Fin 9, j ≠ i → c j = 0) ∨
        ∃ i j : Fin 9, i ≠ j ∧ c i = m ∧ c j = m ∧
          ∀ k : Fin 9, k ≠ i → k ≠ j → c k = 0))) ∧
    ((c 0 = 0 ∧ c 6 = 0) →
      (((∑ i : Fin 9, c i • (fun j : Fin 5 => (x2611_15210_P i j : ZMod m))) = 0) ↔
        ((∃ i : Fin 9, c i = 2 * m ∧ ∀ j : Fin 9, j ≠ i → c j = 0) ∨
          ∃ i j : Fin 9, i ≠ j ∧ c i = m ∧ c j = m ∧
            ∀ k : Fin 9, k ≠ i → k ≠ j → c k = 0))) := by
  have hm' : 0 < m := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    rcases x2611_15210_lem4_1_aux6 m hm c hc hz with hr | he
    · exact Or.inl (x2611_15210_lem4_1_aux7 m c hr)
    · exact Or.inr (x2611_15210_lem4_1_aux9 m hm' c he)
  · intro ho
    constructor
    · intro hz
      rcases x2611_15210_lem4_1_aux6 m hm c hc hz with hr | he
      · exact hr
      · obtain ⟨⟨a,ha⟩, _⟩ := x2611_15210_lem4_1_aux10 m hm' c he
        obtain ⟨b,hb⟩ := ho
        omega
    · intro hr
      exact x2611_15210_lem4_1_aux8 m c (x2611_15210_lem4_1_aux7 m c hr)
  · intro hzero
    constructor
    · intro hz
      rcases x2611_15210_lem4_1_aux6 m hm c hc hz with hr | he
      · exact hr
      · obtain ⟨_, he⟩ := x2611_15210_lem4_1_aux10 m hm' c he
        rcases he with he | he <;> omega
    · intro hr
      exact x2611_15210_lem4_1_aux8 m c (x2611_15210_lem4_1_aux7 m c hr)
end

-- forge:entry x2611_16338_cubic_incidence_counts kind=proved origin=paper
section
/- Section 3: edge and incidence counts -/
open Finset

lemma x2611_16338_cubic_incidence_counts_aux1
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (U : Finset V) :
    (∑ v ∈ U, G.degree v) = ∑ e ∈ G.edgeFinset, (e.toFinset ∩ U).card := by
  classical
  calc
    (∑ v ∈ U, G.degree v) =
        ∑ v ∈ U, ∑ e ∈ G.edgeFinset, if v ∈ e then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [← G.card_incidenceFinset_eq_degree v, G.incidenceFinset_eq_filter]
      simp
    _ = ∑ e ∈ G.edgeFinset, ∑ v ∈ U, if v ∈ e then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ e ∈ G.edgeFinset, (e.toFinset ∩ U).card := by
      apply Finset.sum_congr rfl
      intro e he
      simp only [Finset.sum_boole, Nat.cast_id]
      apply congrArg Finset.card
      ext v
      simp [and_comm]

lemma x2611_16338_cubic_incidence_counts_aux2
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (φ : V → ℕ) (r : ℕ) :
    (x2611_16338_edgeClass G φ r).ncard =
      ∑ e ∈ G.edgeFinset, if x2611_16338_vertexSum φ e = r then 1 else 0 := by
  classical
  rw [Finset.sum_boole, ← Set.ncard_coe_finset]
  congr 1
  ext e
  simp [x2611_16338_edgeClass]

lemma x2611_16338_cubic_incidence_counts_aux3
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (s : ℕ) (hs : 3 ≤ s) (U : Finset V)
    (φ : V → ℕ) (hφ : ∀ v, φ v = if v ∈ U then 1 else s)
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    ((if x2611_16338_vertexSum φ e = 2 then 1 else 0) +
      (if x2611_16338_vertexSum φ e = s + 1 then 1 else 0) +
      (if x2611_16338_vertexSum φ e = 2 * s then 1 else 0) = (1 : ℕ)) ∧
    ((e.toFinset ∩ U).card =
      2 * (if x2611_16338_vertexSum φ e = 2 then 1 else 0) +
      (if x2611_16338_vertexSum φ e = s + 1 then 1 else 0)) := by
  classical
  obtain ⟨u, v⟩ := e
  have huv : u ≠ v := ((G.mem_edgeSet).mp (G.mem_edgeFinset.mp he)).ne
  have h2 : s + 1 ≠ 2 := by omega
  have h1 : s ≠ 1 := by omega
  have hss : s + s ≠ 2 := by omega
  have hc : ({u, v} ∩ U : Finset V) = ({u, v} : Finset V).filter (· ∈ U) := by
    ext w
    simp
  by_cases hu : u ∈ U <;> by_cases hv : v ∈ U <;>
    simp [x2611_16338_vertexSum, hφ, hu, hv, Sym2.toFinset_mk_eq, hc,
      Finset.filter_insert, Finset.filter_singleton, huv, h2, h1, hss,
      Ne.symm h2, Ne.symm h1, Ne.symm hss, two_mul, Nat.add_comm]

lemma x2611_16338_cubic_incidence_counts_aux4
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (s : ℕ) (hs : 3 ≤ s) (U : Finset V)
    (φ : V → ℕ) (hφ : ∀ v, φ v = if v ∈ U then 1 else s) :
    (x2611_16338_edgeClass G φ 2).ncard +
      (x2611_16338_edgeClass G φ (s + 1)).ncard +
      (x2611_16338_edgeClass G φ (2 * s)).ncard = G.edgeSet.ncard ∧
    (∑ v ∈ U, G.degree v) =
      2 * (x2611_16338_edgeClass G φ 2).ncard +
      (x2611_16338_edgeClass G φ (s + 1)).ncard := by
  classical
  have hedge : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  simp_rw [x2611_16338_cubic_incidence_counts_aux2]
  constructor
  · rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, hedge]
    calc
      _ = ∑ e ∈ G.edgeFinset, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro e he
        exact (x2611_16338_cubic_incidence_counts_aux3 G s hs U φ hφ e he).1
      _ = _ := by simp
  · rw [x2611_16338_cubic_incidence_counts_aux1, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    exact (x2611_16338_cubic_incidence_counts_aux3 G s hs U φ hφ e he).2

theorem x2611_16338_cubic_incidence_counts
    (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsRegularOfDegree 3) (s : ℕ)
    (hs : s = Fintype.card V / 2 + 1) (hs3 : 3 ≤ s) (U : Finset V)
    (φ : V → ℕ) (hφ : ∀ v, φ v = if v ∈ U then 1 else s)
    (a b c : ℕ) (ha : a = (x2611_16338_edgeClass G φ 2).ncard)
    (hb : b = (x2611_16338_edgeClass G φ (s + 1)).ncard)
    (hc : c = (x2611_16338_edgeClass G φ (2 * s)).ncard) :
    a + b + c = G.edgeSet.ncard ∧
      G.edgeSet.ncard = 3 * Fintype.card V / 2 ∧
      G.edgeSet.ncard = 3 * s - 3 ∧
      3 * U.card = 2 * a + b ∧
      3 * (Finset.univ \ U).card = 2 * c + b := by
  classical
  obtain ⟨hp, hi⟩ := x2611_16338_cubic_incidence_counts_aux4 G s hs3 U φ hφ
  rw [← ha, ← hb, ← hc] at hp
  rw [← ha, ← hb] at hi
  have hdeg : ∀ v, G.degree v = 3 := hG.degree_eq
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hedge : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  simp_rw [hdeg] at hi hsum
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ] at hi hsum
  rw [← hedge] at hsum
  have hcard : (Finset.univ \ U).card + U.card = Fintype.card V := by
    simpa using Finset.card_sdiff_add_card_eq_card (show U ⊆ Finset.univ from Finset.subset_univ U)
  refine ⟨hp, ?_, ?_, ?_, ?_⟩ <;> omega
end

-- forge:entry x2611_16338_final_distribution kind=proved origin=paper
section
/- Section 3: final distribution -/
open Finset

theorem x2611_16338_final_distribution_aux1
    (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℕ) :
    ∑ v, f v * G.degree v =
      ∑ e ∈ G.edgeFinset, x2611_16338_vertexSum f e := by
  classical
  have hrow (v : V) : ∑ e ∈ G.edgeFinset, G.incMatrix ℕ v e = G.degree v := by
    have hh := G.sum_incMatrix_apply (R := ℕ) (a := v)
    simp only [Nat.cast_id] at hh
    rw [← hh]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    apply G.incMatrix_of_notMem_incidenceSet
    intro h
    exact he (SimpleGraph.mem_edgeFinset.mpr h.1)
  calc
    ∑ v, f v * G.degree v =
        ∑ v, ∑ e ∈ G.edgeFinset, f v * G.incMatrix ℕ v e := by
      simp_rw [← Finset.mul_sum, hrow]
    _ = ∑ e ∈ G.edgeFinset, ∑ v, f v * G.incMatrix ℕ v e := by
      rw [Finset.sum_comm]
    _ = ∑ e ∈ G.edgeFinset, x2611_16338_vertexSum f e := by
      apply Finset.sum_congr rfl
      intro e he
      have he' : e ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp he
      induction e using Sym2.inductionOn with
      | _ u v =>
        have huv : G.Adj u v := G.mem_edgeSet.mp he'
        change (∑ w, f w * G.incMatrix ℕ w s(u, v)) = f u + f v
        calc
          _ = ∑ w, ((if w = u then f w else 0) +
              (if w = v then f w else 0)) := by
            apply Finset.sum_congr rfl
            intro w _
            by_cases hwu : w = u <;> by_cases hwv : w = v <;>
              simp_all [SimpleGraph.incMatrix_apply',
                SimpleGraph.mk'_mem_incidenceSet_iff, huv.ne]
          _ = _ := by simp [Finset.sum_add_distrib]

theorem x2611_16338_final_distribution_aux2
    (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p q : ℕ) (hpq : p ≠ q)
    (U : Finset V) (φ : V → ℕ)
    (hφ : ∀ v, φ v = if v ∈ U then p else q) :
    ∑ v ∈ U, G.degree v =
      2 * (x2611_16338_edgeClass G φ (2 * p)).ncard +
        (x2611_16338_edgeClass G φ (p + q)).ncard := by
  classical
  have hcard (r : ℕ) : (x2611_16338_edgeClass G φ r).ncard =
      (G.edgeFinset.filter (fun e => x2611_16338_vertexSum φ e = r)).card := by
    have heq : x2611_16338_edgeClass G φ r =
        (↑(G.edgeFinset.filter (fun e => x2611_16338_vertexSum φ e = r)) : Set (Sym2 V)) := by
      ext e
      simp [x2611_16338_edgeClass]
    rw [heq, Set.ncard_coe_finset]
  have hpt (e : Sym2 V) : x2611_16338_vertexSum (fun v => if v ∈ U then 1 else 0) e =
      (if x2611_16338_vertexSum φ e = 2 * p then 2 else 0) +
        (if x2611_16338_vertexSum φ e = p + q then 1 else 0) := by
    induction e using Sym2.inductionOn with
    | _ u v =>
      change (if u ∈ U then 1 else 0) + (if v ∈ U then 1 else 0) =
        (if φ u + φ v = 2 * p then 2 else 0) +
        (if φ u + φ v = p + q then 1 else 0)
      rw [hφ u, hφ v]
      by_cases hu : u ∈ U <;> by_cases hv : v ∈ U <;>
        simp [hu, hv] <;> (try split_ifs) <;> omega
  have h := x2611_16338_final_distribution_aux1 V G
    (fun v => if v ∈ U then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul] at h
  simp only [Finset.sum_ite_mem, Finset.univ_inter] at h
  rw [h]
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, hcard (2 * p), hcard (p + q)]
  simp [← Finset.sum_filter, Nat.mul_comm]

theorem x2611_16338_final_distribution
    (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsRegularOfDegree 3)
    (s : ℕ) (hs : s = Fintype.card V / 2 + 1) (hs3 : 3 ≤ s)
    (U : Finset V) (φ : V → ℕ)
    (hφ : ∀ v, φ v = if v ∈ U then 1 else s)
    (hU : U.card = Fintype.card V / 2) (a b c : ℕ)
    (ha : a = (x2611_16338_edgeClass G φ 2).ncard)
    (hb : b = (x2611_16338_edgeClass G φ (s + 1)).ncard)
    (hc : c = (x2611_16338_edgeClass G φ (2 * s)).ncard)
    (hlo : s - 2 ≤ a) (hhi : a ≤ s) :
    (a = s ∧ b = s - 3 ∧ c = s) ∨
    (a = s - 1 ∧ b = s - 1 ∧ c = s - 1) ∨
    (a = s - 2 ∧ b = s + 1 ∧ c = s - 2) := by
  classical
  have hdegree := G.sum_degrees_eq_twice_card_edges
  simp_rw [hG.degree_eq] at hdegree
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hdegree
  have hn : Fintype.card V = 2 * (Fintype.card V / 2) := by omega
  have hcomp : (Finset.univ \ U).card = U.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    omega
  have hleft := x2611_16338_final_distribution_aux2 V G 1 s (by omega) U φ hφ
  have hφ' : ∀ v, φ v = if v ∈ Finset.univ \ U then s else 1 := by
    intro v
    rw [hφ]
    by_cases hv : v ∈ U <;> simp [hv]
  have hright := x2611_16338_final_distribution_aux2 V G s 1 (by omega)
    (Finset.univ \ U) φ hφ'
  simp only [hG.degree_eq, Finset.sum_const, smul_eq_mul, mul_one, Nat.one_add,
    ← ha, ← hb, ← hc, hcomp] at hleft hright
  omega
end

-- forge:entry x2611_16338_swap_decrement kind=proved origin=paper
section
/- Section 3: replacement decreases a by three -/
open SimpleGraph Finset

lemma x2611_16338_swap_decrement_aux1
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) :
    (G.induce (↑U : Set V)).edgeSet.ncard =
      (G.edgeFinset.filter (fun e => e.toFinset ⊆ U)).card := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  exact (G.card_filter_edgeFinset_toFinset_subset U).symm

lemma x2611_16338_swap_decrement_aux2
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (u : V) :
    G.edgeFinset.filter (fun e => e.toFinset ⊆ U.erase u) =
      G.edgeFinset.filter (fun e => e.toFinset ⊆ U) \ G.incidenceFinset u := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ a b =>
    simp [G.incidenceFinset_eq_filter, Sym2.toFinset_mk_eq, Sym2.mem_iff,
      Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.mem_erase,
      ne_comm] <;> tauto

lemma x2611_16338_swap_decrement_aux3
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (v : V)
    (hv : ∀ w, G.Adj v w → w ∉ U) :
    G.edgeFinset.filter (fun e => e.toFinset ⊆ insert v U) =
      G.edgeFinset.filter (fun e => e.toFinset ⊆ U) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ a b =>
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, Sym2.toFinset_mk_eq,
      Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.mem_insert]
    constructor
    · rintro ⟨hab, ha, hb⟩
      have hav : a ≠ v := by
        intro h
        subst a
        rcases hb with h | h
        · subst b
          exact G.loopless.irrefl v hab
        · exact hv b hab h
      have hbv : b ≠ v := by
        intro h
        subst b
        rcases ha with h | h
        · subst a
          exact G.loopless.irrefl v hab
        · exact hv a hab.symm h
      exact ⟨hab, ha.resolve_left hav, hb.resolve_left hbv⟩
    · rintro ⟨hab, ha, hb⟩
      exact ⟨hab, Or.inr ha, Or.inr hb⟩

lemma x2611_16338_swap_decrement_aux4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (u : V)
    (hu : u ∈ U) (hnu : ∀ w, G.Adj u w → w ∈ U) :
    G.incidenceFinset u ⊆ G.edgeFinset.filter (fun e => e.toFinset ⊆ U) := by
  classical
  intro e
  induction e using Sym2.inductionOn with
  | _ a b =>
    simp only [G.incidenceFinset_eq_filter, Finset.mem_filter,
      SimpleGraph.mem_edgeFinset, Sym2.mem_iff, Sym2.toFinset_mk_eq,
      Finset.insert_subset_iff, Finset.singleton_subset_iff]
    rintro ⟨hab, hau | hbu⟩
    · subst a
      exact ⟨hab, hu, hnu b hab⟩
    · subst b
      exact ⟨hab, hnu a hab.symm, hu⟩

theorem x2611_16338_swap_decrement
    (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsRegularOfDegree 3) (s : ℕ)
    (hs : s = Fintype.card V / 2 + 1) (hs3 : 3 ≤ s)
    (U : Finset V) (hU : U.card = Fintype.card V / 2)
    (ha : s < (G.induce (↑U : Set V)).edgeSet.ncard)
    (u v : V) (hu : u ∈ U) (hv : v ∉ U)
    (hnu : ∀ w, G.Adj u w → w ∈ U)
    (hnv : ∀ w, G.Adj v w → w ∉ U) :
    ¬ G.Adj u v ∧ (insert v (U.erase u)).card = Fintype.card V / 2 ∧
      (G.induce (↑(insert v (U.erase u)) : Set V)).edgeSet.ncard =
        (G.induce (↑U : Set V)).edgeSet.ncard - 3 := by
  classical
  refine ⟨fun h => hv (hnu v h), ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (fun h => hv (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem hu]
    have := Finset.card_pos.mpr ⟨u, hu⟩
    omega
  · rw [x2611_16338_swap_decrement_aux1,
      x2611_16338_swap_decrement_aux3 G (U.erase u) v
        (fun w hw h => hnv w hw (Finset.mem_of_mem_erase h)),
      x2611_16338_swap_decrement_aux2,
      Finset.card_sdiff_of_subset (x2611_16338_swap_decrement_aux4 G U u hu hnu),
      G.card_incidenceFinset_eq_degree, hG.degree_eq u,
      x2611_16338_swap_decrement_aux1]
end

-- forge:entry x2611_16338_relabel_one_counts kind=proved origin=paper
section
/- Section 3: relabeling a vertex with exactly one neighbor in U -/
open Finset

lemma x2611_16338_relabel_one_counts_aux1
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u : V) (f : Sym2 V → ℕ) :
    (∑ e ∈ G.incidenceFinset u, f e) =
      ∑ v ∈ G.neighborFinset u, f s(u, v) := by
  classical
  symm
  apply Finset.sum_bij (fun v _ => s(u, v))
  · intro v hv
    simpa using hv
  · intro a ha b hb hab
    exact Sym2.congr_right.mp hab
  · intro e he
    have hei := (G.mem_incidenceFinset u e).mp he
    obtain ⟨v, rfl⟩ := Sym2.mem_iff_exists.mp hei.2
    refine ⟨v, ?_, rfl⟩
    simpa using he
  · intro v hv
    rfl

lemma x2611_16338_relabel_one_counts_aux2
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (φ ψ : V → ℕ) (u : V)
    (h : ∀ v, v ≠ u → ψ v = φ v) (r : ℕ) :
    (x2611_16338_edgeClass G ψ r).ncard +
        (∑ v ∈ G.neighborFinset u, if φ u + φ v = r then 1 else 0) =
      (x2611_16338_edgeClass G φ r).ncard +
        (∑ v ∈ G.neighborFinset u, if ψ u + ψ v = r then 1 else 0) := by
  classical
  have heq :
      (∑ e ∈ G.edgeFinset, if x2611_16338_vertexSum ψ e = r then 1 else 0) +
        (∑ e ∈ G.incidenceFinset u, if x2611_16338_vertexSum φ e = r then 1 else 0) =
      (∑ e ∈ G.edgeFinset, if x2611_16338_vertexSum φ e = r then 1 else 0) +
        (∑ e ∈ G.incidenceFinset u, if x2611_16338_vertexSum ψ e = r then 1 else 0) := by
    rw [G.incidenceFinset_eq_filter, Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hu : u ∈ e
    · simp [hu, Nat.add_comm]
    · have hsum : x2611_16338_vertexSum ψ e = x2611_16338_vertexSum φ e := by
        obtain ⟨a, b⟩ := e
        have ha : a ≠ u := by simpa [Sym2.mem_iff, eq_comm] using fun hh => hu (by simp [hh])
        have hb : b ≠ u := by simpa [Sym2.mem_iff, eq_comm] using fun hh => hu (by simp [hh])
        simp [x2611_16338_vertexSum, h a ha, h b hb]
      simp [hu, hsum]
  rw [x2611_16338_relabel_one_counts_aux1,
    x2611_16338_relabel_one_counts_aux1] at heq
  have hcard (η : V → ℕ) : (x2611_16338_edgeClass G η r).ncard =
      ∑ e ∈ G.edgeFinset, if x2611_16338_vertexSum η e = r then 1 else 0 := by
    rw [Finset.sum_boole, ← Set.ncard_coe_finset]
    congr 1
    ext e
    simp [x2611_16338_edgeClass]
  rw [hcard, hcard]
  dsimp [x2611_16338_vertexSum] at heq ⊢
  exact heq

lemma x2611_16338_relabel_one_counts_aux3
    {V : Type*} [DecidableEq V] (N U : Finset V) (φ : V → ℕ) (s t r : ℕ)
    (hφ : ∀ v, φ v = if v ∈ U then 1 else s) :
    (∑ v ∈ N, if t + φ v = r then 1 else 0) =
      (N.filter (· ∈ U)).card * (if t + 1 = r then 1 else 0) +
      (N.filter (· ∉ U)).card * (if t + s = r then 1 else 0) := by
  classical
  calc
    _ = ∑ v ∈ N, if v ∈ U then (if t + 1 = r then 1 else 0)
        else (if t + s = r then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hmem : v ∈ U <;> simp [hφ, hmem]
    _ = _ := by rw [Finset.sum_ite]; simp

lemma x2611_16338_relabel_one_counts_aux4
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u : V) (U : Finset V)
    (hd : G.degree u = 3) (hdeg : ∃! v, G.Adj u v ∧ v ∈ U) :
    ((G.neighborFinset u).filter (· ∈ U)).card = 1 ∧
      ((G.neighborFinset u).filter (· ∉ U)).card = 2 := by
  classical
  obtain ⟨v, hv, huniq⟩ := hdeg
  have hf : (G.neighborFinset u).filter (· ∈ U) = {v} := by
    ext w
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    exact ⟨fun hw => huniq w hw, fun hw => hw ▸ hv⟩
  have hcard := Finset.card_filter_add_card_filter_not
    (s := G.neighborFinset u) (fun v => v ∈ U)
  rw [hf, Finset.card_singleton, G.card_neighborFinset_eq_degree, hd] at hcard
  constructor
  · simp [hf]
  · omega

theorem x2611_16338_relabel_one_counts
    (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsRegularOfDegree 3) (s : ℕ)
    (hs : s = Fintype.card V / 2 + 1) (hs3 : 3 ≤ s) (U : Finset V)
    (φ : V → ℕ) (hφ : ∀ v, φ v = if v ∈ U then 1 else s)
    (hU : U.card = Fintype.card V / 2)
    (ha : (x2611_16338_edgeClass G φ 2).ncard = s - 2)
    (hb : (x2611_16338_edgeClass G φ (s + 1)).ncard = s + 1)
    (hc : (x2611_16338_edgeClass G φ (2 * s)).ncard = s - 2)
    (u : V) (hu : u ∈ U) (hdeg : ∃! v, G.Adj u v ∧ v ∈ U) :
    (x2611_16338_edgeClass G (Function.update φ u 2) 2).ncard = s - 3 ∧
      (x2611_16338_edgeClass G (Function.update φ u 2) 3).ncard = 1 ∧
      (x2611_16338_edgeClass G (Function.update φ u 2) (s + 1)).ncard = s - 1 ∧
      (x2611_16338_edgeClass G (Function.update φ u 2) (s + 2)).ncard = 2 ∧
      (x2611_16338_edgeClass G (Function.update φ u 2) (2 * s)).ncard = s - 2 := by
  classical
  obtain ⟨hN1, hN2⟩ := x2611_16338_relabel_one_counts_aux4 G u U (hG.degree_eq u) hdeg
  have hup : ∀ v, v ≠ u → Function.update φ u 2 v = φ v := by
    intro v hv
    simp [hv]
  have hold : ∀ r, (∑ v ∈ G.neighborFinset u, if φ u + φ v = r then 1 else 0) =
      (if 2 = r then 1 else 0) + 2 * (if s + 1 = r then 1 else 0) := by
    intro r
    rw [hφ u, if_pos hu, x2611_16338_relabel_one_counts_aux3 _ U φ s 1 r hφ,
      hN1, hN2]
    simp [Nat.add_comm]
  have hnew : ∀ r, (∑ v ∈ G.neighborFinset u,
      if Function.update φ u 2 u + Function.update φ u 2 v = r then 1 else 0) =
      (if 3 = r then 1 else 0) + 2 * (if s + 2 = r then 1 else 0) := by
    intro r
    calc
      _ = ∑ v ∈ G.neighborFinset u, if 2 + φ v = r then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        have hvu : v ≠ u := (G.mem_neighborFinset u v).mp hv |>.ne.symm
        simp [hvu]
      _ = _ := by
        rw [x2611_16338_relabel_one_counts_aux3 _ U φ s 2 r hφ, hN1, hN2]
        simp [Nat.add_comm]
  have hcount : ∀ r,
      (x2611_16338_edgeClass G (Function.update φ u 2) r).ncard +
          ((if 2 = r then 1 else 0) + 2 * (if s + 1 = r then 1 else 0)) =
        (x2611_16338_edgeClass G φ r).ncard +
          ((if 3 = r then 1 else 0) + 2 * (if s + 2 = r then 1 else 0)) := by
    intro r
    have hh := x2611_16338_relabel_one_counts_aux2 G φ (Function.update φ u 2) u hup r
    rwa [hold, hnew] at hh
  have hz : ∀ r, r ≠ 2 → r ≠ s + 1 → r ≠ 2 * s →
      (x2611_16338_edgeClass G φ r).ncard = 0 := by
    intro r hr2 hrs hrss
    have hempty : x2611_16338_edgeClass G φ r = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨a, b⟩ := e
      obtain ⟨he, hsum⟩ := he
      have : φ a + φ b = r := hsum
      by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;>
        simp only [hφ, ha, hb, if_true, if_false] at this <;> omega
    simp [hempty]
  have hz3 := hz 3 (by omega) (by omega) (by omega)
  have hzs2 := hz (s + 2) (by omega) (by omega) (by omega)
  have h2 := hcount 2
  have h3 := hcount 3
  have hs1 := hcount (s + 1)
  have hs2 := hcount (s + 2)
  have h2s := hcount (2 * s)
  have hn1 : s + 1 ≠ 2 := by omega
  have hn2 : s + 2 ≠ 2 := by omega
  have hn3 : s + 1 ≠ 3 := by omega
  have hn4 : s + 2 ≠ 3 := by omega
  have hn5 : 2 * s ≠ 2 := by omega
  have hn6 : 2 * s ≠ 3 := by omega
  have hn7 : s + 1 ≠ 2 * s := by omega
  have hn8 : s + 2 ≠ 2 * s := by omega
  simp only [hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8,
    Ne.symm hn1, Ne.symm hn2, Ne.symm hn3, Ne.symm hn4, Ne.symm hn5, Ne.symm hn6,
    Nat.add_left_cancel_iff, Nat.reduceEqDiff, ite_true, ite_false,
    Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add, ha, hb, hc, hz3, hzs2] at *
  omega
end

-- forge:entry x2611_16338_initial_subset kind=proved origin=paper
section
/- Section 3: initial subset size and edge lower bound -/
open Finset

lemma x2611_16338_initial_subset_aux1
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {U W : Finset V} (hUW : U ⊆ W) :
    (G.induce (↑U : Set V)).edgeFinset.card ≤
      (G.induce (↑W : Set V)).edgeFinset.card := by
  classical
  rw [← G.card_filter_edgeFinset_toFinset_subset U,
    ← G.card_filter_edgeFinset_toFinset_subset W]
  apply Finset.card_le_card
  intro e he
  rcases Finset.mem_filter.mp he with ⟨he, hsub⟩
  exact Finset.mem_filter.mpr ⟨he, hsub.trans hUW⟩

lemma x2611_16338_initial_subset_aux2
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (U : Finset V) {u v : V}
    (hu : u ∈ U) (hv : v ∉ U) (hadj : G.Adj u v) :
    (G.induce (↑U : Set V)).edgeFinset.card <
      (G.induce (↑(insert v U) : Set V)).edgeFinset.card := by
  classical
  rw [← G.card_filter_edgeFinset_toFinset_subset U,
    ← G.card_filter_edgeFinset_toFinset_subset (insert v U)]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro e he
    rcases Finset.mem_filter.mp he with ⟨he, hsub⟩
    exact Finset.mem_filter.mpr ⟨he, hsub.trans (subset_insert v U)⟩
  · intro heq
    have hnew : s(u, v) ∈ {e ∈ G.edgeFinset | e.toFinset ⊆ insert v U} := by
      simp [Sym2.toFinset_mk_eq, hadj, hu, Finset.insert_subset_iff]
    have hold : s(u, v) ∈ {e ∈ G.edgeFinset | e.toFinset ⊆ U} := heq.symm ▸ hnew
    have hsub := (Finset.mem_filter.mp hold).2
    exact hv (hsub (by simp [Sym2.toFinset_mk_eq]))

lemma x2611_16338_initial_subset_aux3
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ v, 2 ≤ G.degree v) (U : Finset V)
    (hclosed : ∀ u ∈ U, ∀ v, G.Adj u v → v ∈ U) :
    U.card ≤ (G.induce (↑U : Set V)).edgeFinset.card := by
  classical
  have hdeg (v : (↑U : Set V)) : 2 ≤ (G.induce (↑U : Set V)).degree v := by
    have heq : (G.induce (↑U : Set V)).degree v = G.degree v := by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (SimpleGraph.degree_induce_of_neighborSet_subset
          (G := G) (s := (↑U : Set V)) (v := v) (by
            intro w hw
            exact hclosed v v.property w hw))
    rw [heq]
    exact hG v
  have hsum : 2 * U.card ≤ 2 * (G.induce (↑U : Set V)).edgeFinset.card := by
    calc
      2 * U.card = ∑ _v : (↑U : Set V), (2 : ℕ) := by simp [mul_comm]
      _ ≤ ∑ v : (↑U : Set V), (G.induce (↑U : Set V)).degree v :=
        Finset.sum_le_sum (fun v _ => hdeg v)
      _ = 2 * (G.induce (↑U : Set V)).edgeFinset.card :=
        (G.induce (↑U : Set V)).sum_degrees_eq_twice_card_edges
  omega

lemma x2611_16338_initial_subset_aux4
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ v, 2 ≤ G.degree v)
    (k : ℕ) (hk : k ≤ Fintype.card V) :
    ∃ U : Finset V, U.card = k ∧ k ≤ (G.induce (↑U : Set V)).edgeFinset.card + 1 := by
  classical
  revert hk
  induction k with
  | zero =>
      intro hk
      exact ⟨∅, rfl, Nat.zero_le _⟩
  | succ k ih =>
      intro hk
      obtain ⟨U, hcard, hedge⟩ := ih (by omega)
      by_cases hcross : ∃ u ∈ U, ∃ v, v ∉ U ∧ G.Adj u v
      · obtain ⟨u, hu, v, hv, hadj⟩ := hcross
        refine ⟨insert v U, by simp [hv, hcard], ?_⟩
        have hlt := x2611_16338_initial_subset_aux2 G U hu hv hadj
        omega
      · have hclosed : ∀ u ∈ U, ∀ v, G.Adj u v → v ∈ U := by
          intro u hu v hadj
          by_contra hv
          exact hcross ⟨u, hu, v, hv, hadj⟩
        have hbound := x2611_16338_initial_subset_aux3 G hG U hclosed
        have hproper : U ≠ Finset.univ := by
          intro heq
          have hc : U.card = Fintype.card V := by simp [heq]
          omega
        obtain ⟨v, hv⟩ : ∃ v, v ∉ U := by
          by_contra h
          apply hproper
          apply Finset.eq_univ_of_forall
          intro v
          by_contra hv
          exact h ⟨v, hv⟩
        refine ⟨insert v U, by simp [hv, hcard], ?_⟩
        have hmono := x2611_16338_initial_subset_aux1 G (subset_insert v U)
        omega

theorem x2611_16338_initial_subset
    (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsRegularOfDegree 3) (s : ℕ)
    (hs : s = Fintype.card V / 2 + 1) (hs3 : 3 ≤ s) :
    ∃ U : Finset V, U.card = Fintype.card V / 2 ∧
      Fintype.card V / 2 - 1 ≤ (G.induce (↑U : Set V)).edgeSet.ncard ∧
      s - 2 ≤ (G.induce (↑U : Set V)).edgeSet.ncard := by
  classical
  have hmin : ∀ v, 2 ≤ G.degree v := by
    intro v
    rw [hG v]
    omega
  obtain ⟨U, hcard, hedge⟩ := x2611_16338_initial_subset_aux4 G hmin
    (Fintype.card V / 2) (Nat.div_le_self _ _)
  have heq : (G.induce (↑U : Set V)).edgeSet.ncard =
      (G.induce (↑U : Set V)).edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  refine ⟨U, hcard, ?_, ?_⟩ <;> omega
end

-- forge:entry x2611_15379_cor1_2_zero kind=proved origin=paper
section
/- Corollary 1.2 (zero exponent) -/
lemma x2611_15379_cor1_2_zero_aux1 (k a b c n : ℕ) :
    x2611_15379_G k a b c
      (fun n : ℕ => ((Real.rpow (n : ℝ) 0) : ℂ)) n = 1 := by
  simp [x2611_15379_G]

theorem x2611_15379_cor1_2_zero (k a b c : ℕ) (hk : 0 < k)
    (ha : 0 < a) (hc : 0 < c) :
    IsLeast {T : ℕ | 0 < T ∧ ∀ n : ℕ, 0 < n →
      (x2611_15379_G k a b c
        (fun n : ℕ => ((Real.rpow (n : ℝ) 0) : ℂ))) (n + T) =
      (x2611_15379_G k a b c
        (fun n : ℕ => ((Real.rpow (n : ℝ) 0) : ℂ))) n} (1) := by
  constructor
  · constructor
    · decide
    · intro n hn
      simp only [x2611_15379_cor1_2_zero_aux1]
  · intro T hT
    exact hT.1
end

-- forge:entry x2611_15210_lem5_1 kind=proved origin=paper
section
/- Lemma 5.1 -/
open scoped BigOperators

lemma x2611_15210_lem5_1_aux1 (k : ℕ) (hodd : Odd k)
    (F : Type*) [Field F] [Fintype F] (hcard : Fintype.card F = 3 ^ k) :
    ¬ IsSquare (-1 : F) := by
  rw [FiniteField.isSquare_neg_one_iff, hcard]
  push Not
  obtain ⟨m, rfl⟩ := hodd
  simp [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]

lemma x2611_15210_lem5_1_aux2 (R : Type*) [CommRing R] (f : ℕ → R)
    (h0 : f 0 = 0) (h1 : f 1 = 0) (h2 : f 2 = 0)
    (h3 : f 3 = 0) (h4 : f 4 = 0) :
    (Matrix.of (fun i j : Fin 6 => f (i.val + j.val))).det = -(f 5) ^ 6 := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix,
    Fin.succAbove, Fin.castSucc, Fin.succ, h0, h1, h2, h3, h4]
  <;> ring

lemma x2611_15210_lem5_1_aux3 (F : Type*) [Field F] [CharP F 3]
    (hn : ¬ IsSquare (-1 : F)) (x : Fin 6 → F)
    (h1 : ∑ i, x i = 0) (h2 : ∑ i, x i ^ 2 = 0) (h4 : ∑ i, x i ^ 4 = 0) :
    ∃ i j : Fin 6, x i = x j ∧ i ≠ j := by
  have h3 : ∑ i, x i ^ 3 = 0 := by rw [← sum_pow_char]; simp [h1]
  have h0 : ∑ i : Fin 6, x i ^ 0 = 0 := by
    simp only [pow_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact (CharP.cast_eq_zero_iff F 3 6).mpr (by decide)
  let V := Matrix.vandermonde x
  have he : V.det ^ 2 = -(∑ i, x i ^ 5) ^ 6 := by
    rw [pow_two]
    conv_lhs => lhs; rw [← Matrix.det_transpose V]
    rw [← Matrix.det_mul]
    have hM : V.transpose * V = Matrix.of (fun i j : Fin 6 => ∑ k, x k ^ (i.val + j.val)) := by
      ext i j
      exact Matrix.vandermonde_transpose_mul_vandermonde x i j
    rw [hM]
    exact x2611_15210_lem5_1_aux2 F (fun n => ∑ i, x i ^ n) h0
      (by simpa using h1) h2 h3 h4
  have hV : V.det = 0 := by
    by_cases hs : (∑ i, x i ^ 5) = 0
    · simpa [hs] using he
    · exfalso
      apply hn
      refine ⟨V.det / (∑ i, x i ^ 5) ^ 3, ?_⟩
      field_simp
      linear_combination -he
  exact Matrix.det_vandermonde_eq_zero_iff.mp hV

lemma x2611_15210_lem5_1_aux4 (F : Type*) [Field F] [CharP F 3]
    (a b c : F) (h1 : a + b + c = 0) (h2 : a ^ 2 + b ^ 2 + c ^ 2 = 0) :
    a = b ∧ b = c := by
  have hc : c = -a-b := by linear_combination h1
  rw [hc] at h2
  have hh : (a-b)^2 = 0 := by
    linear_combination (norm := ring_nf) -h2
    reduce_mod_char!
  have hab : a = b := sub_eq_zero.mp ((sq_eq_zero_iff).mp hh)
  subst b
  constructor
  · rfl
  · rw [hc]
    linear_combination (a * (CharP.cast_eq_zero F 3))

lemma x2611_15210_lem5_1_aux5 (F : Type*) [Field F] [CharP F 3]
    (a b c d : F) (h1 : a+b+c+d = 0)
    (h2 : a^2+b^2+c^2+d^2 = 0) (h4 : a^4+b^4+c^4+d^4 = 0) :
    a = 0 ∨ b = 0 ∨ c = 0 ∨ d = 0 := by
  have hd : d = -a-b-c := by linear_combination h1
  rw [hd] at h2 h4
  have hh : a*b*c*d = 0 := by
    rw [hd]
    linear_combination (norm := ring_nf) -h4 - (a^2+b^2+c^2+(-a-b-c)^2) * h2
    reduce_mod_char!
  simpa only [mul_eq_zero, or_assoc] using hh

lemma x2611_15210_lem5_1_aux6 (F : Type*) [Field F] [CharP F 3] [DecidableEq F]
    (y : Fin 6 → F) (hy0 : y 0 = 0) (hy1 : y 1 = 0)
    (h1 : ∑ i, y i = 0) (h2 : ∑ i, y i ^ 2 = 0) (h4 : ∑ i, y i ^ 4 = 0) :
    (∀ i, y i = 0) ∨ ∃ b : F, b ≠ 0 ∧
      (Finset.univ.filter (fun i => y i = 0)).card = 3 ∧
      (Finset.univ.filter (fun i => y i = b)).card = 3 ∧
      ∀ i, y i = 0 ∨ y i = b := by
  classical
  have h1' : y 2 + y 3 + y 4 + y 5 = 0 := by
    simpa [Fin.sum_univ_succ, hy0, hy1, add_assoc] using h1
  have h2' : y 2 ^ 2 + y 3 ^ 2 + y 4 ^ 2 + y 5 ^ 2 = 0 := by
    simpa [Fin.sum_univ_succ, hy0, hy1, add_assoc] using h2
  have h4' : y 2 ^ 4 + y 3 ^ 4 + y 4 ^ 4 + y 5 ^ 4 = 0 := by
    simpa [Fin.sum_univ_succ, hy0, hy1, add_assoc] using h4
  rcases x2611_15210_lem5_1_aux5 F _ _ _ _ h1' h2' h4' with hz | hz | hz | hz
  · have ht := x2611_15210_lem5_1_aux4 F (y 3) (y 4) (y 5)
      (by simpa [hz] using h1') (by simpa [hz] using h2')
    by_cases hb : y 3 = 0
    · left; intro i; fin_cases i <;> simp_all
    · right
      refine ⟨y 3, hb, ?_, ?_, ?_⟩
      · simp [Fin.card_filter_univ_succ, Finset.filter_singleton, Fin.succ, hy0, hy1, hz, ← ht.1, ← ht.2, hb]
      · simp [Fin.card_filter_univ_succ, Finset.filter_singleton, Fin.succ, hy0, hy1, hz, ← ht.1, ← ht.2, hb, Ne.symm hb]
      · intro i; fin_cases i <;> simp_all
  · have ht := x2611_15210_lem5_1_aux4 F (y 2) (y 4) (y 5)
      (by simpa [hz] using h1') (by simpa [hz] using h2')
    by_cases hb : y 2 = 0
    · left; intro i; fin_cases i <;> simp_all
    · right
      refine ⟨y 2, hb, ?_, ?_, ?_⟩
      · simp [Fin.card_filter_univ_succ, Finset.filter_singleton, Fin.succ, hy0, hy1, hz, ← ht.1, ← ht.2, hb]
      · simp [Fin.card_filter_univ_succ, Finset.filter_singleton, Fin.succ, hy0, hy1, hz, ← ht.1, ← ht.2, hb, Ne.symm hb]
      · intro i; fin_cases i <;> simp_all
  · have ht := x2611_15210_lem5_1_aux4 F (y 2) (y 3) (y 5)
      (by simpa [hz] using h1') (by simpa [hz] using h2')
    by_cases hb : y 2 = 0
    · left; intro i; fin_cases i <;> simp_all
    · right
      refine ⟨y 2, hb, ?_, ?_, ?_⟩
      · simp [Fin.card_filter_univ_succ, Finset.filter_singleton, Fin.succ, hy0, hy1, hz, ← ht.1, ← ht.2, hb]
      · simp [Fin.card_filter_univ_succ, Finset.filter_singleton, Fin.succ, hy0, hy1, hz, ← ht.1, ← ht.2, hb, Ne.symm hb]
      · intro i; fin_cases i <;> simp_all
  · have ht := x2611_15210_lem5_1_aux4 F (y 2) (y 3) (y 4)
      (by simpa [hz] using h1') (by simpa [hz] using h2')
    by_cases hb : y 2 = 0
    · left; intro i; fin_cases i <;> simp_all
    · right
      refine ⟨y 2, hb, ?_, ?_, ?_⟩
      · simp [Fin.card_filter_univ_succ, Finset.filter_singleton, Fin.succ, hy0, hy1, hz, ← ht.1, ← ht.2, hb]
      · simp [Fin.card_filter_univ_succ, Finset.filter_singleton, Fin.succ, hy0, hy1, hz, ← ht.1, ← ht.2, hb, Ne.symm hb]
      · intro i; fin_cases i <;> simp_all

lemma x2611_15210_lem5_1_aux7 (F : Type*) [Field F] [CharP F 3]
    (x : Fin 6 → F) (a : F)
    (h1 : ∑ i, x i = 0) (h2 : ∑ i, x i ^ 2 = 0) (h4 : ∑ i, x i ^ 4 = 0) :
    (∑ i, (x i - a)) = 0 ∧ (∑ i, (x i-a)^2) = 0 ∧ (∑ i, (x i-a)^4) = 0 := by
  have h3 : ∑ i, x i ^ 3 = 0 := by rw [← sum_pow_char]; simp [h1]
  have h6 : (6 : F) = 0 := (CharP.cast_eq_zero_iff F 3 6).mpr (by decide)
  have e2 (t : F) : (t-a)^2 = t^2 + t*a + a^2 := by
    ring_nf
    reduce_mod_char!
    ring_nf
    reduce_mod_char!
  have e4 (t : F) : (t-a)^4 = t^4 - a*t^3 - a^3*t + a^4 := by
    ring_nf
    reduce_mod_char!
  refine ⟨?_, ?_, ?_⟩
  · simp [Finset.sum_sub_distrib, h1, h6, nsmul_eq_mul]
  · simp_rw [e2]
    simp [Finset.sum_add_distrib, ← Finset.sum_mul, h1, h2, h6, nsmul_eq_mul]
  · simp_rw [e4]
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h1, h3, h4, h6, nsmul_eq_mul]

lemma x2611_15210_lem5_1_aux8 (α β : Type*) [Fintype α] [Fintype β]
    (e : α ≃ β) (p : β → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun i => p (e i))).card = (Finset.univ.filter p).card := by
  classical
  rw [← Finset.card_map e.toEmbedding, Finset.map_filter]
  simp

lemma x2611_15210_lem5_1_aux9 (F : Type*) [Field F] [CharP F 3] [DecidableEq F]
    (hn : ¬ IsSquare (-1 : F)) (x : Fin 6 → F)
    (h1 : ∑ i, x i = 0) (h2 : ∑ i, x i ^ 2 = 0) (h4 : ∑ i, x i ^ 4 = 0) :
    (∃ a : F, ∀ i, x i = a) ∨ ∃ a b : F, a ≠ b ∧
      (Finset.univ.filter (fun i => x i = a)).card = 3 ∧
      (Finset.univ.filter (fun i => x i = b)).card = 3 ∧
      ∀ i, x i = a ∨ x i = b := by
  classical
  obtain ⟨i,j,hij,hne⟩ := x2611_15210_lem5_1_aux3 F hn x h1 h2 h4
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair
    (fun t : Fin 2 => (t.castLE (by decide : 2 ≤ 6))) ![i,j]
    (Fin.castLE_injective (by decide : 2 ≤ 6)) (by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all)
  have he0 : e 0 = i := he 0
  have he1 : e 1 = j := he 1
  let z : Fin 6 → F := fun t => x (e t)
  have hz1 : ∑ t, z t = 0 := by simpa [z, e.sum_comp] using h1
  have hz2 : ∑ t, z t ^ 2 = 0 := by exact (Equiv.sum_comp e (fun t => x t ^ 2)).trans h2
  have hz4 : ∑ t, z t ^ 4 = 0 := by exact (Equiv.sum_comp e (fun t => x t ^ 4)).trans h4
  obtain ⟨hs1,hs2,hs4⟩ := x2611_15210_lem5_1_aux7 F z (x i) hz1 hz2 hz4
  let y : Fin 6 → F := fun t => z t - x i
  have hy0 : y 0 = 0 := by simp [y,z,he0]
  have hy1 : y 1 = 0 := by simp [y,z,he1,← hij]
  rcases x2611_15210_lem5_1_aux6 F y hy0 hy1 hs1 hs2 hs4 with hy | ⟨b,hb,hc0,hcb,hy⟩
  · left
    refine ⟨x i, ?_⟩
    intro t
    obtain ⟨s,rfl⟩ := e.surjective t
    exact sub_eq_zero.mp (hy s)
  · right
    refine ⟨x i, b + x i, ?_, ?_, ?_, ?_⟩
    · intro h
      apply hb
      linear_combination -h
    · rw [← x2611_15210_lem5_1_aux8 _ _ e (fun t => x t = x i)]
      simpa [y,z,sub_eq_zero] using hc0
    · rw [← x2611_15210_lem5_1_aux8 _ _ e (fun t => x t = b + x i)]
      simpa [y,z,sub_eq_iff_eq_add] using hcb
    · intro t
      obtain ⟨s,rfl⟩ := e.surjective t
      rcases hy s with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (sub_eq_iff_eq_add.mp h)

lemma x2611_15210_lem5_1_aux10 (F : Type*) [Field F] [CharP F 3] [DecidableEq F]
    (hn : ¬ IsSquare (-1 : F)) (I : Finset (F × Fin 2)) (hI : I.card = 6) :
    (∑ p ∈ I, (![p.1, p.1 ^ 2, p.1 ^ 4] : Fin 3 → F)) ≠ 0 := by
  classical
  intro hs
  let e : Fin 6 ≃ I := (I.equivFinOfCardEq hI).symm
  let x : Fin 6 → F := fun t => (e t).val.1
  have heS (n : ℕ) : (∑ t, x t ^ n) = ∑ p ∈ I, p.1 ^ n := by
    change (∑ t, (e t).val.1 ^ n) = _
    rw [Equiv.sum_comp e (fun t : I => t.val.1 ^ n)]
    exact Finset.sum_coe_sort I (fun p : F × Fin 2 => p.1 ^ n)
  have h1 : ∑ t, x t = 0 := by
    have h := congrArg (fun v : Fin 3 → F => v 0) hs
    simp only [Finset.sum_apply, Pi.zero_apply, Matrix.cons_val_zero] at h
    have he1 := heS 1
    simp only [pow_one] at he1
    rw [he1]
    exact h
  have h2 : ∑ t, x t ^ 2 = 0 := by
    rw [heS]
    simpa using congrArg (fun v : Fin 3 → F => v 1) hs
  have h4 : ∑ t, x t ^ 4 = 0 := by
    rw [heS]
    simpa using congrArg (fun v : Fin 3 → F => v 2) hs
  have hbound (a : F) : (Finset.univ.filter (fun t => x t = a)).card ≤ 2 := by
    let T := Finset.univ.filter (fun t => x t = a)
    have hinj : Function.Injective (fun t : T => (e t.val).val.2) := by
      intro s t hst
      apply Subtype.ext
      apply e.injective
      apply Subtype.ext
      apply Prod.ext _ hst
      exact (Finset.mem_filter.mp s.property).2.trans (Finset.mem_filter.mp t.property).2.symm
    have hh := Fintype.card_le_of_injective _ hinj
    change T.card ≤ 2
    simpa only [Fintype.card_coe, Fintype.card_fin] using hh
  rcases x2611_15210_lem5_1_aux9 F hn x h1 h2 h4 with ⟨a,ha⟩ | ⟨a,b,hab,hca,hcb,hx⟩
  · have hb := hbound a
    have hc : (Finset.univ.filter (fun t => x t = a)).card = 6 := by simp [ha]
    omega
  · have hb := hbound a
    omega

lemma x2611_15210_lem5_1_aux11 (k : ℕ) (F : Type*) [Field F] [Fintype F] [CharP F 3]
    (hcard : Fintype.card F = 3 ^ k) :
    Nonempty ((Fin 3 → F) ≃+ (Fin (3*k) → ZMod 3)) := by
  classical
  letI : Algebra (ZMod 3) F := ZMod.algebra F 3
  have hdF : Module.finrank (ZMod 3) F = k := by
    apply Nat.pow_right_injective (a := 3) (by decide)
    simpa only [ZMod.card, hcard] using (Module.card_eq_pow_finrank (K := ZMod 3) (V := F)).symm
  have hd : Module.finrank (ZMod 3) (Fin 3 → F) =
      Module.finrank (ZMod 3) (Fin (3*k) → ZMod 3) := by
    simp [Module.finrank_pi_fintype, hdF]
  exact ⟨(LinearEquiv.ofFinrankEq (R := ZMod 3) (Fin 3 → F) (Fin (3*k) → ZMod 3) hd).toAddEquiv⟩

lemma x2611_15210_lem5_1_aux12 (k : ℕ) (F : Type*) [Field F] [Fintype F] [CharP F 3]
    [DecidableEq F] (hn : ¬ IsSquare (-1 : F)) (hcard : Fintype.card F = 3 ^ k) :
    2 * 3 ^ k ≤ x2611_15210_A 6 (Fin (3*k) → ZMod 3) := by
  classical
  obtain ⟨e⟩ := x2611_15210_lem5_1_aux11 k F hcard
  have hz : ∀ g : Fin (3*k) → ZMod 3, 6 • g = 0 := by
    intro g
    ext j
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
    rw [show ((6 : ℕ) : ZMod 3) = 0 from
      (CharP.cast_eq_zero_iff (ZMod 3) 3 6).mpr (by decide), zero_mul]
  have hmain := x2611_15210_lem2_2_aux5 6 (by decide) (Fin (3*k) → ZMod 3) hz
    (F × Fin 2) (fun p => e (![p.1,p.1^2,p.1^4]))
  have hle : Fintype.card (F × Fin 2) ≤ x2611_15210_A 6 (Fin (3*k) → ZMod 3) := by
    apply hmain
    intro I hI hs
    apply x2611_15210_lem5_1_aux10 F hn I hI
    apply e.injective
    simpa only [map_sum, map_zero] using hs
  simpa [Fintype.card_prod, hcard, Nat.mul_comm] using hle

theorem x2611_15210_lem5_1 (k : ℕ) (hk : 1 ≤ k) (hodd : Odd k)
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hcard : Fintype.card F = 3 ^ k) :
    (∀ x : Fin 6 → F, (∑ i, x i) = 0 → (∑ i, x i ^ 2) = 0 →
      (∑ i, x i ^ 4) = 0 →
      (∃ a : F, ∀ i, x i = a) ∨ ∃ a b : F, a ≠ b ∧
        (Finset.univ.filter (fun i : Fin 6 => x i = a)).card = 3 ∧
        (Finset.univ.filter (fun i : Fin 6 => x i = b)).card = 3 ∧
        ∀ i, x i = a ∨ x i = b) ∧
    2 * 3 ^ k ≤ x2611_15210_A 6 (Fin (3 * k) → ZMod 3) := by
  letI : CharP F 3 := charP_of_card_eq_prime_pow hcard
  have hn := x2611_15210_lem5_1_aux1 k hodd F hcard
  exact ⟨fun x h1 h2 h4 => x2611_15210_lem5_1_aux9 F hn x h1 h2 h4,
    x2611_15210_lem5_1_aux12 k F hn hcard⟩
end

-- forge:entry x2611_15379_lem2_1 kind=proved origin=paper
section
/- Lemma 2.1 -/
theorem x2611_15379_lem2_1_aux1 {α : Type*} (f : ℕ → α) (p : ℕ)
    (hp : ∀ n : ℕ, 0 < n → f (n + p) = f n) (k n : ℕ) (hn : 0 < n) :
    f (n + k * p) = f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc, hp (n + k * p) (by omega), ih]

theorem x2611_15379_lem2_1_aux2 {α : Type*} (f : ℕ → α) {p T : ℕ}
    (hp : ∀ n : ℕ, 0 < n → f (n + p) = f n) (hdiv : p ∣ T) :
    ∀ n : ℕ, 0 < n → f (n + T) = f n := by
  obtain ⟨k, rfl⟩ := hdiv
  intro n hn
  simpa only [Nat.mul_comm] using x2611_15379_lem2_1_aux1 f p hp k n hn

theorem x2611_15379_lem2_1_aux3 {α : Type*} (f : ℕ → α) {q T : ℕ}
    (hq : IsLeast {p : ℕ | 0 < p ∧ ∀ n : ℕ, 0 < n → f (n + p) = f n} q)
    (hT : ∀ n : ℕ, 0 < n → f (n + T) = f n) : q ∣ T := by
  have hmod : ∀ n : ℕ, 0 < n → f (n + T % q) = f n := by
    intro n hn
    calc
      f (n + T % q) = f ((n + T % q) + (T / q) * q) :=
        (x2611_15379_lem2_1_aux1 f q hq.1.2 (T / q) (n + T % q) (by omega)).symm
      _ = f (n + T) := by
        rw [Nat.mul_comm (T / q) q, Nat.add_assoc, Nat.mod_add_div]
      _ = f n := hT n hn
  apply Nat.dvd_of_mod_eq_zero
  by_contra hne
  have hpos : 0 < T % q := Nat.pos_of_ne_zero hne
  have hle := hq.2 ⟨hpos, hmod⟩
  exact (not_lt_of_ge hle) (Nat.mod_lt T hq.1.1)

theorem x2611_15379_lem2_1 (m : ℕ) (q : Fin m → ℕ) (H : Fin m → ℕ → ℂ)
    (hq : ∀ i, 0 < q i) (hcop : Pairwise (fun i j => Nat.Coprime (q i) (q j)))
    (hnz : ∀ i n, 0 < n → H i n ≠ 0)
    (hperiod : ∀ i, IsLeast {T : ℕ | 0 < T ∧ ∀ n : ℕ, 0 < n → (H i) (n + T) = (H i) n} (q i)) :
    IsLeast {T : ℕ | 0 < T ∧ ∀ n : ℕ, 0 < n →
      (fun n : ℕ => ∏ i : Fin m, H i n) (n + T) =
      (fun n : ℕ => ∏ i : Fin m, H i n) n} (∏ i : Fin m, q i) := by
  classical
  constructor
  · refine ⟨Finset.prod_pos (fun i _ => hq i), ?_⟩
    intro n hn
    apply Finset.prod_congr rfl
    intro i hi
    exact x2611_15379_lem2_1_aux2 (H i) (hperiod i).1.2
      (Finset.dvd_prod_of_mem q hi) n hn
  · intro T hT
    have hiT : ∀ i, q i ∣ T := by
      intro i
      let R : ℕ := ∏ j ∈ (Finset.univ : Finset (Fin m)).erase i, q j
      have hR : Nat.Coprime (q i) R := by
        apply Nat.coprime_prod_right_iff.mpr
        intro j hj
        exact hcop (Finset.ne_of_mem_erase hj).symm
      have hRT : ∀ n : ℕ, 0 < n →
          (∏ j : Fin m, H j (n + T * R)) = ∏ j : Fin m, H j n :=
        x2611_15379_lem2_1_aux2 (fun n => ∏ j : Fin m, H j n) hT.2
          (dvd_mul_right T R)
      have hiRT : ∀ n : ℕ, 0 < n → H i (n + T * R) = H i n := by
        intro n hn
        have hrest : (∏ j ∈ (Finset.univ : Finset (Fin m)).erase i,
            H j (n + T * R)) = ∏ j ∈ (Finset.univ : Finset (Fin m)).erase i, H j n := by
          apply Finset.prod_congr rfl
          intro j hj
          apply x2611_15379_lem2_1_aux2 (H j) (hperiod j).1.2 _ n hn
          exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem q hj) T
        have heq := hRT n hn
        rw [← Finset.mul_prod_erase Finset.univ (fun j => H j (n + T * R))
          (Finset.mem_univ i),
          ← Finset.mul_prod_erase Finset.univ (fun j => H j n) (Finset.mem_univ i),
          hrest] at heq
        exact mul_right_cancel₀ (Finset.prod_ne_zero_iff.mpr (fun j _ => hnz j n hn)) heq
      exact hR.dvd_of_dvd_mul_right
        (x2611_15379_lem2_1_aux3 (H i) (hperiod i) hiRT)
    have hdiv : (∏ i : Fin m, q i) ∣ T := by
      apply Fintype.prod_dvd_of_isRelPrime
      · intro i j hij
        exact Nat.coprime_iff_isRelPrime.mp (hcop hij)
      · exact hiT
    exact Nat.le_of_dvd hT.1 hdiv
end

-- forge:entry x2611_16338_zero_neighbor_completion_table kind=proved origin=paper
section
/- Section 3: first completion table -/
lemma x2611_16338_zero_neighbor_completion_table_aux1 {α : Type*} [Fintype α]
    (A : Set α) (lo hi : ℕ) (hcard : A.ncard = hi + 1 - lo) :
    ∃ f : α → ℕ, Set.InjOn f A ∧ f '' A = Set.Icc lo hi := by
  classical
  obtain ⟨g, hg, hgi⟩ := x2611_16338_lemma2_1_aux1 A.toFinset
  let f := fun x => lo + g x
  have hfi : Set.InjOn f A := by
    intro x hx y hy he
    apply hgi (by simpa using hx) (by simpa using hy)
    dsimp [f] at he
    omega
  refine ⟨f, hfi, ?_⟩
  apply Set.eq_of_subset_of_ncard_le
  · rintro y ⟨x, hx, rfl⟩
    have hh := hg x (by simpa using hx)
    have hc : A.toFinset.card = hi + 1 - lo := by
      calc
        A.toFinset.card = (↑A.toFinset : Set α).ncard := (Set.ncard_coe_finset _).symm
        _ = hi + 1 - lo := by simpa only [Set.coe_toFinset] using hcard
    dsimp [f]
    constructor <;> omega
  · rw [hfi.ncard_image]
    simpa using hcard.ge
  · exact Set.finite_Icc _ _

lemma x2611_16338_zero_neighbor_completion_table_aux2 {α : Type*} [Fintype α]
    (E : Set α) (w : α → ℕ) (lo hi : ℕ → ℕ)
    (hc : ∀ r, ({e | e ∈ E ∧ w e = r} : Set α).ncard = hi r + 1 - lo r) :
    ∃ ψ : α → ℕ, ∀ r,
      Set.InjOn ψ {e | e ∈ E ∧ w e = r} ∧
      ψ '' {e | e ∈ E ∧ w e = r} = Set.Icc (lo r) (hi r) := by
  classical
  choose f hf hi using fun r =>
    x2611_16338_zero_neighbor_completion_table_aux1 {e | e ∈ E ∧ w e = r} (lo r) (hi r) (hc r)
  refine ⟨fun e => f (w e) e, fun r => ?_⟩
  have heq : Set.EqOn (fun e => f (w e) e) (f r) {e | e ∈ E ∧ w e = r} := by
    intro e he
    change f (w e) e = f r e
    rw [he.2]
  exact ⟨(hf r).congr heq.symm, (Set.image_congr heq).trans (hi r)⟩

lemma x2611_16338_zero_neighbor_completion_table_aux3
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 3 ≤ s) (U : Finset V) (φ : V → ℕ)
    (hφ : ∀ v, φ v = if v ∈ U then 1 else s) (u : V) (hu : u ∈ U)
    (hdeg : ∀ v, G.Adj u v → v ∉ U) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    (x2611_16338_vertexSum φ e = 2 ∨ x2611_16338_vertexSum φ e = s + 1 ∨
      x2611_16338_vertexSum φ e = 2 * s) ∧
    (if e ∈ G.incidenceSet u then
      x2611_16338_vertexSum φ e = s + 1 ∧
      x2611_16338_vertexSum (Function.update φ u 2) e = s + 2
    else x2611_16338_vertexSum (Function.update φ u 2) e = x2611_16338_vertexSum φ e) := by
  have hsum (e : Sym2 V) : x2611_16338_vertexSum φ e = 2 ∨
      x2611_16338_vertexSum φ e = s + 1 ∨ x2611_16338_vertexSum φ e = 2 * s := by
    induction e using Sym2.inductionOn with
    | _ a b =>
      simp only [x2611_16338_vertexSum, Sym2.lift_mk, hφ]
      split_ifs <;> omega
  refine ⟨hsum e, ?_⟩
  induction e using Sym2.inductionOn with
  | _ a b =>
    have hab : G.Adj a b := he
    by_cases ha : a = u
    · subst a
      have hbu := hab.ne.symm
      have hb := hdeg b hab
      have hi : s(u, b) ∈ G.incidenceSet u := G.mk'_mem_incidenceSet_left_iff.mpr hab
      simp only [if_pos hi]
      simp [x2611_16338_vertexSum, hφ, hu, hb, hbu] <;> omega
    · by_cases hb : b = u
      · subst b
        have haU := hdeg a hab.symm
        have hi : s(a, u) ∈ G.incidenceSet u := G.mk'_mem_incidenceSet_right_iff.mpr hab
        simp only [if_pos hi]
        simp [x2611_16338_vertexSum, hφ, hu, haU, ha] <;> omega
      · have hi : s(a, b) ∉ G.incidenceSet u := by
          simp [SimpleGraph.mk'_mem_incidenceSet_iff, Ne.symm ha, Ne.symm hb]
        simp [hi, x2611_16338_vertexSum, Function.update_of_ne ha, Function.update_of_ne hb]

lemma x2611_16338_zero_neighbor_completion_table_aux4
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 3 ≤ s) (U : Finset V) (φ : V → ℕ)
    (hφ : ∀ v, φ v = if v ∈ U then 1 else s) (u : V) (hu : u ∈ U)
    (hdeg : ∀ v, G.Adj u v → v ∉ U) :
    x2611_16338_edgeClass G (Function.update φ u 2) 2 = x2611_16338_edgeClass G φ 2 ∧
    x2611_16338_edgeClass G (Function.update φ u 2) (s + 1) =
      x2611_16338_edgeClass G φ (s + 1) \ G.incidenceSet u ∧
    x2611_16338_edgeClass G (Function.update φ u 2) (s + 2) = G.incidenceSet u ∧
    x2611_16338_edgeClass G (Function.update φ u 2) (2 * s) = x2611_16338_edgeClass G φ (2 * s) := by
  have h (e : Sym2 V) (he : e ∈ G.edgeSet) :=
    x2611_16338_zero_neighbor_completion_table_aux3 G s hs U φ hφ u hu hdeg e he
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext e <;>
    simp only [x2611_16338_edgeClass, Set.mem_setOf_eq, Set.mem_sdiff]
  all_goals by_cases he : e ∈ G.edgeSet
  all_goals try { have hn : e ∉ G.incidenceSet u := fun hi => he hi.1; simp [he, hn] }
  all_goals
    have ⟨hh, hh'⟩ := h e he
    by_cases hi : e ∈ G.incidenceSet u
    · simp only [if_pos hi] at hh'
      obtain ⟨hold, hnew⟩ := hh'
      simp only [he, hi, true_and, not_true_eq_false, and_false, iff_true]
      simp only [hnew, hold] <;> clear * - s hs <;> constructor <;> intro hn <;> first | exact False.elim hn | omega
    · simp only [if_neg hi] at hh'
      simp only [he, hi, true_and, not_false_eq_true, and_true, iff_false]
      rcases hh with hh | hh | hh <;> omega

theorem x2611_16338_zero_neighbor_completion_table (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsRegularOfDegree 3) (s : ℕ) (hs : s = Fintype.card V / 2 + 1) (hs3 : 3 ≤ s) (U : Finset V) (φ : V → ℕ) (hφ : ∀ v, φ v = if v ∈ U then 1 else s) (hU : U.card = Fintype.card V / 2) (ha : (x2611_16338_edgeClass G φ (2)).ncard = s - 2) (hb : (x2611_16338_edgeClass G φ (s + 1)).ncard = s + 1) (hc : (x2611_16338_edgeClass G φ (2 * s)).ncard = s - 2) (u : V) (hu : u ∈ U) (hdeg : ∀ v, G.Adj u v → v ∉ U) : ∃ ψ : Sym2 V → ℕ, x2611_16338_totalLabeling G s (Function.update φ u 2) ψ ∧ ∀ r lo hi : ℕ, (r, lo, hi) ∈ ([(2, 1, s - 2), (s + 1, 1, s - 2), (s + 2, s - 2, s), (2 * s, 3, s)] : List (ℕ × ℕ × ℕ)) → ψ '' x2611_16338_edgeClass G (Function.update φ u 2) r = Set.Icc lo hi ∧ (fun e => x2611_16338_vertexSum (Function.update φ u 2) e + ψ e) '' x2611_16338_edgeClass G (Function.update φ u 2) r = Set.Icc (r + lo) (r + hi) := by
  classical
  let χ := Function.update φ u 2
  let w := x2611_16338_vertexSum χ
  have hclasses := x2611_16338_zero_neighbor_completion_table_aux4 G s hs3 U φ hφ u hu hdeg
  have hI : (G.incidenceSet u).ncard = 3 := by
    rw [← G.coe_incidenceFinset, Set.ncard_coe_finset, G.card_incidenceFinset_eq_degree, hG u]
  have hsub : G.incidenceSet u ⊆ x2611_16338_edgeClass G φ (s + 1) := by
    intro e he
    have hh := x2611_16338_zero_neighbor_completion_table_aux3 G s hs3 U φ hφ u hu hdeg e he.1
    simp only [if_pos he] at hh
    exact ⟨he.1, hh.2.1⟩
  have hcards : (x2611_16338_edgeClass G χ 2).ncard = s - 2 ∧
      (x2611_16338_edgeClass G χ (s + 1)).ncard = s - 2 ∧
      (x2611_16338_edgeClass G χ (s + 2)).ncard = 3 ∧
      (x2611_16338_edgeClass G χ (2 * s)).ncard = s - 2 := by
    change (x2611_16338_edgeClass G (Function.update φ u 2) 2).ncard = _ ∧ _
    rw [hclasses.1, hclasses.2.1, hclasses.2.2.1, hclasses.2.2.2,
      Set.ncard_sdiff hsub, ha, hb, hc, hI]
    omega
  have hsum (e : Sym2 V) (he : e ∈ G.edgeSet) :
      w e = 2 ∨ w e = s + 1 ∨ w e = s + 2 ∨ w e = 2 * s := by
    have ⟨hh, hh'⟩ := x2611_16338_zero_neighbor_completion_table_aux3 G s hs3 U φ hφ u hu hdeg e he
    dsimp only [w, χ]
    split_ifs at hh' <;> omega
  let lo : ℕ → ℕ := fun r => if r = 2 ∨ r = s + 1 then 1 else if r = s + 2 then s - 2 else if r = 2 * s then 3 else 1
  let hi : ℕ → ℕ := fun r => if r = 2 ∨ r = s + 1 then s - 2 else if r = s + 2 ∨ r = 2 * s then s else 0
  have hvals : lo 2 = 1 ∧ hi 2 = s - 2 ∧ lo (s + 1) = 1 ∧ hi (s + 1) = s - 2 ∧
      lo (s + 2) = s - 2 ∧ hi (s + 2) = s ∧ lo (2 * s) = 3 ∧ hi (2 * s) = s := by
    simp [lo, hi, show 2 * s ≠ 2 by omega, show 2 * s ≠ s + 1 by omega,
      show s + 2 ≠ 2 by omega, show 2 * s ≠ s + 2 by omega, show s ≠ 0 by omega]
  have hcard (r : ℕ) : ({e | e ∈ G.edgeSet ∧ w e = r} : Set (Sym2 V)).ncard = hi r + 1 - lo r := by
    change (x2611_16338_edgeClass G χ r).ncard = _
    by_cases h2 : r = 2
    · subst r
      rw [hcards.1, hvals.1, hvals.2.1]
      omega
    by_cases hB : r = s + 1
    · subst r
      rw [hcards.2.1, hvals.2.2.1, hvals.2.2.2.1]
      omega
    by_cases hD : r = s + 2
    · subst r
      rw [hcards.2.2.1, hvals.2.2.2.2.1, hvals.2.2.2.2.2.1]
      omega
    by_cases hC : r = 2 * s
    · subst r
      rw [hcards.2.2.2, hvals.2.2.2.2.2.2.1, hvals.2.2.2.2.2.2.2]
      omega
    have hempty : x2611_16338_edgeClass G χ r = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro e he
      have hh := hsum e he.1
      have her : w e = r := he.2
      omega
    simp [hempty, lo, hi, h2, hB, hD, hC]
  obtain ⟨ψ, hψ⟩ := x2611_16338_zero_neighbor_completion_table_aux2 G.edgeSet w lo hi hcard
  have himg (r : ℕ) : ψ '' x2611_16338_edgeClass G χ r = Set.Icc (lo r) (hi r) := (hψ r).2
  have hbnd (e : Sym2 V) (he : e ∈ G.edgeSet) : lo (w e) ≤ ψ e ∧ ψ e ≤ hi (w e) := by
    apply (himg (w e)).subset
    exact ⟨e, ⟨he, rfl⟩, rfl⟩
  refine ⟨ψ, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro v
    by_cases hv : v = u
    · subst v
      simp only [Function.update_self]
      omega
    · rw [Function.update_of_ne hv, hφ]
      split_ifs <;> omega
  · intro e he
    have hh := hbnd e he
    rcases hsum e he with hh' | hh' | hh' | hh' <;>
      rw [hh'] at hh <;> simp only [hvals.1, hvals.2.1, hvals.2.2.1,
        hvals.2.2.2.1, hvals.2.2.2.2.1, hvals.2.2.2.2.2.1,
        hvals.2.2.2.2.2.2.1, hvals.2.2.2.2.2.2.2] at hh <;> omega
  · intro e he f hf hef
    have heB := hbnd e he
    have hfB := hbnd f hf
    change w e + ψ e = w f + ψ f at hef
    have hwe : w e = w f := by
      rcases hsum e he with hew | hew | hew | hew <;>
        rcases hsum f hf with hfw | hfw | hfw | hfw <;>
        rw [hew] at heB <;> rw [hfw] at hfB <;>
        simp only [hvals.1, hvals.2.1, hvals.2.2.1,
          hvals.2.2.2.1, hvals.2.2.2.2.1, hvals.2.2.2.2.2.1,
          hvals.2.2.2.2.2.2.1, hvals.2.2.2.2.2.2.2] at heB hfB <;> omega
    apply (hψ (w e)).1 ⟨he, rfl⟩ ⟨hf, hwe.symm⟩
    omega
  · intro r l h hr
    have hv : lo r = l ∧ hi r = h := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hr
      rcases hr with hr | hr | hr | hr
      · rcases hr with ⟨rfl, rfl, rfl⟩
        exact ⟨hvals.1, hvals.2.1⟩
      · rcases hr with ⟨rfl, rfl, rfl⟩
        exact ⟨hvals.2.2.1, hvals.2.2.2.1⟩
      · rcases hr with ⟨rfl, rfl, rfl⟩
        exact ⟨hvals.2.2.2.2.1, hvals.2.2.2.2.2.1⟩
      · rcases hr with ⟨rfl, rfl, rfl⟩
        exact ⟨hvals.2.2.2.2.2.2.1, hvals.2.2.2.2.2.2.2⟩
    refine ⟨by simpa only [hv.1, hv.2] using himg r, ?_⟩
    calc
      (fun e => x2611_16338_vertexSum χ e + ψ e) '' x2611_16338_edgeClass G χ r =
          (fun n => r + n) '' (ψ '' x2611_16338_edgeClass G χ r) := by
        rw [Set.image_image]
        apply Set.image_congr
        intro e he
        exact congrArg (fun n => n + ψ e) he.2
      _ = Set.Icc (r + l) (r + h) := by
        rw [himg r, hv.1, hv.2, Set.image_const_add_Icc]
end

-- forge:entry x2611_15379_lem2_2 kind=proved origin=paper
section
/- Lemma 2.2 -/
open Finset

theorem x2611_15379_lem2_2_aux1 (k : ℕ) (P : ℤ → Prop) [DecidablePred P] :
    ((Finset.Icc (0 : ℤ) (k : ℤ)).filter P).card =
      (k + 1).count (fun i : ℕ => P (i : ℤ)) := by
  rw [Int.Icc_eq_finset_map, Finset.filter_map, Finset.card_map]
  simp [Nat.count_eq_card_filter_range, Function.Embedding.trans_apply]

theorem x2611_15379_lem2_2_aux2 (q k : ℕ) (hq : 0 < q) (u z : ℤ)
    (hu : IsCoprime u (q : ℤ)) (r : ℕ) (hr : (q : ℤ) ∣ z + u * r) :
    ((Finset.Icc (0 : ℤ) (k : ℤ)).filter
      (fun i => (q : ℤ) ∣ z + u * i)).card =
      (k + 1) / q + if r % q < (k + 1) % q then 1 else 0 := by
  classical
  have he (i : ℤ) : (q : ℤ) ∣ z + u * i ↔ i ≡ (r : ℤ) [ZMOD q] := by
    rw [Int.modEq_iff_dvd]
    constructor
    · intro hi
      have hd : (q : ℤ) ∣ u * ((r : ℤ) - i) := by
        convert Int.dvd_sub hr hi using 2 <;> ring
      exact hu.symm.dvd_of_dvd_mul_left hd
    · intro hi
      have hd := dvd_mul_of_dvd_right hi u
      convert Int.dvd_sub hr hd using 2 <;> ring
  simp_rw [he]
  rw [x2611_15379_lem2_2_aux1]
  simpa only [Int.natCast_modEq_iff] using Nat.count_modEq_card (k + 1) hq r

theorem x2611_15379_lem2_2_aux3 (q : ℕ) (hq : 0 < q) (u z : ℤ)
    (hu : IsCoprime u (q : ℤ)) :
    ∃ r : ℕ, r < q ∧ (q : ℤ) ∣ z + u * r := by
  obtain ⟨a, b, hab⟩ := hu
  let r : ℤ := (-a * z) % q
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by exact_mod_cast hq.ne')
  have hrq : r < q := Int.emod_lt_of_pos _ (by exact_mod_cast hq)
  refine ⟨r.toNat, by omega, ?_⟩
  rw [Int.toNat_of_nonneg hr0]
  have hd : (q : ℤ) ∣ (-a * z) - r := (Int.mod_modEq (-a * z) q).dvd
  have hb : (q : ℤ) ∣ z + u * (-a * z) := by
    refine ⟨b * z, ?_⟩
    nlinarith [congrArg (fun t : ℤ => t * z) hab]
  have hd' := dvd_mul_of_dvd_right hd u
  convert Int.dvd_sub hb hd' using 2 <;> ring


theorem x2611_15379_lem2_2_aux4 (q k : ℕ) (u z : ℤ) :
    ((Finset.Icc (0 : ℤ) (k : ℤ)).filter
      (fun i => (q : ℤ) ∣ (z + u) + u * i)).card +
      (if (q : ℤ) ∣ z then 1 else 0) =
    ((Finset.Icc (0 : ℤ) (k : ℤ)).filter
      (fun i => (q : ℤ) ∣ z + u * i)).card +
      (if (q : ℤ) ∣ z + u * (k + 1 : ℕ) then 1 else 0) := by
  classical
  simp_rw [x2611_15379_lem2_2_aux1]
  have hs := Nat.count_succ (fun i : ℕ => (q : ℤ) ∣ z + u * i) (k + 1)
  have ht := Nat.count_succ' (fun i : ℕ => (q : ℤ) ∣ z + u * i) (k + 1)
  have he : (fun i : ℕ => (q : ℤ) ∣ z + u * (i + 1 : ℕ)) =
      (fun i : ℕ => (q : ℤ) ∣ (z + u) + u * i) := by
    funext i
    congr 1
    push_cast
    ring
  simp only [he] at ht
  simp only [Nat.cast_zero, mul_zero, add_zero] at ht
  exact ht.symm.trans hs


theorem x2611_15379_lem2_2_aux5 (q k : ℕ) (u : ℤ) :
    Function.Periodic (fun z : ℤ =>
      ((Finset.Icc (0 : ℤ) (k : ℤ)).filter
        (fun i => (q : ℤ) ∣ z + u * i)).card) (q : ℤ) := by
  classical
  intro z
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i hi
  rw [show z + (q : ℤ) + u * i = (z + u * i) + q by ring,
    Int.dvd_add_left (Int.dvd_refl _)]

theorem x2611_15379_lem2_2_aux6 (q k : ℕ) (u : ℤ)
    (hu : IsCoprime u (q : ℤ)) (hn : ¬ q ∣ k + 1) (T : ℤ)
    (hT : Function.Periodic (fun z : ℤ =>
      ((Finset.Icc (0 : ℤ) (k : ℤ)).filter
        (fun i => (q : ℤ) ∣ z + u * i)).card) T) : (q : ℤ) ∣ T := by
  classical
  have hnu : ¬ (q : ℤ) ∣ u * (k + 1 : ℕ) := by
    intro h
    apply hn
    exact_mod_cast hu.symm.dvd_of_dvd_mul_left h
  have h0 := x2611_15379_lem2_2_aux4 q k u 0
  simp only [zero_add, Int.dvd_zero, if_true, hnu, if_false] at h0
  have ht := x2611_15379_lem2_2_aux4 q k u T
  have ht0 := hT 0
  have htu := hT u
  simp only [zero_add] at ht0
  dsimp only at htu
  rw [add_comm T u, htu, ht0] at ht
  by_contra h
  simp only [h, if_false] at ht
  split_ifs at ht <;> omega


theorem x2611_15379_lem2_2 (p k j : ℕ) (hp : Nat.Prime p) (u : ℤ)
    (hu : Int.gcd u (p : ℤ) = 1) (hk : 0 < k) (hj : 0 < j) (hpk : p ^ j ≤ k) :
    (p ^ j ∣ k + 1 → ∀ z : ℤ, x2611_15379_N p j k u z = (k + 1) / p ^ j) ∧
    (¬ p ^ j ∣ k + 1 →
      (∃ ℓ : ℕ, (∀ z : ℤ, x2611_15379_N p j k u z = ℓ ∨
        x2611_15379_N p j k u z = ℓ + 1) ∧
        (∃ z : ℤ, x2611_15379_N p j k u z = ℓ) ∧
        (∃ z : ℤ, x2611_15379_N p j k u z = ℓ + 1)) ∧
      IsLeast {T : ℤ | 0 < T ∧ Function.Periodic (x2611_15379_N p j k u) T}
        ((p : ℤ) ^ j)) := by
  classical
  have hq : 0 < p ^ j := pow_pos hp.pos j
  have hcop : IsCoprime u ((p ^ j : ℕ) : ℤ) := by
    simpa only [Nat.cast_pow] using
      (Int.isCoprime_iff_gcd_eq_one.mpr hu).pow_right (n := j)
  have hc (z : ℤ) (r : ℕ) (hr : ((p ^ j : ℕ) : ℤ) ∣ z + u * r) :
      x2611_15379_N p j k u z = (k + 1) / p ^ j +
        if r % p ^ j < (k + 1) % p ^ j then 1 else 0 := by
    simpa only [x2611_15379_N, Nat.cast_pow] using
      x2611_15379_lem2_2_aux2 (p ^ j) k hq u z hcop r hr
  constructor
  · intro hd z
    obtain ⟨r, hr, hz⟩ := x2611_15379_lem2_2_aux3 (p ^ j) hq u z hcop
    simpa [Nat.mod_eq_zero_of_dvd hd] using hc z r hz
  · intro hd
    constructor
    · refine ⟨(k + 1) / p ^ j, ?_, ?_, ?_⟩
      · intro z
        obtain ⟨r, hr, hz⟩ := x2611_15379_lem2_2_aux3 (p ^ j) hq u z hcop
        have he := hc z r hz
        split_ifs at he with h
        · exact Or.inr he
        · exact Or.inl (by simpa using he)
      · let r := (k + 1) % p ^ j
        refine ⟨-u * r, ?_⟩
        have hr : ((p ^ j : ℕ) : ℤ) ∣ -u * r + u * r := by
          simp
        have he := hc (-u * r) r hr
        simpa [r, Nat.mod_eq_of_lt (Nat.mod_lt (k + 1) hq)] using he
      · refine ⟨0, ?_⟩
        have hr : ((p ^ j : ℕ) : ℤ) ∣ (0 : ℤ) + u * (0 : ℕ) := by simp
        have he := hc 0 0 hr
        have hm : 0 < (k + 1) % p ^ j := Nat.pos_of_ne_zero
          (fun h => hd (Nat.dvd_of_mod_eq_zero h))
        simpa [hm] using he
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact_mod_cast hq
      · intro z
        simpa only [x2611_15379_N, Nat.cast_pow] using
          x2611_15379_lem2_2_aux5 (p ^ j) k u z
      · intro T hT
        have hper : Function.Periodic (fun z : ℤ =>
            ((Finset.Icc (0 : ℤ) (k : ℤ)).filter
              (fun i => ((p ^ j : ℕ) : ℤ) ∣ z + u * i)).card) T := by
          intro z
          simpa only [x2611_15379_N, Nat.cast_pow] using hT.2 z
        have hdT := x2611_15379_lem2_2_aux6 (p ^ j) k u hcop hd T hper
        simpa only [Nat.cast_pow] using Int.le_of_dvd hT.1 hdT
end

-- forge:entry x2611_15358_small_component_bound kind=proved origin=paper
section
/- Lemma 2.6, proof (small-component estimate) -/
lemma x2611_15358_small_component_bound_aux1
    {V : Type*} [Finite V] (G : SimpleGraph V) (k : ℕ)
    (hcard : Nat.card V < 2 * k) {C D : G.ConnectedComponent}
    (hC : k ≤ Nat.card C.supp) (hD : k ≤ Nat.card D.supp) : C = D := by
  by_contra hne
  have hd := G.pairwise_disjoint_supp_connectedComponent hne
  have hb := Set.ncard_le_card (C.supp ∪ D.supp)
  rw [Set.ncard_union_eq hd] at hb
  simp only [Nat.card_coe_set_eq] at hC hD
  omega

lemma x2611_15358_small_component_bound_aux2
    {V : Type*} [Finite V] (G : SimpleGraph V) (hcard : Nat.card V ≤ 7) :
    Nat.card G.ConnectedComponent - 1 ≤
      Nat.card {C : G.ConnectedComponent // Nat.card C.supp = 1} +
      Nat.card {C : G.ConnectedComponent // Nat.card C.supp = 2} +
      Nat.card {C : G.ConnectedComponent // Nat.card C.supp = 3} := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let f : G.ConnectedComponent → ℕ := fun C => Nat.card C.supp
  have hpos (C : G.ConnectedComponent) : 0 < f C := by
    have h := C.nonempty_supp.ncard_pos
    simpa only [f, Nat.card_coe_set_eq] using h
  have hbig : (Finset.univ.filter (fun C : G.ConnectedComponent => ¬ f C ≤ 3)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro C hC D hD
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC hD
    apply x2611_15358_small_component_bound_aux1 G 4 (by omega)
    · change 4 ≤ f C
      omega
    · change 4 ≤ f D
      omega
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset G.ConnectedComponent)) (fun C => f C ≤ 3)
  have heq : Finset.univ.filter (fun C : G.ConnectedComponent => f C ≤ 3) =
      ((Finset.univ.filter (fun C => f C = 1)) ∪
       (Finset.univ.filter (fun C => f C = 2))) ∪
       (Finset.univ.filter (fun C => f C = 3)) := by
    ext C
    have hp := hpos C
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  have hsmall : (Finset.univ.filter (fun C : G.ConnectedComponent => f C ≤ 3)).card ≤
      (Finset.univ.filter (fun C => f C = 1)).card +
      (Finset.univ.filter (fun C => f C = 2)).card +
      (Finset.univ.filter (fun C => f C = 3)).card := by
    rw [heq]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hcount (k : ℕ) : Nat.card {C : G.ConnectedComponent // Nat.card C.supp = k} =
      (Finset.univ.filter (fun C : G.ConnectedComponent => f C = k)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcount 1, hcount 2, hcount 3, Nat.card_eq_fintype_card]
  simp only [Finset.card_univ] at hsplit
  omega

theorem x2611_15358_small_component_bound (G : SimpleGraph (Fin 14))
    (hdeg : ∀ v : Fin 14, 4 ≤ Nat.card (G.neighborSet v))
    (hq : Nat.card (Gᶜ).edgeSet ≤ 15) :
    x2611_15358_D G ≤ x2611_15358_N G 1 + x2611_15358_N G 2 + x2611_15358_N G 3 := by
  classical
  unfold x2611_15358_D x2611_15358_N
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro U hU
  apply x2611_15358_small_component_bound_aux2
  have hcard := (Finset.mem_powersetCard.mp hU).2
  simpa using hcard.le
end

-- forge:entry x2611_16338_one_neighbor_completion_table kind=proved origin=paper
section
/- Section 3: second completion table -/
lemma x2611_16338_one_neighbor_completion_table_aux1
    {α : Type*} (A : Set α) (hA : A.Finite) (lo hi : ℕ)
    (hc : A.ncard = hi + 1 - lo) :
    ∃ f : α → ℕ, Set.BijOn f A (Set.Icc lo hi) := by
  apply hA.exists_bijOn_of_encard_eq
  rw [← hA.cast_ncard_eq, ← (Set.finite_Icc lo hi).cast_ncard_eq,
    Set.ncard_Icc_nat, hc]

lemma x2611_16338_one_neighbor_completion_table_aux2
    {α : Type*} [Finite α] (E : Set α) (f : α → ℕ)
    (s : ℕ) (R : Set ℕ) (lo hi : ℕ → ℕ)
    (hcover : ∀ e ∈ E, f e ∈ R)
    (hc : ∀ r ∈ R, {e | e ∈ E ∧ f e = r}.ncard = hi r + 1 - lo r)
    (hb : ∀ r ∈ R, 1 ≤ lo r ∧ hi r ≤ s)
    (hsep : ∀ r ∈ R, ∀ t ∈ R, ∀ a ∈ Set.Icc (lo r) (hi r),
      ∀ b ∈ Set.Icc (lo t) (hi t), r + a = t + b → r = t) :
    ∃ ψ : α → ℕ,
      (∀ e ∈ E, 1 ≤ ψ e ∧ ψ e ≤ s) ∧
      Set.InjOn (fun e => f e + ψ e) E ∧
      ∀ r ∈ R,
        ψ '' {e | e ∈ E ∧ f e = r} = Set.Icc (lo r) (hi r) ∧
        (fun e => f e + ψ e) '' {e | e ∈ E ∧ f e = r} =
          Set.Icc (r + lo r) (r + hi r) := by
  classical
  have hex : ∀ r : ℕ, ∃ g : α → ℕ, r ∈ R →
      Set.BijOn g {e | e ∈ E ∧ f e = r} (Set.Icc (lo r) (hi r)) := by
    intro r
    by_cases hr : r ∈ R
    · obtain ⟨g, hg⟩ := x2611_16338_one_neighbor_completion_table_aux1
        {e | e ∈ E ∧ f e = r} (Set.toFinite _) (lo r) (hi r) (hc r hr)
      exact ⟨g, fun _ => hg⟩
    · exact ⟨fun _ => 0, fun h => (hr h).elim⟩
  choose g hg using hex
  let ψ : α → ℕ := fun e => g (f e) e
  have hj : ∀ r ∈ R, Set.BijOn ψ {e | e ∈ E ∧ f e = r}
      (Set.Icc (lo r) (hi r)) := by
    intro r hr
    apply (hg r hr).congr
    intro e he
    simp only [ψ, he.2]
  have hm (e) (he : e ∈ E) : ψ e ∈ Set.Icc (lo (f e)) (hi (f e)) :=
    (hj (f e) (hcover e he)).mapsTo ⟨he, rfl⟩
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro e he
    have hm' := hm e he
    have hb' := hb (f e) (hcover e he)
    exact ⟨hb'.1.trans hm'.1, hm'.2.trans hb'.2⟩
  · intro e he d hd hed
    have heq := hsep (f e) (hcover e he) (f d) (hcover d hd)
      (ψ e) (hm e he) (ψ d) (hm d hd) hed
    apply (hj (f e) (hcover e he)).injOn ⟨he, rfl⟩ ⟨hd, heq.symm⟩
    dsimp only at hed
    omega
  · intro r hr
    have him := (hj r hr).image_eq
    refine ⟨him, ?_⟩
    calc
      (fun e => f e + ψ e) '' {e | e ∈ E ∧ f e = r} =
          (fun n => r + n) '' (ψ '' {e | e ∈ E ∧ f e = r}) := by
        rw [Set.image_image]
        apply Set.image_congr
        intro e he
        simp only [Function.comp_apply, he.2]
      _ = Set.Icc (r + lo r) (r + hi r) := by
        rw [him, Set.image_const_add_Icc]

theorem x2611_16338_one_neighbor_completion_table
    (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsRegularOfDegree 3) (s : ℕ)
    (hs : s = Fintype.card V / 2 + 1) (hs3 : 3 ≤ s) (U : Finset V)
    (φ : V → ℕ) (hφ : ∀ v, φ v = if v ∈ U then 1 else s)
    (hU : U.card = Fintype.card V / 2)
    (ha : (x2611_16338_edgeClass G φ 2).ncard = s - 2)
    (hb : (x2611_16338_edgeClass G φ (s + 1)).ncard = s + 1)
    (hc : (x2611_16338_edgeClass G φ (2 * s)).ncard = s - 2)
    (u : V) (hu : u ∈ U) (hdeg : ∃! v, G.Adj u v ∧ v ∈ U) :
    ∃ ψ : Sym2 V → ℕ,
      x2611_16338_totalLabeling G s (Function.update φ u 2) ψ ∧
      ∀ r lo hi : ℕ,
        (r, lo, hi) ∈ ([(2, 1, s - 3), (3, s - 2, s - 2),
          (s + 1, 1, s - 1), (s + 2, s - 1, s), (2 * s, 3, s)] :
            List (ℕ × ℕ × ℕ)) →
        ψ '' x2611_16338_edgeClass G (Function.update φ u 2) r = Set.Icc lo hi ∧
        (fun e => x2611_16338_vertexSum (Function.update φ u 2) e + ψ e) ''
          x2611_16338_edgeClass G (Function.update φ u 2) r =
            Set.Icc (r + lo) (r + hi) := by
  classical
  obtain ⟨hc2, hc3, hcs1, hcs2, hc2s⟩ :=
    x2611_16338_relabel_one_counts V G hG s hs hs3 U φ hφ hU ha hb hc u hu hdeg
  let η := Function.update φ u 2
  let f := x2611_16338_vertexSum η
  let R : Set ℕ := {2, 3, s + 1, s + 2, 2 * s}
  let lo : ℕ → ℕ := fun r =>
    if r = 2 then 1 else if r = 3 then s - 2 else
      if r = s + 1 then 1 else if r = s + 2 then s - 1 else 3
  let hi : ℕ → ℕ := fun r =>
    if r = 2 then s - 3 else if r = 3 then s - 2 else
      if r = s + 1 then s - 1 else s
  have hval (v) : η v = 1 ∨ η v = 2 ∨ η v = s := by
    by_cases hv : v = u
    · simp [η, hv]
    · simp only [η, Function.update_of_ne hv, hφ]
      split_ifs <;> simp
  have hηu : η u = 2 := by simp [η]
  have hval' (v) (hv : v ≠ u) : η v = 1 ∨ η v = s := by
    simp only [η, Function.update_of_ne hv, hφ]
    split_ifs <;> simp
  have hcover : ∀ e ∈ G.edgeSet, f e ∈ R := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab : a ≠ b := (show G.Adj a b from he).ne
      change η a + η b ∈ R
      by_cases hau : a = u
      · have hbu : b ≠ u := fun h => hab (hau.trans h.symm)
        have hb := hval' b hbu
        rw [hau, hηu]
        rcases hb with hb | hb <;> simp [hb, R] <;> omega
      · have ha := hval' a hau
        have hb := hval b
        rcases ha with ha | ha <;> rcases hb with hb | hb | hb <;>
          simp [ha, hb, R] <;> omega
  have hneq : 2 ≠ s + 1 ∧ 2 ≠ s + 2 ∧ 2 ≠ 2 * s ∧
      3 ≠ s + 1 ∧ 3 ≠ s + 2 ∧ 3 ≠ 2 * s ∧
      s + 1 ≠ 2 * s ∧ s + 2 ≠ 2 * s := by omega
  rcases hneq with ⟨hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8⟩
  have hp2 : lo 2 = 1 ∧ hi 2 = s - 3 := by simp [lo, hi]
  have hp3 : lo 3 = s - 2 ∧ hi 3 = s - 2 := by simp [lo, hi]
  have hps1 : lo (s + 1) = 1 ∧ hi (s + 1) = s - 1 := by
    simp [lo, hi, Ne.symm hn1, Ne.symm hn4]
  have hps2 : lo (s + 2) = s - 1 ∧ hi (s + 2) = s := by
    simp [lo, hi, Ne.symm hn2, Ne.symm hn5] <;> omega
  have hp2s : lo (2 * s) = 3 ∧ hi (2 * s) = s := by
    simp [lo, hi, Ne.symm hn3, Ne.symm hn6, Ne.symm hn7, Ne.symm hn8]
  have hcounts : ∀ r ∈ R,
      {e | e ∈ G.edgeSet ∧ f e = r}.ncard = hi r + 1 - lo r := by
    intro r hr
    simp only [R, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    change (x2611_16338_edgeClass G (Function.update φ u 2) r).ncard = _
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp only [hp2.1, hp2.2, hp3.1, hp3.2, hps1.1, hps1.2,
        hps2.1, hps2.2, hp2s.1, hp2s.2] <;> omega
  have hbounds : ∀ r ∈ R, 1 ≤ lo r ∧ hi r ≤ s := by
    intro r hr
    simp only [R, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp only [hp2.1, hp2.2, hp3.1, hp3.2, hps1.1, hps1.2,
        hps2.1, hps2.2, hp2s.1, hp2s.2] <;> omega
  have hsep : ∀ r ∈ R, ∀ t ∈ R, ∀ a ∈ Set.Icc (lo r) (hi r),
      ∀ b ∈ Set.Icc (lo t) (hi t), r + a = t + b → r = t := by
    intro r hr t ht a ha b hb heq
    simp only [R, Set.mem_insert_iff, Set.mem_singleton_iff] at hr ht
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rcases ht with rfl | rfl | rfl | rfl | rfl <;>
      simp only [hp2.1, hp2.2, hp3.1, hp3.2, hps1.1, hps1.2,
        hps2.1, hps2.2, hp2s.1, hp2s.2, Set.mem_Icc] at ha hb <;> omega
  obtain ⟨ψ, hψ, hinj, him⟩ := x2611_16338_one_neighbor_completion_table_aux2
    G.edgeSet f s R lo hi hcover hcounts hbounds hsep
  refine ⟨ψ, ⟨?_, hψ, hinj⟩, ?_⟩
  · intro v
    change 1 ≤ η v ∧ η v ≤ s
    rcases hval v with hv | hv | hv <;> omega
  · intro r l h hrow
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrow
    rcases hrow with hrow | hrow | hrow | hrow | hrow
    all_goals
      rcases hrow with ⟨hr, hl, hh⟩
      subst r l h
    · have hh := him 2 (by simp [R])
      simpa only [hp2.1, hp2.2, f, η, x2611_16338_edgeClass] using hh
    · have hh := him 3 (by simp [R])
      simpa only [hp3.1, hp3.2, f, η, x2611_16338_edgeClass] using hh
    · have hh := him (s + 1) (by simp [R])
      simpa only [hps1.1, hps1.2, f, η, x2611_16338_edgeClass] using hh
    · have hh := him (s + 2) (by simp [R])
      simpa only [hps2.1, hps2.2, f, η, x2611_16338_edgeClass] using hh
    · have hh := him (2 * s) (by simp [R])
      simpa only [hp2s.1, hp2s.2, f, η, x2611_16338_edgeClass] using hh
end

-- forge:entry x2611_15358_pair_common_bound kind=proved origin=paper
section
/- Lemma 2.6, proof (common neighbors of a pair) -/
lemma x2611_15358_pair_common_bound_aux1 {V : Type*} [Finite V]
    (H : SimpleGraph V) (S : Finset V) :
    S.card * Nat.card {v : V // ∀ x ∈ S, H.Adj x v} ≤ Nat.card H.edgeSet := by
  classical
  let f : S × {v : V // ∀ x ∈ S, H.Adj x v} → H.edgeSet :=
    fun p => ⟨s(p.1.1, p.2.1), H.mem_edgeSet.mpr (p.2.2 _ p.1.2)⟩
  have hf : Function.Injective f := by
    intro p q hpq
    have he : s(p.1.1, p.2.1) = s(q.1.1, q.2.1) := congrArg Subtype.val hpq
    rcases Sym2.eq_iff.mp he with h | h
    · exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
    · have hloop := q.2.2 p.1.1 p.1.2
      rw [← h.1] at hloop
      exact (H.irrefl hloop).elim
  simpa only [Nat.card_prod, Nat.card_eq_finsetCard]
    using Nat.card_le_card_of_injective f hf

theorem x2611_15358_pair_common_bound (G : SimpleGraph (Fin 14))
    (hdeg : ∀ v : Fin 14, 4 ≤ Nat.card (G.neighborSet v))
    (hq : Nat.card (Gᶜ).edgeSet ≤ 15) (S : Finset (Fin 14)) (hS : S.card = 2) :
    x2611_15358_t G S ≤ (Nat.card (Gᶜ).edgeSet) / 2 ∧
      (Nat.card (Gᶜ).edgeSet) / 2 ≤ 15 / 2 ∧ (15 : ℕ) / 2 = 7 := by
  have h := x2611_15358_pair_common_bound_aux1 Gᶜ S
  rw [hS] at h
  change 2 * x2611_15358_t G S ≤ Nat.card (Gᶜ).edgeSet at h
  omega
end

-- forge:entry x2611_15379_thmB kind=proved origin=paper
section
/- Theorem B ([3], Theorem 1.2) -/
open scoped BigOperators

lemma x2611_15379_thmB_aux1 {α : Type*} (f : ℕ → α) (L c P : ℕ)
    (hL : 0 < L) (hper : ∀ n, f (n + L) = f n)
    (hP : IsLeast {T : ℕ | 0 < T ∧ ∀ n : ℕ, 0 < n → f (n + T) = f n} P) :
    IsLeast {T : ℕ | 0 < T ∧ ∀ n : ℕ, 0 < n →
      f (n + T + c) = f (n + c)} P := by
  have hiter (n q : ℕ) : f (n + q * L) = f n := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul, ← Nat.add_assoc, hper, ih]
  constructor
  · refine ⟨hP.1.1, ?_⟩
    intro n hn
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hP.1.2 (n + c) (by omega)
  · intro T hT
    apply hP.2
    refine ⟨hT.1, ?_⟩
    intro n hn
    have hc : c * (L - 1) + c = c * L := by
      rw [← Nat.mul_succ]
      congr 1
      omega
    have H := hT.2 (n + c * (L - 1)) (by omega)
    have h1 : n + c * (L - 1) + T + c = (n + T) + c * L := by omega
    have h2 : n + c * (L - 1) + c = n + c * L := by omega
    rw [h1, h2, hiter, hiter] at H
    exact H

lemma x2611_15379_thmB_aux2 {K : Type*} [Field K] [CharZero K]
    (f : ℕ → ℕ) (g : ℕ → K) (C : K) (hC : C ≠ 0)
    (hfg : ∀ n, 0 < n → g n = C * (f n : K)) (P : ℕ)
    (hP : IsLeast {T : ℕ | 0 < T ∧ ∀ n : ℕ, 0 < n → f (n + T) = f n} P) :
    IsLeast {T : ℕ | 0 < T ∧ ∀ n : ℕ, 0 < n → g (n + T) = g n} P := by
  constructor
  · refine ⟨hP.1.1, ?_⟩
    intro n hn
    rw [hfg (n + P) (by omega), hfg n hn, hP.1.2 n hn]
  · intro T hT
    apply hP.2
    refine ⟨hT.1, ?_⟩
    intro n hn
    have H := hT.2 n hn
    rw [hfg (n + T) (by omega), hfg n hn] at H
    exact_mod_cast (mul_left_cancel₀ hC H)

lemma x2611_15379_thmB_aux3 (L d c : ℕ) (hL : 0 < L) (hd : 0 < d) :
    IsLeast {T : ℕ | 0 < T ∧ ∀ n : ℕ, 0 < n →
      (∏ i ∈ Finset.range d, Nat.gcd (n + T + c + i) L) =
        ∏ i ∈ Finset.range d, Nat.gcd (n + c + i) L}
      (∏ p ∈ (L.primeFactors.filter (fun p => d.factorization p < L.factorization p)),
        p ^ L.factorization p) := by
  exact x2611_15379_thmB_aux1
    (fun n => ∏ i ∈ Finset.range d, Nat.gcd (n + i) L) L c _ hL
    (fun n => x2611_15379_thmA_aux2 L d n L hL (Or.inl dvd_rfl))
    (x2611_15379_thmA_aux7 L d hL hd)

lemma x2611_15379_thmB_aux4 (N a : ℕ) :
    0 < ∏ p ∈ (N.primeFactors.filter (fun p => ¬ p ∣ a)), p ^ N.factorization p := by
  classical
  exact Finset.prod_pos (fun p hp => pow_pos
    (Nat.pos_of_mem_primeFactors (Finset.mem_filter.mp hp).1) _)

lemma x2611_15379_thmB_aux5 (s : Finset ℕ) (e : ℕ → ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p) (p : ℕ) :
    (∏ q ∈ s, q ^ e q).factorization p = if p ∈ s then e p else 0 := by
  classical
  rw [Nat.factorization_prod_apply (fun q hq => pow_ne_zero _ (hs q hq).ne_zero)]
  trans ∑ q ∈ s, if q = p then e q else 0
  · apply Finset.sum_congr rfl
    intro q hq
    simp [(hs q hq).factorization_pow, Finsupp.single_apply]
  · simp

lemma x2611_15379_thmB_aux6 (N a : ℕ) (hN : N ≠ 0) :
    let M := ∏ p ∈ (N.primeFactors.filter (fun p => ¬ p ∣ a)), p ^ N.factorization p
    M ∣ N ∧ Nat.Coprime a M ∧
      ∀ d : ℕ, d ∣ N → Nat.Coprime a d → d ∣ M := by
  classical
  dsimp only
  let s := N.primeFactors.filter (fun p => ¬ p ∣ a)
  let M := ∏ p ∈ s, p ^ N.factorization p
  have hM : M ≠ 0 := Nat.ne_of_gt (x2611_15379_thmB_aux4 N a)
  have hfac (p : ℕ) : M.factorization p = if p ∈ s then N.factorization p else 0 :=
    x2611_15379_thmB_aux5 s N.factorization
      (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1) p
  have hd : M ∣ N := by
    apply (Nat.factorization_le_iff_dvd hM hN).mp
    intro p
    rw [hfac]
    split_ifs <;> omega
  have hc : Nat.Coprime a M := by
    apply Nat.coprime_of_dvd'
    intro p hp hpa hpM
    have H := (hp.dvd_iff_one_le_factorization hM).mp hpM
    rw [hfac] at H
    split_ifs at H with hps
    · exact False.elim ((Finset.mem_filter.mp hps).2 hpa)
    · omega
  refine ⟨hd, hc, ?_⟩
  intro d hdN hda
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hN hdN
  apply (Nat.factorization_le_iff_dvd hd0 hM).mp
  intro p
  rw [hfac]
  split_ifs with hps
  · exact ((Nat.factorization_le_iff_dvd hd0 hN).mpr hdN) p
  · by_cases hp : Nat.Prime p
    · by_cases hpd : p ∣ d
      · have hpa : ¬ p ∣ a := by
          intro hpa
          have H : p ∣ 1 := by
            rw [← hda.gcd_eq_one]
            exact Nat.dvd_gcd hpa hpd
          exact hp.not_dvd_one H
        exact False.elim (hps (Finset.mem_filter.mpr
          ⟨hp.mem_primeFactors (hpd.trans hdN) hN, hpa⟩))
      · simp [Nat.factorization_eq_zero_of_not_dvd hpd]
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

lemma x2611_15379_thmB_aux7 (k a b n i j : ℕ) (hab : Nat.Coprime a b)
    (hi : i ≤ k) (hj : j ≤ k) (hne : i ≠ j) :
    Nat.gcd (b + a * (n + i)) (b + a * (n + j)) ∣ Nat.lcmUpto k := by
  have H (i j : ℕ) (hi : i ≤ k) (hj : j ≤ k) (hij : i < j) :
      Nat.gcd (b + a * (n + i)) (b + a * (n + j)) ∣ Nat.lcmUpto k := by
    let d := Nat.gcd (b + a * (n + i)) (b + a * (n + j))
    have hcop : Nat.Coprime a (b + a * (n + i)) := by
      simpa using (Nat.coprime_add_mul_right_right a b (n + i)).mpr hab
    have hcopd : Nat.Coprime d a :=
      (Nat.Coprime.of_dvd_right (Nat.gcd_dvd_left _ _) hcop).symm
    have hdiff : d ∣ a * (j - i) := by
      have H := Nat.dvd_sub (Nat.gcd_dvd_right (b + a * (n + i))
        (b + a * (n + j))) (Nat.gcd_dvd_left (b + a * (n + i))
        (b + a * (n + j)))
      have he : b + a * (n + j) - (b + a * (n + i)) = a * (j - i) := by
        rw [Nat.add_sub_add_left, ← Nat.mul_sub, Nat.add_sub_add_left]
      rwa [he] at H
    exact ((hcopd.dvd_mul_left).mp hdiff).trans
      (Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact H i j hi hj hij
  · rw [Nat.gcd_comm]
    exact H j i hj hi hji

lemma x2611_15379_thmB_aux8 (k a b : ℕ) (M : ℕ) (hM : 0 < M)
    (hd : M ∣ Nat.lcmUpto k) (hcop : Nat.Coprime a M) :
    ∃ c : ℕ, ∀ n : ℕ,
      (∀ i : ℕ, Nat.gcd (b + a * (n + i)) M = Nat.gcd (n + c + i) M) ∧
      M ∣ (Finset.range (k + 1)).lcm (fun i => b + a * (n + i)) := by
  obtain ⟨c, hc, hmod⟩ := Nat.exists_mul_mod_eq_of_coprime b hcop (Nat.ne_of_gt hM)
  have hcmod : Nat.ModEq M (a * c) b := hmod
  have heq (n i : ℕ) : Nat.ModEq M (b + a * (n + i)) (a * (n + c + i)) := by
    convert hcmod.symm.add_right (a * (n + i)) using 1 <;> ring
  refine ⟨c, ?_⟩
  intro n
  refine ⟨?_, ?_⟩
  · intro i
    rw [(heq n i).gcd_eq, hcop.gcd_mul_left_cancel]
  · by_cases hl0 : (Finset.range (k + 1)).lcm (fun i => b + a * (n + i)) = 0
    · simp [hl0]
    apply (Nat.factorization_le_iff_dvd (Nat.ne_of_gt hM) hl0).mp
    intro p
    by_cases hp : Nat.Prime p
    · by_cases hpe : M.factorization p = 0
      · simp [hpe]
      · have hpd : p ∣ Nat.lcmUpto k :=
          (Nat.dvd_of_factorization_pos hpe).trans hd
        have hpk : p ≤ k := by
          have H := hp.mem_primeFactors hpd (Nat.lcmUpto_ne_zero k)
          rw [Nat.primeFactors_lcmUpto] at H
          exact Nat.le_of_mem_primesLE H
        have hk : k ≠ 0 := by have := hp.pos; omega
        have hpow : p ^ M.factorization p ≤ k := by
          have H := ((Nat.factorization_le_iff_dvd (Nat.ne_of_gt hM)
            (Nat.lcmUpto_ne_zero k)).mpr hd) p
          rw [Nat.factorization_lcmUpto k hp] at H
          exact (Nat.pow_le_pow_right hp.pos H).trans (Nat.pow_log_le_self p hk)
        have hq : 0 < p ^ M.factorization p := pow_pos hp.pos _
        obtain ⟨i, hi, hqi⟩ := x2611_15379_thmA_aux10
          (p ^ M.factorization p) (n + c) hq
        have hqM : p ^ M.factorization p ∣ M :=
          (hp.pow_dvd_iff_le_factorization (Nat.ne_of_gt hM)).mpr le_rfl
        have hqi' : p ^ M.factorization p ∣ b + a * (n + i) := by
          apply ((heq n i).dvd_iff hqM).mpr
          exact dvd_mul_of_dvd_right hqi a
        have hl : p ^ M.factorization p ∣
              (Finset.range (k + 1)).lcm (fun i => b + a * (n + i)) := hqi'.trans (Finset.dvd_lcm (f := fun i => b + a * (n + i))
          (Finset.mem_range.mpr (by omega)))
        exact (hp.pow_dvd_iff_le_factorization hl0).mp hl
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]


lemma x2611_15379_thmB_aux9 {α : Type*} (s : Finset α) (hs : s.Nonempty)
    (g : ℕ) (f : α → ℕ) : s.lcm (fun i => g * f i) = g * s.lcm f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert i s hi ih =>
    by_cases hs' : s.Nonempty
    · rw [Finset.lcm_insert, Finset.lcm_insert, ih hs']
      exact Nat.lcm_mul_left _ _ _
    · have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      subst s
      simp

lemma x2611_15379_thmB_aux10 (k a b g M c : ℕ)
    (ha : 0 < a) (hg : 0 < g) (hM : 0 < M)
    (hdiv : ∀ n : ℕ, M ∣ (Finset.range (k + 1)).lcm (fun i => b + a * (n + i)))
    (hshift : ∀ n i : ℕ, Nat.gcd (b + a * (n + i)) M = Nat.gcd (n + c + i) M)
    (hpair' : ∀ n i j : ℕ, i ≤ k → j ≤ k → i ≠ j →
      Nat.gcd (b + a * (n + i)) (b + a * (n + j)) ∣ M)
    (n : ℕ) (hn : 0 < n) :
    x2611_15379_G k (g * a) (g * b) 1 (fun m : ℕ => (m : ℂ)) n =
      ((g : ℂ) ^ k / (M : ℂ)) *
        ((∏ i ∈ Finset.range (k + 1), Nat.gcd (n + c + i) M : ℕ) : ℂ) := by
  let s := Finset.range (k + 1)
  let f := fun i => b + a * (n + i)
  have hs : s.Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hf : ∀ i ∈ s, f i ≠ 0 := by
    intro i hi
    dsimp [f]
    have H := Nat.mul_pos ha (by omega : 0 < n + i)
    omega
  have he (i : ℕ) : g * b + g * a * (n + i * 1) = g * f i := by dsimp [f]; ring
  have hgf : ∀ i ∈ s, g * f i ≠ 0 := fun i hi => mul_ne_zero (Nat.ne_of_gt hg) (hf i hi)
  have hL : g * M ≠ 0 := mul_ne_zero (Nat.ne_of_gt hg) (Nat.ne_of_gt hM)
  have hpairg : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Nat.gcd (g * f i) (g * f j) ∣ g * M := by
    intro i hi j hj hij
    rw [Nat.gcd_mul_left]
    exact Nat.mul_dvd_mul_left g (hpair' n i j
      (by have := Finset.mem_range.mp hi; omega)
      (by have := Finset.mem_range.mp hj; omega) hij)
  have hdivg : g * M ∣ s.lcm (fun i => g * f i) := by
    rw [x2611_15379_thmB_aux9 s hs g f]
    exact Nat.mul_dvd_mul_left g (hdiv n)
  have H := x2611_15379_thmA_aux9 s hs (fun i => g * f i) hgf
    (g * M) hL hpairg hdivg
  have hgc (i : ℕ) : Nat.gcd (g * f i) (g * M) = g * Nat.gcd (n + c + i) M := by
    rw [Nat.gcd_mul_left, hshift]
  have hprod : (∏ i ∈ s, Nat.gcd (g * f i) (g * M)) =
      g ^ (k + 1) * ∏ i ∈ s, Nat.gcd (n + c + i) M := by
    simp_rw [hgc]
    rw [Finset.prod_mul_distrib]
    simp [s]
  rw [hprod] at H
  have hlcm : s.lcm (fun i => g * f i) ≠ 0 := Finset.lcm_ne_zero_iff.mpr hgf
  have hgC : (g : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hg
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  have hlC : ((s.lcm (fun i => g * f i) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hlcm
  have HC : ((∏ i ∈ s, g * f i : ℕ) : ℂ) * ((g : ℂ) * (M : ℂ)) =
      (g : ℂ) ^ (k + 1) * ((∏ i ∈ s, Nat.gcd (n + c + i) M : ℕ) : ℂ) *
        ((s.lcm (fun i => g * f i) : ℕ) : ℂ) := by exact_mod_cast H
  unfold x2611_15379_G
  simp_rw [he]
  rw [← Nat.cast_prod]
  change ((∏ i ∈ s, g * f i : ℕ) : ℂ) / ((s.lcm (fun i => g * f i) : ℕ) : ℂ) = _
  apply (div_eq_iff hlC).mpr
  apply (mul_right_cancel₀ (mul_ne_zero hgC hMC))
  rw [HC]
  field_simp
  ring

lemma x2611_15379_thmB_aux20 (k a b : ℕ) (ha : 0 < a) :
    ∃ (C : ℂ) (c : ℕ), C ≠ 0 ∧ ∀ n : ℕ, 0 < n →
      x2611_15379_G k a b 1 (fun m : ℕ => (m : ℂ)) n =
        C * ((∏ i ∈ Finset.range (k + 1),
          Nat.gcd (n + c + i)
            (∏ p ∈ ((Nat.lcmUpto k).primeFactors.filter
              (fun p => ¬ p ∣ a / Nat.gcd a b)),
                p ^ (Nat.lcmUpto k).factorization p) : ℕ) : ℂ) := by
  classical
  let g := Nat.gcd a b
  have hg : 0 < g := Nat.gcd_pos_of_pos_left b ha
  obtain ⟨A, B, hAB, hae, hbe⟩ := Nat.exists_coprime a b
  have hAeq : a / Nat.gcd a b = A := by
    change a / g = A
    calc
      a / g = (A * g) / g := congrArg (fun x : ℕ => x / g) hae
      _ = A := Nat.mul_div_cancel A hg
  rw [hAeq]
  let M := ∏ p ∈ ((Nat.lcmUpto k).primeFactors.filter (fun p => ¬ p ∣ A)),
    p ^ (Nat.lcmUpto k).factorization p
  have hM : 0 < M := x2611_15379_thmB_aux4 _ _
  obtain ⟨hd, hcop, hmax⟩ := x2611_15379_thmB_aux6 (Nat.lcmUpto k) A
    (Nat.lcmUpto_ne_zero k)
  change M ∣ Nat.lcmUpto k at hd
  change Nat.Coprime A M at hcop
  change ∀ d : ℕ, d ∣ Nat.lcmUpto k → Nat.Coprime A d → d ∣ M at hmax
  obtain ⟨c, hc⟩ := x2611_15379_thmB_aux8 k A B M hM hd hcop
  have hA : 0 < A := by
    by_contra H
    have : A = 0 := by omega
    simp [this] at hae
    omega
  have hpair (n i j : ℕ) (hi : i ≤ k) (hj : j ≤ k) (hij : i ≠ j) :
      Nat.gcd (B + A * (n + i)) (B + A * (n + j)) ∣ M := by
    apply hmax _ (x2611_15379_thmB_aux7 k A B n i j hAB hi hj hij)
    apply Nat.Coprime.of_dvd_right (Nat.gcd_dvd_left _ _)
    simpa using (Nat.coprime_add_mul_right_right A B (n + i)).mpr hAB
  refine ⟨(g : ℂ) ^ k / (M : ℂ), c, ?_, ?_⟩
  · exact div_ne_zero (pow_ne_zero _ (by exact_mod_cast Nat.ne_of_gt hg))
      (by exact_mod_cast Nat.ne_of_gt hM)
  · intro n hn
    have hae' : a = g * A := by simpa [g, Nat.mul_comm] using hae
    have hbe' : b = g * B := by simpa [g, Nat.mul_comm] using hbe
    rw [hae', hbe']
    exact x2611_15379_thmB_aux10 k A B g M c hA hg hM
      (fun n => (hc n).2) (fun n i => (hc n).1 i) hpair n hn

lemma x2611_15379_thmB_aux21 (N a d : ℕ) (hN : N ≠ 0) :
    let M := ∏ q ∈ (N.primeFactors.filter (fun q => ¬ q ∣ a)), q ^ N.factorization q
    (∏ p ∈ (M.primeFactors.filter (fun p => d.factorization p < M.factorization p)),
      p ^ M.factorization p) =
      ∏ p ∈ (N.primeFactors.filter (fun p => ¬ p ∣ a ∧ d.factorization p < N.factorization p)),
        p ^ N.factorization p := by
  classical
  let s := N.primeFactors.filter (fun p => ¬ p ∣ a)
  let M := ∏ p ∈ s, p ^ N.factorization p
  have hfac (p : ℕ) : M.factorization p = if p ∈ s then N.factorization p else 0 :=
    x2611_15379_thmB_aux5 s N.factorization
      (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1) p
  have hpr : M.primeFactors = s := by
    ext p
    rw [← Nat.support_factorization, Finsupp.mem_support_iff, hfac]
    by_cases hp : p ∈ s
    · have H : N.factorization p ≠ 0 := by
        rw [← Finsupp.mem_support_iff, Nat.support_factorization]
        exact (Finset.mem_filter.mp hp).1
      simp [hp, H]
    · simp [hp]
  change (∏ p ∈ (M.primeFactors.filter _), _) = _
  rw [hpr]
  apply Finset.prod_congr ?_ ?_
  · ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, he⟩
      rw [hfac, if_pos hp] at he
      exact ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2, he⟩
    · rintro ⟨hp, hpa, he⟩
      have hs : p ∈ s := Finset.mem_filter.mpr ⟨hp, hpa⟩
      exact ⟨hs, by rwa [hfac, if_pos hs]⟩
  · intro p hp
    have hs : p ∈ s := Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.1⟩
    rw [hfac, if_pos hs]

lemma x2611_15379_thmB_aux22 (k p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpk : p ≤ k) (hqk : q ≤ k)
    (hpe : (Nat.lcmUpto k).factorization p ≤ (k + 1).factorization p)
    (hqe : (Nat.lcmUpto k).factorization q ≤ (k + 1).factorization q) : p = q := by
  have H (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q)
      (hpk : p ≤ k) (hqk : q ≤ k)
      (hpe : (Nat.lcmUpto k).factorization p ≤ (k + 1).factorization p)
      (hqe : (Nat.lcmUpto k).factorization q ≤ (k + 1).factorization q) : False := by
    let r := p ^ (Nat.lcmUpto k).factorization p
    let s := q ^ (Nat.lcmUpto k).factorization q
    have hr : 0 < r := pow_pos hp.pos _
    have hdr : r ∣ k + 1 := (hp.pow_dvd_iff_le_factorization (by omega)).mpr hpe
    have hds : s ∣ k + 1 := (hq.pow_dvd_iff_le_factorization (by omega)).mpr hqe
    have hcop : Nat.Coprime r s := Nat.coprime_pow_primes _ _ hp hq (by omega)
    have hprod : r * s ≤ k + 1 := Nat.le_of_dvd (by omega)
      (hcop.mul_dvd_of_dvd_of_dvd hdr hds)
    have hqpos : 0 < (Nat.lcmUpto k).factorization q := by
      apply hq.factorization_pos_of_dvd (Nat.lcmUpto_ne_zero k)
      exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hq.one_le, hqk⟩)
    have hqs : q ≤ s := Nat.le_pow hqpos
    have hlt : p * r < r * s := by nlinarith
    have hmax : k < p * r := by
      dsimp [r]
      rw [Nat.factorization_lcmUpto k hp]
      simpa [pow_succ, Nat.mul_comm] using Nat.lt_pow_succ_log_self hp.one_lt k
    omega
  rcases lt_trichotomy p q with h | h | h
  · exact False.elim (H p q hp hq h hpk hqk hpe hqe)
  · exact h
  · exact False.elim (H q p hq hp h hqk hpk hqe hpe)

lemma x2611_15379_thmB_aux23 (s : Finset ℕ) (f : ℕ → ℕ)
    (hs : ∀ p ∈ s, ∀ q ∈ s, p = q) (hf : ∀ p ∈ s, 0 < f p) :
    max 1 (s.sup f) = ∏ p ∈ s, f p := by
  classical
  rcases s.eq_empty_or_nonempty with h | ⟨p, hp⟩
  · simp [h]
  · have he : s = {p} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hp, fun q hq => hs q hq p hp⟩
    simp [he, max_eq_right (Nat.succ_le_of_lt (hf p hp))]

lemma x2611_15379_thmB_aux24 (k a : ℕ) (ha : 0 < a) :
    x2611_15379_hongQianPeriod k a =
      ∏ p ∈ ((Nat.lcmUpto k).primeFactors.filter (fun p =>
        ¬ p ∣ a ∧ (k + 1).factorization p < (Nat.lcmUpto k).factorization p)),
        p ^ (Nat.lcmUpto k).factorization p := by
  classical
  let N := Nat.lcmUpto k
  let s := N.primeFactors
  let e := fun p => p ^ N.factorization p
  let t := s.filter (fun p => ¬ p ∣ a)
  let E := t.filter (fun p => N.factorization p ≤ (k + 1).factorization p)
  let R := t.filter (fun p => ¬ N.factorization p ≤ (k + 1).factorization p)
  let B := s.filter (fun p => p ∣ a)
  have hE : (Finset.range (k + 1)).filter (fun p => Nat.Prime p ∧ ¬ p ∣ a ∧
      N.factorization p ≤ (k + 1).factorization p) = E := by
    ext p
    simp only [E, t, s, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hp, hprime, hpa, he⟩
      refine ⟨⟨?_, hpa⟩, he⟩
      change p ∈ (Nat.lcmUpto k).primeFactors
      rw [Nat.primeFactors_lcmUpto, Nat.mem_primesLE]
      exact ⟨by omega, hprime⟩
    · rintro ⟨⟨hp, hpa⟩, he⟩
      change p ∈ (Nat.lcmUpto k).primeFactors at hp
      rw [Nat.primeFactors_lcmUpto, Nat.mem_primesLE] at hp
      exact ⟨by omega, hp.2, hpa, he⟩
  have hEs : ∀ p ∈ E, ∀ q ∈ E, p = q := by
    intro p hp q hq
    have hp' := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
    have hq' := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    have hpk : p ≤ k := by
      change p ∈ (Nat.lcmUpto k).primeFactors at hp'
      rw [Nat.primeFactors_lcmUpto] at hp'
      exact Nat.le_of_mem_primesLE hp'
    have hqk : q ≤ k := by
      change q ∈ (Nat.lcmUpto k).primeFactors at hq'
      rw [Nat.primeFactors_lcmUpto] at hq'
      exact Nat.le_of_mem_primesLE hq'
    exact x2611_15379_thmB_aux22 k p q
      (Nat.prime_of_mem_primeFactors ((Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1))
      (Nat.prime_of_mem_primeFactors ((Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1))
      hpk hqk (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2
  have hsup : max 1 (E.sup e) = ∏ p ∈ E, e p :=
    x2611_15379_thmB_aux23 E e hEs (fun p hp => pow_pos
      (Nat.pos_of_mem_primeFactors (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1) _)
  have hB : (Nat.gcd a N).primeFactors = B := by
    ext p
    simp only [B, s, Finset.mem_filter, Nat.mem_primeFactors]
    have hg : Nat.gcd a N ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left N ha)
    simp only [hg, true_and, and_true, Nat.dvd_gcd_iff]
    have hN : N ≠ 0 := Nat.lcmUpto_ne_zero k
    tauto
  have hsplit : (∏ p ∈ B, e p) * (∏ p ∈ t, e p) = N := by
    simpa [B, t, s] using (Finset.prod_filter_mul_prod_filter_not s
      (fun p => p ∣ a) e).trans ((Nat.prod_primeFactors_pow_factorization
        (n := N) (Nat.lcmUpto_ne_zero k)).symm)
  have hsplit' : (∏ p ∈ E, e p) * (∏ p ∈ R, e p) = ∏ p ∈ t, e p :=
    Finset.prod_filter_mul_prod_filter_not t (fun p => N.factorization p ≤ (k + 1).factorization p) e
  have hN : N = ((∏ p ∈ E, e p) * (∏ p ∈ B, e p)) * ∏ p ∈ R, e p := by
    rw [← hsplit, ← hsplit']
    ring
  have hD : 0 < (∏ p ∈ E, e p) * (∏ p ∈ B, e p) := by
    apply Nat.mul_pos <;> apply Finset.prod_pos
    · intro p hp
      exact pow_pos (Nat.pos_of_mem_primeFactors
        (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1) _
    · intro p hp
      exact pow_pos (Nat.pos_of_mem_primeFactors (Finset.mem_filter.mp hp).1) _
  unfold x2611_15379_hongQianPeriod
  change N / (max 1 (((Finset.range (k + 1)).filter _).sup e) *
    ∏ p ∈ (Nat.gcd a N).primeFactors, e p) = _
  rw [hE, hsup, hB, hN, Nat.mul_div_right _ hD]
  apply Finset.prod_congr ?_ (fun _ _ => rfl)
  ext p
  simp [R, t, s, N, not_le, and_assoc]

lemma x2611_15379_thmB_aux30 (k a : ℕ) (ha : 0 < a) :
    x2611_15379_hongQianPeriod k a =
      ∏ p ∈ ((∏ q ∈ ((Nat.lcmUpto k).primeFactors.filter (fun q => ¬ q ∣ a)),
        q ^ (Nat.lcmUpto k).factorization q).primeFactors.filter
          (fun p => (k + 1).factorization p <
            (∏ q ∈ ((Nat.lcmUpto k).primeFactors.filter (fun q => ¬ q ∣ a)),
              q ^ (Nat.lcmUpto k).factorization q).factorization p)),
        p ^ (∏ q ∈ ((Nat.lcmUpto k).primeFactors.filter (fun q => ¬ q ∣ a)),
              q ^ (Nat.lcmUpto k).factorization q).factorization p := by
  rw [x2611_15379_thmB_aux24 k a ha]
  exact (x2611_15379_thmB_aux21 (Nat.lcmUpto k) a (k + 1) (Nat.lcmUpto_ne_zero k)).symm

theorem x2611_15379_thmB (k a b : ℕ) (ha : 0 < a) :
    IsLeast {T : ℕ | 0 < T ∧ ∀ n : ℕ, 0 < n →
      (x2611_15379_G k a b 1 (fun n : ℕ => (n : ℂ))) (n + T) =
        (x2611_15379_G k a b 1 (fun n : ℕ => (n : ℂ))) n}
      (x2611_15379_hongQianPeriod k (a / Nat.gcd a b)) := by
  classical
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have hA : 0 < a / Nat.gcd a b := Nat.div_pos
    (Nat.le_of_dvd ha (Nat.gcd_dvd_left a b)) hg
  rw [x2611_15379_thmB_aux30 k (a / Nat.gcd a b) hA]
  obtain ⟨C, c, hC, hG⟩ := x2611_15379_thmB_aux20 k a b ha
  let L := ∏ p ∈ ((Nat.lcmUpto k).primeFactors.filter
      (fun p => ¬ p ∣ a / Nat.gcd a b)), p ^ (Nat.lcmUpto k).factorization p
  have hL : 0 < L := x2611_15379_thmB_aux4 _ _
  apply x2611_15379_thmB_aux2
    (fun n => ∏ i ∈ Finset.range (k + 1), Nat.gcd (n + c + i) L)
    (x2611_15379_G k a b 1 (fun n : ℕ => (n : ℂ))) C hC hG
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    x2611_15379_thmB_aux3 L (k + 1) c hL (by omega)
end

-- forge:entry x2611_15358_N1_bound kind=proved origin=paper
section
/- Lemma 2.6, proof (N₁ estimate) -/
lemma x2611_15358_N1_bound_aux1 {V : Type*} (G : SimpleGraph V)
    {v w : V} (hv : G.IsIsolated v) (h : G.Reachable v w) : v = w := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons h p => exact False.elim (hv _ h)

lemma x2611_15358_N1_bound_aux2 {V : Type*} [Finite V] (G : SimpleGraph V) :
    Nat.card {C : G.ConnectedComponent // Nat.card C.supp = 1} =
      Nat.card {v : V // G.IsIsolated v} := by
  classical
  have hs (v : V) (hv : G.IsIsolated v) :
      (G.connectedComponentMk v).supp = {v} := by
    ext w
    simp only [SimpleGraph.ConnectedComponent.mem_supp_iff,
      SimpleGraph.ConnectedComponent.eq, Set.mem_singleton_iff]
    constructor
    · intro h
      exact (x2611_15358_N1_bound_aux1 G hv h.symm).symm
    · rintro rfl
      exact SimpleGraph.Reachable.refl _
  let f : {v : V // G.IsIsolated v} →
      {C : G.ConnectedComponent // Nat.card C.supp = 1} :=
    fun v => ⟨G.connectedComponentMk v, by
      rw [hs v v.property]
      simp⟩
  apply (Nat.card_congr (Equiv.ofBijective f ?_)).symm
  constructor
  · intro v w h
    apply Subtype.ext
    exact x2611_15358_N1_bound_aux1 G v.property
      (SimpleGraph.ConnectedComponent.eq.mp (congrArg Subtype.val h))
  · intro C
    have hc : C.val.supp.ncard = 1 := by
      simpa only [Nat.card_coe_set_eq] using C.property
    obtain ⟨v, hv⟩ := Set.ncard_eq_one.mp hc
    have hvm : v ∈ C.val.supp := by rw [hv]; simp
    have hi : G.IsIsolated v := by
      intro w hw
      have hwm := (C.val.mem_supp_congr_adj hw).mp hvm
      rw [hv, Set.mem_singleton_iff] at hwm
      exact hw.ne hwm.symm
    refine ⟨⟨v, hi⟩, ?_⟩
    apply Subtype.ext
    exact hvm

lemma x2611_15358_N1_bound_aux3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) :
    Nat.card {C : (G.induce (↑U : Set V)).ConnectedComponent //
      Nat.card C.supp = 1} =
      ∑ v : V, if v ∈ U ∧ (∀ w ∈ U, ¬ G.Adj v w) then 1 else 0 := by
  classical
  rw [x2611_15358_N1_bound_aux2]
  have he : {v : (↑U : Set V) // (G.induce (↑U : Set V)).IsIsolated v} ≃
      {v : V // v ∈ U ∧ ∀ w ∈ U, ¬ G.Adj v w} :=
    { toFun := fun v => ⟨v.val.val, v.val.property,
        fun w hw => v.property ⟨w, hw⟩⟩
      invFun := fun v => ⟨⟨v.val, v.property.1⟩,
        fun w => v.property.2 w.val w.property⟩
      left_inv := fun v => rfl
      right_inv := fun v => rfl }
  rw [Nat.card_congr he, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]

lemma x2611_15358_N1_bound_aux4 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (k : ℕ) :
    (∑ U ∈ Finset.univ.powersetCard (k + 1),
      if v ∈ U ∧ (∀ w ∈ U, ¬ G.Adj v w) then 1 else 0) =
      (Nat.card ((Gᶜ).neighborSet v)).choose k := by
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree, ← Finset.card_powersetCard]
  apply Finset.card_bij (fun U _ => U.erase v)
  · intro U hU
    simp only [Finset.mem_filter, Finset.mem_powersetCard,
      Finset.subset_univ, true_and] at hU
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro w hw
      have hw' := Finset.mem_erase.mp hw
      apply (Gᶜ).mem_neighborFinset v w |>.mpr
      exact ⟨hw'.1.symm, hU.2.2 w hw'.2⟩
    · rw [Finset.card_erase_of_mem hU.2.1, hU.1]
      omega
  · intro U hU W hW hUW
    simp only [Finset.mem_filter] at hU hW
    have h1 := Finset.insert_erase hU.2.1
    have h2 := Finset.insert_erase hW.2.1
    rw [← h1, ← h2, hUW]
  · intro T hT
    have ht := Finset.mem_powersetCard.mp hT
    have hv : v ∉ T := by
      intro hv
      have ha := (Gᶜ).mem_neighborFinset v v |>.mp (ht.1 hv)
      exact (Gᶜ).loopless.irrefl v ha
    refine ⟨insert v T, ?_, Finset.erase_insert hv⟩
    simp only [Finset.mem_filter, Finset.mem_powersetCard,
      Finset.subset_univ, true_and]
    refine ⟨by rw [Finset.card_insert_of_notMem hv, ht.2],
      Finset.mem_insert_self _ _, ?_⟩
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact G.irrefl
    · exact ((Gᶜ).mem_neighborFinset v w |>.mp (ht.1 hw)).2

theorem x2611_15358_N1_bound (G : SimpleGraph (Fin 14))
    (hdeg : ∀ v : Fin 14, 4 ≤ Nat.card (G.neighborSet v))
    (hq : Nat.card (Gᶜ).edgeSet ≤ 15) :
    x2611_15358_N G 1 = Finset.univ.sum (fun v : Fin 14 => ((fun v : Fin 14 => Nat.card ((Gᶜ).neighborSet v)) v).choose 6) ∧
    Finset.univ.sum (fun v : Fin 14 => ((fun v : Fin 14 => Nat.card ((Gᶜ).neighborSet v)) v).choose 6) ≤ 10 * (Finset.univ.sum (fun v : Fin 14 => Nat.card ((Gᶜ).neighborSet v))) ∧
    10 * (Finset.univ.sum (fun v : Fin 14 => Nat.card ((Gᶜ).neighborSet v))) = 20 * (Nat.card (Gᶜ).edgeSet) := by
  classical
  constructor
  · unfold x2611_15358_N
    simp_rw [x2611_15358_N1_bound_aux3]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    exact x2611_15358_N1_bound_aux4 G v 6
  · constructor
    · rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro v hv
      have hd := hdeg v
      simp only [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] at hd ⊢
      have hc := G.degree_compl v
      have hbound : (Gᶜ).degree v ≤ 9 := by simp only [Fintype.card_fin] at hc; omega
      interval_cases h : (Gᶜ).degree v <;> norm_num [Nat.choose] at *
    · simp only [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree,
        SimpleGraph.card_edgeSet]
      rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
      omega
end

-- forge:entry x2611_15358_euler_arithmetic kind=proved origin=paper
section
/- Theorem 3.1, proof (explicit binomial arithmetic) -/
theorem x2611_15358_euler_arithmetic (m : ℤ) (hm_lo : 76 ≤ m) (hm_hi : m ≤ 91) :
    14 * (Nat.choose 13 6 : ℤ) - m * (Nat.choose 12 5 : ℤ) +
      (2 * m - 28) * (Nat.choose 11 4 : ℤ) - (m - 14) * (Nat.choose 10 3 : ℤ) =
      16464 - 252 * m := by
  norm_num [Nat.choose] <;> ring
end

-- forge:entry x2611_15358_triple_common_bound kind=proved origin=paper
section
/- Lemma 2.6, proof (common neighbors of a triple) -/
theorem x2611_15358_triple_common_bound (G : SimpleGraph (Fin 14))
    (hdeg : ∀ v : Fin 14, 4 ≤ Nat.card (G.neighborSet v))
    (hq : Nat.card (Gᶜ).edgeSet ≤ 15) (S : Finset (Fin 14)) (hS : S.card = 3) :
    x2611_15358_t G S ≤ (Nat.card (Gᶜ).edgeSet) / 3 ∧
      (Nat.card (Gᶜ).edgeSet) / 3 ≤ 5 := by
  have h := x2611_15358_pair_common_bound_aux1 Gᶜ S
  rw [hS] at h
  change 3 * x2611_15358_t G S ≤ Nat.card (Gᶜ).edgeSet at h
  omega
end

-- forge:entry x2611_15358_pair_double_count kind=proved origin=paper
section
/- Lemma 2.6, proof (pair double count) -/
open scoped BigOperators

lemma x2611_15358_pair_double_count_aux1
    {α β : Type*} [Fintype α] [Fintype β]
    (r : α → β → Prop) (k : ℕ) :
    (Finset.univ.powersetCard k : Finset (Finset α)).sum
        (fun S => Nat.card {b : β // ∀ a ∈ S, r a b}) =
      Finset.univ.sum (fun b : β => (Nat.card {a : α // r a b}).choose k) := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc
    _ = ∑ b : β, ((Finset.univ.powersetCard k : Finset (Finset α)).filter
        (fun S => ∀ a ∈ S, r a b)).card := by
      simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow] using
        (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (s := Finset.univ.powersetCard k) (t := Finset.univ)
          (fun (S : Finset α) (b : β) => ∀ a ∈ S, r a b))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [← Finset.card_powersetCard]
      congr 1
      ext S
      simp [Finset.mem_powersetCard, Finset.subset_iff, and_comm]

theorem x2611_15358_pair_double_count (G : SimpleGraph (Fin 14))
    (hdeg : ∀ v : Fin 14, 4 ≤ Nat.card (G.neighborSet v))
    (hq : Nat.card (Gᶜ).edgeSet ≤ 15) :
    (Finset.univ.powersetCard 2 : Finset (Finset (Fin 14))).sum
        (fun S => x2611_15358_t G S) =
      Finset.univ.sum (fun v : Fin 14 =>
        ((fun v : Fin 14 => Nat.card ((Gᶜ).neighborSet v)) v).choose 2) := by
  simpa only [x2611_15358_t, SimpleGraph.neighborSet, SimpleGraph.adj_comm,
    Set.coe_ofPred] using
    (x2611_15358_pair_double_count_aux1 (Gᶜ).Adj 2)
end

end Mathlib2
