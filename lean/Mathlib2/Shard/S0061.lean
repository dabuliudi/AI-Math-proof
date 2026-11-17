/- Mathlib2 分片 61（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0052
import Mathlib2.Shard.S0053
import Mathlib2.Shard.S0054
import Mathlib2.Shard.S0055
import Mathlib2.Shard.S0056
import Mathlib2.Shard.S0057
import Mathlib2.Shard.S0058
import Mathlib2.Shard.S0059
import Mathlib2.Shard.S0060
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry x2611_15358_lem2_6 kind=proved origin=paper
section
/- Lemma 2.6 -/
open Finset

lemma x2611_15358_lem2_6_aux1 {V : Type*} [Fintype V]
    (H : SimpleGraph V) (S : Finset V) :
    S.card * Nat.card {v : V // ∀ x ∈ S, H.Adj x v} ≤ Nat.card H.edgeSet := by
  classical
  let T := Finset.univ.filter (fun v : V => ∀ x ∈ S, H.Adj x v)
  have hT : T.card = Nat.card {v : V // ∀ x ∈ S, H.Adj x v} := by
    simp [T, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hdis (x : V) (hx : x ∈ S) : x ∉ T := by
    simp only [T, mem_filter, mem_univ, true_and]
    exact fun h => H.irrefl (h x hx)
  have h := Finset.card_le_card_of_injOn (fun p : V × V => s(p.1, p.2))
    (s := S ×ˢ T) (t := H.edgeFinset) ?_ ?_
  · rw [card_product, hT, H.edgeFinset_card, ← Nat.card_eq_fintype_card] at h
    exact h
  · rintro ⟨x,y⟩ hp
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    exact H.mem_edgeFinset.mpr ((mem_filter.mp hy).2 x hx)
  · rintro ⟨x,y⟩ hp ⟨z,w⟩ hq heq
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    obtain ⟨hz,hw⟩ := Finset.mem_product.mp hq
    rcases Sym2.eq_iff.mp heq with h | h
    · exact Prod.ext h.1 h.2
    · have hxw : x = w := h.1
      exact False.elim (hdis x hx (hxw.symm ▸ hw))

lemma x2611_15358_lem2_6_aux2 {V : Type*} [Fintype V]
    (H : SimpleGraph V) (k : ℕ) :
    ∑ S ∈ (Finset.univ : Finset V).powersetCard k,
      Nat.card {v : V // ∀ x ∈ S, H.Adj x v} =
    ∑ v : V, (Nat.card (H.neighborSet v)).choose k := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  have heq : ((Finset.univ : Finset V).powersetCard k).filter
      (fun S => ∀ x ∈ S, H.Adj x v) = (H.neighborFinset v).powersetCard k := by
    ext S
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
    constructor
    · rintro ⟨hc, ha⟩
      exact ⟨fun x hx => (H.mem_neighborFinset v x).mpr (ha x hx).symm, hc⟩
    · rintro ⟨ha,hc⟩
      exact ⟨hc, fun x hx => ((H.mem_neighborFinset v x).mp (ha hx)).symm⟩
  calc
    _ = (((Finset.univ : Finset V).powersetCard k).filter
      (fun S => ∀ x ∈ S, H.Adj x v)).card := by simp
    _ = _ := by rw [heq, card_powersetCard]; congr 1; simp [SimpleGraph.neighborFinset, Set.toFinset_card, Fintype.card_subtype]

lemma x2611_15358_lem2_6_aux3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (k : ℕ) :
    Nat.card {C : (G.induce (↑U : Set V)).ConnectedComponent // Nat.card C.supp = k} ≤
    (((Finset.univ : Finset V).powersetCard k).filter (fun S =>
      S ⊆ U ∧ ∀ x ∈ S, ∀ y ∈ U \ S, (Gᶜ).Adj x y)).card := by
  classical
  let f (C : (G.induce (↑U : Set V)).ConnectedComponent) : Finset V :=
    C.supp.toFinset.image Subtype.val
  have hm (C : (G.induce (↑U : Set V)).ConnectedComponent) (x : U) :
      x.1 ∈ f C ↔ x ∈ C.supp := by
    simp [f]
  have hc (C : (G.induce (↑U : Set V)).ConnectedComponent) :
      (f C).card = Nat.card C.supp := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
    simp [Nat.card_eq_fintype_card]
  let F : {C : (G.induce (↑U : Set V)).ConnectedComponent // Nat.card C.supp = k} →
      {S // S ∈ ((Finset.univ : Finset V).powersetCard k).filter (fun S =>
        S ⊆ U ∧ ∀ x ∈ S, ∀ y ∈ U \ S, (Gᶜ).Adj x y)} := fun C =>
    ⟨f C.1, by
      simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
      refine ⟨(hc C.1).trans C.2, ?_, ?_⟩
      · intro x hx
        obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
        exact z.2
      · intro x hx y hy
        obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
        have hys := mem_sdiff.mp hy
        rw [SimpleGraph.compl_adj]
        refine ⟨?_, ?_⟩
        · intro heq
          exact hys.2 (heq ▸ mem_image.mpr ⟨z,hz,rfl⟩)
        · intro hadj
          have hz' : z ∈ C.1.supp := Set.mem_toFinset.mp hz
          have hy' := C.1.mem_supp_of_adj_mem_supp hz'
            (show (G.induce (↑U : Set V)).Adj z ⟨y,hys.1⟩ from hadj)
          exact hys.2 ((hm C.1 ⟨y,hys.1⟩).mpr hy')⟩
  have h := Nat.card_le_card_of_injective F (by
    intro C D h
    apply Subtype.ext
    apply SimpleGraph.ConnectedComponent.supp_injective
    ext x
    have hh : f C.1 = f D.1 := congrArg Subtype.val h
    rw [← hm C.1 x, ← hm D.1 x, hh])
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using h

lemma x2611_15358_lem2_6_aux4 {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) (n : ℕ) :
    (((Finset.univ : Finset V).powersetCard n).filter (fun U =>
      S ⊆ U ∧ ∀ x ∈ S, ∀ y ∈ U \ S, H.Adj x y)).card ≤
      (Nat.card {v : V // ∀ x ∈ S, H.Adj x v}).choose (n - S.card) := by
  classical
  let T := Finset.univ.filter (fun v : V => ∀ x ∈ S, H.Adj x v)
  have hT : T.card = Nat.card {v : V // ∀ x ∈ S, H.Adj x v} := by
    simp [T, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← hT, ← card_powersetCard]
  apply card_le_card_of_injOn (fun U : Finset V => U \ S)
  · intro U hU
    obtain ⟨hU, hSU, ha⟩ := mem_filter.mp hU
    apply mem_powersetCard.mpr
    refine ⟨?_, ?_⟩
    · intro y hy
      exact mem_filter.mpr ⟨mem_univ _, fun x hx => ha x hx y hy⟩
    · rw [card_sdiff_of_subset hSU, (mem_powersetCard.mp hU).2]
  · intro U hU W hW heq
    have hSU := (mem_filter.mp hU).2.1
    have hSW := (mem_filter.mp hW).2.1
    change U \ S = W \ S at heq
    rw [← sdiff_union_of_subset hSU, ← sdiff_union_of_subset hSW, heq]

lemma x2611_15358_lem2_6_aux5 (G : SimpleGraph (Fin 14)) (k : ℕ) :
    x2611_15358_N G k ≤
      ∑ S ∈ (Finset.univ : Finset (Fin 14)).powersetCard k,
        (x2611_15358_t G S).choose (7-k) := by
  classical
  unfold x2611_15358_N
  calc
    _ ≤ ∑ U ∈ (Finset.univ : Finset (Fin 14)).powersetCard 7,
      (((Finset.univ : Finset (Fin 14)).powersetCard k).filter (fun S =>
        S ⊆ U ∧ ∀ x ∈ S, ∀ y ∈ U \ S, (Gᶜ).Adj x y)).card := by
      exact Finset.sum_le_sum (fun U _ => by simpa using x2611_15358_lem2_6_aux3 G U k)
    _ = ∑ S ∈ (Finset.univ : Finset (Fin 14)).powersetCard k,
      (((Finset.univ : Finset (Fin 14)).powersetCard 7).filter (fun U =>
        S ⊆ U ∧ ∀ x ∈ S, ∀ y ∈ U \ S, (Gᶜ).Adj x y)).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro S hS
      have hc := (mem_powersetCard.mp hS).2
      simpa [hc, x2611_15358_t] using x2611_15358_lem2_6_aux4 Gᶜ S 7

lemma x2611_15358_lem2_6_aux6 (G : SimpleGraph (Fin 14))
    (hdeg : ∀ v : Fin 14, 4 ≤ Nat.card (G.neighborSet v)) (v : Fin 14) :
    Nat.card ((Gᶜ).neighborSet v) ≤ 9 := by
  classical
  have hv := hdeg v
  rw [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree] at hv
  rw [Nat.card_eq_fintype_card, Gᶜ.card_neighborSet_eq_degree, G.degree_compl]
  simp only [Fintype.card_fin]
  omega

lemma x2611_15358_lem2_6_aux7 (G : SimpleGraph (Fin 14))
    (hdeg : ∀ v : Fin 14, 4 ≤ Nat.card (G.neighborSet v))
    (S : Finset (Fin 14)) (hS : S.Nonempty) : x2611_15358_t G S ≤ 9 := by
  classical
  obtain ⟨x,hx⟩ := hS
  have hb : Nat.card {v : Fin 14 // ∀ y ∈ S, (Gᶜ).Adj y v} ≤
      Nat.card ((Gᶜ).neighborSet x) := by
    apply Nat.card_le_card_of_injective
      (fun v => (⟨v.1,v.2 x hx⟩ : (Gᶜ).neighborSet x))
    intro a b h
    exact Subtype.ext (congrArg (fun z : (Gᶜ).neighborSet x => z.1) h)
  exact hb.trans (x2611_15358_lem2_6_aux6 G hdeg x)

lemma x2611_15358_lem2_6_aux8 (G : SimpleGraph (Fin 14)) (k c b : ℕ)
    (ht : ∀ S ∈ (Finset.univ : Finset (Fin 14)).powersetCard k,
      (x2611_15358_t G S).choose (7-k) ≤ c * x2611_15358_t G S)
    (hd : ∀ v : Fin 14, c * (Nat.card ((Gᶜ).neighborSet v)).choose k ≤
      b * Nat.card ((Gᶜ).neighborSet v)) :
    x2611_15358_N G k ≤ b * ∑ v : Fin 14, Nat.card ((Gᶜ).neighborSet v) := by
  classical
  calc
    _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin 14)).powersetCard k,
      (x2611_15358_t G S).choose (7-k) := x2611_15358_lem2_6_aux5 G k
    _ ≤ c * ∑ S ∈ (Finset.univ : Finset (Fin 14)).powersetCard k,
      x2611_15358_t G S := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum ht
    _ = c * ∑ v : Fin 14, (Nat.card ((Gᶜ).neighborSet v)).choose k := by
      rw [show (∑ S ∈ (Finset.univ : Finset (Fin 14)).powersetCard k,
        x2611_15358_t G S) = _ from x2611_15358_lem2_6_aux2 Gᶜ k]
    _ ≤ _ := by
      simp only [Finset.mul_sum]
      exact Finset.sum_le_sum (fun v _ => hd v)

lemma x2611_15358_lem2_6_aux9 (n : ℕ) (hn : n ≤ 9) :
    n.choose 6 ≤ 10*n ∧ 3*n.choose 2 ≤ 12*n ∧ n.choose 3 ≤ 10*n := by
  interval_cases n <;> decide

lemma x2611_15358_lem2_6_aux10 (n : ℕ) (hn : n ≤ 7) : n.choose 5 ≤ 3*n := by
  interval_cases n <;> decide

lemma x2611_15358_lem2_6_aux11 (n : ℕ) (hn : n ≤ 5) : n.choose 4 ≤ n := by
  interval_cases n <;> decide

theorem x2611_15358_lem2_6 (G : SimpleGraph (Fin 14))
    (hdeg : ∀ v : Fin 14, 4 ≤ Nat.card (G.neighborSet v))
    (hq : Nat.card (Gᶜ).edgeSet ≤ 15) :
    x2611_15358_D G ≤ 64 * Nat.card (Gᶜ).edgeSet := by
  classical
  have h1 : x2611_15358_N G 1 ≤ 10 * ∑ v : Fin 14, Nat.card ((Gᶜ).neighborSet v) := by
    apply x2611_15358_lem2_6_aux8 G 1 10 10
    · intro S hS
      have hc := (mem_powersetCard.mp hS).2
      have hb := x2611_15358_lem2_6_aux7 G hdeg S (card_pos.mp (by omega))
      exact (x2611_15358_lem2_6_aux9 _ hb).1
    · intro v
      simp
  have h2 : x2611_15358_N G 2 ≤ 12 * ∑ v : Fin 14, Nat.card ((Gᶜ).neighborSet v) := by
    apply x2611_15358_lem2_6_aux8 G 2 3 12
    · intro S hS
      have hc := (mem_powersetCard.mp hS).2
      have hb := x2611_15358_lem2_6_aux1 Gᶜ S
      rw [hc] at hb
      have ht : x2611_15358_t G S ≤ 7 := by
        unfold x2611_15358_t
        omega
      exact x2611_15358_lem2_6_aux10 _ ht
    · intro v
      exact (x2611_15358_lem2_6_aux9 _ (x2611_15358_lem2_6_aux6 G hdeg v)).2.1
  have h3 : x2611_15358_N G 3 ≤ 10 * ∑ v : Fin 14, Nat.card ((Gᶜ).neighborSet v) := by
    apply x2611_15358_lem2_6_aux8 G 3 1 10
    · intro S hS
      have hc := (mem_powersetCard.mp hS).2
      have hb := x2611_15358_lem2_6_aux1 Gᶜ S
      rw [hc] at hb
      have ht : x2611_15358_t G S ≤ 5 := by
        unfold x2611_15358_t
        omega
      simpa using x2611_15358_lem2_6_aux11 _ ht
    · intro v
      simpa using (x2611_15358_lem2_6_aux9 _ (x2611_15358_lem2_6_aux6 G hdeg v)).2.2
  have hsum : (∑ v : Fin 14, Nat.card ((Gᶜ).neighborSet v)) = 2 * Nat.card (Gᶜ).edgeSet := by
    simp only [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, SimpleGraph.edgeFinset_card]
  have hD := x2611_15358_small_component_bound G hdeg hq
  rw [hsum] at h1 h2 h3
  omega
end

-- forge:entry x2611_15358_triple_double_count kind=proved origin=paper
section
/- Lemma 2.6, proof (triple double count) -/
lemma x2611_15358_triple_double_count_aux1 {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) :
    (Finset.univ.powersetCard k : Finset (Finset V)).sum
        (fun S => Nat.card {v : V // ∀ x ∈ S, G.Adj x v}) =
      Finset.univ.sum (fun v : V => (Nat.card (G.neighborSet v)).choose k) := by
  classical
  calc
    _ = ∑ S ∈ (Finset.univ.powersetCard k : Finset (Finset V)),
        ∑ v : V, if (∀ x ∈ S, G.Adj x v) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ v : V, ∑ S ∈ (Finset.univ.powersetCard k : Finset (Finset V)),
        if (∀ x ∈ S, G.Adj x v) then 1 else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, smul_eq_mul, mul_one]
      have hs : (Finset.univ.powersetCard k : Finset (Finset V)).filter
          (fun S => ∀ x ∈ S, G.Adj x v) = (G.neighborFinset v).powersetCard k := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        constructor
        · rintro ⟨hcard, hadj⟩
          refine ⟨?_, hcard⟩
          intro x hx
          exact (G.mem_neighborFinset v x).mpr (G.adj_symm (hadj x hx))
        · rintro ⟨hsub, hcard⟩
          refine ⟨hcard, ?_⟩
          intro x hx
          exact G.adj_symm ((G.mem_neighborFinset v x).mp (hsub hx))
      rw [hs, Finset.card_powersetCard, SimpleGraph.card_neighborFinset_eq_degree,
        Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]

theorem x2611_15358_triple_double_count (G : SimpleGraph (Fin 14))
    (hdeg : ∀ v : Fin 14, 4 ≤ Nat.card (G.neighborSet v))
    (hq : Nat.card (Gᶜ).edgeSet ≤ 15) :
    (Finset.univ.powersetCard 3 : Finset (Finset (Fin 14))).sum
        (fun S => x2611_15358_t G S) =
      Finset.univ.sum (fun v : Fin 14 =>
        ((fun v : Fin 14 => Nat.card ((Gᶜ).neighborSet v)) v).choose 3) := by
  exact x2611_15358_triple_double_count_aux1 Gᶜ 3
end

-- forge:entry x2611_15358_N2_bound kind=proved origin=paper
section
/- Lemma 2.6, proof (N₂ estimate) -/
lemma x2611_15358_N2_bound_aux1 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (k : ℕ) :
    Nat.card {C : (G.induce (↑U : Set V)).ConnectedComponent // Nat.card C.supp = k} ≤
      ∑ S ∈ Finset.univ.powersetCard k,
        if S ⊆ U ∧ (∀ x ∈ S, ∀ y ∈ U \ S, (Gᶜ).Adj x y) then 1 else 0 := by
  classical
  let A := (Finset.univ.powersetCard k).filter
    (fun S => S ⊆ U ∧ ∀ x ∈ S, ∀ y ∈ U \ S, (Gᶜ).Adj x y)
  let f : {C : (G.induce (↑U : Set V)).ConnectedComponent // Nat.card C.supp = k} → A :=
    fun C => ⟨C.val.supp.toFinset.image (fun x => x.val), by
      have hcard : (C.val.supp.toFinset.image (fun x => x.val)).card = k := by
        rw [Finset.card_image_of_injective _ Subtype.val_injective]
        simpa only [Set.toFinset_card, Nat.card_eq_fintype_card] using C.property
      have hsub : C.val.supp.toFinset.image (fun x => x.val) ⊆ U := by
        intro x hx
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
        exact v.property
      refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩,
        hsub, ?_⟩
      intro x hx y hy
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      have hv' : v ∈ C.val.supp := Set.mem_toFinset.mp hv
      have hy' := Finset.mem_sdiff.mp hy
      refine ⟨?_, ?_⟩
      · intro he
        apply hy'.2
        rw [← he]
        exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
      · intro ha
        have hm : (⟨y, hy'.1⟩ : (↑U : Set V)) ∈ C.val.supp :=
          C.val.mem_supp_of_adj_mem_supp hv' ha
        exact hy'.2 (Finset.mem_image.mpr ⟨⟨y, hy'.1⟩, Set.mem_toFinset.mpr hm, rfl⟩)⟩
  have hf : Function.Injective f := by
    intro C D h
    apply Subtype.ext
    apply SimpleGraph.ConnectedComponent.supp_injective
    have he := congrArg Subtype.val h
    change C.val.supp.toFinset.image (fun x => x.val) =
      D.val.supp.toFinset.image (fun x => x.val) at he
    have ht := Finset.image_injective Subtype.val_injective he
    exact Set.toFinset_inj.mp ht
  have h := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_eq_sum_ones,
    Finset.sum_filter, A] using h

lemma x2611_15358_N2_bound_aux2 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (n : ℕ) :
    (∑ U ∈ Finset.univ.powersetCard (n + S.card),
      if S ⊆ U ∧ (∀ x ∈ S, ∀ y ∈ U \ S, (Gᶜ).Adj x y) then 1 else 0) =
      (Nat.card {v : V // ∀ x ∈ S, (Gᶜ).Adj x v}).choose n := by
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  let T := Finset.univ.filter (fun v => ∀ x ∈ S, (Gᶜ).Adj x v)
  have ht : T.card = Nat.card {v : V // ∀ x ∈ S, (Gᶜ).Adj x v} := by
    simp [T, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← ht, ← Finset.card_powersetCard]
  apply Finset.card_bij (fun U _ => U \ S)
  · intro U hU
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and] at hU
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, ?_⟩
    · intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x hx => hU.2.2 x hx v hv⟩
    · rw [Finset.card_sdiff_of_subset hU.2.1, hU.1]
      omega
  · intro U hU W hW hUW
    simp only [Finset.mem_filter] at hU hW
    have h1 := Finset.sdiff_union_of_subset hU.2.1
    have h2 := Finset.sdiff_union_of_subset hW.2.1
    rw [← h1, ← h2, hUW]
  · intro R hR
    have hr := Finset.mem_powersetCard.mp hR
    have hd : Disjoint R S := by
      apply Finset.disjoint_left.mpr
      intro v hv hs
      have ha := (Finset.mem_filter.mp (hr.1 hv)).2 v hs
      exact (Gᶜ).irrefl ha
    refine ⟨R ∪ S, ?_, Finset.union_sdiff_cancel_right hd⟩
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    refine ⟨by rw [Finset.card_union_of_disjoint hd, hr.2], Finset.subset_union_right, ?_⟩
    intro x hx y hy
    have hyR : y ∈ R := by
      rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hy).1 with h | h
      · exact h
      · exact False.elim ((Finset.mem_sdiff.mp hy).2 h)
    exact (Finset.mem_filter.mp (hr.1 hyR)).2 x hx

lemma x2611_15358_N2_bound_aux3 {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (k : ℕ) :
    (∑ S ∈ Finset.univ.powersetCard k, Nat.card {v : V // ∀ x ∈ S, H.Adj x v}) =
      ∑ v : V, (Nat.card (H.neighborSet v)).choose k := by
  classical
  have ht (S : Finset V) : Nat.card {v : V // ∀ x ∈ S, H.Adj x v} =
      ∑ v : V, if ∀ x ∈ S, H.Adj x v then 1 else 0 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [ht]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  simp only [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree, ← Finset.card_powersetCard]
  congr 1
  ext S
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
  constructor
  · rintro ⟨hc, ha⟩
    exact ⟨fun x hx => (H.mem_neighborFinset v x).mpr (ha x hx).symm, hc⟩
  · rintro ⟨ha, hc⟩
    exact ⟨hc, fun x hx => ((H.mem_neighborFinset v x).mp (ha hx)).symm⟩

lemma x2611_15358_N2_bound_aux4 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n k : ℕ) :
    (∑ U ∈ (Finset.univ.powersetCard (n + k) : Finset (Finset V)),
      Nat.card {C : (G.induce (↑U : Set V)).ConnectedComponent // Nat.card C.supp = k}) ≤
      ∑ S ∈ Finset.univ.powersetCard k,
        (Nat.card {v : V // ∀ x ∈ S, (Gᶜ).Adj x v}).choose n := by
  classical
  calc
    _ ≤ ∑ U ∈ Finset.univ.powersetCard (n + k),
        ∑ S ∈ Finset.univ.powersetCard k,
          if S ⊆ U ∧ (∀ x ∈ S, ∀ y ∈ U \ S, (Gᶜ).Adj x y) then 1 else 0 := by
      apply Finset.sum_le_sum
      intro U hU
      exact x2611_15358_N2_bound_aux1 G U k
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S hS
      have hs := (Finset.mem_powersetCard.mp hS).2
      simpa only [hs] using x2611_15358_N2_bound_aux2 G S n

theorem x2611_15358_N2_bound (G : SimpleGraph (Fin 14))
    (hdeg : ∀ v : Fin 14, 4 ≤ Nat.card (G.neighborSet v))
    (hq : Nat.card (Gᶜ).edgeSet ≤ 15) :
    x2611_15358_N G 2 ≤ (Finset.univ.powersetCard 2 : Finset (Finset (Fin 14))).sum (fun S => (x2611_15358_t G S).choose 5) ∧
    (Finset.univ.powersetCard 2 : Finset (Finset (Fin 14))).sum (fun S => (x2611_15358_t G S).choose 5) ≤ 3 * ((Finset.univ.powersetCard 2 : Finset (Finset (Fin 14))).sum (fun S => x2611_15358_t G S)) ∧
    3 * ((Finset.univ.powersetCard 2 : Finset (Finset (Fin 14))).sum (fun S => x2611_15358_t G S)) = 3 * (Finset.univ.sum (fun v : Fin 14 => ((fun v : Fin 14 => Nat.card ((Gᶜ).neighborSet v)) v).choose 2)) ∧
    3 * (Finset.univ.sum (fun v : Fin 14 => ((fun v : Fin 14 => Nat.card ((Gᶜ).neighborSet v)) v).choose 2)) ≤ 12 * (Finset.univ.sum (fun v : Fin 14 => Nat.card ((Gᶜ).neighborSet v))) ∧
    12 * (Finset.univ.sum (fun v : Fin 14 => Nat.card ((Gᶜ).neighborSet v))) = 24 * (Nat.card (Gᶜ).edgeSet) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [x2611_15358_N, x2611_15358_t] using
      x2611_15358_N2_bound_aux4 G 5 2
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro S hS
    have hs := (Finset.mem_powersetCard.mp hS).2
    have hb := x2611_15358_pair_common_bound G hdeg hq S hs
    have ht : x2611_15358_t G S ≤ 7 := by omega
    interval_cases h : x2611_15358_t G S <;> norm_num [Nat.choose]
  · exact congrArg (fun n : ℕ => 3 * n) (x2611_15358_N2_bound_aux3 Gᶜ 2)
  · rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hv
    have hd := hdeg v
    simp only [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] at hd ⊢
    have hc := G.degree_compl v
    have hb : (Gᶜ).degree v ≤ 9 := by simp only [Fintype.card_fin] at hc; omega
    interval_cases h : (Gᶜ).degree v <;> norm_num [Nat.choose]
  · simp only [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree,
      SimpleGraph.card_edgeSet]
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
    omega
end

-- forge:entry x2611_10667_remark3_2_valuation kind=proved origin=paper
section
/- Remark 3.2 (valuation identity) -/
theorem x2611_10667_remark3_2_valuation
    (q r : ℕ) (hq : q.Prime) (hr : r.Prime) (hq2 : 2 < q) (hr2 : 2 < r)
    (hqr : q ≠ r) (t : ℚ) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hv : 0 < padicValRat q (t - 1)) :
    padicValRat q (t - 1) = padicValRat q (t⁻¹ - 1) := by
  letI : Fact q.Prime := ⟨hq⟩
  have ht_sub : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have ht_val : padicValRat q t = 0 := by
    have h := padicValRat.add_eq_of_lt (p := q) (q := 1) (r := t - 1)
      (by simpa using ht0) one_ne_zero ht_sub (by simpa using hv)
    simpa using h
  have hid : t⁻¹ - 1 = -(t - 1) / t := by
    field_simp [ht0]
    <;> ring
  rw [hid, padicValRat.div (neg_ne_zero.mpr ht_sub) ht0,
    padicValRat.neg, ht_val, sub_zero]
end

-- forge:entry x2611_10200_thm1_1 kind=proved origin=paper
section
/- Theorem 1.1 (Exact threshold) -/
open scoped BigOperators

lemma x2611_10200_thm1_1_aux1 (H : ℕ → ℤ)
    (hpos : ∀ n : ℕ, 1 ≤ n → 1 ≤ H n)
    (hgap : ∀ n : ℕ, 1 ≤ n → 0 ≤ x2611_10200_B H n) :
    x2611_10200_complete H := by
  classical
  have hrep : ∀ n : ℕ, ∀ t : ℤ, 0 ≤ t → t ≤ (Finset.Icc 1 n).sum H →
      ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 n ∧ t = S.sum H := by
    intro n
    induction n with
    | zero =>
      intro t ht hbound
      have ht0 : t = 0 := by simpa using (le_antisymm hbound ht)
      exact ⟨∅, by simp, by simp [ht0]⟩
    | succ n ih =>
      intro t ht hbound
      have hsum : (Finset.Icc 1 (n + 1)).sum H =
          (Finset.Icc 1 n).sum H + H (n + 1) :=
        Finset.sum_Icc_succ_top (by omega) H
      by_cases hsmall : t ≤ (Finset.Icc 1 n).sum H
      · obtain ⟨S, hS, heq⟩ := ih t ht hsmall
        refine ⟨S, ?_, heq⟩
        intro i hi
        have hi' := Finset.mem_Icc.mp (hS hi)
        exact Finset.mem_Icc.mpr ⟨hi'.1, by omega⟩
      · have hb := hgap (n + 1) (by omega)
        simp only [x2611_10200_B, Nat.add_sub_cancel] at hb
        change 0 ≤ 1 + (Finset.Icc 1 n).sum H - H (n + 1) at hb
        rw [hsum] at hbound
        obtain ⟨S, hS, heq⟩ := ih (t - H (n + 1)) (by omega) (by omega)
        have hnot : n + 1 ∉ S := by
          intro hh
          have hh' := Finset.mem_Icc.mp (hS hh)
          omega
        refine ⟨insert (n + 1) S, ?_, ?_⟩
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · simp
          · have hi' := Finset.mem_Icc.mp (hS hi)
            exact Finset.mem_Icc.mpr ⟨hi'.1, by omega⟩
        · rw [Finset.sum_insert hnot]
          change t = H (n + 1) + S.sum H
          omega
  have hbound : ∀ n : ℕ, (n : ℤ) ≤ (Finset.Icc 1 n).sum H := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega) H]
      have hp := hpos (n + 1) (by omega)
      push_cast
      change (n : ℤ) + 1 ≤ (Finset.Icc 1 n).sum H + H (n + 1)
      omega
  intro t ht
  obtain ⟨S, hS, heq⟩ := hrep t.toNat t (by omega)
    (by simpa only [Int.toNat_of_nonneg (by omega : 0 ≤ t)] using hbound t.toNat)
  exact ⟨S, fun i hi => (Finset.mem_Icc.mp (hS hi)).1, heq⟩

theorem x2611_10200_thm1_1 (g k N : ℕ) (hg : 1 ≤ g) (hk : 1 ≤ k)
    (hN : 1 ≤ N) (H : ℕ → ℤ) (hH : x2611_10200_standard g k N H) :
    x2611_10200_complete H ↔
      1 ≤ N ∧ (N : ℤ) ≤ Int.floor (x2611_10200_M g k) := by
  constructor
  · intro hc
    refine ⟨hN, Int.le_floor.mpr ?_⟩
    simpa using (x2611_10200_lem2_1 g k N hg hk hN).2.2.2 H hH hc
  · rintro ⟨_, hfloor⟩
    have hM : (N : ℝ) ≤ x2611_10200_M g k := by
      simpa using Int.le_floor.mp hfloor
    have hf : ∀ m : ℤ, 0 ≤ x2611_10200_f g k N m := by
      by_cases hg1 : g = 1
      · subst g
        exact (x2611_10200_lem4_1 k N hk hN hM).1
      · exact (x2611_10200_lem3_1 g k N (by omega) hk hN hM).1
    apply x2611_10200_thm1_1_aux1 H
      (x2611_10200_lem2_1_aux1 g k N hg hk hN H hH).1
    intro n hn
    have hB := x2611_10200_brown_gap_coefficients g k N hg hk hN H hH
    by_cases hsmall : n ≤ g + 1
    · rw [hB.1 n hn hsmall]
    · have heq : n = (n - (g + 2)) + g + 2 := by omega
      rw [heq, hB.2]
      exact hf _
end

-- forge:entry x2611_15505_lem3_1 kind=proved origin=paper
section
/- Lemma 3.1 -/
open Polynomial

lemma x2611_15505_lem3_1_aux1 (p : Polynomial ℝ) (a b : ℝ)
    (hab : a < b) (hs : p.eval a * p.eval b < 0) :
    ∃ x : ℝ, a < x ∧ x < b ∧ p.eval x = 0 := by
  rcases mul_neg_iff.mp hs with h | h
  · obtain ⟨x, hx, he⟩ := intermediate_value_Ioo' hab.le p.continuous.continuousOn ⟨h.2, h.1⟩
    exact ⟨x, hx.1, hx.2, he⟩
  · obtain ⟨x, hx, he⟩ := intermediate_value_Ioo hab.le p.continuous.continuousOn h
    exact ⟨x, hx.1, hx.2, he⟩

lemma x2611_15505_lem3_1_aux2 (w : List ℕ) (j : ℕ) :
    (Finset.univ.filter (fun i : Fin w.length => w.get i = j)).card = w.count j := by
  exact Fin.card_filter_univ_eq_vector_get_eq_count j ⟨w, rfl⟩

lemma x2611_15505_lem3_1_aux3 {m : ℕ} (p : Polynomial ℝ)
    (x : Fin m → ℝ) (hx : Function.Injective x) (S : Finset (Fin m))
    (hp : p ≠ 0) (hd : p.natDegree ≤ S.card)
    (hr : ∀ i ∈ S, p.eval (x i) = 0) :
    p.roots = S.val.map x := by
  let e : Fin m ↪ ℝ := ⟨x, hx⟩
  have he := Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
    (p := p) (S := S.map e) ?_ (by simpa using hd) hp
  · simpa [e] using he
  · intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hy
    exact hr i hi

theorem x2611_15505_lem3_1 (n : ℕ) (p : Polynomial ℤ) (hp : p ≠ 0) (hdeg : p.natDegree = n)
  (w : List ℕ) (hw : x2611_15505_word_multiplicities n w)
  (q : ℕ) (hq : 0 < q) (b : Fin (w.length + 1) → ℤ) (hb : StrictMono b)
  (hsign : ∀ i : Fin w.length,
    (((Polynomial.derivative : Polynomial ℝ → Polynomial ℝ)^[w.get i] (p.map (Int.castRingHom ℝ))).eval ((b i.castSucc : ℝ) / (q : ℝ))) *
    (((Polynomial.derivative : Polynomial ℝ → Polynomial ℝ)^[w.get i] (p.map (Int.castRingHom ℝ))).eval ((b i.succ : ℝ) / (q : ℝ))) < 0) :
  x2611_15505_realizes n (p.map (Int.castRingHom ℝ)) w := by
  classical
  have hpR : p.map (Int.castRingHom ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hp
  have hdR : (p.map (Int.castRingHom ℝ)).natDegree = n := by
    rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective, hdeg]
  let a : Fin (w.length + 1) → ℝ := fun i => (b i : ℝ) / (q : ℝ)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have ha : StrictMono a := by
    intro i j hij
    apply (div_lt_div_iff_of_pos_right hqR).mpr
    exact_mod_cast hb hij
  have hex : ∀ i : Fin w.length, ∃ x : ℝ,
      a i.castSucc < x ∧ x < a i.succ ∧
      ((Polynomial.derivative : Polynomial ℝ → Polynomial ℝ)^[w.get i]
        (p.map (Int.castRingHom ℝ))).eval x = 0 := by
    intro i
    exact x2611_15505_lem3_1_aux1 _ _ _ (ha Fin.castSucc_lt_succ) (hsign i)
  choose x hx using hex
  have hmono : StrictMono x := by
    intro i j hij
    have hle : a i.succ ≤ a j.castSucc := by
      apply ha.monotone
      show i.val + 1 ≤ j.val
      exact Nat.succ_le_of_lt hij
    exact ((hx i).2.1.trans_le hle).trans (hx j).1
  refine ⟨hpR, hdR, hw, x, hmono, ?_⟩
  intro j hj
  have hjmem : j ∈ w := List.count_pos_iff.mp (by rw [hw.2.2 j hj]; omega)
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hjmem
  have hne : ((Polynomial.derivative : Polynomial ℝ → Polynomial ℝ)^[j]
      (p.map (Int.castRingHom ℝ))) ≠ 0 := by
    intro hz
    have hs := hsign i
    rw [hi, hz] at hs
    simpa using hs
  apply x2611_15505_lem3_1_aux3 _ x hmono.injective _ hne
  · rw [x2611_15505_lem3_1_aux2, hw.2.2 j hj]
    simpa [hdR] using Polynomial.natDegree_iterate_derivative
      (p.map (Int.castRingHom ℝ)) j
  · intro k hk
    have hk' : w.get k = j := (Finset.mem_filter.mp hk).2
    have hxk := (hx k).2.2
    rw [hk'] at hxk
    exact hxk
end

-- forge:entry x2611_15505_lem2_1 kind=proved origin=paper
section
/- Lemma 2.1 -/
lemma x2611_15505_lem2_1_aux1 {α : Type*} (a b : α) (m : ℕ) :
    a :: (List.replicate m [b, a]).flatten =
      (List.replicate m [a, b]).flatten ++ [a] := by
  induction m with
  | zero => simp
  | succ m ih =>
    simpa [List.replicate_succ, List.flatten_cons] using congrArg (fun l => a :: b :: l) ih

lemma x2611_15505_lem2_1_aux2 {α : Type*} [DecidableEq α]
    (w : List α) (a b : α) (hab : a ≠ b)
    (h : ∀ k : ℕ, k ≤ w.length →
      (w.take k).count b ≤ (w.take k).count a ∧
      (w.take k).count a ≤ (w.take k).count b + 1) :
    ∃ m : ℕ, w.filter (fun x => x = a ∨ x = b) =
        (List.replicate m [a, b]).flatten ∨
      w.filter (fun x => x = a ∨ x = b) =
        (List.replicate m [a, b]).flatten ++ [a] := by
  induction w generalizing a b with
  | nil => exact ⟨0, Or.inl (by simp)⟩
  | cons x w ih =>
    by_cases hxa : x = a
    · subst x
      have ht : ∀ k : ℕ, k ≤ w.length →
          (w.take k).count a ≤ (w.take k).count b ∧
          (w.take k).count b ≤ (w.take k).count a + 1 := by
        intro k hk
        have hh := h (k + 1) (by simpa using Nat.succ_le_succ hk)
        simp [List.take_succ_cons, hab, hab.symm] at hh
        omega
      obtain ⟨m, hm | hm⟩ := ih b a hab.symm ht
      · refine ⟨m, Or.inr ?_⟩
        have he : w.filter (fun x => x = a ∨ x = b) =
            (List.replicate m [b, a]).flatten := by simpa only [or_comm] using hm
        rw [List.filter_cons_of_pos (by simp)]
        rw [he]
        exact x2611_15505_lem2_1_aux1 a b m
      · refine ⟨m + 1, Or.inl ?_⟩
        have he : w.filter (fun x => x = a ∨ x = b) =
            (List.replicate m [b, a]).flatten ++ [b] := by simpa only [or_comm] using hm
        rw [List.filter_cons_of_pos (by simp)]
        rw [he, ← List.cons_append, x2611_15505_lem2_1_aux1 a b m]
        simp [List.replicate_succ', List.flatten_append, List.append_assoc]
    · by_cases hxb : x = b
      · subst x
        have hh := h 1 (by simp)
        simp [hab, hab.symm] at hh
      · have ht : ∀ k : ℕ, k ≤ w.length →
            (w.take k).count b ≤ (w.take k).count a ∧
            (w.take k).count a ≤ (w.take k).count b + 1 := by
          intro k hk
          have hh := h (k + 1) (by simpa using Nat.succ_le_succ hk)
          simpa [List.take_succ_cons, hxa, hxb] using hh
        obtain ⟨m, hm⟩ := ih a b hab ht
        exact ⟨m, by simpa [hxa, hxb] using hm⟩

lemma x2611_15505_lem2_1_aux3 {α : Type*} [DecidableEq α]
    (w : List α) (a b : α) (hab : a ≠ b) (m : ℕ)
    (ha : w.count a = m + 1) (hb : w.count b = m)
    (h : ∀ k : ℕ, k ≤ w.length →
      (w.take k).count b ≤ (w.take k).count a ∧
      (w.take k).count a ≤ (w.take k).count b + 1) :
    w.filter (fun x => x = a ∨ x = b) =
      (List.replicate m [a, b]).flatten ++ [a] := by
  obtain ⟨r, he | he⟩ := x2611_15505_lem2_1_aux2 w a b hab h
  · have hca := congrArg (List.count a) he
    have hcb := congrArg (List.count b) he
    simp [List.count_flatten, hab, hab.symm, ha, hb] at hca hcb
    omega
  · have hcb := congrArg (List.count b) he
    have hr : m = r := by
      simpa [List.count_flatten, hab, hab.symm, hb] using hcb
    simpa [hr] using he

lemma x2611_15505_lem2_1_aux4 {α : Type*} [DecidableEq α]
    (a b : α) (hab : a ≠ b) (m k : ℕ) :
    (((List.replicate m [a, b]).flatten ++ [a]).take k).count b ≤
        (((List.replicate m [a, b]).flatten ++ [a]).take k).count a ∧
    (((List.replicate m [a, b]).flatten ++ [a]).take k).count a ≤
        (((List.replicate m [a, b]).flatten ++ [a]).take k).count b + 1 := by
  induction m generalizing k with
  | zero =>
    cases k <;> simp [hab, hab.symm]
  | succ m ih =>
    cases k with
    | zero => simp
    | succ k =>
      cases k with
      | zero => simp [List.replicate_succ, hab, hab.symm]
      | succ k =>
        simpa [List.replicate_succ, List.flatten_cons, List.take_succ_cons,
          hab, hab.symm] using ih k

lemma x2611_15505_lem2_1_aux5 {α : Type*} [DecidableEq α]
    (w : List α) (a b : α) (hab : a ≠ b) (m : ℕ)
    (h : w.filter (fun x => x = a ∨ x = b) =
      (List.replicate m [a, b]).flatten ++ [a]) (k : ℕ) :
    (w.take k).count b ≤ (w.take k).count a ∧
    (w.take k).count a ≤ (w.take k).count b + 1 := by
  have hp := (List.take_prefix k w).filter (fun x => x = a ∨ x = b)
  rw [h] at hp
  have he := List.prefix_iff_eq_take.mp hp
  have hh := x2611_15505_lem2_1_aux4 a b hab m
    (((w.take k).filter (fun x => x = a ∨ x = b)).length)
  rw [← he] at hh
  simpa using hh

theorem x2611_15505_lem2_1 (n : ℕ) (w : List ℕ)
    (hw : x2611_15505_word_multiplicities n w) :
    x2611_15505_formal_word n w ↔
    ∀ k : ℕ, k ≤ w.length → ∀ j : ℕ, j + 1 < n →
      0 ≤ ((w.take k).count j : ℤ) - ((w.take k).count (j + 1) : ℤ) ∧
      ((w.take k).count j : ℤ) - ((w.take k).count (j + 1) : ℤ) ≤ 1 := by
  constructor
  · intro h k hk j hj
    have hh := x2611_15505_lem2_1_aux5 w j (j + 1) (by omega)
      (n - j - 1) (h.2 j hj) k
    omega
  · intro h
    refine ⟨hw, ?_⟩
    intro j hj
    apply x2611_15505_lem2_1_aux3 w j (j + 1) (by omega) (n - j - 1)
    · have hc := hw.2.2 j (by omega)
      omega
    · have hc := hw.2.2 (j + 1) hj
      omega
    · intro k hk
      have hh := h k hk j hj
      omega
end

-- forge:entry x2611_15512_thm2_3 kind=proved origin=paper
section
/- Theorem 2.3 -/
open SimpleGraph

lemma x2611_15512_thm2_3_aux1 {V : Type*} [Fintype V] {G : SimpleGraph V}
    (M : G.Subgraph) (hM : M.IsMatching) (C : Set V) (hC : G.IsVertexCover C) :
    M.edgeSet.ncard ≤ C.ncard := by
  classical
  have hex : ∀ e : M.edgeSet, ∃ v : C, (v : V) ∈ (e : Sym2 V) := by
    rintro ⟨⟨v, w⟩, he⟩
    rcases hC (M.adj_sub he) with hv | hw
    · exact ⟨⟨v, hv⟩, Sym2.mem_mk_left _ _⟩
    · exact ⟨⟨w, hw⟩, Sym2.mem_mk_right _ _⟩
  choose f hf using hex
  have hrecover (e : M.edgeSet) :
      hM.toEdge ⟨f e, M.mem_verts_of_mem_edge e.property (hf e)⟩ = e := by
    obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp (hf e)
    have ha : M.Adj (f e) w := by
      have := e.property
      rw [hw] at this
      exact this
    apply Subtype.ext
    simpa only [hw] using congrArg Subtype.val (hM.toEdge_eq_of_adj ha)
  have hinj : Function.Injective f := by
    intro e e' he
    rw [← hrecover e, ← hrecover e']
    congr 1
    exact Subtype.ext (congrArg (fun z : C => (z : V)) he)
  simpa only [Nat.card_coe_set_eq] using Nat.card_le_card_of_injective f hinj

lemma x2611_15512_thm2_3_aux2 {V : Type*} [Fintype V] (G : SimpleGraph V)
    (C : Set V) (hC : G.IsVertexCover C)
    (hmin : ∀ D : Set V, G.IsVertexCover D → C.ncard ≤ D.ncard)
    (S : Set V) (hSC : S ⊆ C) (hind : G.IsIndepSet S) :
    S.ncard ≤ (⋃ x ∈ S, (G.between C Cᶜ).neighborSet x).ncard := by
  classical
  let N := ⋃ x ∈ S, (G.between C Cᶜ).neighborSet x
  have hcover : G.IsVertexCover ((C \ S) ∪ N) := by
    intro v w ha
    by_cases hv : v ∈ S
    · by_cases hw : w ∈ C
      · exact Or.inr (Or.inl ⟨hw, fun hwS => hind hv hwS ha.ne ha⟩)
      · exact Or.inr (Or.inr (by
          simp only [N, Set.mem_iUnion, mem_neighborSet]
          exact ⟨v, hv, ha, Or.inl ⟨hSC hv, hw⟩⟩))
    · by_cases hw : w ∈ S
      · by_cases hvC : v ∈ C
        · exact Or.inl (Or.inl ⟨hvC, hv⟩)
        · exact Or.inl (Or.inr (by
            simp only [N, Set.mem_iUnion, mem_neighborSet]
            exact ⟨w, hw, ha.symm, Or.inl ⟨hSC hw, hvC⟩⟩))
      · rcases hC ha with hvC | hwC
        · exact Or.inl (Or.inl ⟨hvC, hv⟩)
        · exact Or.inr (Or.inl ⟨hwC, hw⟩)
  have h1 := hmin _ hcover
  have h2 := Set.ncard_union_le (C \ S) N
  have h3 := Set.ncard_sdiff_add_ncard_of_subset hSC
  dsimp [N] at *
  omega

lemma x2611_15512_thm2_3_aux3 {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.IsBipartite) (C : Set V) (hC : G.IsVertexCover C)
    (hmin : ∀ D : Set V, G.IsVertexCover D → C.ncard ≤ D.ncard) :
    ∀ S ⊆ C, S.ncard ≤ (⋃ x ∈ S, (G.between C Cᶜ).neighborSet x).ncard := by
  classical
  obtain ⟨s, t, hst⟩ := hG.exists_isBipartiteWith
  have hb : G.IsBipartiteWith s sᶜ := by
    refine ⟨disjoint_compl_right, ?_⟩
    intro v w ha
    rcases hst.mem_of_adj ha with ⟨hv, hw⟩ | ⟨hv, hw⟩
    · exact Or.inl ⟨hv, hst.disjoint.notMem_of_mem_right hw⟩
    · exact Or.inr ⟨hst.disjoint.notMem_of_mem_right hv, hw⟩
  intro S hSC
  let K := G.between C Cᶜ
  let N₁ := ⋃ x ∈ S ∩ s, K.neighborSet x
  let N₂ := ⋃ x ∈ S \ s, K.neighborSet x
  have hind₁ : G.IsIndepSet (S ∩ s) := by
    intro v hv w hw hne ha
    exact (hb.mem_of_mem_adj hv.2 ha) hw.2
  have hind₂ : G.IsIndepSet (S \ s) := by
    intro v hv w hw hne ha
    exact hv.2 (hb.mem_of_mem_adj' hw.2 ha)
  have h1 := x2611_15512_thm2_3_aux2 G C hC hmin (S ∩ s)
    (fun _ h => hSC h.1) hind₁
  have h2 := x2611_15512_thm2_3_aux2 G C hC hmin (S \ s)
    (fun _ h => hSC h.1) hind₂
  have hd : Disjoint N₁ N₂ := by
    rw [Set.disjoint_left]
    intro v hv₁ hv₂
    simp only [N₁, N₂, Set.mem_iUnion, mem_neighborSet] at hv₁ hv₂
    obtain ⟨x, hx, hxa⟩ := hv₁
    obtain ⟨y, hy, hya⟩ := hv₂
    exact (hb.mem_of_mem_adj hx.2 hxa.1) (hb.symm.mem_of_mem_adj hy.2 hya.1)
  have hsub : N₁ ∪ N₂ ⊆ ⋃ x ∈ S, K.neighborSet x := by
    intro v hv
    simp only [N₁, N₂, Set.mem_union, Set.mem_iUnion] at hv ⊢
    rcases hv with ⟨x, hx, ha⟩ | ⟨x, hx, ha⟩
    · exact ⟨x, hx.1, ha⟩
    · exact ⟨x, hx.1, ha⟩
  have h3 := Set.ncard_le_ncard hsub
  rw [Set.ncard_union_eq hd] at h3
  have h4 := Set.ncard_inter_add_ncard_sdiff_eq_ncard S s
  change (S ∩ s).ncard ≤ N₁.ncard at h1
  change (S \ s).ncard ≤ N₂.ncard at h2
  change S.ncard ≤ (⋃ x ∈ S, K.neighborSet x).ncard
  omega

lemma x2611_15512_thm2_3_aux4 {V : Type*} [Fintype V] {G : SimpleGraph V}
    (M : G.Subgraph) (hM : M.IsMatching) (C : Set V) (hsub : C ⊆ M.verts)
    (hcross : ∀ ⦃v w⦄, M.Adj v w → v ∈ C → w ∉ C) :
    C.ncard ≤ M.edgeSet.ncard := by
  classical
  let f : C → M.edgeSet := fun v => hM.toEdge ⟨v, hsub v.property⟩
  have hinj : Function.Injective f := by
    intro x y he
    obtain ⟨w, hw, _⟩ := hM (hsub x.property)
    have hx : f x = ⟨s((x : V), w), hw⟩ := hM.toEdge_eq_of_adj hw
    have hy : (y : V) ∈ (s((x : V), w) : Sym2 V) := by
      have hy' := hM.mem_coe_toEdge (hsub y.property)
      change (y : V) ∈ ((f y : M.edgeSet) : Sym2 V) at hy'
      rw [← he, hx] at hy'
      exact hy'
    rcases Sym2.mem_iff.mp hy with hy | hy
    · exact Subtype.ext hy.symm
    · exact (hcross hw x.property (hy ▸ y.property)).elim
  simpa only [Nat.card_coe_set_eq] using Nat.card_le_card_of_injective f hinj

theorem x2611_15512_thm2_3 {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.IsBipartite) :
    ∃ (H : G.Subgraph) (C : Set V), H.IsMatching ∧ G.IsVertexCover C ∧
      H.edgeSet.ncard = C.ncard ∧
      (∀ N : G.Subgraph, N.IsMatching → N.edgeSet.ncard ≤ H.edgeSet.ncard) ∧
      (∀ D : Set V, G.IsVertexCover D → C.ncard ≤ D.ncard) := by
  classical
  obtain ⟨C, hCeq, hC⟩ := G.vertexCoverNum_exists
  have hmin : ∀ D : Set V, G.IsVertexCover D → C.ncard ≤ D.ncard := by
    intro D hD
    have h := hD.vertexCoverNum_le
    rw [← hCeq, ← (Set.toFinite C).cast_ncard_eq,
      ← (Set.toFinite D).cast_ncard_eq] at h
    exact_mod_cast h
  let K := G.between C Cᶜ
  obtain ⟨M, hCM, hM⟩ := exists_isMatching_of_forall_ncard_le
    (G.between_isBipartiteWith disjoint_compl_right)
    (x2611_15512_thm2_3_aux3 G hG C hC hmin)
  let H : G.Subgraph := {
    verts := M.verts
    Adj := M.Adj
    adj_sub := fun h => (M.adj_sub h).1
    edge_vert := M.edge_vert
    symm := M.symm }
  have hH : H.IsMatching := hM
  have heq : H.edgeSet.ncard = C.ncard := by
    apply Nat.le_antisymm (x2611_15512_thm2_3_aux1 H hH C hC)
    apply x2611_15512_thm2_3_aux4 H hH C hCM
    intro v w ha hv hw
    have hcross := (M.adj_sub ha).2
    simp only [Set.mem_compl_iff] at hcross
    tauto
  refine ⟨H, C, hH, hC, heq, ?_, hmin⟩
  intro N hN
  rw [heq]
  exact x2611_15512_thm2_3_aux1 N hN C hC
end

-- forge:entry x2611_12360_thm1_3_s1h1 kind=proved origin=decomposition
section
/- x2611_12360_thm1_3 的证明骨架中第 1 个空洞 -/
lemma x2611_12360_thm1_3_s1h1_aux1 {ι : Type*} (f : ι → ℝ) (σ : ℝ)
    (k : ι) (n m : ℤ) (L : List (ι × ℤ))
    (hnm : n + 1 ≤ m) (hlast : (k, m) ∈ (k, n) :: L)
    (hchain : ((k, n) :: L).IsChain (fun a b =>
      (-f b.1 + (b.2 : ℝ)) - (-f a.1 + (a.2 : ℝ)) ≤ σ)) :
    ∀ γ : ℝ, ∃ i, x2611_12360_modMem 1 (Set.Ico 0 σ) (f i + γ) := by
  intro γ
  by_contra! h
  let d : ℤ := ⌊γ - (-f k + (n : ℝ))⌋
  have hdlo : -f k + (n : ℝ) + (d : ℝ) ≤ γ := by
    have hh := Int.floor_le (γ - (-f k + (n : ℝ)))
    change (d : ℝ) ≤ _ at hh
    linarith
  have hdhi : γ < -f k + (m : ℝ) + (d : ℝ) := by
    have hh := Int.lt_floor_add_one (γ - (-f k + (n : ℝ)))
    change _ < (d : ℝ) + 1 at hh
    have hnm' : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hnm
    linarith
  have hb (q : ι × ℤ) (hq : -f q.1 + (q.2 : ℝ) + (d : ℝ) ≤ γ) :
      -f q.1 + (q.2 : ℝ) + (d : ℝ) ≤ γ - σ := by
    by_contra! hh
    apply h q.1
    refine ⟨γ - (-f q.1 + (q.2 : ℝ) + (d : ℝ)),
      ⟨by linarith, by linarith⟩, q.2 + d, ?_⟩
    push_cast
    ring
  have hc : ((k, n) :: L).IsChain (fun a b =>
      (-f a.1 + (a.2 : ℝ) + (d : ℝ) ≤ γ - σ) →
      (-f b.1 + (b.2 : ℝ) + (d : ℝ) ≤ γ - σ)) := by
    apply hchain.imp
    intro a b hab ha
    apply hb b
    linarith
  have hall : ∀ q ∈ (k, n) :: L,
      -f q.1 + (q.2 : ℝ) + (d : ℝ) ≤ γ - σ :=
    hc.induction _ _ (fun {_ _} h h' => h h') (fun _ => hb (k, n) hdlo)
  have hm := hall (k, m) hlast
  have hsig : 0 ≤ σ := by
    by_contra! hs
    have hlast' : -f k + (m : ℝ) + (d : ℝ) ≤ γ - σ := hm
    have hfirst' := hb (k,n) hdlo
    have hstep : ((k,n) :: L).IsChain (fun a b =>
        -f b.1 + (b.2 : ℝ) ≤ -f a.1 + (a.2 : ℝ)) := by
      apply hchain.imp
      intro a b hab
      linarith
    have hall' : ∀ q ∈ (k,n) :: L, -f q.1 + (q.2 : ℝ) ≤ -f k + (n : ℝ) :=
      hstep.induction _ _ (fun {_ _} h h' => le_trans h h') (fun _ => le_rfl)
    have hh := hall' (k,m) hlast
    linarith
  linarith

lemma x2611_12360_thm1_3_s1h1_aux2 (U b : ℝ)
    (hUlo : (199 : ℝ) / 23100 ≤ U) (hUhi : U ≤ (221 : ℝ) / 23100)
    (hl : (0 : ℝ) ≤ b) (hr : b ≤ ((1 / 4) : ℝ)) :
    ∀ γ : ℝ, ∃ k : Fin 21, x2611_12360_modMem 1 (Set.Ico 0 (8 / 33))
      (U * ((k.val : ℝ) - 10) ^ 2 + b * ((k.val : ℝ) - 10) + γ) := by
  have H := x2611_12360_thm1_3_s1h1_aux1
    (fun k : Fin 21 => U * ((k.val : ℝ) - 10) ^ 2 + b * ((k.val : ℝ) - 10))
    ((8 : ℝ) / 33)
  by_cases hm : b ≤ ((1 / 16) : ℝ)
  · have hr := hm
    by_cases hm : b ≤ ((1 / 32) : ℝ)
    · have hr := hm
      apply H 5 0 1 [(7, 0), (20, 1), (19, 1), (18, 1), (17, 1), (1, 1), (2, 1), (3, 1), (5, 1)]
      · norm_num
      · simp
      · norm_num [List.isChain_cons, List.isChain_nil]
        all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
    · have hl : ((1 / 32) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
      apply H 18 0 1 [(17, 0), (16, 0), (15, 0), (14, 0), (0, 0), (1, 0), (2, 0), (3, 0), (6, 0), (18, 1)]
      · norm_num
      · simp
      · norm_num [List.isChain_cons, List.isChain_nil]
        all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
  · have hl : ((1 / 16) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
    by_cases hm : b ≤ ((1 / 8) : ℝ)
    · have hr := hm
      apply H 14 0 1 [(13, 0), (12, 0), (11, 0), (10, 0), (8, 0), (16, 1), (15, 1), (14, 1)]
      · norm_num
      · simp
      · norm_num [List.isChain_cons, List.isChain_nil]
        all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
    · have hl : ((1 / 8) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
      by_cases hm : b ≤ ((3 / 16) : ℝ)
      · have hr := hm
        apply H 11 0 1 [(10, 0), (9, 0), (8, 0), (7, 0), (5, 0), (13, 1), (12, 1), (11, 1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons, List.isChain_nil]
          all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
      · have hl : ((3 / 16) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
        apply H 7 0 1 [(6, 0), (5, 0), (4, 0), (10, 1), (9, 1), (8, 1), (7, 1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons, List.isChain_nil]
          all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp

lemma x2611_12360_thm1_3_s1h1_aux3 (U b : ℝ)
    (hUlo : (199 : ℝ) / 23100 ≤ U) (hUhi : U ≤ (221 : ℝ) / 23100)
    (hl : ((1 / 4) : ℝ) ≤ b) (hr : b ≤ ((3 / 8) : ℝ)) :
    ∀ γ : ℝ, ∃ k : Fin 21, x2611_12360_modMem 1 (Set.Ico 0 (8 / 33))
      (U * ((k.val : ℝ) - 10) ^ 2 + b * ((k.val : ℝ) - 10) + γ) := by
  have H := x2611_12360_thm1_3_s1h1_aux1
    (fun k : Fin 21 => U * ((k.val : ℝ) - 10) ^ 2 + b * ((k.val : ℝ) - 10))
    ((8 : ℝ) / 33)
  by_cases hm : b ≤ ((21 / 64) : ℝ)
  · have hr := hm
    by_cases hm : b ≤ ((9 / 32) : ℝ)
    · have hr := hm
      apply H 10 0 1 [(13, 1), (9, 0), (12, 1), (8, 0), (7, 0), (6, 0), (10, 1)]
      · norm_num
      · simp
      · norm_num [List.isChain_cons, List.isChain_nil]
        all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
    · have hl : ((9 / 32) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
      by_cases hm : b ≤ ((5 / 16) : ℝ)
      · have hr := hm
        apply H 7 0 1 [(10, 1), (6, 0), (5, 0), (12, 2), (17, 4), (19, 5), (8, 1), (11, 2), (7, 1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons, List.isChain_nil]
          all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
      · have hl : ((5 / 16) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
        apply H 16 0 1 [(18, 1), (10, -2), (15, 0), (17, 1), (5, -3), (4, -3), (8, -2), (16, 1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons, List.isChain_nil]
          all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
  · have hl : ((21 / 64) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
    by_cases hm : b ≤ ((11 / 32) : ℝ)
    · have hr := hm
      apply H 4 0 1 [(3, 0), (7, 1), (15, 4), (17, 5), (1, 0), (5, 1), (8, 2), (4, 1)]
      · norm_num
      · simp
      · norm_num [List.isChain_cons, List.isChain_nil]
        all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
    · have hl : ((11 / 32) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
      by_cases hm : b ≤ ((23 / 64) : ℝ)
      · have hr := hm
        apply H 12 0 1 [(14, 1), (16, 2), (0, -3), (4, -2), (7, -1), (17, 3), (12, 1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons, List.isChain_nil]
          all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
      · have hl : ((23 / 64) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
        apply H 16 0 1 [(1, -5), (8, -3), (13, -1), (15, 0), (7, -3), (3, -4), (6, -3), (16, 1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons, List.isChain_nil]
          all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp

lemma x2611_12360_thm1_3_s1h1_aux4 (U b : ℝ)
    (hUlo : (199 : ℝ) / 23100 ≤ U) (hUhi : U ≤ (221 : ℝ) / 23100)
    (hl : ((3 / 8) : ℝ) ≤ b) (hr : b ≤ ((1 / 2) : ℝ)) :
    ∀ γ : ℝ, ∃ k : Fin 21, x2611_12360_modMem 1 (Set.Ico 0 (8 / 33))
      (U * ((k.val : ℝ) - 10) ^ 2 + b * ((k.val : ℝ) - 10) + γ) := by
  have H := x2611_12360_thm1_3_s1h1_aux1
    (fun k : Fin 21 => U * ((k.val : ℝ) - 10) ^ 2 + b * ((k.val : ℝ) - 10))
    ((8 : ℝ) / 33)
  by_cases hm : b ≤ ((27 / 64) : ℝ)
  · have hr := hm
    by_cases hm : b ≤ ((51 / 128) : ℝ)
    · have hr := hm
      by_cases hm : b ≤ ((25 / 64) : ℝ)
      · have hr := hm
        apply H 15 0 1 [(4, -4), (7, -3), (12, -1), (16, 1), (2, -4), (11, -1), (13, 0), (15, 1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons, List.isChain_nil]
          all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
      · have hl : ((25 / 64) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
        apply H 10 0 1 [(12, 1), (14, 2), (6, -1), (11, 1), (15, 3), (10, 1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons, List.isChain_nil]
          all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
    · have hl : ((51 / 128) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
      by_cases hm : b ≤ ((13 / 32) : ℝ)
      · have hr := hm
        apply H 3 0 1 [(6, 1), (11, 3), (15, 5), (1, 0), (4, 1), (14, 5), (3, 1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons, List.isChain_nil]
          all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
      · have hl : ((13 / 32) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
        by_cases hm : b ≤ ((53 / 128) : ℝ)
        · have hr := hm
          apply H 5 0 1 [(10, 2), (14, 4), (9, 2), (11, 3), (13, 4), (5, 1)]
          · norm_num
          · simp
          · norm_num [List.isChain_cons, List.isChain_nil]
            all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
        · have hl : ((53 / 128) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
          apply H 5 0 1 [(10, 2), (12, 3), (0, -1), (9, 2), (11, 3), (13, 4), (5, 1)]
          · norm_num
          · simp
          · norm_num [List.isChain_cons, List.isChain_nil]
            all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
  · have hl : ((27 / 64) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
    by_cases hm : b ≤ ((59 / 128) : ℝ)
    · have hr := hm
      by_cases hm : b ≤ ((7 / 16) : ℝ)
      · have hr := hm
        apply H 8 0 1 [(10, 1), (12, 2), (4, -1), (9, 1), (11, 2), (13, 3), (8, 1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons, List.isChain_nil]
          all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
      · have hl : ((7 / 16) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
        by_cases hm : b ≤ ((29 / 64) : ℝ)
        · have hr := hm
          apply H 8 0 1 [(10, 1), (12, 2), (7, 0), (9, 1), (6, 0), (8, 1)]
          · norm_num
          · simp
          · norm_num [List.isChain_cons, List.isChain_nil]
            all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
        · have hl : ((29 / 64) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
          apply H 0 0 1 [(3, 1), (8, 3), (10, 4), (19, 9), (7, 3), (9, 4), (11, 5), (0, 1)]
          · norm_num
          · simp
          · norm_num [List.isChain_cons, List.isChain_nil]
            all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
    · have hl : ((59 / 128) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
      by_cases hm : b ≤ ((15 / 32) : ℝ)
      · have hr := hm
        apply H 18 0 1 [(3, -7), (10, -4), (2, -7), (7, -5), (11, -3), (18, 1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons, List.isChain_nil]
          all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
      · have hl : ((15 / 32) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
        by_cases hm : b ≤ ((31 / 64) : ℝ)
        · have hr := hm
          apply H 10 0 1 [(5, -2), (7, -1), (9, 0), (18, 5), (16, 4), (19, 6), (10, 1)]
          · norm_num
          · simp
          · norm_num [List.isChain_cons, List.isChain_nil]
            all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
        · have hl : ((31 / 64) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
          apply H 5 0 1 [(7, 1), (9, 2), (4, 0), (6, 1), (10, 3), (17, 7), (5, 1)]
          · norm_num
          · simp
          · norm_num [List.isChain_cons, List.isChain_nil]
            all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp

lemma x2611_12360_thm1_3_s1h1_aux5 (U b : ℝ)
    (hUlo : (199 : ℝ) / 23100 ≤ U) (hUhi : U ≤ (221 : ℝ) / 23100)
    (hl : ((1 / 2) : ℝ) ≤ b) (hr : b ≤ ((5 / 8) : ℝ)) :
    ∀ γ : ℝ, ∃ k : Fin 21, x2611_12360_modMem 1 (Set.Ico 0 (8 / 33))
      (U * ((k.val : ℝ) - 10) ^ 2 + b * ((k.val : ℝ) - 10) + γ) := by
  have H := x2611_12360_thm1_3_s1h1_aux1
    (fun k : Fin 21 => U * ((k.val : ℝ) - 10) ^ 2 + b * ((k.val : ℝ) - 10))
    ((8 : ℝ) / 33)
  by_cases hm : b ≤ ((9 / 16) : ℝ)
  · have hr := hm
    by_cases hm : b ≤ ((17 / 32) : ℝ)
    · have hr := hm
      by_cases hm : b ≤ ((33 / 64) : ℝ)
      · have hr := hm
        apply H 4 0 1 [(6, 1), (8, 2), (3, 0), (5, 1), (9, 3), (16, 7), (4, 1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons, List.isChain_nil]
          all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
      · have hl : ((33 / 64) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
        apply H 8 0 1 [(15, 4), (3, -2), (5, -1), (7, 0), (2, -2), (4, -1), (6, 0), (8, 1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons, List.isChain_nil]
          all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
    · have hl : ((17 / 32) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
      by_cases hm : b ≤ ((69 / 128) : ℝ)
      · have hr := hm
        apply H 6 0 1 [(18, 7), (3, -1), (5, 0), (7, 1), (14, 5), (4, 0), (6, 1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons, List.isChain_nil]
          all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
      · have hl : ((69 / 128) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
        by_cases hm : b ≤ ((35 / 64) : ℝ)
        · have hr := hm
          apply H 4 0 1 [(6, 1), (1, -1), (3, 0), (5, 1), (14, 6), (17, 8), (4, 1)]
          · norm_num
          · simp
          · norm_num [List.isChain_cons, List.isChain_nil]
            all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
        · have hl : ((35 / 64) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
          apply H 12 0 1 [(15, 2), (6, -3), (13, 1), (16, 3), (3, -4), (5, -3), (14, 2), (12, 1)]
          · norm_num
          · simp
          · norm_num [List.isChain_cons, List.isChain_nil]
            all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
  · have hl : ((9 / 16) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
    by_cases hm : b ≤ ((19 / 32) : ℝ)
    · have hr := hm
      by_cases hm : b ≤ ((37 / 64) : ℝ)
      · have hr := hm
        apply H 6 0 1 [(16, 6), (20, 9), (1, -2), (3, -1), (7, 1), (12, 4), (15, 6), (2, -1), (6, 1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons, List.isChain_nil]
          all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
      · have hl : ((37 / 64) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
        by_cases hm : b ≤ ((75 / 128) : ℝ)
        · have hr := hm
          apply H 4 0 1 [(20, 10), (11, 4), (14, 6), (5, 1), (15, 7), (19, 10), (4, 1)]
          · norm_num
          · simp
          · norm_num [List.isChain_cons, List.isChain_nil]
            all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
        · have hl : ((75 / 128) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
          apply H 4 0 1 [(11, 4), (14, 6), (1, -1), (3, 0), (12, 5), (19, 10), (0, -1), (2, 0), (4, 1)]
          · norm_num
          · simp
          · norm_num [List.isChain_cons, List.isChain_nil]
            all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
    · have hl : ((19 / 32) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
      by_cases hm : b ≤ ((77 / 128) : ℝ)
      · have hr := hm
        apply H 4 0 1 [(11, 4), (14, 6), (18, 9), (12, 5), (10, 4), (13, 6), (4, 1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons, List.isChain_nil]
          all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
      · have hl : ((77 / 128) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
        by_cases hm : b ≤ ((39 / 64) : ℝ)
        · have hr := hm
          apply H 1 0 1 [(5, 2), (10, 5), (13, 7), (2, 1), (14, 8), (18, 11), (1, 1)]
          · norm_num
          · simp
          · norm_num [List.isChain_cons, List.isChain_nil]
            all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
        · have hl : ((39 / 64) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
          apply H 10 0 1 [(13, 2), (17, 5), (0, -5), (4, -3), (18, 6), (9, 0), (19, 7), (20, 8), (10, 1)]
          · norm_num
          · simp
          · norm_num [List.isChain_cons, List.isChain_nil]
            all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp

lemma x2611_12360_thm1_3_s1h1_aux6 (U b : ℝ)
    (hUlo : (199 : ℝ) / 23100 ≤ U) (hUhi : U ≤ (221 : ℝ) / 23100)
    (hl : ((5 / 8) : ℝ) ≤ b) (hr : b ≤ ((3 / 4) : ℝ)) :
    ∀ γ : ℝ, ∃ k : Fin 21, x2611_12360_modMem 1 (Set.Ico 0 (8 / 33))
      (U * ((k.val : ℝ) - 10) ^ 2 + b * ((k.val : ℝ) - 10) + γ) := by
  have H := x2611_12360_thm1_3_s1h1_aux1
    (fun k : Fin 21 => U * ((k.val : ℝ) - 10) ^ 2 + b * ((k.val : ℝ) - 10))
    ((8 : ℝ) / 33)
  by_cases hm : b ≤ ((43 / 64) : ℝ)
  · have hr := hm
    by_cases hm : b ≤ ((41 / 64) : ℝ)
    · have hr := hm
      apply H 7 0 1 [(10, 2), (17, 7), (8, 1), (18, 8), (19, 9), (20, 10), (7, 1)]
      · norm_num
      · simp
      · norm_num [List.isChain_cons, List.isChain_nil]
        all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
    · have hl : ((41 / 64) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
      by_cases hm : b ≤ ((21 / 32) : ℝ)
      · have hr := hm
        apply H 7 0 1 [(10, 2), (17, 7), (18, 8), (19, 9), (20, 10), (12, 4), (7, 1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons, List.isChain_nil]
          all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
      · have hl : ((21 / 32) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
        apply H 6 0 1 [(9, 2), (16, 7), (17, 8), (18, 9), (19, 10), (20, 11), (6, 1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons, List.isChain_nil]
          all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
  · have hl : ((43 / 64) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
    by_cases hm : b ≤ ((11 / 16) : ℝ)
    · have hr := hm
      apply H 18 0 1 [(19, 1), (20, 2), (15, -2), (16, -1), (17, 0), (18, 1)]
      · norm_num
      · simp
      · norm_num [List.isChain_cons, List.isChain_nil]
        all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
    · have hl : ((11 / 16) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
      by_cases hm : b ≤ ((23 / 32) : ℝ)
      · have hr := hm
        apply H 18 0 1 [(19, 1), (14, -3), (15, -2), (16, -1), (17, 0), (18, 1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons, List.isChain_nil]
          all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
      · have hl : ((23 / 32) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
        apply H 14 0 1 [(15, 1), (16, 2), (17, 3), (18, 4), (19, 5), (13, 0), (14, 1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons, List.isChain_nil]
          all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp

lemma x2611_12360_thm1_3_s1h1_aux7 (U b : ℝ)
    (hUlo : (199 : ℝ) / 23100 ≤ U) (hUhi : U ≤ (221 : ℝ) / 23100)
    (hl : ((3 / 4) : ℝ) ≤ b) (hr : b ≤ (1 : ℝ)) :
    ∀ γ : ℝ, ∃ k : Fin 21, x2611_12360_modMem 1 (Set.Ico 0 (8 / 33))
      (U * ((k.val : ℝ) - 10) ^ 2 + b * ((k.val : ℝ) - 10) + γ) := by
  have H := x2611_12360_thm1_3_s1h1_aux1
    (fun k : Fin 21 => U * ((k.val : ℝ) - 10) ^ 2 + b * ((k.val : ℝ) - 10))
    ((8 : ℝ) / 33)
  by_cases hm : b ≤ ((7 / 8) : ℝ)
  · have hr := hm
    by_cases hm : b ≤ ((13 / 16) : ℝ)
    · have hr := hm
      apply H 12 0 1 [(13, 1), (14, 2), (15, 3), (16, 4), (10, -1), (11, 0), (12, 1)]
      · norm_num
      · simp
      · norm_num [List.isChain_cons, List.isChain_nil]
        all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
    · have hl : ((13 / 16) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
      apply H 11 0 1 [(12, 1), (13, 2), (14, 3), (7, -3), (8, -2), (9, -1), (10, 0), (11, 1)]
      · norm_num
      · simp
      · norm_num [List.isChain_cons, List.isChain_nil]
        all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
  · have hl : ((7 / 8) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
    by_cases hm : b ≤ ((15 / 16) : ℝ)
    · have hr := hm
      apply H 7 0 1 [(8, 1), (9, 2), (10, 3), (12, 5), (4, -2), (5, -1), (6, 0), (7, 1)]
      · norm_num
      · simp
      · norm_num [List.isChain_cons, List.isChain_nil]
        all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
    · have hl : ((15 / 16) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
      by_cases hm : b ≤ ((31 / 32) : ℝ)
      · have hr := hm
        apply H 2 0 1 [(3, 1), (4, 2), (5, 3), (6, 4), (7, 5), (9, 7), (2, 1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons, List.isChain_nil]
          all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp
      · have hl : ((31 / 32) : ℝ) ≤ b := le_of_lt (lt_of_not_ge hm)
        apply H 0 0 1 [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (0, 1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons, List.isChain_nil]
          all_goals (repeat' constructor) <;> first | linarith only [hUlo, hUhi, hl, hr] | simp

lemma x2611_12360_thm1_3_s1h1_aux8 (U b : ℝ)
    (hUlo : (199 : ℝ) / 23100 ≤ U) (hUhi : U ≤ (221 : ℝ) / 23100)
    (hl : 0 ≤ b) (hr : b ≤ 1) :
    ∀ γ : ℝ, ∃ k : Fin 21, x2611_12360_modMem 1 (Set.Ico 0 (8 / 33))
      (U * ((k.val : ℝ) - 10) ^ 2 + b * ((k.val : ℝ) - 10) + γ) := by
  by_cases h1 : b ≤ 1 / 4
  · exact x2611_12360_thm1_3_s1h1_aux2 U b hUlo hUhi hl h1
  have h1' : (1 : ℝ) / 4 ≤ b := le_of_not_ge h1
  by_cases h2 : b ≤ 3 / 8
  · exact x2611_12360_thm1_3_s1h1_aux3 U b hUlo hUhi h1' h2
  have h2' : (3 : ℝ) / 8 ≤ b := le_of_not_ge h2
  by_cases h3 : b ≤ 1 / 2
  · exact x2611_12360_thm1_3_s1h1_aux4 U b hUlo hUhi h2' h3
  have h3' : (1 : ℝ) / 2 ≤ b := le_of_not_ge h3
  by_cases h4 : b ≤ 5 / 8
  · exact x2611_12360_thm1_3_s1h1_aux5 U b hUlo hUhi h3' h4
  have h4' : (5 : ℝ) / 8 ≤ b := le_of_not_ge h4
  by_cases h5 : b ≤ 3 / 4
  · exact x2611_12360_thm1_3_s1h1_aux6 U b hUlo hUhi h4' h5
  have h5' : (3 : ℝ) / 4 ≤ b := le_of_not_ge h5
  exact x2611_12360_thm1_3_s1h1_aux7 U b hUlo hUhi h5' hr

theorem x2611_12360_thm1_3_s1h1 : ∀ (U : ℝ), 199 / 23100 ≤ U → U ≤ 221 / 23100 → ∀ (β γ : ℝ), ∃ k ∈ Finset.range 21, x2611_12360_modMem 1 (Set.Ico 0 (8 / 33)) (U * (↑k : ℝ) ^ 2 + β * (↑k : ℝ) + γ) := by
  intro U hUlo hUhi β γ
  let n : ℤ := ⌊β + 20 * U⌋
  let b : ℝ := β + 20 * U - (n : ℝ)
  have hb0 : 0 ≤ b := by
    have hh := Int.floor_le (β + 20 * U)
    change (n : ℝ) ≤ _ at hh
    dsimp [b]
    linarith
  have hb1 : b ≤ 1 := by
    have hh := Int.lt_floor_add_one (β + 20 * U)
    change _ < (n : ℝ) + 1 at hh
    dsimp [b]
    linarith
  obtain ⟨k, x, hx, m, hm⟩ := x2611_12360_thm1_3_s1h1_aux8 U b hUlo hUhi hb0 hb1
    (γ + 10 * β + 100 * U)
  refine ⟨k.val, Finset.mem_range.mpr k.isLt, x, hx,
    m + n * ((k.val : ℤ) - 10), ?_⟩
  push_cast
  dsimp [b] at hm
  nlinarith only [hm]
end

-- forge:entry x2611_16458_lem2_2 kind=proved origin=paper
section
/- Lemma 2.2 -/
lemma x2611_16458_lem2_2_aux1 {V A : Type*} (G : SimpleGraph V)
    (f : V → A) (hf : ∀ v w, G.Adj v w → f v = f w)
    {u v : V} (h : G.Reachable u v) : f u = f v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons h p ih => exact (hf _ _ h).trans ih

lemma x2611_16458_lem2_2_aux2 {V : Type*} [Finite V] (G : SimpleGraph V) :
    Nat.card {f : V → Bool // ∀ v w, G.Adj v w → f v = f w} =
      2 ^ Nat.card G.ConnectedComponent := by
  classical
  let F : (G.ConnectedComponent → Bool) →
      {f : V → Bool // ∀ v w, G.Adj v w → f v = f w} :=
    fun f => ⟨fun v => f (G.connectedComponentMk v),
      fun v w h => congrArg f (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h)⟩
  have hi : Function.Injective F := by
    intro f g h
    funext c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h v => exact congrArg (fun k => k.val v) h
  have hs : Function.Surjective F := by
    intro f
    refine ⟨Quot.lift f.val (fun v w h => x2611_16458_lem2_2_aux1 G f.val f.prop h), ?_⟩
    rfl
  have hc := Nat.card_congr (Equiv.ofBijective F ⟨hi, hs⟩)
  simpa [Nat.card_fun] using hc.symm

lemma x2611_16458_lem2_2_aux3 {V : Type*} [Finite V] (P N : SimpleGraph V) :
    Nat.card {f : V → Bool //
      (∀ v w, P.Adj v w → f v = f w) ∧
      (∀ v w, N.Adj v w → f v ≠ f w)} =
      @ite ℕ (x2611_16458_balanced P N) (Classical.propDecidable _)
        (2 ^ Nat.card (P ⊔ N).ConnectedComponent) 0 := by
  classical
  by_cases hb : x2611_16458_balanced P N
  · rw [if_pos hb]
    obtain ⟨ε, hεP, hεN⟩ := hb
    let F : {f : V → Bool //
        (∀ v w, P.Adj v w → f v = f w) ∧
        (∀ v w, N.Adj v w → f v ≠ f w)} →
        {f : V → Bool // ∀ v w, (P ⊔ N).Adj v w → f v = f w} :=
      fun f => ⟨fun v => Bool.xor (ε v) (f.val v), by
        intro v w h
        rcases h with h | h
        · dsimp only
          rw [hεP _ _ h, f.prop.1 _ _ h]
        · have h₁ := hεN _ _ h
          have h₂ := f.prop.2 _ _ h
          cases hεv : ε v <;> cases hεw : ε w <;>
            cases hfv : f.val v <;> cases hfw : f.val w <;> simp_all⟩
    have hi : Function.Injective F := by
      intro f g h
      apply Subtype.ext
      funext v
      have hv := congrArg (fun k => k.val v) h
      change Bool.xor (ε v) (f.val v) = Bool.xor (ε v) (g.val v) at hv
      cases ε v <;> simpa using hv
    have hs : Function.Surjective F := by
      intro f
      refine ⟨⟨fun v => Bool.xor (ε v) (f.val v), ?_⟩, ?_⟩
      · constructor
        · intro v w h
          have hh := f.prop v w (Or.inl h)
          dsimp only
          rw [hεP _ _ h, hh]
        · intro v w h
          have hh := f.prop v w (Or.inr h)
          have he := hεN _ _ h
          cases hev : ε v <;> cases hew : ε w <;>
            cases hfv : f.val v <;> cases hfw : f.val w <;> simp_all
      · apply Subtype.ext
        funext v
        change Bool.xor (ε v) (Bool.xor (ε v) (f.val v)) = f.val v
        cases ε v <;> cases f.val v <;> rfl
    exact (Nat.card_congr (Equiv.ofBijective F ⟨hi, hs⟩)).trans
      (x2611_16458_lem2_2_aux2 (P ⊔ N))
  · rw [if_neg hb]
    haveI : IsEmpty {f : V → Bool //
        (∀ v w, P.Adj v w → f v = f w) ∧
        (∀ v w, N.Adj v w → f v ≠ f w)} :=
      ⟨fun f => hb ⟨f.val, f.prop⟩⟩
    exact Nat.card_of_isEmpty

lemma x2611_16458_lem2_2_aux4 {V : Type*} (R : V → V → Prop)
    (hR : ∀ v w, R v w → R w v) (v w : V) :
    (∀ a b, s(a, b) = s(v, w) → R a b) ↔ R v w := by
  constructor
  · exact fun h => h v w rfl
  · intro h a b he
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    · exact hR _ _ h

lemma x2611_16458_lem2_2_aux5 {V : Type*} [Finite V] (P N : SimpleGraph V) :
    (x2611_16458_zeroFree P N).eval 2 =
      (Nat.card {f : V → Bool //
        (∀ v w, P.Adj v w → f v ≠ f w) ∧
        (∀ v w, N.Adj v w → f v = f w)} : ℤ) := by
  classical
  letI := Fintype.ofFinite V
  let E := P.edgeFinset.disjSum N.edgeFinset
  let S : Sym2 V ⊕ Sym2 V → Finset (V → Bool) := fun e =>
    Finset.univ.filter (fun f => match e with
      | Sum.inl e => ∀ v w, s(v, w) = e → f v = f w
      | Sum.inr e => ∀ v w, s(v, w) = e → f v ≠ f w)
  have hSP (f : V → Bool) (v w : V) :
      f ∈ S (Sum.inl s(v, w)) ↔ f v = f w := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact x2611_16458_lem2_2_aux4 _ (fun _ _ => Eq.symm) v w
  have hSN (f : V → Bool) (v w : V) :
      f ∈ S (Sum.inr s(v, w)) ↔ f v ≠ f w := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact x2611_16458_lem2_2_aux4 _ (fun _ _ => Ne.symm) v w
  have hcount (F : Finset (Sym2 V ⊕ Sym2 V)) (hF : F ⊆ E) :
      (F.inf S).card =
        if x2611_16458_balanced
            (SimpleGraph.fromEdgeSet {e | Sum.inl e ∈ F})
            (SimpleGraph.fromEdgeSet {e | Sum.inr e ∈ F}) then
          2 ^ Nat.card ((SimpleGraph.fromEdgeSet {e | Sum.inl e ∈ F} : SimpleGraph V) ⊔
            SimpleGraph.fromEdgeSet {e | Sum.inr e ∈ F}).ConnectedComponent else 0 := by
    let P' : SimpleGraph V := SimpleGraph.fromEdgeSet {e | Sum.inl e ∈ F}
    let N' : SimpleGraph V := SimpleGraph.fromEdgeSet {e | Sum.inr e ∈ F}
    have he : F.inf S = Finset.univ.filter (fun f : V → Bool =>
        (∀ v w, P'.Adj v w → f v = f w) ∧
        (∀ v w, N'.Adj v w → f v ≠ f w)) := by
      ext f
      simp only [Finset.mem_inf, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        constructor
        · intro v w hvw
          exact (hSP f v w).mp (h _ hvw.1)
        · intro v w hvw
          exact (hSN f v w).mp (h _ hvw.1)
      · intro h e he
        cases e with
        | inl e =>
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          intro v w hvw
          have hm : Sum.inl s(v, w) ∈ F := hvw ▸ he
          have hp : P.Adj v w := by
            simpa only [E, Finset.inl_mem_disjSum, SimpleGraph.mem_edgeFinset,
              SimpleGraph.mem_edgeSet] using hF hm
          exact h.1 _ _ ⟨hm, hp.ne⟩
        | inr e =>
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          intro v w hvw
          have hm : Sum.inr s(v, w) ∈ F := hvw ▸ he
          have hn : N.Adj v w := by
            simpa only [E, Finset.inr_mem_disjSum, SimpleGraph.mem_edgeFinset,
              SimpleGraph.mem_edgeSet] using hF hm
          exact h.2 _ _ ⟨hm, hn.ne⟩
    rw [he]
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using
      x2611_16458_lem2_2_aux3 P' N'
  have hgood : (E.inf fun e => (S e)ᶜ) = Finset.univ.filter (fun f : V → Bool =>
      (∀ v w, P.Adj v w → f v ≠ f w) ∧
      (∀ v w, N.Adj v w → f v = f w)) := by
    ext f
    simp only [Finset.mem_inf, Finset.mem_compl, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro h
      constructor
      · intro v w hvw
        exact fun heq => h (Sum.inl s(v, w))
          (by simpa [E] using hvw) ((hSP f v w).mpr heq)
      · intro v w hvw
        exact not_not.mp (fun hne => h (Sum.inr s(v, w))
          (by simpa [E] using hvw) ((hSN f v w).mpr hne))
    · intro h e he
      cases e with
      | inl e =>
        induction e using Sym2.ind with
        | h v w =>
          have hp : P.Adj v w := by simpa [E] using he
          exact fun hh => h.1 v w hp ((hSP f v w).mp hh)
      | inr e =>
        induction e using Sym2.ind with
        | h v w =>
          have hn : N.Adj v w := by simpa [E] using he
          exact fun hh => (hSN f v w).mp hh (h.2 v w hn)
  have hie := Finset.inclusion_exclusion_card_inf_compl E S
  rw [hgood] at hie
  have hpoly : (x2611_16458_zeroFree P N).eval 2 =
      ∑ F ∈ E.powerset, (-1 : ℤ) ^ F.card * ((F.inf S).card : ℤ) := by
    simp only [x2611_16458_zeroFree, Polynomial.eval_finset_sum]
    apply Finset.sum_congr rfl
    intro F hF
    rw [hcount F (Finset.mem_powerset.mp hF)]
    split_ifs <;> simp_all
  rw [hpoly, ← hie]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem x2611_16458_lem2_2 (V : Type*) [Finite V] (P N : SimpleGraph V)
    (hconn : (P ⊔ N).Connected) :
    (x2611_16458_zeroFree P N).eval 2 = 0 ∨
    (x2611_16458_zeroFree P N).eval 2 = 2 := by
  classical
  have hcn : (N ⊔ P).Connected := by simpa only [sup_comm] using hconn
  letI : Nonempty V := hconn.nonempty
  letI : Subsingleton (N ⊔ P).ConnectedComponent :=
    hcn.preconnected.subsingleton_connectedComponent
  have hcard : Nat.card (N ⊔ P).ConnectedComponent = 1 := Nat.card_unique
  rw [x2611_16458_lem2_2_aux5]
  have hc := x2611_16458_lem2_2_aux3 N P
  simp only [and_comm, hcard, pow_one] at hc
  rw [hc]
  by_cases hb : x2611_16458_balanced N P
  · exact Or.inr (by simp [hb])
  · exact Or.inl (by simp [hb])
end

-- forge:entry x2611_16899_thm1_eq2_s1h1_s1h1 kind=proved origin=decomposition
section
/- x2611_16899_thm1_eq2_s1h1 的证明骨架中第 1 个空洞 -/
open scoped BigOperators MonomialOrder
open MvPolynomial

lemma x2611_16899_thm1_eq2_s1h1_s1h1_aux1
    {σ R : Type*} [CommSemiring R] (τ : R) (i j : σ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 2),
      C (τ ^ k) * X i ^ k * X j ^ (n + 1 - k) : MvPolynomial σ R) =
      X j ^ (n + 1) + (C τ * X i) *
        ∑ k ∈ Finset.range (n + 1), C (τ ^ k) * X i ^ k * X j ^ (n - k) := by
  rw [Finset.sum_range_succ']
  simp only [pow_zero, map_one, mul_one, one_mul, Nat.sub_zero,
    Nat.add_sub_add_right]
  rw [add_comm, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  simp only [pow_succ, map_mul]
  ring

lemma x2611_16899_thm1_eq2_s1h1_s1h1_aux2
    {σ R : Type*} [CommRing R] [IsDomain R] (m : MonomialOrder σ)
    (τ : R) (i j : σ) (hij : Finsupp.single i 1 ≺[m] Finsupp.single j 1) (n : ℕ) :
    m.degree (∑ k ∈ Finset.range (n + 1),
      C (τ ^ k) * X i ^ k * X j ^ (n - k) : MvPolynomial σ R) =
      n • Finsupp.single j 1 ∧
    m.leadingCoeff (∑ k ∈ Finset.range (n + 1),
      C (τ ^ k) * X i ^ k * X j ^ (n - k) : MvPolynomial σ R) = 1 := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 by omega,
      x2611_16899_thm1_eq2_s1h1_s1h1_aux1]
    have hlt : m.degree ((C τ * X i) *
        ∑ k ∈ Finset.range (n + 1), C (τ ^ k) * X i ^ k * X j ^ (n - k))
        ≺[m] m.degree (X j ^ (n + 1) : MvPolynomial σ R) := by
      apply lt_of_le_of_lt m.degree_mul_le
      rw [map_add, ih.1]
      have hb := m.degree_mul_le (f := C τ) (g := X i)
      simp only [m.degree_C, m.degree_X, zero_add] at hb
      apply lt_of_le_of_lt (add_le_add hb (le_refl _))
      simp only [m.degree_X, m.degree_pow]
      simpa [add_smul, add_comm, add_left_comm, add_assoc] using
        add_lt_add_of_lt_of_le hij (le_refl (m.toSyn (n • Finsupp.single j 1)))
    constructor
    · rw [m.degree_add_of_lt hlt, m.degree_pow, m.degree_X]
    · rw [m.leadingCoeff_add_of_lt hlt, m.leadingCoeff_pow, m.leadingCoeff_X, one_pow]

lemma x2611_16899_thm1_eq2_s1h1_s1h1_aux3
    {σ R : Type*} [CommRing R] [IsDomain R] (m : MonomialOrder σ)
    (τ : R) (i j : σ) (hij : Finsupp.single i 1 ≺[m] Finsupp.single j 1) (n : ℕ) :
    m.degree ((X j - X i) * ∑ k ∈ Finset.range (n + 1),
      C (τ ^ k) * X i ^ k * X j ^ (n - k) : MvPolynomial σ R) =
      (n + 1) • Finsupp.single j 1 ∧
    m.leadingCoeff ((X j - X i) * ∑ k ∈ Finset.range (n + 1),
      C (τ ^ k) * X i ^ k * X j ^ (n - k) : MvPolynomial σ R) = 1 := by
  have hlt : m.degree (X i : MvPolynomial σ R) ≺[m]
      m.degree (X j : MvPolynomial σ R) := by simpa only [m.degree_X] using hij
  have hs := x2611_16899_thm1_eq2_s1h1_s1h1_aux2 m τ i j hij n
  have hl : m.leadingCoeff (X j - X i : MvPolynomial σ R) = 1 := by
    rw [m.leadingCoeff_sub_of_lt hlt, m.leadingCoeff_X]
  have hne : m.leadingCoeff (X j - X i : MvPolynomial σ R) *
      m.leadingCoeff (∑ k ∈ Finset.range (n + 1),
        C (τ ^ k) * X i ^ k * X j ^ (n - k)) ≠ 0 := by
    rw [hl, hs.2, one_mul]
    exact one_ne_zero
  constructor
  · rw [m.degree_mul_of_mul_leadingCoeff_ne_zero hne,
      m.degree_sub_of_lt hlt, m.degree_X, hs.1]
    simp [add_smul, add_comm]
  · rw [m.leadingCoeff_mul, hl, hs.2, one_mul]

lemma x2611_16899_thm1_eq2_s1h1_s1h1_aux4 (n a : ℕ) :
    (∑ ij : Fin n × Fin n,
      if ij.1 < ij.2 then a • Finsupp.single ij.2 1 else 0) =
      (Finsupp.equivFunOnFinite.symm : (Fin n → ℕ) → Fin n →₀ ℕ)
        (fun i => a * (i : ℕ)) := by
  classical
  ext j
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  rw [Fintype.sum_prod_type]
  simp [Finsupp.single_apply, Finset.sum_ite, Finset.filter_gt_eq_Iio, mul_comm]

theorem x2611_16899_thm1_eq2_s1h1_s1h1 : ∀ (n : ℕ) (τ : RatFunc ℚ), MvPolynomial.coeff ((Finsupp.equivFunOnFinite.symm : (Fin n → ℕ) → Fin n →₀ ℕ) fun (i : Fin n) => (n + 1) * (↑i : ℕ)) (∏ ij : Fin n × Fin n, if ij.1 < ij.2 then (MvPolynomial.X ij.2 - MvPolynomial.X ij.1) * ∑ k ∈ Finset.range (n + 1), (MvPolynomial.C : RatFunc ℚ → MvPolynomial (Fin n) (RatFunc ℚ)) (τ ^ k) * MvPolynomial.X ij.1 ^ k * MvPolynomial.X ij.2 ^ (n - k) else 1) = 1 := by
  classical
  intro n τ
  let m : MonomialOrder (Fin n) :=
    (MonomialOrder.lex : MonomialOrder (OrderDual (Fin n)))
  have hm (i j : Fin n) (hij : i < j) :
      Finsupp.single i 1 ≺[m] Finsupp.single j 1 := by
    change ∃ k : Fin n, (∀ l : Fin n, k < l →
      (Finsupp.single i 1 : Fin n →₀ ℕ) l = Finsupp.single j 1 l) ∧
      (Finsupp.single i 1 : Fin n →₀ ℕ) k < Finsupp.single j 1 k
    refine ⟨j, ?_, ?_⟩
    · intro l hl
      simp [ne_of_lt (lt_trans hij hl), ne_of_lt hl]
    · simp [ne_of_lt hij]
  let P : Fin n × Fin n → MvPolynomial (Fin n) (RatFunc ℚ) := fun ij =>
    if ij.1 < ij.2 then (X ij.2 - X ij.1) *
      ∑ k ∈ Finset.range (n + 1), C (τ ^ k) * X ij.1 ^ k * X ij.2 ^ (n - k)
    else 1
  have hd (ij : Fin n × Fin n) :
      m.degree (P ij) = if ij.1 < ij.2 then (n + 1) • Finsupp.single ij.2 1 else 0 := by
    dsimp [P]
    split_ifs with hij
    · exact (x2611_16899_thm1_eq2_s1h1_s1h1_aux3 m τ ij.1 ij.2 (hm _ _ hij) n).1
    · exact m.degree_one
  have hl (ij : Fin n × Fin n) : m.leadingCoeff (P ij) = 1 := by
    dsimp [P]
    split_ifs with hij
    · exact (x2611_16899_thm1_eq2_s1h1_s1h1_aux3 m τ ij.1 ij.2 (hm _ _ hij) n).2
    · exact m.leadingCoeff_one
  have hs : (∑ ij : Fin n × Fin n, m.degree (P ij)) =
      (Finsupp.equivFunOnFinite.symm : (Fin n → ℕ) → Fin n →₀ ℕ)
        (fun i => (n + 1) * (i : ℕ)) := by
    simp_rw [hd]
    exact x2611_16899_thm1_eq2_s1h1_s1h1_aux4 n (n + 1)
  have h := m.coeff_prod_sum_degree P Finset.univ
  rw [hs] at h
  simpa only [hl, Finset.prod_const_one] using h
end

-- forge:entry x2611_15505_formal_counts kind=proved origin=paper
section
/- Section 2 table (formal words, degrees 1 through 6) -/
lemma x2611_15505_formal_counts_aux1 (n L : ℕ) :
    {w : List ℕ | w.length = L ∧ ∀ k ∈ w, k < n}.Finite := by
  induction L with
  | zero =>
      have : {w : List ℕ | w.length = 0 ∧ ∀ k ∈ w, k < n} = {[]} := by
        ext w
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, List.length_eq_zero_iff]
        constructor
        · exact And.left
        · rintro rfl; simp
      rw [this]
      exact Set.finite_singleton _
  | succ L ih =>
      have heq : {w : List ℕ | w.length = L + 1 ∧ ∀ k ∈ w, k < n} =
          ⋃ i : Fin n, List.cons i.val '' {w : List ℕ | w.length = L ∧ ∀ k ∈ w, k < n} := by
        ext w
        cases w with
        | nil => simp
        | cons a w =>
            simp only [Set.mem_setOf_eq, List.length_cons, Nat.add_right_cancel_iff,
              List.mem_cons, forall_eq_or_imp, Set.mem_iUnion, Set.mem_image, List.cons.injEq]
            constructor
            · rintro ⟨hl, ha, hw⟩
              exact ⟨⟨a, ha⟩, w, ⟨hl, hw⟩, rfl, rfl⟩
            · rintro ⟨i, v, ⟨hl, hv⟩, hia, rfl⟩
              exact ⟨hl, hia ▸ i.isLt, hv⟩
      rw [heq]
      exact Set.finite_iUnion fun i => ih.image _

lemma x2611_15505_formal_counts_aux2 (n L : ℕ) (P : List ℕ → Prop) :
    {w : List ℕ | w.length = L + 1 ∧ (∀ k ∈ w, k < n) ∧ P w}.ncard =
      ∑ i : Fin n, {w : List ℕ | w.length = L ∧ (∀ k ∈ w, k < n) ∧ P (i.val :: w)}.ncard := by
  classical
  let S (i : Fin n) : Set (List ℕ) :=
    {w | w.length = L ∧ (∀ k ∈ w, k < n) ∧ P (i.val :: w)}
  have hf (i : Fin n) : (S i).Finite :=
    (x2611_15505_formal_counts_aux1 n L).subset (fun _ h => ⟨h.1, h.2.1⟩)
  have heq : {w : List ℕ | w.length = L + 1 ∧ (∀ k ∈ w, k < n) ∧ P w} =
      ⋃ i : Fin n, List.cons i.val '' S i := by
    ext w
    cases w with
    | nil => simp
    | cons a w =>
      simp only [Set.mem_setOf_eq, List.length_cons, Nat.add_right_cancel_iff,
        List.mem_cons, forall_eq_or_imp, Set.mem_iUnion, Set.mem_image, List.cons.injEq]
      constructor
      · rintro ⟨hl, ⟨ha, hw⟩, hp⟩
        exact ⟨⟨a, ha⟩, w, ⟨hl, hw, hp⟩, rfl, rfl⟩
      · rintro ⟨i, v, ⟨hl, hv, hp⟩, hia, rfl⟩
        subst a
        exact ⟨hl, ⟨i.isLt, hv⟩, hp⟩
  rw [heq, Set.ncard_iUnion_of_finite (fun i => (hf i).image _)]
  · rw [finsum_eq_sum_of_fintype]
    apply Finset.sum_congr rfl
    intro i _
    exact Set.ncard_image_of_injective _ List.cons_injective
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨w, hw, rfl⟩ ⟨v, hv, hvw⟩
    exact hij (Fin.ext (List.cons.inj hvw).1.symm)

lemma x2611_15505_formal_counts_aux3 (n L : ℕ) (t : Fin n → List ℕ) :
    {w : List ℕ | w.length = L + 1 ∧ (∀ k ∈ w, k < n) ∧
      ∀ j : Fin n, w.filter (fun k => k = j.val ∨ k = j.val + 1) = t j}.ncard =
    ∑ i : Fin n, {w : List ℕ | w.length = L ∧ (∀ k ∈ w, k < n) ∧
      ∀ j : Fin n, (if i.val = j.val ∨ i.val = j.val + 1 then
        i.val :: w.filter (fun k => k = j.val ∨ k = j.val + 1)
        else w.filter (fun k => k = j.val ∨ k = j.val + 1)) = t j}.ncard := by
  simpa only [List.filter_cons, Bool.or_eq_true, decide_eq_true_eq] using
    x2611_15505_formal_counts_aux2 n L
      (fun w => ∀ j : Fin n, w.filter (fun k => k = j.val ∨ k = j.val + 1) = t j)

lemma x2611_15505_formal_counts_aux4 (n : ℕ) (w : List ℕ) :
    x2611_15505_formal_word n w ↔
    w.length = n * (n + 1) / 2 ∧ (∀ k ∈ w, k < n) ∧
      ∀ j : Fin n, w.filter (fun k => k = j.val ∨ k = j.val + 1) =
        (List.replicate (n - j.val - 1) [j.val, j.val + 1]).flatten ++ [j.val] := by
  constructor
  · rintro ⟨⟨hl, hb, hc⟩, hf⟩
    refine ⟨hl, hb, ?_⟩
    intro j
    by_cases hj : j.val + 1 < n
    · exact hf j.val hj
    · have hlast : j.val + 1 = n := by omega
      have hfilter : w.filter (fun k => k = j.val ∨ k = j.val + 1) =
          w.filter (fun k => k = j.val) := by
        apply List.filter_congr
        intro k hk
        have hklt := hb k hk
        have hne : k ≠ j.val + 1 := by omega
        simp [hne]
      rw [hfilter, List.filter_eq, hc j.val j.isLt]
      have h1 : n - j.val = 1 := by omega
      have h0 : n - j.val - 1 = 0 := by omega
      simp [h1, h0]
  · rintro ⟨hl, hb, hf⟩
    refine ⟨⟨hl, hb, ?_⟩, ?_⟩
    · intro j hj
      have he := congrArg (List.count j) (hf ⟨j, hj⟩)
      have hne : j + 1 ≠ j := by omega
      simp [List.count_flatten, List.map_replicate, List.sum_replicate, hne] at he
      omega
    · intro j hj
      exact hf ⟨j, by omega⟩

lemma x2611_15505_formal_counts_aux5 (P : List ℕ → Prop) (h : P []) :
    {w : List ℕ | w.length = 0 ∧ P w}.ncard = 1 := by
  have heq : {w : List ℕ | w.length = 0 ∧ P w} = {[]} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, List.length_eq_zero_iff]
    constructor
    · exact And.left
    · rintro rfl; exact ⟨rfl, h⟩
  rw [heq]
  exact Set.ncard_singleton _

theorem x2611_15505_formal_counts : {w : List ℕ | x2611_15505_formal_word 1 w}.ncard = 1 ∧
  {w : List ℕ | x2611_15505_formal_word 2 w}.ncard = 1 ∧
  {w : List ℕ | x2611_15505_formal_word 3 w}.ncard = 2 ∧
  {w : List ℕ | x2611_15505_formal_word 4 w}.ncard = 12 ∧
  {w : List ℕ | x2611_15505_formal_word 5 w}.ncard = 286 ∧
  {w : List ℕ | x2611_15505_formal_word 6 w}.ncard = 33592 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have h1_0 : ({w : List ℕ | w.length = 0 ∧ (∀ k ∈ w, k < 1) ∧ w.filter (fun k => k = 0 ∨ k = 1) = []}).ncard = 1 := by
      apply x2611_15505_formal_counts_aux5
      simp
    have h1_1 : ({w : List ℕ | w.length = 1 ∧ (∀ k ∈ w, k < 1) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0]}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 1 0]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h1_0]
    have heq : {w : List ℕ | x2611_15505_formal_word 1 w} = {w : List ℕ | w.length = 1 ∧ (∀ k ∈ w, k < 1) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0]} := by
      ext w
      simp only [Set.mem_setOf_eq]
      rw [x2611_15505_formal_counts_aux4]
      norm_num [Fin.forall_fin_succ, List.replicate_succ]
    rw [heq]
    exact h1_1
  ·
    have h2_0 : ({w : List ℕ | w.length = 0 ∧ (∀ k ∈ w, k < 2) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [] ∧ w.filter (fun k => k = 1 ∨ k = 2) = []}).ncard = 1 := by
      apply x2611_15505_formal_counts_aux5
      simp
    have h2_1 : ({w : List ℕ | w.length = 1 ∧ (∀ k ∈ w, k < 2) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = []}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 2 0]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h2_0]
    have h2_2 : ({w : List ℕ | w.length = 2 ∧ (∀ k ∈ w, k < 2) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1]}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 2 1]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h2_1]
    have h2_3 : ({w : List ℕ | w.length = 3 ∧ (∀ k ∈ w, k < 2) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1]}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 2 2]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h2_2]
    have heq : {w : List ℕ | x2611_15505_formal_word 2 w} = {w : List ℕ | w.length = 3 ∧ (∀ k ∈ w, k < 2) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1]} := by
      ext w
      simp only [Set.mem_setOf_eq]
      rw [x2611_15505_formal_counts_aux4]
      norm_num [Fin.forall_fin_succ, List.replicate_succ]
    rw [heq]
    exact h2_3
  ·
    have h3_0 : ({w : List ℕ | w.length = 0 ∧ (∀ k ∈ w, k < 3) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [] ∧ w.filter (fun k => k = 2 ∨ k = 3) = []}).ncard = 1 := by
      apply x2611_15505_formal_counts_aux5
      simp
    have h3_1 : ({w : List ℕ | w.length = 1 ∧ (∀ k ∈ w, k < 3) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [] ∧ w.filter (fun k => k = 2 ∨ k = 3) = []}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 3 0]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h3_0]
    have h3_2 : ({w : List ℕ | w.length = 2 ∧ (∀ k ∈ w, k < 3) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = []}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 3 1]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h3_1]
    have h3_3 : ({w : List ℕ | w.length = 3 ∧ (∀ k ∈ w, k < 3) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2]}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 3 2]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h3_2]
    have h3_4 : ({w : List ℕ | w.length = 3 ∧ (∀ k ∈ w, k < 3) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = []}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 3 2]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h3_2]
    have h3_5 : ({w : List ℕ | w.length = 4 ∧ (∀ k ∈ w, k < 3) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2]}).ncard = 2 := by
      rw [x2611_15505_formal_counts_aux2 3 3]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h3_3, h3_4]
    have h3_6 : ({w : List ℕ | w.length = 5 ∧ (∀ k ∈ w, k < 3) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2]}).ncard = 2 := by
      rw [x2611_15505_formal_counts_aux2 3 4]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h3_5]
    have h3_7 : ({w : List ℕ | w.length = 6 ∧ (∀ k ∈ w, k < 3) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2]}).ncard = 2 := by
      rw [x2611_15505_formal_counts_aux2 3 5]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h3_6]
    have heq : {w : List ℕ | x2611_15505_formal_word 3 w} = {w : List ℕ | w.length = 6 ∧ (∀ k ∈ w, k < 3) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2]} := by
      ext w
      simp only [Set.mem_setOf_eq]
      rw [x2611_15505_formal_counts_aux4]
      norm_num [Fin.forall_fin_succ, List.replicate_succ]
    rw [heq]
    exact h3_7
  ·
    have h4_0 : ({w : List ℕ | w.length = 0 ∧ (∀ k ∈ w, k < 4) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [] ∧ w.filter (fun k => k = 3 ∨ k = 4) = []}).ncard = 1 := by
      apply x2611_15505_formal_counts_aux5
      simp
    have h4_1 : ({w : List ℕ | w.length = 1 ∧ (∀ k ∈ w, k < 4) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [] ∧ w.filter (fun k => k = 3 ∨ k = 4) = []}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 4 0]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h4_0]
    have h4_2 : ({w : List ℕ | w.length = 2 ∧ (∀ k ∈ w, k < 4) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [] ∧ w.filter (fun k => k = 3 ∨ k = 4) = []}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 4 1]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h4_1]
    have h4_3 : ({w : List ℕ | w.length = 3 ∧ (∀ k ∈ w, k < 4) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = []}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 4 2]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h4_2]
    have h4_4 : ({w : List ℕ | w.length = 3 ∧ (∀ k ∈ w, k < 4) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [] ∧ w.filter (fun k => k = 3 ∨ k = 4) = []}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 4 2]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h4_2]
    have h4_5 : ({w : List ℕ | w.length = 4 ∧ (∀ k ∈ w, k < 4) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3]}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 4 3]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h4_3]
    have h4_6 : ({w : List ℕ | w.length = 4 ∧ (∀ k ∈ w, k < 4) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = []}).ncard = 2 := by
      rw [x2611_15505_formal_counts_aux2 4 3]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h4_3, h4_4]
    have h4_7 : ({w : List ℕ | w.length = 5 ∧ (∀ k ∈ w, k < 4) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3]}).ncard = 3 := by
      rw [x2611_15505_formal_counts_aux2 4 4]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h4_5, h4_6]
    have h4_8 : ({w : List ℕ | w.length = 5 ∧ (∀ k ∈ w, k < 4) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = []}).ncard = 2 := by
      rw [x2611_15505_formal_counts_aux2 4 4]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h4_6]
    have h4_9 : ({w : List ℕ | w.length = 6 ∧ (∀ k ∈ w, k < 4) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3]}).ncard = 5 := by
      rw [x2611_15505_formal_counts_aux2 4 5]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h4_7, h4_8]
    have h4_10 : ({w : List ℕ | w.length = 6 ∧ (∀ k ∈ w, k < 4) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = []}).ncard = 2 := by
      rw [x2611_15505_formal_counts_aux2 4 5]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h4_8]
    have h4_11 : ({w : List ℕ | w.length = 7 ∧ (∀ k ∈ w, k < 4) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3]}).ncard = 5 := by
      rw [x2611_15505_formal_counts_aux2 4 6]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h4_9]
    have h4_12 : ({w : List ℕ | w.length = 7 ∧ (∀ k ∈ w, k < 4) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3]}).ncard = 7 := by
      rw [x2611_15505_formal_counts_aux2 4 6]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h4_9, h4_10]
    have h4_13 : ({w : List ℕ | w.length = 8 ∧ (∀ k ∈ w, k < 4) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3]}).ncard = 12 := by
      rw [x2611_15505_formal_counts_aux2 4 7]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h4_11, h4_12]
    have h4_14 : ({w : List ℕ | w.length = 9 ∧ (∀ k ∈ w, k < 4) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3]}).ncard = 12 := by
      rw [x2611_15505_formal_counts_aux2 4 8]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h4_13]
    have h4_15 : ({w : List ℕ | w.length = 10 ∧ (∀ k ∈ w, k < 4) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3]}).ncard = 12 := by
      rw [x2611_15505_formal_counts_aux2 4 9]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h4_14]
    have heq : {w : List ℕ | x2611_15505_formal_word 4 w} = {w : List ℕ | w.length = 10 ∧ (∀ k ∈ w, k < 4) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3]} := by
      ext w
      simp only [Set.mem_setOf_eq]
      rw [x2611_15505_formal_counts_aux4]
      norm_num [Fin.forall_fin_succ, List.replicate_succ]
    rw [heq]
    exact h4_15
  ·
    have h5_0 : ({w : List ℕ | w.length = 0 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [] ∧ w.filter (fun k => k = 4 ∨ k = 5) = []}).ncard = 1 := by
      apply x2611_15505_formal_counts_aux5
      simp
    have h5_1 : ({w : List ℕ | w.length = 1 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [] ∧ w.filter (fun k => k = 4 ∨ k = 5) = []}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 5 0]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_0]
    have h5_2 : ({w : List ℕ | w.length = 2 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [] ∧ w.filter (fun k => k = 4 ∨ k = 5) = []}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 5 1]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_1]
    have h5_3 : ({w : List ℕ | w.length = 3 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [] ∧ w.filter (fun k => k = 4 ∨ k = 5) = []}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 5 2]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_2]
    have h5_4 : ({w : List ℕ | w.length = 3 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [] ∧ w.filter (fun k => k = 4 ∨ k = 5) = []}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 5 2]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_2]
    have h5_5 : ({w : List ℕ | w.length = 4 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = []}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 5 3]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_3]
    have h5_6 : ({w : List ℕ | w.length = 4 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [] ∧ w.filter (fun k => k = 4 ∨ k = 5) = []}).ncard = 2 := by
      rw [x2611_15505_formal_counts_aux2 5 3]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_3, h5_4]
    have h5_7 : ({w : List ℕ | w.length = 5 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4]}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 5 4]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_5]
    have h5_8 : ({w : List ℕ | w.length = 5 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = []}).ncard = 3 := by
      rw [x2611_15505_formal_counts_aux2 5 4]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_5, h5_6]
    have h5_9 : ({w : List ℕ | w.length = 5 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [] ∧ w.filter (fun k => k = 4 ∨ k = 5) = []}).ncard = 2 := by
      rw [x2611_15505_formal_counts_aux2 5 4]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_6]
    have h5_10 : ({w : List ℕ | w.length = 6 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4]}).ncard = 4 := by
      rw [x2611_15505_formal_counts_aux2 5 5]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_7, h5_8]
    have h5_11 : ({w : List ℕ | w.length = 6 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = []}).ncard = 5 := by
      rw [x2611_15505_formal_counts_aux2 5 5]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_8, h5_9]
    have h5_12 : ({w : List ℕ | w.length = 6 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [] ∧ w.filter (fun k => k = 4 ∨ k = 5) = []}).ncard = 2 := by
      rw [x2611_15505_formal_counts_aux2 5 5]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_9]
    have h5_13 : ({w : List ℕ | w.length = 7 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4]}).ncard = 9 := by
      rw [x2611_15505_formal_counts_aux2 5 6]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_10, h5_11]
    have h5_14 : ({w : List ℕ | w.length = 7 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = []}).ncard = 5 := by
      rw [x2611_15505_formal_counts_aux2 5 6]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_11]
    have h5_15 : ({w : List ℕ | w.length = 7 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = []}).ncard = 7 := by
      rw [x2611_15505_formal_counts_aux2 5 6]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_11, h5_12]
    have h5_16 : ({w : List ℕ | w.length = 8 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4]}).ncard = 14 := by
      rw [x2611_15505_formal_counts_aux2 5 7]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_13, h5_14]
    have h5_17 : ({w : List ℕ | w.length = 8 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4]}).ncard = 16 := by
      rw [x2611_15505_formal_counts_aux2 5 7]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_13, h5_15]
    have h5_18 : ({w : List ℕ | w.length = 8 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = []}).ncard = 12 := by
      rw [x2611_15505_formal_counts_aux2 5 7]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_14, h5_15]
    have h5_19 : ({w : List ℕ | w.length = 9 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4]}).ncard = 14 := by
      rw [x2611_15505_formal_counts_aux2 5 8]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_16]
    have h5_20 : ({w : List ℕ | w.length = 9 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4]}).ncard = 42 := by
      rw [x2611_15505_formal_counts_aux2 5 8]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_16, h5_17, h5_18]
    have h5_21 : ({w : List ℕ | w.length = 9 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = []}).ncard = 12 := by
      rw [x2611_15505_formal_counts_aux2 5 8]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_18]
    have h5_22 : ({w : List ℕ | w.length = 10 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4]}).ncard = 56 := by
      rw [x2611_15505_formal_counts_aux2 5 9]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_19, h5_20]
    have h5_23 : ({w : List ℕ | w.length = 10 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4]}).ncard = 54 := by
      rw [x2611_15505_formal_counts_aux2 5 9]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_20, h5_21]
    have h5_24 : ({w : List ℕ | w.length = 10 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = []}).ncard = 12 := by
      rw [x2611_15505_formal_counts_aux2 5 9]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_21]
    have h5_25 : ({w : List ℕ | w.length = 11 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4]}).ncard = 110 := by
      rw [x2611_15505_formal_counts_aux2 5 10]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_22, h5_23]
    have h5_26 : ({w : List ℕ | w.length = 11 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4]}).ncard = 66 := by
      rw [x2611_15505_formal_counts_aux2 5 10]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_23, h5_24]
    have h5_27 : ({w : List ℕ | w.length = 12 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4]}).ncard = 110 := by
      rw [x2611_15505_formal_counts_aux2 5 11]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_25]
    have h5_28 : ({w : List ℕ | w.length = 12 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4]}).ncard = 176 := by
      rw [x2611_15505_formal_counts_aux2 5 11]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_25, h5_26]
    have h5_29 : ({w : List ℕ | w.length = 13 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4]}).ncard = 286 := by
      rw [x2611_15505_formal_counts_aux2 5 12]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_27, h5_28]
    have h5_30 : ({w : List ℕ | w.length = 14 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4]}).ncard = 286 := by
      rw [x2611_15505_formal_counts_aux2 5 13]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_29]
    have h5_31 : ({w : List ℕ | w.length = 15 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4]}).ncard = 286 := by
      rw [x2611_15505_formal_counts_aux2 5 14]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h5_30]
    have heq : {w : List ℕ | x2611_15505_formal_word 5 w} = {w : List ℕ | w.length = 15 ∧ (∀ k ∈ w, k < 5) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4]} := by
      ext w
      simp only [Set.mem_setOf_eq]
      rw [x2611_15505_formal_counts_aux4]
      norm_num [Fin.forall_fin_succ, List.replicate_succ]
    rw [heq]
    exact h5_31
  ·
    have h6_0 : ({w : List ℕ | w.length = 0 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 1 := by
      apply x2611_15505_formal_counts_aux5
      simp
    have h6_1 : ({w : List ℕ | w.length = 1 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 6 0]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_0]
    have h6_2 : ({w : List ℕ | w.length = 2 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 6 1]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_1]
    have h6_3 : ({w : List ℕ | w.length = 3 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 6 2]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_2]
    have h6_4 : ({w : List ℕ | w.length = 3 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 6 2]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_2]
    have h6_5 : ({w : List ℕ | w.length = 4 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 6 3]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_3]
    have h6_6 : ({w : List ℕ | w.length = 4 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 2 := by
      rw [x2611_15505_formal_counts_aux2 6 3]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_3, h6_4]
    have h6_7 : ({w : List ℕ | w.length = 5 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 6 4]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_5]
    have h6_8 : ({w : List ℕ | w.length = 5 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 3 := by
      rw [x2611_15505_formal_counts_aux2 6 4]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_5, h6_6]
    have h6_9 : ({w : List ℕ | w.length = 5 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 2 := by
      rw [x2611_15505_formal_counts_aux2 6 4]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_6]
    have h6_10 : ({w : List ℕ | w.length = 6 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 1 := by
      rw [x2611_15505_formal_counts_aux2 6 5]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_7]
    have h6_11 : ({w : List ℕ | w.length = 6 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 4 := by
      rw [x2611_15505_formal_counts_aux2 6 5]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_7, h6_8]
    have h6_12 : ({w : List ℕ | w.length = 6 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 5 := by
      rw [x2611_15505_formal_counts_aux2 6 5]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_8, h6_9]
    have h6_13 : ({w : List ℕ | w.length = 6 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 2 := by
      rw [x2611_15505_formal_counts_aux2 6 5]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_9]
    have h6_14 : ({w : List ℕ | w.length = 7 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 5 := by
      rw [x2611_15505_formal_counts_aux2 6 6]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_10, h6_11]
    have h6_15 : ({w : List ℕ | w.length = 7 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 9 := by
      rw [x2611_15505_formal_counts_aux2 6 6]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_11, h6_12]
    have h6_16 : ({w : List ℕ | w.length = 7 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 5 := by
      rw [x2611_15505_formal_counts_aux2 6 6]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_12]
    have h6_17 : ({w : List ℕ | w.length = 7 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 7 := by
      rw [x2611_15505_formal_counts_aux2 6 6]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_12, h6_13]
    have h6_18 : ({w : List ℕ | w.length = 8 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 14 := by
      rw [x2611_15505_formal_counts_aux2 6 7]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_14, h6_15]
    have h6_19 : ({w : List ℕ | w.length = 8 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 14 := by
      rw [x2611_15505_formal_counts_aux2 6 7]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_15, h6_16]
    have h6_20 : ({w : List ℕ | w.length = 8 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 16 := by
      rw [x2611_15505_formal_counts_aux2 6 7]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_15, h6_17]
    have h6_21 : ({w : List ℕ | w.length = 8 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 12 := by
      rw [x2611_15505_formal_counts_aux2 6 7]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_16, h6_17]
    have h6_22 : ({w : List ℕ | w.length = 9 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 28 := by
      rw [x2611_15505_formal_counts_aux2 6 8]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_18, h6_19]
    have h6_23 : ({w : List ℕ | w.length = 9 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 14 := by
      rw [x2611_15505_formal_counts_aux2 6 8]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_19]
    have h6_24 : ({w : List ℕ | w.length = 9 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 30 := by
      rw [x2611_15505_formal_counts_aux2 6 8]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_18, h6_20]
    have h6_25 : ({w : List ℕ | w.length = 9 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 42 := by
      rw [x2611_15505_formal_counts_aux2 6 8]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_19, h6_20, h6_21]
    have h6_26 : ({w : List ℕ | w.length = 9 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 12 := by
      rw [x2611_15505_formal_counts_aux2 6 8]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_21]
    have h6_27 : ({w : List ℕ | w.length = 10 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 42 := by
      rw [x2611_15505_formal_counts_aux2 6 9]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_22, h6_23]
    have h6_28 : ({w : List ℕ | w.length = 10 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 100 := by
      rw [x2611_15505_formal_counts_aux2 6 9]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_22, h6_24, h6_25]
    have h6_29 : ({w : List ℕ | w.length = 10 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 56 := by
      rw [x2611_15505_formal_counts_aux2 6 9]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_23, h6_25]
    have h6_30 : ({w : List ℕ | w.length = 10 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 54 := by
      rw [x2611_15505_formal_counts_aux2 6 9]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_25, h6_26]
    have h6_31 : ({w : List ℕ | w.length = 10 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 12 := by
      rw [x2611_15505_formal_counts_aux2 6 9]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_26]
    have h6_32 : ({w : List ℕ | w.length = 11 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4, 5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 42 := by
      rw [x2611_15505_formal_counts_aux2 6 10]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_27]
    have h6_33 : ({w : List ℕ | w.length = 11 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 198 := by
      rw [x2611_15505_formal_counts_aux2 6 10]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_27, h6_28, h6_29]
    have h6_34 : ({w : List ℕ | w.length = 11 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 154 := by
      rw [x2611_15505_formal_counts_aux2 6 10]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_28, h6_30]
    have h6_35 : ({w : List ℕ | w.length = 11 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 110 := by
      rw [x2611_15505_formal_counts_aux2 6 10]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_29, h6_30]
    have h6_36 : ({w : List ℕ | w.length = 11 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 66 := by
      rw [x2611_15505_formal_counts_aux2 6 10]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_30, h6_31]
    have h6_37 : ({w : List ℕ | w.length = 12 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4, 5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 240 := by
      rw [x2611_15505_formal_counts_aux2 6 11]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_32, h6_33]
    have h6_38 : ({w : List ℕ | w.length = 12 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 462 := by
      rw [x2611_15505_formal_counts_aux2 6 11]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_33, h6_34, h6_35]
    have h6_39 : ({w : List ℕ | w.length = 12 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 110 := by
      rw [x2611_15505_formal_counts_aux2 6 11]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_35]
    have h6_40 : ({w : List ℕ | w.length = 12 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 220 := by
      rw [x2611_15505_formal_counts_aux2 6 11]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_34, h6_36]
    have h6_41 : ({w : List ℕ | w.length = 12 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 176 := by
      rw [x2611_15505_formal_counts_aux2 6 11]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_35, h6_36]
    have h6_42 : ({w : List ℕ | w.length = 13 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4, 5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 702 := by
      rw [x2611_15505_formal_counts_aux2 6 12]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_37, h6_38]
    have h6_43 : ({w : List ℕ | w.length = 13 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 572 := by
      rw [x2611_15505_formal_counts_aux2 6 12]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_38, h6_39]
    have h6_44 : ({w : List ℕ | w.length = 13 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 858 := by
      rw [x2611_15505_formal_counts_aux2 6 12]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_38, h6_40, h6_41]
    have h6_45 : ({w : List ℕ | w.length = 13 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 286 := by
      rw [x2611_15505_formal_counts_aux2 6 12]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_39, h6_41]
    have h6_46 : ({w : List ℕ | w.length = 14 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4, 5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 1274 := by
      rw [x2611_15505_formal_counts_aux2 6 13]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_42, h6_43]
    have h6_47 : ({w : List ℕ | w.length = 14 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4, 5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 1560 := by
      rw [x2611_15505_formal_counts_aux2 6 13]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_42, h6_44]
    have h6_48 : ({w : List ℕ | w.length = 14 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 1716 := by
      rw [x2611_15505_formal_counts_aux2 6 13]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_43, h6_44, h6_45]
    have h6_49 : ({w : List ℕ | w.length = 14 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 286 := by
      rw [x2611_15505_formal_counts_aux2 6 13]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_45]
    have h6_50 : ({w : List ℕ | w.length = 15 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4, 5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 1274 := by
      rw [x2611_15505_formal_counts_aux2 6 14]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_46]
    have h6_51 : ({w : List ℕ | w.length = 15 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4, 5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 4550 := by
      rw [x2611_15505_formal_counts_aux2 6 14]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_46, h6_47, h6_48]
    have h6_52 : ({w : List ℕ | w.length = 15 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 2002 := by
      rw [x2611_15505_formal_counts_aux2 6 14]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_48, h6_49]
    have h6_53 : ({w : List ℕ | w.length = 15 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = []}).ncard = 286 := by
      rw [x2611_15505_formal_counts_aux2 6 14]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_49]
    have h6_54 : ({w : List ℕ | w.length = 16 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4, 5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 5824 := by
      rw [x2611_15505_formal_counts_aux2 6 15]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_50, h6_51]
    have h6_55 : ({w : List ℕ | w.length = 16 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4, 5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 6552 := by
      rw [x2611_15505_formal_counts_aux2 6 15]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_51, h6_52]
    have h6_56 : ({w : List ℕ | w.length = 16 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 2288 := by
      rw [x2611_15505_formal_counts_aux2 6 15]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_52, h6_53]
    have h6_57 : ({w : List ℕ | w.length = 17 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4, 5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 12376 := by
      rw [x2611_15505_formal_counts_aux2 6 16]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_54, h6_55]
    have h6_58 : ({w : List ℕ | w.length = 17 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [4, 3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4, 5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 8840 := by
      rw [x2611_15505_formal_counts_aux2 6 16]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_55, h6_56]
    have h6_59 : ({w : List ℕ | w.length = 18 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4, 5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 12376 := by
      rw [x2611_15505_formal_counts_aux2 6 17]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_57]
    have h6_60 : ({w : List ℕ | w.length = 18 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [3, 2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4, 5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 21216 := by
      rw [x2611_15505_formal_counts_aux2 6 17]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_57, h6_58]
    have h6_61 : ({w : List ℕ | w.length = 19 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [2, 1, 2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4, 5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 33592 := by
      rw [x2611_15505_formal_counts_aux2 6 18]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_59, h6_60]
    have h6_62 : ({w : List ℕ | w.length = 20 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [1, 0, 1, 0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4, 5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 33592 := by
      rw [x2611_15505_formal_counts_aux2 6 19]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_61]
    have h6_63 : ({w : List ℕ | w.length = 21 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4, 5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]}).ncard = 33592 := by
      rw [x2611_15505_formal_counts_aux2 6 20]
      norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.filter_cons, Bool.or_eq_true, decide_eq_true_eq, List.cons.injEq, List.cons_ne_nil, true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false, if_true, if_false, Set.setOf_false, Set.ncard_empty, h6_62]
    have heq : {w : List ℕ | x2611_15505_formal_word 6 w} = {w : List ℕ | w.length = 21 ∧ (∀ k ∈ w, k < 6) ∧ w.filter (fun k => k = 0 ∨ k = 1) = [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] ∧ w.filter (fun k => k = 1 ∨ k = 2) = [1, 2, 1, 2, 1, 2, 1, 2, 1] ∧ w.filter (fun k => k = 2 ∨ k = 3) = [2, 3, 2, 3, 2, 3, 2] ∧ w.filter (fun k => k = 3 ∨ k = 4) = [3, 4, 3, 4, 3] ∧ w.filter (fun k => k = 4 ∨ k = 5) = [4, 5, 4] ∧ w.filter (fun k => k = 5 ∨ k = 6) = [5]} := by
      ext w
      simp only [Set.mem_setOf_eq]
      rw [x2611_15505_formal_counts_aux4]
      norm_num [Fin.forall_fin_succ, List.replicate_succ]
    rw [heq]
    exact h6_63
end

-- forge:entry x2611_11287_thm1_2_lower_s1h2 kind=proved origin=decomposition
section
/- x2611_11287_thm1_2_lower 的证明骨架中第 2 个空洞 -/
open TensorProduct

lemma x2611_11287_thm1_2_lower_s1h2_aux1 {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [StrongRankCondition R] [StrongRankCondition S] [Module.Flat R S]
    {M N P Q : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module S P] [AddCommGroup Q] [Module S Q]
    (f : M →ₗ[R] N) (g : P →ₗ[S] Q) [Module.Free R (LinearMap.ker f)]
    (e : S ⊗[R] M ≃ₗ[S] P) (e' : S ⊗[R] N ≃ₗ[S] Q)
    (h : ∀ x, e' ((AlgebraTensorModule.lTensor S S f) x) = g (e x)) :
    Module.finrank R (LinearMap.ker f) = Module.finrank S (LinearMap.ker g) := by
  have hk : (LinearMap.ker (AlgebraTensorModule.lTensor S S f)).map e.toLinearMap =
      LinearMap.ker g := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (AlgebraTensorModule.lTensor S S f) x = 0 at hx
      change g (e x) = 0
      rw [← h, hx, map_zero]
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      change g y = 0 at hy
      change (AlgebraTensorModule.lTensor S S f) (e.symm y) = 0
      apply e'.injective
      rw [h, e.apply_symm_apply, hy, map_zero]
  calc
    Module.finrank R (LinearMap.ker f) = Module.finrank S (S ⊗[R] LinearMap.ker f) :=
      Module.finrank_baseChange.symm
    _ = Module.finrank S (LinearMap.ker (AlgebraTensorModule.lTensor S S f)) :=
      (LinearMap.tensorKerEquiv S S f).finrank_eq
    _ = Module.finrank S (LinearMap.ker g) := (e.ofSubmodules _ _ hk).finrank_eq

lemma x2611_11287_thm1_2_lower_s1h2_aux2 (F : Type*) [Field F] (n : ℕ) :
    ∃ e : F ⊗[ℤ] Matrix (Fin n) (Fin n) ℤ ≃ₗ[F] Matrix (Fin n) (Fin n) F,
    ∀ (c : F) (X : Matrix (Fin n) (Fin n) ℤ),
      e (c ⊗ₜ[ℤ] X) = c • X.map (Int.castRingHom F) := by
  let e : F ⊗[ℤ] Matrix (Fin n) (Fin n) ℤ ≃ₗ[F] Matrix (Fin n) (Fin n) F :=
    (TensorProduct.piRight ℤ F F (fun _ : Fin n => Fin n → ℤ)).trans
      (LinearEquiv.piCongrRight (fun _ : Fin n => TensorProduct.piScalarRight ℤ F F (Fin n)))
  refine ⟨e, ?_⟩
  intro c X
  ext i j
  change (X i j) • c = c * (X i j : F)
  rw [← Int.cast_smul_eq_zsmul F]
  simp [mul_comm]


lemma x2611_11287_thm1_2_lower_s1h2_aux3 (R : Type*) [CommRing R] (n : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    (Subalgebra.centralizer R {A}).toSubmodule =
    LinearMap.ker (LinearMap.mulLeft R A - LinearMap.mulRight R A) := by
  ext X
  simp [Subalgebra.mem_centralizer_iff, sub_eq_zero]



theorem x2611_11287_thm1_2_lower_s1h2 : ∀ (F : Type*) [inst : Field F] [CharZero F]
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ),
    Module.finrank ℤ ↥((Subalgebra.toSubmodule : Subalgebra ℤ (Matrix (Fin n) (Fin n) ℤ) → Submodule ℤ (Matrix (Fin n) (Fin n) ℤ)) (Subalgebra.centralizer ℤ {A})) =
    Module.finrank F ↥((Subalgebra.toSubmodule : Subalgebra F (Matrix (Fin n) (Fin n) F) → Submodule F (Matrix (Fin n) (Fin n) F)) (Subalgebra.centralizer F {A.map (⇑(Int.castRingHom F) : ℤ → F)})) := by
  intro F _ _ n A
  rw [x2611_11287_thm1_2_lower_s1h2_aux3, x2611_11287_thm1_2_lower_s1h2_aux3]
  let f := LinearMap.mulLeft ℤ A - LinearMap.mulRight ℤ A
  let AF := A.map (Int.castRingHom F)
  let g := LinearMap.mulLeft F AF - LinearMap.mulRight F AF
  obtain ⟨e, he⟩ := x2611_11287_thm1_2_lower_s1h2_aux2 F n
  apply x2611_11287_thm1_2_lower_s1h2_aux1 f g e e
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c X =>
      rw [AlgebraTensorModule.lTensor_tmul, he, he]
      change c • (A * X - X * A).map (Int.castRingHom F) =
        AF * (c • X.map (Int.castRingHom F)) - (c • X.map (Int.castRingHom F)) * AF
      simp [AF, Matrix.map_sub, Matrix.map_mul_intCast, smul_sub]
  | add x y hx hy => simp only [map_add, hx, hy]
end

-- forge:entry x2611_15512_lem2_4_s1h1 kind=proved origin=decomposition
section
/- x2611_15512_lem2_4 的证明骨架中第 1 个空洞 -/
open Classical

lemma x2611_15512_lem2_4_s1h1_aux1 {α S : Type*} [CommSemiring S]
    (A : Finset α) :
    MvPolynomial.IsHomogeneous (∏ a ∈ A, (MvPolynomial.X a : MvPolynomial α S)) A.card := by
  classical
  simpa using MvPolynomial.IsHomogeneous.prod A
    (fun a => (MvPolynomial.X a : MvPolynomial α S)) (fun _ => 1)
    (fun a _ => MvPolynomial.isHomogeneous_X S a)

lemma x2611_15512_lem2_4_s1h1_aux2 {α S : Type*} [CommSemiring S]
    (P Q : MvPolynomial α S) (a b : ℕ)
    (hP : ∀ d : α →₀ ℕ, Finsupp.degree d < a → MvPolynomial.coeff d P = 0)
    (hQ : ∀ d : α →₀ ℕ, Finsupp.degree d < b → MvPolynomial.coeff d Q = 0)
    (d : α →₀ ℕ) (hd : Finsupp.degree d < a + b) :
    MvPolynomial.coeff d (P * Q) = 0 := by
  classical
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have heq : ij.1 + ij.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  have hdeg : Finsupp.degree ij.1 + Finsupp.degree ij.2 = Finsupp.degree d := by
    rw [← map_add, heq]
  by_cases h : Finsupp.degree ij.1 < a
  · simp [hP _ h]
  · simp [hQ ij.2 (by omega)]

lemma x2611_15512_lem2_4_s1h1_aux3 {α S : Type*} [CommSemiring S]
    (E : Finset α) (d : α →₀ ℕ) :
    MvPolynomial.coeff d (∏ a ∈ E, (1 + MvPolynomial.X a : MvPolynomial α S)) =
      MvPolynomial.coeff d (∑ A ∈ E.powersetCard (Finsupp.degree d),
        ∏ a ∈ A, MvPolynomial.X a : MvPolynomial α S) := by
  classical
  rw [Finset.prod_one_add, MvPolynomial.coeff_sum, MvPolynomial.coeff_sum]
  symm
  apply Finset.sum_subset
  · intro A hA
    exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hA).1
  · intro A hA hnot
    apply (x2611_15512_lem2_4_s1h1_aux1 (S := S) A).coeff_eq_zero
    intro h
    apply hnot
    exact Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hA, h.symm⟩

lemma x2611_15512_lem2_4_s1h1_aux4 {α S : Type*} [CommRing S]
    (E : Finset α) (d : α →₀ ℕ) (hd : Finsupp.degree d < 3) :
    MvPolynomial.coeff d
      ((∏ a ∈ E, (1 + MvPolynomial.X a : MvPolynomial α S)) - 1 -
        (∑ a ∈ E, MvPolynomial.X a) -
        (∑ A ∈ E.powersetCard 2, ∏ a ∈ A, MvPolynomial.X a)) = 0 := by
  classical
  have hS : MvPolynomial.IsHomogeneous
      (∑ a ∈ E, MvPolynomial.X a : MvPolynomial α S) 1 :=
    MvPolynomial.IsHomogeneous.sum E _ 1 (fun a _ => MvPolynomial.isHomogeneous_X S a)
  have hT : MvPolynomial.IsHomogeneous
      (∑ A ∈ E.powersetCard 2, ∏ a ∈ A, MvPolynomial.X a : MvPolynomial α S) 2 := by
    apply MvPolynomial.IsHomogeneous.sum
    intro A hA
    convert x2611_15512_lem2_4_s1h1_aux1 (S := S) A using 1
    exact (Finset.mem_powersetCard.mp hA).2.symm
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_sub,
    x2611_15512_lem2_4_s1h1_aux3]
  have hcases : Finsupp.degree d = 0 ∨ Finsupp.degree d = 1 ∨ Finsupp.degree d = 2 := by omega
  rcases hcases with h | h | h
  · rw [h, Finset.powersetCard_zero]
    simp only [Finset.sum_singleton, Finset.prod_empty]
    rw [hS.coeff_eq_zero (by omega), hT.coeff_eq_zero (by omega)]
    ring
  · rw [h, Finset.powersetCard_one]
    simp only [Finset.sum_map, Function.Embedding.coeFn_mk, Finset.prod_singleton]
    rw [(MvPolynomial.isHomogeneous_one α S).coeff_eq_zero (by omega),
      hT.coeff_eq_zero (by omega)]
    ring
  · rw [h, (MvPolynomial.isHomogeneous_one α S).coeff_eq_zero (by omega),
      hS.coeff_eq_zero (by omega)]
    ring

lemma x2611_15512_lem2_4_s1h1_aux5 {α β M : Type*} [Fintype β] [AddCommMonoid M]
    (E : Finset α) (p : α → β) (f : Finset α → M) :
    (∑ v : β, ∑ A ∈ (E.filter (fun a => p a = v)).powersetCard 2, f A) =
      ∑ A ∈ E.powersetCard 2, if (A.image p).card = 1 then f A else 0 := by
  classical
  have hfiber (v : β) :
      (E.filter (fun a => p a = v)).powersetCard 2 =
        (E.powersetCard 2).filter (fun A => ∀ a ∈ A, p a = v) := by
    ext A
    simp only [Finset.mem_powersetCard, Finset.mem_filter]
    constructor
    · rintro ⟨hs, hc⟩
      exact ⟨⟨fun a ha => (Finset.mem_filter.mp (hs ha)).1, hc⟩,
        fun a ha => (Finset.mem_filter.mp (hs ha)).2⟩
    · rintro ⟨⟨hs, hc⟩, hp⟩
      exact ⟨fun a ha => Finset.mem_filter.mpr ⟨hs ha, hp a ha⟩, hc⟩
  simp_rw [hfiber, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hA).2
  have hforall (v : β) : (∀ x ∈ ({a, b} : Finset α), p x = v) ↔ (p a = v ∧ p b = v) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      exact ⟨h a (Or.inl rfl), h b (Or.inr rfl)⟩
    · rintro ⟨ha, hb⟩ x (rfl | rfl)
      · exact ha
      · exact hb
  simp_rw [hforall, ite_and]
  by_cases hp : p a = p b
  · simp [hp, eq_comm]
  · simp [hp, Finset.card_pair hp, eq_comm]

lemma x2611_15512_lem2_4_s1h1_aux6 {α L R M : Type*}
    [Fintype L] [Fintype R] [AddCommMonoid M]
    (E : Finset α) (l : α → L) (r : α → R)
    (hsimple : Set.InjOn (fun a => (l a, r a)) (↑E : Set α))
    (f : Finset α → M) :
    (∑ v : L, ∑ A ∈ (E.filter (fun a => l a = v)).powersetCard 2, f A) +
      (∑ v : R, ∑ A ∈ (E.filter (fun a => r a = v)).powersetCard 2, f A) +
      (∑ A ∈ (E.powersetCard 2).filter
        (fun A => (A.image l).card = 2 ∧ (A.image r).card = 2), f A) =
      ∑ A ∈ E.powersetCard 2, f A := by
  classical
  rw [x2611_15512_lem2_4_s1h1_aux5 E l f, x2611_15512_lem2_4_s1h1_aux5 E r f,
    Finset.sum_filter, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A hA
  have hAE := (Finset.mem_powersetCard.mp hA).1
  obtain ⟨a, b, hab, hAB⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hA).2
  have ha : a ∈ E := hAE (by simp [hAB])
  have hb : b ∈ E := hAE (by simp [hAB])
  have hne : ¬ (l a = l b ∧ r a = r b) := by
    rintro ⟨hl, hr⟩
    exact hab (hsimple ha hb (Prod.ext hl hr))
  subst A
  by_cases hl : l a = l b
  · have hr : r a ≠ r b := fun h => hne ⟨hl, h⟩
    simp [hl, Finset.card_pair hr]
  · by_cases hr : r a = r b
    · simp [hr, Finset.card_pair hl]
    · simp [Finset.card_pair hl, Finset.card_pair hr]

lemma x2611_15512_lem2_4_s1h1_aux7 {α : Type*}
    (S A B P H : MvPolynomial α ℝ)
    (hS : MvPolynomial.IsHomogeneous S 1)
    (hH : MvPolynomial.IsHomogeneous H 2)
    (hA : ∀ d : α →₀ ℕ, Finsupp.degree d < 2 → MvPolynomial.coeff d (A - S) = 0)
    (hB : ∀ d : α →₀ ℕ, Finsupp.degree d < 2 → MvPolynomial.coeff d (B - S) = 0)
    (hP : ∀ d : α →₀ ℕ, Finsupp.degree d < 2 → MvPolynomial.coeff d (P - S) = 0)
    (hW : ∀ d : α →₀ ℕ, Finsupp.degree d < 3 →
      MvPolynomial.coeff d ((A - S) + (B - S) + H - (P - S)) = 0)
    (d : α →₀ ℕ) (hd : Finsupp.degree d < 4) :
    MvPolynomial.coeff d (A * B + P * (H - S)) = 0 := by
  have h₁ := x2611_15512_lem2_4_s1h1_aux2 (A - S) (B - S) 2 2 hA hB d hd
  have h₂ := x2611_15512_lem2_4_s1h1_aux2 S ((A - S) + (B - S) + H - (P - S)) 1 3
    (fun e he => hS.coeff_eq_zero (d := e) (by omega)) hW d hd
  have h₃ := x2611_15512_lem2_4_s1h1_aux2 (P - S) H 2 2 hP
    (fun e he => hH.coeff_eq_zero (d := e) (by omega)) d hd
  have heq : A * B + P * (H - S) =
      (A - S) * (B - S) + S * ((A - S) + (B - S) + H - (P - S)) + (P - S) * H := by ring
  rw [heq, MvPolynomial.coeff_add, MvPolynomial.coeff_add, h₁, h₂, h₃]
  ring

lemma x2611_15512_lem2_4_s1h1_aux8 {α β : Type*} [Fintype β]
    (E : Finset α) (p : α → β)
    (d : α →₀ ℕ) (hd : Finsupp.degree d < 3) :
    MvPolynomial.coeff d
      (x2611_15512_graph_star E p - (∑ a ∈ E, MvPolynomial.X a) -
        (∑ v : β, ∑ A ∈ (E.filter (fun a => p a = v)).powersetCard 2,
          ∏ a ∈ A, MvPolynomial.X a)) = 0 := by
  classical
  have hlin := Finset.sum_fiberwise E p (fun a => (MvPolynomial.X a : MvPolynomial α ℝ))
  have heq :
      x2611_15512_graph_star E p - (∑ a ∈ E, MvPolynomial.X a) -
        (∑ v : β, ∑ A ∈ (E.filter (fun a => p a = v)).powersetCard 2,
          ∏ a ∈ A, MvPolynomial.X a) =
      ∑ v : β, ((∏ a ∈ E.filter (fun a => p a = v), (1 + MvPolynomial.X a)) - 1 -
        (∑ a ∈ E.filter (fun a => p a = v), MvPolynomial.X a) -
        (∑ A ∈ (E.filter (fun a => p a = v)).powersetCard 2,
          ∏ a ∈ A, MvPolynomial.X a)) := by
    simp only [Finset.sum_sub_distrib]
    rw [hlin]
    unfold x2611_15512_graph_star
    simp only [Finset.sum_sub_distrib]
  rw [heq, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro v hv
  exact x2611_15512_lem2_4_s1h1_aux4 _ d hd

theorem x2611_15512_lem2_4_s1h1 {α L R : Type*} [Fintype L] [Fintype R]
    (E : Finset α) (l : α → L) (r : α → R)
    (hsimple : Set.InjOn (fun a => (l a, r a)) (↑E : Set α))
    (d : α →₀ ℕ) (hd : Finsupp.degree d < 4) :
    MvPolynomial.coeff d (x2611_15512_graph_d E l r) = 0 := by
  classical
  let S : MvPolynomial α ℝ := ∑ a ∈ E, MvPolynomial.X a
  let P : MvPolynomial α ℝ := (∏ a ∈ E, (1 + MvPolynomial.X a)) - 1
  let T : MvPolynomial α ℝ := ∑ A ∈ E.powersetCard 2, ∏ a ∈ A, MvPolynomial.X a
  let U : MvPolynomial α ℝ :=
    ∑ v : L, ∑ A ∈ (E.filter (fun a => l a = v)).powersetCard 2, ∏ a ∈ A, MvPolynomial.X a
  let V : MvPolynomial α ℝ :=
    ∑ v : R, ∑ A ∈ (E.filter (fun a => r a = v)).powersetCard 2, ∏ a ∈ A, MvPolynomial.X a
  let H : MvPolynomial α ℝ :=
    ∑ A ∈ (E.powersetCard 2).filter
      (fun A => (A.image l).card = 2 ∧ (A.image r).card = 2), ∏ a ∈ A, MvPolynomial.X a
  have hpair : U + V + H = T := x2611_15512_lem2_4_s1h1_aux6 E l r hsimple
    (fun A => (∏ a ∈ A, MvPolynomial.X a : MvPolynomial α ℝ))
  have hquad (F : Finset (Finset α)) (hF : ∀ A ∈ F, A.card = 2) :
      MvPolynomial.IsHomogeneous (∑ A ∈ F, ∏ a ∈ A, MvPolynomial.X a : MvPolynomial α ℝ) 2 := by
    apply MvPolynomial.IsHomogeneous.sum
    intro A hA
    convert x2611_15512_lem2_4_s1h1_aux1 (S := ℝ) A using 1
    exact (hF A hA).symm
  have hT : MvPolynomial.IsHomogeneous T 2 := hquad _
    (fun A hA => (Finset.mem_powersetCard.mp hA).2)
  have hU : MvPolynomial.IsHomogeneous U 2 :=
    MvPolynomial.IsHomogeneous.sum _ _ 2 (fun v _ => hquad _
      (fun A hA => (Finset.mem_powersetCard.mp hA).2))
  have hV : MvPolynomial.IsHomogeneous V 2 :=
    MvPolynomial.IsHomogeneous.sum _ _ 2 (fun v _ => hquad _
      (fun A hA => (Finset.mem_powersetCard.mp hA).2))
  have hH : MvPolynomial.IsHomogeneous H 2 := hquad _
    (fun A hA => (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA).1).2)
  have hS : MvPolynomial.IsHomogeneous S 1 :=
    MvPolynomial.IsHomogeneous.sum _ _ 1 (fun a _ => MvPolynomial.isHomogeneous_X ℝ a)
  have hleft : ∀ e : α →₀ ℕ, Finsupp.degree e < 3 →
      MvPolynomial.coeff e (x2611_15512_graph_star E l - S - U) = 0 :=
    x2611_15512_lem2_4_s1h1_aux8 E l
  have hright : ∀ e : α →₀ ℕ, Finsupp.degree e < 3 →
      MvPolynomial.coeff e (x2611_15512_graph_star E r - S - V) = 0 :=
    x2611_15512_lem2_4_s1h1_aux8 E r
  have hwhole : ∀ e : α →₀ ℕ, Finsupp.degree e < 3 →
      MvPolynomial.coeff e (P - S - T) = 0 := x2611_15512_lem2_4_s1h1_aux4 E
  have hremove (A B Q : MvPolynomial α ℝ)
      (hrem : ∀ e : α →₀ ℕ, Finsupp.degree e < 3 → MvPolynomial.coeff e (A - B - Q) = 0)
      (hQ : MvPolynomial.IsHomogeneous Q 2) :
      ∀ e : α →₀ ℕ, Finsupp.degree e < 2 → MvPolynomial.coeff e (A - B) = 0 := by
    intro e he
    have h := hrem e (by omega)
    rw [MvPolynomial.coeff_sub, hQ.coeff_eq_zero (by omega), sub_zero] at h
    exact h
  unfold x2611_15512_graph_d
  change MvPolynomial.coeff d
    (x2611_15512_graph_star E l * x2611_15512_graph_star E r + P * (H - S)) = 0
  apply x2611_15512_lem2_4_s1h1_aux7 S _ _ P H hS hH
    (hremove _ _ _ hleft hU) (hremove _ _ _ hright hV) (hremove _ _ _ hwhole hT) _ d hd
  intro e he
  have heq :
      (x2611_15512_graph_star E l - S) + (x2611_15512_graph_star E r - S) + H - (P - S) =
        (x2611_15512_graph_star E l - S - U) +
          (x2611_15512_graph_star E r - S - V) - (P - S - T) := by
    rw [← hpair]
    ring
  rw [heq, MvPolynomial.coeff_sub, MvPolynomial.coeff_add,
    hleft e he, hright e he, hwhole e he]
  ring
end

-- forge:entry x2611_15210_thm1_2_s1h1 kind=proved origin=decomposition
section
/- x2611_15210_thm1_2 的证明骨架中第 1 个空洞 -/
theorem x2611_15210_thm1_2_s1h1 : ∀ (m : ℕ), 3 ≤ m → Odd m → ∀ (r : ℕ),
    (↑m : ℝ) / (12 * Real.exp 1) * x2611_15210_rho m ^ r ≤
      (↑(x2611_15210_A (2 * m) (Fin r → ZMod m)) : ℝ) := by
  intro m hm hodd r
  exact ((x2611_15210_thm4_2 m hm hodd).2.1 r).1
end

-- forge:entry x2611_11287_thm1_2_lower_s1h3 kind=proved origin=decomposition
section
/- x2611_11287_thm1_2_lower 的证明骨架中第 3 个空洞 -/
open Polynomial
open scoped DirectSum

lemma x2611_11287_thm1_2_lower_s1h3_aux1
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) :
    ∃ g : V →ₗ[K] Module.End K V,
      Function.Injective g ∧ ∀ v, f * g v = g v * f := by
  classical
  obtain ⟨ι, hι, p, hp, k, ⟨e⟩⟩ :=
    Module.equiv_directSum_of_isTorsion
      (Module.AEval.isTorsion_of_finiteDimensional K V f)
  letI := hι
  let B := ∀ i : ι, K[X] ⧸ Submodule.span K[X] {p i ^ k i}
  let eP : Module.AEval K V f ≃ₗ[K[X]] B :=
    e.trans (DirectSum.linearEquivFunOnFintype K[X] ι _)
  let eK : V ≃ₗ[K] B :=
    (Module.AEval.of K V f).trans (eP.restrictScalars K)
  have he (v : V) : eK (f v) = (X : K[X]) • eK v := by
    change eP (Module.AEval.of K V f (f v)) = _
    rw [← Module.AEval'.X_smul_of f, eP.map_smul]
    rfl
  let gB : B →ₐ[K] Module.End K V :=
    (eK.symm.conjAlgEquiv K).toAlgHom.comp (Algebra.lmul K B)
  have hgB (b : B) (v : V) : gB b v = eK.symm (b * eK v) := rfl
  have hc (b : B) : f * gB b = gB b * f := by
    ext v
    apply eK.injective
    change eK (f (gB b v)) = eK (gB b (f v))
    rw [he, hgB, hgB, eK.apply_symm_apply, eK.apply_symm_apply, he]
    exact (mul_smul_comm (X : K[X]) b (eK v)).symm
  refine ⟨gB.toLinearMap.comp eK.toLinearMap, ?_, fun v => hc (eK v)⟩
  exact ((eK.symm.conjAlgEquiv K).injective.comp Algebra.lmul_injective).comp eK.injective

theorem x2611_11287_thm1_2_lower_s1h3 :
    ∀ (F : Type*) [inst : Field F] (n : ℕ) (A : Matrix (Fin n) (Fin n) F),
      n ≤ Module.finrank F ↥((Subalgebra.toSubmodule :
        Subalgebra F (Matrix (Fin n) (Fin n) F) →
        Submodule F (Matrix (Fin n) (Fin n) F)) (Subalgebra.centralizer F {A})) := by
  intro F inst n A
  classical
  let E := Matrix.toLinAlgEquiv' (R := F) (n := Fin n)
  obtain ⟨g, hg, hc⟩ := x2611_11287_thm1_2_lower_s1h3_aux1 (E A)
  let h : (Fin n → F) →ₗ[F] Matrix (Fin n) (Fin n) F :=
    E.symm.toLinearMap.comp g
  have hm (v : Fin n → F) : h v ∈ (Subalgebra.centralizer F {A}).toSubmodule := by
    change h v ∈ Subalgebra.centralizer F {A}
    rw [Subalgebra.mem_centralizer_iff]
    intro C hC
    have hCA : C = A := Set.mem_singleton_iff.mp hC
    subst C
    apply E.injective
    simp only [map_mul]
    change E A * E (E.symm (g v)) = E (E.symm (g v)) * E A
    simpa only [E.apply_symm_apply] using hc v
  let j := h.codRestrict (Subalgebra.centralizer F {A}).toSubmodule hm
  have hj : Function.Injective j := by
    intro v w hvw
    apply hg
    apply E.symm.injective
    exact congrArg Subtype.val hvw
  have hd := LinearMap.finrank_le_finrank_of_injective hj
  simpa using hd
end

-- forge:entry x2611_16458_ex4_4 kind=proved origin=paper
section
/- Example 4.4 (counterexample and polynomial values) -/
lemma x2611_16458_ex4_4_aux1 {V : Type*} [Fintype V] [DecidableEq V]
    (P N : SimpleGraph V) [DecidableRel P.Adj] [DecidableRel N.Adj] :
    x2611_16458_zeroFree P N =
      ∑ F ∈ (P.edgeFinset.disjSum N.edgeFinset).powerset,
        (by
          let Q : SimpleGraph V := SimpleGraph.fromEdgeSet {e | Sum.inl e ∈ F}
          let R : SimpleGraph V := SimpleGraph.fromEdgeSet {e | Sum.inr e ∈ F}
          letI : DecidableRel Q.Adj := by dsimp [Q]; infer_instance
          letI : DecidableRel R.Adj := by dsimp [R]; infer_instance
          letI : Decidable (x2611_16458_balanced Q R) := by
            unfold x2611_16458_balanced
            infer_instance
          exact if x2611_16458_balanced Q R then
            Polynomial.C ((-1 : ℤ) ^ F.card) * Polynomial.X ^
              Fintype.card (Q ⊔ R).ConnectedComponent
          else 0) := by
  classical
  unfold x2611_16458_zeroFree
  apply Finset.sum_congr
  · congr 1
    ext e
    cases e <;> simp
  · intro F hF
    dsimp only
    split_ifs <;> simp only [Nat.card_eq_fintype_card]


lemma x2611_16458_ex4_4_aux2 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (x2611_16458_zeroFree G ⊥).eval 1 = (by classical exact if G = ⊥ then 1 else 0) := by
  classical
  rw [x2611_16458_ex4_4_aux1, Polynomial.eval_finsetSum]
  calc
    _ = ∑ F ∈ (G.edgeFinset.disjSum (⊥ : SimpleGraph V).edgeFinset).powerset,
        (-1 : ℤ) ^ F.card := by
      apply Finset.sum_congr
      · congr 1
        ext e
        cases e <;> simp
      · intro F hF
        dsimp only
        have hn : SimpleGraph.fromEdgeSet {e | Sum.inr e ∈ F} = (⊥ : SimpleGraph V) := by
          ext v w
          simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_setOf_eq, SimpleGraph.bot_adj,
            iff_false, not_and]
          intro hh
          have := (Finset.mem_powerset.mp hF) hh
          simpa only [Finset.inr_mem_disjSum, SimpleGraph.mem_edgeFinset,
            SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false] using this
        have hb : x2611_16458_balanced (SimpleGraph.fromEdgeSet {e | Sum.inl e ∈ F})
            (⊥ : SimpleGraph V) := by
          exact ⟨fun _ => false, by simp, by simp⟩
        simp only [hn, if_pos hb, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one]
    _ = _ := by
      rw [Finset.sum_powerset_neg_one_pow_card]
      simp only [Finset.disjSum_eq_empty, SimpleGraph.edgeFinset_eq_empty, and_true]

lemma x2611_16458_ex4_4_aux3 {V : Type*} [Finite V] :
    x2611_16458_zeroFree (⊥ : SimpleGraph V) ⊥ = Polynomial.X ^ Nat.card V := by
  classical
  have hb : x2611_16458_balanced (⊥ : SimpleGraph V) ⊥ := by
    exact ⟨fun _ => false, by simp, by simp⟩
  have hc : Nat.card (⊥ : SimpleGraph V).ConnectedComponent = Nat.card V := by
    apply Nat.card_congr
    exact (Equiv.ofBijective (⊥ : SimpleGraph V).connectedComponentMk
      ⟨by intro v w h; exact SimpleGraph.reachable_bot.mp (SimpleGraph.ConnectedComponent.exact h),
       by intro c; induction c using SimpleGraph.ConnectedComponent.ind with | h v => exact ⟨v, rfl⟩⟩).symm
  simp [x2611_16458_zeroFree, SimpleGraph.edgeFinset, hb, hc]


theorem x2611_16458_ex4_4 (P N : SimpleGraph (Fin 5)) (Z h : Polynomial ℤ)
    (hP : P = x2611_16458_edges 5 [(1,2),(2,3)])
    (hN : N = x2611_16458_edges 5 [(1,3)])
    (hZ : Z = x2611_16458_zeroFree P N)
    (hh : h = x2611_16458_numerator 5 Z) :
    Z = Polynomial.X ^ 3 * (Polynomial.X ^ 2 - 3 * Polynomial.X + 3) ∧
    Z.comp (Polynomial.X - 1) = (Polynomial.X - 1) ^ 3 *
      (Polynomial.X ^ 2 - 5 * Polynomial.X + 7) ∧
    h = Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 + 48 * Polynomial.X ^ 4 +
        62 * Polynomial.X ^ 5 + 7 * Polynomial.X ^ 6 ∧
    (∀ i : ℕ, 0 ≤ h.coeff i) ∧
    Z.eval 1 = 1 ∧
    (¬ ∃ m : ℕ, ∃ G : SimpleGraph (Fin m), x2611_16458_zeroFree G ⊥ = Z) := by
  subst P
  subst N
  subst Z
  subst h
  have hz : x2611_16458_zeroFree (x2611_16458_edges 5 [(1,2),(2,3)])
      (x2611_16458_edges 5 [(1,3)]) =
      Polynomial.X ^ 3 * (Polynomial.X ^ 2 - 3 * Polynomial.X + 3) := by
    letI : DecidableRel (x2611_16458_edges 5 [(1,2),(2,3)]).Adj := by
      unfold x2611_16458_edges
      infer_instance
    letI : DecidableRel (x2611_16458_edges 5 [(1,3)]).Adj := by
      unfold x2611_16458_edges
      infer_instance
    rw [x2611_16458_ex4_4_aux1]
    let E : Finset (Sym2 (Fin 5) ⊕ Sym2 (Fin 5)) :=
      {Sum.inl s((0 : Fin 5),1), Sum.inl s((1 : Fin 5),2), Sum.inr s((0 : Fin 5),2)}
    have he : (x2611_16458_edges 5 [(1,2),(2,3)]).edgeFinset.disjSum
        (x2611_16458_edges 5 [(1,3)]).edgeFinset = E := by decide
    rw [he]
    have hep : E.powerset = {∅,
        {Sum.inl s((0 : Fin 5),1)},
        {Sum.inl s((1 : Fin 5),2)},
        {Sum.inr s((0 : Fin 5),2)},
        {Sum.inl s((0 : Fin 5),1), Sum.inl s((1 : Fin 5),2)},
        {Sum.inl s((0 : Fin 5),1), Sum.inr s((0 : Fin 5),2)},
        {Sum.inl s((1 : Fin 5),2), Sum.inr s((0 : Fin 5),2)},
        E} := by decide
    have hc : ∀ F ∈ E.powerset, (by
        let Q : SimpleGraph (Fin 5) := SimpleGraph.fromEdgeSet {e | Sum.inl e ∈ F}
        let R : SimpleGraph (Fin 5) := SimpleGraph.fromEdgeSet {e | Sum.inr e ∈ F}
        letI : DecidableRel Q.Adj := by dsimp [Q]; infer_instance
        letI : DecidableRel R.Adj := by dsimp [R]; infer_instance
        exact (x2611_16458_balanced Q R ↔ F ≠ E) ∧
          Fintype.card (Q ⊔ R).ConnectedComponent = (if F = E then 3 else 5 - F.card)) := by
      intro F hF
      rw [hep] at hF
      simp only [Finset.mem_insert, Finset.mem_singleton] at hF
      rcases hF with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · dsimp only
        rw [← Nat.card_eq_fintype_card]
        have hQ : SimpleGraph.fromEdgeSet {e | Sum.inl e ∈ (∅ : Finset (Sym2 (Fin 5) ⊕ Sym2 (Fin 5)))} =
            x2611_16458_edges 5 [] := by
          ext a b
          fin_cases a <;> fin_cases b <;>
            simp [E, SimpleGraph.fromEdgeSet_adj, x2611_16458_edges, SimpleGraph.fromRel_adj]
        have hR : SimpleGraph.fromEdgeSet {e | Sum.inr e ∈ (∅ : Finset (Sym2 (Fin 5) ⊕ Sym2 (Fin 5)))} =
            x2611_16458_edges 5 [] := by
          ext a b
          fin_cases a <;> fin_cases b <;>
            simp [E, SimpleGraph.fromEdgeSet_adj, x2611_16458_edges, SimpleGraph.fromRel_adj]
        rw [hQ, hR]
        constructor
        · constructor
          · intro _
            decide
          · intro _
            refine ⟨(fun _ => false : Fin 5 → Bool), ?_, ?_⟩ <;>
              dsimp [x2611_16458_edges, SimpleGraph.fromRel] <;> decide
        · letI : DecidableRel ((x2611_16458_edges 5 []) ⊔
              (x2611_16458_edges 5 [])).Adj := by
            unfold x2611_16458_edges
            infer_instance
          rw [Nat.card_eq_fintype_card]
          decide
      · dsimp only
        rw [← Nat.card_eq_fintype_card]
        have hQ : SimpleGraph.fromEdgeSet {e | Sum.inl e ∈ ({Sum.inl s((0 : Fin 5),1)} : Finset (Sym2 (Fin 5) ⊕ Sym2 (Fin 5)))} =
            x2611_16458_edges 5 [(1,2)] := by
          ext a b
          fin_cases a <;> fin_cases b <;>
            simp [E, SimpleGraph.fromEdgeSet_adj, x2611_16458_edges, SimpleGraph.fromRel_adj]
        have hR : SimpleGraph.fromEdgeSet {e | Sum.inr e ∈ ({Sum.inl s((0 : Fin 5),1)} : Finset (Sym2 (Fin 5) ⊕ Sym2 (Fin 5)))} =
            x2611_16458_edges 5 [] := by
          ext a b
          fin_cases a <;> fin_cases b <;>
            simp [E, SimpleGraph.fromEdgeSet_adj, x2611_16458_edges, SimpleGraph.fromRel_adj]
        rw [hQ, hR]
        constructor
        · constructor
          · intro _
            decide
          · intro _
            refine ⟨(fun _ => false : Fin 5 → Bool), ?_, ?_⟩ <;>
              dsimp [x2611_16458_edges, SimpleGraph.fromRel] <;> decide
        · letI : DecidableRel ((x2611_16458_edges 5 [(1,2)]) ⊔
              (x2611_16458_edges 5 [])).Adj := by
            unfold x2611_16458_edges
            infer_instance
          rw [Nat.card_eq_fintype_card]
          decide
      · dsimp only
        rw [← Nat.card_eq_fintype_card]
        have hQ : SimpleGraph.fromEdgeSet {e | Sum.inl e ∈ ({Sum.inl s((1 : Fin 5),2)} : Finset (Sym2 (Fin 5) ⊕ Sym2 (Fin 5)))} =
            x2611_16458_edges 5 [(2,3)] := by
          ext a b
          fin_cases a <;> fin_cases b <;>
            simp [E, SimpleGraph.fromEdgeSet_adj, x2611_16458_edges, SimpleGraph.fromRel_adj]
        have hR : SimpleGraph.fromEdgeSet {e | Sum.inr e ∈ ({Sum.inl s((1 : Fin 5),2)} : Finset (Sym2 (Fin 5) ⊕ Sym2 (Fin 5)))} =
            x2611_16458_edges 5 [] := by
          ext a b
          fin_cases a <;> fin_cases b <;>
            simp [E, SimpleGraph.fromEdgeSet_adj, x2611_16458_edges, SimpleGraph.fromRel_adj]
        rw [hQ, hR]
        constructor
        · constructor
          · intro _
            decide
          · intro _
            refine ⟨(fun _ => false : Fin 5 → Bool), ?_, ?_⟩ <;>
              dsimp [x2611_16458_edges, SimpleGraph.fromRel] <;> decide
        · letI : DecidableRel ((x2611_16458_edges 5 [(2,3)]) ⊔
              (x2611_16458_edges 5 [])).Adj := by
            unfold x2611_16458_edges
            infer_instance
          rw [Nat.card_eq_fintype_card]
          decide
      · dsimp only
        rw [← Nat.card_eq_fintype_card]
        have hQ : SimpleGraph.fromEdgeSet {e | Sum.inl e ∈ ({Sum.inr s((0 : Fin 5),2)} : Finset (Sym2 (Fin 5) ⊕ Sym2 (Fin 5)))} =
            x2611_16458_edges 5 [] := by
          ext a b
          fin_cases a <;> fin_cases b <;>
            simp [E, SimpleGraph.fromEdgeSet_adj, x2611_16458_edges, SimpleGraph.fromRel_adj]
        have hR : SimpleGraph.fromEdgeSet {e | Sum.inr e ∈ ({Sum.inr s((0 : Fin 5),2)} : Finset (Sym2 (Fin 5) ⊕ Sym2 (Fin 5)))} =
            x2611_16458_edges 5 [(1,3)] := by
          ext a b
          fin_cases a <;> fin_cases b <;>
            simp [E, SimpleGraph.fromEdgeSet_adj, x2611_16458_edges, SimpleGraph.fromRel_adj]
        rw [hQ, hR]
        constructor
        · constructor
          · intro _
            decide
          · intro _
            refine ⟨(fun v => decide (v = 2) : Fin 5 → Bool), ?_, ?_⟩ <;>
              dsimp [x2611_16458_edges, SimpleGraph.fromRel] <;> decide
        · letI : DecidableRel ((x2611_16458_edges 5 []) ⊔
              (x2611_16458_edges 5 [(1,3)])).Adj := by
            unfold x2611_16458_edges
            infer_instance
          rw [Nat.card_eq_fintype_card]
          decide
      · dsimp only
        rw [← Nat.card_eq_fintype_card]
        have hQ : SimpleGraph.fromEdgeSet {e | Sum.inl e ∈ ({Sum.inl s((0 : Fin 5),1), Sum.inl s((1 : Fin 5),2)} : Finset (Sym2 (Fin 5) ⊕ Sym2 (Fin 5)))} =
            x2611_16458_edges 5 [(1,2),(2,3)] := by
          ext a b
          fin_cases a <;> fin_cases b <;>
            simp [E, SimpleGraph.fromEdgeSet_adj, x2611_16458_edges, SimpleGraph.fromRel_adj]
        have hR : SimpleGraph.fromEdgeSet {e | Sum.inr e ∈ ({Sum.inl s((0 : Fin 5),1), Sum.inl s((1 : Fin 5),2)} : Finset (Sym2 (Fin 5) ⊕ Sym2 (Fin 5)))} =
            x2611_16458_edges 5 [] := by
          ext a b
          fin_cases a <;> fin_cases b <;>
            simp [E, SimpleGraph.fromEdgeSet_adj, x2611_16458_edges, SimpleGraph.fromRel_adj]
        rw [hQ, hR]
        constructor
        · constructor
          · intro _
            decide
          · intro _
            refine ⟨(fun _ => false : Fin 5 → Bool), ?_, ?_⟩ <;>
              dsimp [x2611_16458_edges, SimpleGraph.fromRel] <;> decide
        · letI : DecidableRel ((x2611_16458_edges 5 [(1,2),(2,3)]) ⊔
              (x2611_16458_edges 5 [])).Adj := by
            unfold x2611_16458_edges
            infer_instance
          rw [Nat.card_eq_fintype_card]
          decide
      · dsimp only
        rw [← Nat.card_eq_fintype_card]
        have hQ : SimpleGraph.fromEdgeSet {e | Sum.inl e ∈ ({Sum.inl s((0 : Fin 5),1), Sum.inr s((0 : Fin 5),2)} : Finset (Sym2 (Fin 5) ⊕ Sym2 (Fin 5)))} =
            x2611_16458_edges 5 [(1,2)] := by
          ext a b
          fin_cases a <;> fin_cases b <;>
            simp [E, SimpleGraph.fromEdgeSet_adj, x2611_16458_edges, SimpleGraph.fromRel_adj]
        have hR : SimpleGraph.fromEdgeSet {e | Sum.inr e ∈ ({Sum.inl s((0 : Fin 5),1), Sum.inr s((0 : Fin 5),2)} : Finset (Sym2 (Fin 5) ⊕ Sym2 (Fin 5)))} =
            x2611_16458_edges 5 [(1,3)] := by
          ext a b
          fin_cases a <;> fin_cases b <;>
            simp [E, SimpleGraph.fromEdgeSet_adj, x2611_16458_edges, SimpleGraph.fromRel_adj]
        rw [hQ, hR]
        constructor
        · constructor
          · intro _
            decide
          · intro _
            refine ⟨(fun v => decide (v = 2) : Fin 5 → Bool), ?_, ?_⟩ <;>
              dsimp [x2611_16458_edges, SimpleGraph.fromRel] <;> decide
        · letI : DecidableRel ((x2611_16458_edges 5 [(1,2)]) ⊔
              (x2611_16458_edges 5 [(1,3)])).Adj := by
            unfold x2611_16458_edges
            infer_instance
          rw [Nat.card_eq_fintype_card]
          decide
      · dsimp only
        rw [← Nat.card_eq_fintype_card]
        have hQ : SimpleGraph.fromEdgeSet {e | Sum.inl e ∈ ({Sum.inl s((1 : Fin 5),2), Sum.inr s((0 : Fin 5),2)} : Finset (Sym2 (Fin 5) ⊕ Sym2 (Fin 5)))} =
            x2611_16458_edges 5 [(2,3)] := by
          ext a b
          fin_cases a <;> fin_cases b <;>
            simp [E, SimpleGraph.fromEdgeSet_adj, x2611_16458_edges, SimpleGraph.fromRel_adj]
        have hR : SimpleGraph.fromEdgeSet {e | Sum.inr e ∈ ({Sum.inl s((1 : Fin 5),2), Sum.inr s((0 : Fin 5),2)} : Finset (Sym2 (Fin 5) ⊕ Sym2 (Fin 5)))} =
            x2611_16458_edges 5 [(1,3)] := by
          ext a b
          fin_cases a <;> fin_cases b <;>
            simp [E, SimpleGraph.fromEdgeSet_adj, x2611_16458_edges, SimpleGraph.fromRel_adj]
        rw [hQ, hR]
        constructor
        · constructor
          · intro _
            decide
          · intro _
            refine ⟨(fun v => decide (v = 0) : Fin 5 → Bool), ?_, ?_⟩ <;>
              dsimp [x2611_16458_edges, SimpleGraph.fromRel] <;> decide
        · letI : DecidableRel ((x2611_16458_edges 5 [(2,3)]) ⊔
              (x2611_16458_edges 5 [(1,3)])).Adj := by
            unfold x2611_16458_edges
            infer_instance
          rw [Nat.card_eq_fintype_card]
          decide
      · dsimp only
        rw [← Nat.card_eq_fintype_card]
        have hQ : SimpleGraph.fromEdgeSet {e | Sum.inl e ∈ E} =
            x2611_16458_edges 5 [(1,2),(2,3)] := by
          ext a b
          fin_cases a <;> fin_cases b <;>
            simp [E, SimpleGraph.fromEdgeSet_adj, x2611_16458_edges, SimpleGraph.fromRel_adj]
        have hR : SimpleGraph.fromEdgeSet {e | Sum.inr e ∈ E} =
            x2611_16458_edges 5 [(1,3)] := by
          ext a b
          fin_cases a <;> fin_cases b <;>
            simp [E, SimpleGraph.fromEdgeSet_adj, x2611_16458_edges, SimpleGraph.fromRel_adj]
        rw [hQ, hR]
        constructor
        · simp only [ne_self_iff_false, iff_false]
          rintro ⟨ε, hp, hn⟩
          exact (hn 0 2 (by decide)) ((hp 0 1 (by decide)).trans (hp 1 2 (by decide)))
        · letI : DecidableRel ((x2611_16458_edges 5 [(1,2),(2,3)]) ⊔
              (x2611_16458_edges 5 [(1,3)])).Adj := by
            unfold x2611_16458_edges
            infer_instance
          rw [Nat.card_eq_fintype_card]
          decide
    calc
      _ = ∑ F ∈ E.powerset, if F = E then (0 : Polynomial ℤ) else
          Polynomial.C ((-1 : ℤ)^F.card) * Polynomial.X ^ (5-F.card) := by
        apply Finset.sum_congr rfl
        intro F hF
        dsimp only at hc ⊢
        by_cases hf : F = E
        · have hh := not_iff_not.mpr (hc F hF).1
          have hn : ¬ x2611_16458_balanced (SimpleGraph.fromEdgeSet {e | Sum.inl e ∈ F})
              (SimpleGraph.fromEdgeSet {e | Sum.inr e ∈ F}) := hh.mpr (by simpa using hf)
          simp only [if_neg hn, if_pos hf]
        · have hh := (hc F hF).1.mpr hf
          simp [hh, hf, (hc F hF).2]
      _ = _ := by
        rw [hep]
        repeat rw [Finset.sum_insert (by decide)]
        simp only [Finset.sum_singleton, Finset.sum_empty]
        have hne : (∅ : Finset (Sym2 (Fin 5) ⊕ Sym2 (Fin 5))) ≠ E ∧
            {Sum.inl s((0 : Fin 5),1)} ≠ E ∧
            {Sum.inl s((1 : Fin 5),2)} ≠ E ∧
            {Sum.inr s((0 : Fin 5),2)} ≠ E ∧
            {Sum.inl s((0 : Fin 5),1), Sum.inl s((1 : Fin 5),2)} ≠ E ∧
            {Sum.inl s((0 : Fin 5),1), Sum.inr s((0 : Fin 5),2)} ≠ E ∧
            {Sum.inl s((1 : Fin 5),2), Sum.inr s((0 : Fin 5),2)} ≠ E := by decide
        rcases hne with ⟨hn0, hn1, hn2, hn3, hn4, hn5, hn6⟩
        have hc4 : ({Sum.inl s((0 : Fin 5),1), Sum.inl s((1 : Fin 5),2)} :
            Finset (Sym2 (Fin 5) ⊕ Sym2 (Fin 5))).card = 2 := by decide
        have hc5 : ({Sum.inl s((0 : Fin 5),1), Sum.inr s((0 : Fin 5),2)} :
            Finset (Sym2 (Fin 5) ⊕ Sym2 (Fin 5))).card = 2 := by decide
        have hc6 : ({Sum.inl s((1 : Fin 5),2), Sum.inr s((0 : Fin 5),2)} :
            Finset (Sym2 (Fin 5) ⊕ Sym2 (Fin 5))).card = 2 := by decide
        norm_num [hn0, hn1, hn2, hn3, hn4, hn5, hn6, hc4, hc5, hc6]
        ring
  have hcomp : (x2611_16458_zeroFree (x2611_16458_edges 5 [(1,2),(2,3)])
      (x2611_16458_edges 5 [(1,3)])).comp (Polynomial.X - 1) =
      (Polynomial.X - 1) ^ 3 * (Polynomial.X ^ 2 - 5 * Polynomial.X + 7) := by
    rw [hz]
    simp only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.sub_comp,
      Polynomial.add_comp, Polynomial.X_comp, Polynomial.ofNat_comp]
    ring
  have hhpoly : x2611_16458_numerator 5
      (x2611_16458_zeroFree (x2611_16458_edges 5 [(1,2),(2,3)])
        (x2611_16458_edges 5 [(1,3)])) =
      Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 + 48 * Polynomial.X ^ 4 +
        62 * Polynomial.X ^ 5 + 7 * Polynomial.X ^ 6 := by
    rw [hz]
    norm_num [x2611_16458_numerator, Finset.sum_range_succ, Nat.choose]
  have heval : (x2611_16458_zeroFree (x2611_16458_edges 5 [(1,2),(2,3)])
      (x2611_16458_edges 5 [(1,3)])).eval 1 = 1 := by
    rw [hz]
    norm_num
  refine ⟨hz, hcomp, hhpoly, ?_, heval, ?_⟩
  · rw [hhpoly]
    intro i
    simp only [Polynomial.coeff_add, Polynomial.coeff_ofNat_mul, Polynomial.coeff_X_pow]
    positivity
  · classical
    rintro ⟨m, G, hG⟩
    have hg : G = ⊥ := by
      by_contra hne
      have hu := x2611_16458_ex4_4_aux2 G
      rw [if_neg hne, hG, heval] at hu
      norm_num at hu
    rw [hg, x2611_16458_ex4_4_aux3, Nat.card_fin, hz] at hG
    have hG' : (Polynomial.X ^ m : Polynomial ℤ) =
        Polynomial.X ^ 5 - 3 * Polynomial.X ^ 4 + 3 * Polynomial.X ^ 3 := by
      rw [hG]
      ring
    have hc := congrArg (fun p : Polynomial ℤ => p.coeff 3) hG'
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_ofNat_mul,
      Polynomial.coeff_X_pow] at hc
    norm_num at hc
    split_ifs at hc <;> norm_num at hc
end

-- forge:entry x2611_15505_eq5 kind=proved origin=paper
section
/- Section 4.1, equation (5) -/
open scoped BigOperators

lemma x2611_15505_eq5_aux1 (m : ℕ) (f : Polynomial ℝ) (x y : ℕ → ℝ)
    (hx : x2611_15505_ordered_roots f m (fun i => x i))
    (hy : x2611_15505_ordered_roots f.derivative (m - 1) (fun i => y i)) :
    ∀ i : Fin (m - 1), x i.val < y i.val ∧ y i.val < x (i.val + 1) := by
  classical
  have hr (i : Fin m) : f.eval (x i) = 0 := by
    apply (Polynomial.mem_roots hx.1).mp
    rw [hx.2.2.2]
    exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  have hex (i : Fin (m - 1)) : ∃ j : Fin (m - 1),
      x i.val < y j.val ∧ y j.val < x (i.val + 1) := by
    have hlt : x i.val < x (i.val + 1) :=
      hx.2.2.1 (show (⟨i.val, by omega⟩ : Fin m) < ⟨i.val + 1, by omega⟩ from by change i.val < i.val + 1; omega)
    obtain ⟨t, ht, hd⟩ := exists_deriv_eq_zero hlt f.continuousOn
      ((hr ⟨i.val, by omega⟩).trans (hr ⟨i.val + 1, by omega⟩).symm)
    have hd' : t ∈ f.derivative.roots := by
      apply (Polynomial.mem_roots hy.1).mpr
      simpa only [Polynomial.IsRoot, f.deriv] using hd
    rw [hy.2.2.2] at hd'
    obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hd'
    exact ⟨j, ht⟩
  choose g hg using hex
  have hgmono : StrictMono g := by
    intro i j hij
    apply hy.2.2.1.lt_iff_lt.mp
    have hle : x (i.val + 1) ≤ x j.val :=
      hx.2.2.1.monotone (show (⟨i.val + 1, by omega⟩ : Fin m) ≤ ⟨j.val, by omega⟩ from hij)
    exact (hg i).2.trans_le (hle.trans (hg j).1.le)
  have hgid := hgmono.eq_id
  intro i
  simpa [hgid] using hg i

lemma x2611_15505_eq5_aux2 (m : ℕ) (f : Polynomial ℝ) (x : Fin m → ℝ)
    (hx : x2611_15505_ordered_roots f m x) (t : ℝ)
    (hnt : ∀ i, t ≠ x i) (hd : f.derivative.eval t = 0) :
    ∑ i : Fin m, 1 / (t - x i) = 0 := by
  classical
  have hs : f.Splits := Polynomial.splits_iff_card_roots.mpr (by simp [hx.2.2.2, hx.2.1])
  have hn : f.eval t ≠ 0 := by
    intro h
    have ht := (Polynomial.mem_roots hx.1).mpr h
    rw [hx.2.2.2] at ht
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp ht
    exact hnt i hi.symm
  have h := hs.eval_derivative_div_eval_of_ne_zero hn
  rw [hd, zero_div, hx.2.2.2, Multiset.map_map] at h
  simpa [List.sum_ofFn] using h.symm

lemma x2611_15505_eq5_aux3 (m k : ℕ) (hkm : k ≤ m) (a b : ℝ) :
    (∑ i ∈ Finset.range m, if i < k then a else b) =
      (k : ℝ) * a + ((m - k : ℕ) : ℝ) * b := by
  rw [← Finset.sum_range_add_sum_Ico _ hkm]
  congr 1
  · simp only [Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.mp hi))]
    simp
  · have h : (∑ i ∈ Finset.Ico k m, if i < k then a else b) =
        ∑ i ∈ Finset.Ico k m, b := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [if_neg (by have := (Finset.mem_Ico.mp hi).1; omega)]
    rw [h]
    simp

lemma x2611_15505_eq5_aux4 (m k : ℕ) (hm : 3 ≤ m) (hk : 1 ≤ k) (hkm : k < m)
    (x : ℕ → ℝ) (hx : ∀ i j, i < j → j < m → x i < x j)
    (t : ℝ) (ha : x (k - 1) < t) (hb : t < x k)
    (hs : (∑ i ∈ Finset.range m, 1 / (t - x i)) = 0) :
    1 / (t - x (k - 1)) + ((m - k : ℕ) : ℝ) / (t - x k) < 0 ∧
    0 < (k : ℝ) / (t - x (k - 1)) + 1 / (t - x k) := by
  classical
  let A := 1 / (t - x (k - 1))
  let B := 1 / (t - x k)
  let v := fun i => 1 / (t - x i)
  let L := fun i => (if i = k - 1 then A else 0) + (if i < k then 0 else B)
  let U := fun i => (if i < k then A else 0) + (if i = k then B else 0)
  have hta : 0 < t - x (k - 1) := sub_pos.mpr ha
  have htb : t - x k < 0 := sub_neg.mpr hb
  have hleft (i : ℕ) (hi : i < k) : x i ≤ x (k - 1) := by
    by_cases he : i = k - 1
    · simp [he]
    · exact (hx i (k - 1) (by omega) (by omega)).le
  have hright (i : ℕ) (hi : k ≤ i) (him : i < m) : x k ≤ x i := by
    by_cases he : i = k
    · simp [he]
    · exact (hx k i (by omega) him).le
  have hbounds (i : ℕ) (him : i < m) : L i ≤ v i ∧ v i ≤ U i := by
    by_cases hi : i < k
    · have hxi := hleft i hi
      have hp : 0 < t - x i := by linarith
      have hr : v i ≤ A := one_div_le_one_div_of_le hta (by linarith)
      have hne : i ≠ k := by omega
      dsimp [L, U]
      simp only [if_pos hi, if_neg hne, add_zero]
      by_cases he : i = k - 1
      · subst i; simp [v, A]
      · rw [if_neg he]
        exact ⟨(one_div_pos.mpr hp).le, hr⟩
    · have hxi := hright i (by omega) him
      have hn : t - x i < 0 := by linarith
      have hr : B ≤ v i := one_div_le_one_div_of_neg_of_le htb (by linarith)
      have hne : i ≠ k - 1 := by omega
      dsimp [L, U]
      simp only [if_neg hi, if_neg hne, zero_add]
      by_cases he : i = k
      · subst i; simp [v, B]
      · rw [if_neg he]
        exact ⟨hr, (one_div_neg.mpr hn).le⟩
  have hstrict : ∃ i ∈ Finset.range m, L i < v i ∧ v i < U i := by
    by_cases hk1 : k = 1
    · refine ⟨2, Finset.mem_range.mpr (by omega), ?_⟩
      have hxx : x k < x 2 := hx k 2 (by omega) (by omega)
      have hn : t - x 2 < 0 := by linarith
      have hr : B < v 2 := one_div_lt_one_div_of_neg_of_lt htb (by linarith)
      simpa [L, U, hk1, v] using And.intro hr (one_div_neg.mpr hn)
    · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
      have hxx : x 0 < x (k - 1) := hx 0 (k - 1) (by omega) (by omega)
      have hp : 0 < t - x 0 := by linarith
      have hr : v 0 < A := one_div_lt_one_div_of_lt hta (by linarith)
      have hne : 0 ≠ k - 1 := by omega
      have hne' : 0 ≠ k := by omega
      simpa [L, U, hne, hne', show 0 < k by omega, v] using
        And.intro (one_div_pos.mpr hp) hr
  have hL : (∑ i ∈ Finset.range m, L i) < 0 := by
    rw [← hs]
    apply Finset.sum_lt_sum
    · intro i hi; exact (hbounds i (Finset.mem_range.mp hi)).1
    · obtain ⟨i, hi, h⟩ := hstrict
      exact ⟨i, hi, h.1⟩
  have hU : 0 < (∑ i ∈ Finset.range m, U i) := by
    rw [← hs]
    apply Finset.sum_lt_sum
    · intro i hi; exact (hbounds i (Finset.mem_range.mp hi)).2
    · obtain ⟨i, hi, h⟩ := hstrict
      exact ⟨i, hi, h.2⟩
  have heL : (∑ i ∈ Finset.range m, L i) = A + ((m - k : ℕ) : ℝ) * B := by
    simp only [L, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
    rw [x2611_15505_eq5_aux3 m k (by omega)]
    ring
  have heU : (∑ i ∈ Finset.range m, U i) = (k : ℝ) * A + B := by
    simp only [U, Finset.sum_add_distrib]
    rw [x2611_15505_eq5_aux3 m k (by omega)]
    simp [Finset.sum_ite_eq', hkm]
  rw [heL] at hL
  rw [heU] at hU
  simpa [A, B, div_eq_mul_inv] using And.intro hL hU

theorem x2611_15505_eq5 (m : ℕ) (hm : 3 ≤ m) (f : Polynomial ℝ) (x y : ℕ → ℝ)
  (hx : x2611_15505_ordered_roots f m (fun i => x i))
  (hy : x2611_15505_ordered_roots f.derivative (m - 1) (fun i => y i))
  (k : ℕ) (hk1 : 1 ≤ k) (hkm : k < m) :
  (((m : ℝ) - (k : ℝ)) * x (k - 1) + x k) / ((m : ℝ) - (k : ℝ) + 1) < y (k - 1) ∧
  y (k - 1) < (x (k - 1) + (k : ℝ) * x k) / ((k : ℝ) + 1) := by
  classical
  have hmon (i j : ℕ) (hij : i < j) (hjm : j < m) : x i < x j :=
    hx.2.2.1 (show (⟨i, by omega⟩ : Fin m) < ⟨j, hjm⟩ from hij)
  have hgap := x2611_15505_eq5_aux1 m f x y hx hy ⟨k - 1, by omega⟩
  have hkp : k - 1 + 1 = k := by omega
  simp only [hkp] at hgap
  have hnt (i : Fin m) : y (k - 1) ≠ x i := by
    by_cases hi : i.val < k
    · have hle : x i ≤ x (k - 1) := by
        by_cases he : i.val = k - 1
        · simp [he]
        · exact (hmon i (k - 1) (by omega) (by omega)).le
      exact ne_of_gt (hle.trans_lt hgap.1)
    · have hle : x k ≤ x i := by
        by_cases he : i.val = k
        · simp [he]
        · exact (hmon k i (by omega) i.isLt).le
      exact ne_of_lt (hgap.2.trans_le hle)
  have hd : f.derivative.eval (y (k - 1)) = 0 := by
    apply (Polynomial.mem_roots hy.1).mp
    rw [hy.2.2.2]
    exact Multiset.mem_map.mpr ⟨⟨k - 1, by omega⟩, by simp, rfl⟩
  have hs := x2611_15505_eq5_aux2 m f (fun i => x i) hx (y (k - 1)) hnt hd
  rw [Fin.sum_univ_eq_sum_range (fun i => 1 / (y (k - 1) - x i))] at hs
  obtain ⟨hL, hU⟩ := x2611_15505_eq5_aux4 m k hm hk1 hkm x hmon
    (y (k - 1)) hgap.1 hgap.2 hs
  have ha : 0 < y (k - 1) - x (k - 1) := sub_pos.mpr hgap.1
  have hb : 0 < x k - y (k - 1) := sub_pos.mpr hgap.2
  have hn : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := Nat.cast_sub hkm.le
  have hneg : y (k - 1) - x k = -(x k - y (k - 1)) := by ring
  rw [hneg, div_neg] at hL hU
  have hL' : 1 / (y (k - 1) - x (k - 1)) <
      ((m - k : ℕ) : ℝ) / (x k - y (k - 1)) := by linarith
  have hU' : 1 / (x k - y (k - 1)) <
      (k : ℝ) / (y (k - 1) - x (k - 1)) := by linarith
  have hcL := (div_lt_div_iff₀ ha hb).mp hL'
  have hcU := (div_lt_div_iff₀ hb ha).mp hU'
  rw [hn] at hcL
  have hmk : (k : ℝ) < m := by exact_mod_cast hkm
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  constructor
  · apply (div_lt_iff₀ (show (0 : ℝ) < (m : ℝ) - k + 1 by linarith)).mpr
    nlinarith
  · apply (lt_div_iff₀ (show (0 : ℝ) < (k : ℝ) + 1 by linarith)).mpr
    nlinarith
end

-- forge:entry x2611_15505_eq8 kind=proved origin=paper
section
/- Section 4.1, equation (8) -/
open scoped BigOperators

lemma x2611_15505_eq8_aux1 (n : ℕ) (p : Polynomial ℝ)
    (x : Fin (n + 1) → ℝ) (y : Fin n → ℝ)
    (hp : p ≠ 0) (hd : p.derivative ≠ 0)
    (hx : StrictMono x) (hy : StrictMono y)
    (hxr : p.roots = Finset.univ.val.map x)
    (hyr : p.derivative.roots = Finset.univ.val.map y) :
    ∀ i : Fin n, x i.castSucc < y i ∧ y i < x i.succ := by
  classical
  have hx0 (i : Fin (n + 1)) : p.eval (x i) = 0 := by
    apply (Polynomial.mem_roots hp).mp
    rw [hxr]
    exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  have hex (i : Fin n) : ∃ j : Fin n, x i.castSucc < y j ∧ y j < x i.succ := by
    obtain ⟨z, hz, hz0⟩ := exists_deriv_eq_zero
      (hx (Fin.castSucc_lt_succ (i := i))) p.continuousOn ((hx0 _).trans (hx0 _).symm)
    have hzm : z ∈ p.derivative.roots := by
      apply (Polynomial.mem_roots hd).mpr
      simpa only [Polynomial.IsRoot, p.deriv] using hz0
    rw [hyr] at hzm
    obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hzm
    exact ⟨j, hz⟩
  choose g hg using hex
  have hgm : StrictMono g := by
    intro i j hij
    apply hy.lt_iff_lt.mp
    have hxx : x i.succ ≤ x j.castSucc := hx.monotone (by simpa using hij)
    exact (hg i).2.trans_le (hxx.trans (hg j).1.le)
  have hgid : g = id := hgm.eq_id
  simpa only [hgid, id_eq] using hg

lemma x2611_15505_eq8_aux2 {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (u v : ℝ) (hz : ∀ i, u < z i ∧ z i < v) :
    (Fintype.card ι : ℝ) * ((∑ i, 1 / (z i - u)) + ∑ i, 1 / (v - z i)) ≤
      (v - u) * (∑ i, 1 / (z i - u)) * ∑ i, 1 / (v - z i) := by
  classical
  have hav : Antivary (fun i => 1 / (z i - u)) (fun i => 1 / (v - z i)) := by
    intro i j hij
    have hzi : 0 < v - z i := sub_pos.mpr (hz i).2
    have hzj : 0 < v - z j := sub_pos.mpr (hz j).2
    have hzij : z i < z j := by
      have := (one_div_lt_one_div hzi hzj).mp hij
      linarith
    exact one_div_le_one_div_of_le (sub_pos.mpr (hz i).1) (by linarith)
  have hc := hav.card_mul_sum_le_sum_mul_sum
  have hi (i : ι) :
      (v - u) * ((1 / (z i - u)) * (1 / (v - z i))) =
        1 / (z i - u) + 1 / (v - z i) := by
    field_simp [(sub_pos.mpr (hz i).1).ne', (sub_pos.mpr (hz i).2).ne']
    <;> ring
  have he : (v - u) * (∑ i, (1 / (z i - u)) * (1 / (v - z i))) =
      (∑ i, 1 / (z i - u)) + ∑ i, 1 / (v - z i) := by
    rw [Finset.mul_sum]
    simp_rw [hi]
    rw [Finset.sum_add_distrib]
  by_cases h : Nonempty ι
  · obtain ⟨i⟩ := h
    have huv : 0 ≤ v - u := by have := hz i; linarith
    have hc' := mul_le_mul_of_nonneg_left hc huv
    rw [← mul_assoc, mul_comm (v - u) (Fintype.card ι : ℝ), mul_assoc, he] at hc'
    simpa only [mul_assoc] using hc'
  · haveI : IsEmpty ι := not_nonempty_iff.mp h
    simp

lemma x2611_15505_eq8_aux3 (k a b u v : ℝ) (hk : 0 ≤ k)
    (hau : a < u) (huv : u < v) (hvb : v < b)
    (hc : k * ((1 / (u - a) + 1 / (u - b)) +
        (-(1 / (v - a) + 1 / (v - b)))) ≤
      (v - u) * (1 / (u - a) + 1 / (u - b)) *
        (-(1 / (v - a) + 1 / (v - b)))) :
    Real.sqrt (k / (k + 2)) * (b - a) ≤ v - u := by
  let A := 1 / (u - a) + 1 / (u - b)
  let B := -(1 / (v - a) + 1 / (v - b))
  let D := (u - a) * (b - u)
  let E := (v - a) * (b - v)
  let L := a + b - 2 * u
  let R := 2 * v - a - b
  have hD : 0 < D := mul_pos (sub_pos.mpr hau) (sub_pos.mpr (huv.trans hvb))
  have hE : 0 < E := mul_pos (sub_pos.mpr (hau.trans huv)) (sub_pos.mpr hvb)
  have hA : A * D = L := by
    dsimp [A, D, L]
    field_simp [ne_of_gt (sub_pos.mpr hau), ne_of_lt (sub_neg.mpr (huv.trans hvb))]
    <;> ring
  have hB : B * E = R := by
    dsimp [B, E, R]
    field_simp [ne_of_gt (sub_pos.mpr (hau.trans huv)), ne_of_lt (sub_neg.mpr hvb)]
    <;> ring
  change k * (A + B) ≤ (v - u) * A * B at hc
  have hc' : k * (L * E + R * D) ≤ (v - u) * L * R := by
    calc
      k * (L * E + R * D) = (k * (A + B)) * (D * E) := by rw [← hA, ← hB]; ring
      _ ≤ ((v - u) * A * B) * (D * E) := mul_le_mul_of_nonneg_right hc (mul_pos hD hE).le
      _ = (v - u) * L * R := by rw [← hA, ← hB]; ring
  have hi : 2 * (L * E + R * D) = (v - u) * ((b - a) ^ 2 - L * R) := by
    dsimp [L, R, D, E]
    ring
  have hmain : k * (b - a) ^ 2 ≤ (k + 2) * (L * R) := by
    have hh : (v - u) * (k * (b - a) ^ 2 - (k + 2) * (L * R)) ≤ 0 := by
      nlinarith only [hc', hi]
    exact le_of_sub_nonpos (nonpos_of_mul_nonpos_right hh (sub_pos.mpr huv))
  have hLR : L * R ≤ (v - u) ^ 2 := by
    dsimp [L, R]
    nlinarith only [sq_nonneg (a + b - u - v)]
  have hsq : k / (k + 2) * (b - a) ^ 2 ≤ (v - u) ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : 0 < k + 2)]
    have hh := mul_le_mul_of_nonneg_left hLR (by linarith : 0 ≤ k + 2)
    nlinarith only [hmain, hh]
  have hs : (Real.sqrt (k / (k + 2))) ^ 2 = k / (k + 2) :=
    Real.sq_sqrt (div_nonneg hk (by linarith))
  have hs' : (Real.sqrt (k / (k + 2)) * (b - a)) ^ 2 ≤ (v - u) ^ 2 := by
    simpa only [mul_pow, hs] using hsq
  exact le_of_sq_le_sq hs' (sub_pos.mpr huv).le

lemma x2611_15505_eq8_aux4 (n : ℕ) (p : Polynomial ℝ) (x : Fin n → ℝ)
    (hn : p.natDegree = n) (hr : p.roots = Finset.univ.val.map x)
    (u : ℝ) (hu : p.eval u ≠ 0) (hd : p.derivative.eval u = 0) :
    (∑ i, 1 / (u - x i)) = 0 := by
  classical
  have hs : p.Splits := Polynomial.splits_iff_card_roots.mpr (by simp [hr, hn])
  have hh := hs.eval_derivative_div_eval_of_ne_zero hu
  rw [hd, zero_div, hr, Multiset.map_map] at hh
  change 0 = ∑ i, 1 / (u - x i) at hh
  exact hh.symm

lemma x2611_15505_eq8_aux5 (n : ℕ) (p : Polynomial ℝ)
    (x : Fin (n + 1) → ℝ) (hp : p ≠ 0) (hx : StrictMono x)
    (hr : p.roots = Finset.univ.val.map x) (i : Fin n) (u : ℝ)
    (hu : x i.castSucc < u ∧ u < x i.succ) : p.eval u ≠ 0 := by
  classical
  intro h
  have hm := (Polynomial.mem_roots hp).mpr h
  rw [hr] at hm
  obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp hm
  by_cases hji : j ≤ i.castSucc
  · have hh := hx.monotone hji
    rw [hj] at hh
    linarith [hu.1]
  · have hji' : i.succ ≤ j := by simpa only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] using
      (Nat.succ_le_of_lt (show i.val < j.val from not_le.mp hji))
    have hh := hx.monotone hji'
    rw [hj] at hh
    linarith [hu.2]

theorem x2611_15505_eq8 (m : ℕ) (hm : 3 ≤ m) (f : Polynomial ℝ) (x y : ℕ → ℝ)
  (hx : x2611_15505_ordered_roots f m (fun i => x i))
  (hy : x2611_15505_ordered_roots f.derivative (m - 1) (fun i => y i)) :
  Real.sqrt (((m : ℝ) - 2) / (m : ℝ)) * (x (m - 1) - x 0) ≤
    y (m - 2) - y 0 := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 3 := ⟨m - 3, by omega⟩
  have hy' : x2611_15505_ordered_roots f.derivative (n + 2) (fun i => y i) := by
    exact hy
  rcases hx with ⟨hf, hdeg, hxm, hxr⟩
  rcases hy' with ⟨hdf, hddeg, hym, hyr⟩
  let X : Fin (n + 3) → ℝ := fun i => x i
  let Y : Fin (n + 2) → ℝ := fun i => y i
  have hi := x2611_15505_eq8_aux1 (n + 2) f X Y hf hdf hxm hym hxr hyr
  let a := x 0
  let b := x (n + 2)
  let u := y 0
  let v := y (n + 1)
  let z : Fin (n + 1) → ℝ := fun i => X i.castSucc.succ
  have hau : a < u := (hi 0).1
  have hvb : v < b := (hi (Fin.last (n + 1))).2
  have huv : u < v := hym (show (0 : Fin (n + 2)) < Fin.last (n + 1) by
    change (0 : ℕ) < n + 1
    omega)
  have hz : ∀ i, u < z i ∧ z i < v := by
    intro i
    constructor
    · have hh := (hi 0).2
      have hh' : X (0 : Fin (n + 2)).succ ≤ z i := hxm.monotone (show
          (0 : Fin (n + 2)).succ ≤ i.castSucc.succ from by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_zero, Fin.val_castSucc]
        omega)
      exact hh.trans_le hh'
    · have hh := (hi (Fin.last (n + 1))).1
      have hh' : z i ≤ X (Fin.last (n + 1)).castSucc := hxm.monotone (show
          i.castSucc.succ ≤ (Fin.last (n + 1)).castSucc from by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc, Fin.val_last]
        omega)
      exact hh'.trans_lt hh
  have hu0 : f.eval u ≠ 0 :=
    x2611_15505_eq8_aux5 (n + 2) f X hf hxm hxr 0 u (hi 0)
  have hv0 : f.eval v ≠ 0 :=
    x2611_15505_eq8_aux5 (n + 2) f X hf hxm hxr (Fin.last (n + 1)) v
      (hi (Fin.last (n + 1)))
  have hdroot (i : Fin (n + 2)) : f.derivative.eval (Y i) = 0 := by
    apply (Polynomial.mem_roots hdf).mp
    rw [hyr]
    exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  have hlu := x2611_15505_eq8_aux4 (n + 3) f X hdeg hxr u hu0 (hdroot 0)
  have hlv := x2611_15505_eq8_aux4 (n + 3) f X hdeg hxr v hv0 (hdroot (Fin.last (n + 1)))
  have hsum (t : ℝ) : (∑ i, 1 / (t - X i)) =
      1 / (t - a) + (∑ i, 1 / (t - z i)) + 1 / (t - b) := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
    rfl
  rw [hsum] at hlu hlv
  have hneg : (∑ i, 1 / (u - z i)) = -(∑ i, 1 / (z i - u)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [show u - z i = -(z i - u) by ring, div_neg]
  have hA : (∑ i, 1 / (z i - u)) = 1 / (u - a) + 1 / (u - b) := by
    rw [hneg] at hlu
    linarith only [hlu]
  have hB : (∑ i, 1 / (v - z i)) = -(1 / (v - a) + 1 / (v - b)) := by
    linarith only [hlv]
  have hc := x2611_15505_eq8_aux2 z u v hz
  rw [hA, hB, Fintype.card_fin] at hc
  have hr := x2611_15505_eq8_aux3 (n + 1 : ℕ) a b u v (Nat.cast_nonneg _) hau huv hvb hc
  have hratio : (((n + 3 : ℕ) : ℝ) - 2) / ((n + 3 : ℕ) : ℝ) =
      (n + 1 : ℕ) / ((n + 1 : ℕ) + (2 : ℝ)) := by
    push_cast
    ring
  simpa only [show n + 3 - 1 = n + 2 by omega,
    show n + 3 - 2 = n + 1 by omega, hratio, a, b, u, v] using hr
end

-- forge:entry x2611_16899_thm1_eq2_s1h1_s1h2 kind=proved origin=decomposition
section
/- x2611_16899_thm1_eq2_s1h1 的证明骨架中第 2 个空洞 -/
open scoped BigOperators
open MvPolynomial

lemma x2611_16899_thm1_eq2_s1h1_s1h2_aux1
    {σ R : Type*} [CommSemiring R] (w : σ → ℕ)
    (p q : MvPolynomial σ R) (D : ℕ) (hp : p.IsWeightedHomogeneous w D)
    (m : σ →₀ ℕ) (hm : Finsupp.weight w m < D) : coeff m (p * q) = 0 := by
  classical
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ab hab
  by_cases h : coeff ab.1 p = 0
  · simp [h]
  · have he := hp h
    have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have hw := congrArg (Finsupp.weight w) hs
    rw [map_add, he] at hw
    omega

lemma x2611_16899_thm1_eq2_s1h1_s1h2_aux2
    {σ R : Type*} [CommRing R] (w : σ → ℕ) (a b : σ)
    (ha : w a = 1) (hb : w b = 1) (t : R) (N : ℕ) :
    IsWeightedHomogeneous w
      ((X b - X a) * ∑ k ∈ Finset.range (N + 1), C (t ^ k) * X a ^ k * X b ^ (N-k))
      (N + 1) := by
  have hxa : IsWeightedHomogeneous w (X a : MvPolynomial σ R) 1 := by
    simpa [ha] using isWeightedHomogeneous_X (R := R) w a
  have hxb : IsWeightedHomogeneous w (X b : MvPolynomial σ R) 1 := by
    simpa [hb] using isWeightedHomogeneous_X (R := R) w b
  have hs : IsWeightedHomogeneous w
      (∑ k ∈ Finset.range (N + 1), C (t ^ k) * X a ^ k * X b ^ (N-k)) N := by
    apply IsWeightedHomogeneous.sum
    intro k hk
    have hk' : k ≤ N := by simpa using hk
    simpa [Nat.sub_add_cancel hk', Nat.add_sub_of_le hk'] using
      (((hxa.pow k).C_mul (t ^ k)).mul (hxb.pow (N-k)))
  simpa [Nat.add_comm] using (hxb.sub hxa).mul hs

lemma x2611_16899_thm1_eq2_s1h1_s1h2_aux3
    (n N : ℕ) (i : Fin n) :
    (∑ ab : Fin n × Fin n, if ab.1 < ab.2 ∧ ab.2 ≤ i then N else 0) =
      N * ∑ b : Fin n, if b ≤ i then b.val else 0 := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hbi : b ≤ i
  · simp only [hbi, and_true, if_true]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc : (Finset.univ.filter (fun a : Fin n => a < b)).card = b.val := by
      have hf : Finset.univ.filter (fun a : Fin n => a < b) = Finset.Iio b := by
        ext a; simp
      rw [hf]
      exact Fin.card_Iio b
    rw [hc, Nat.mul_comm]
    simp
  · simp [hbi]

lemma x2611_16899_thm1_eq2_s1h1_s1h2_aux4
    {σ R : Type*} [DecidableEq σ] [CommRing R] [IsAddTorsionFree R]
    (i j : σ) (m : σ →₀ ℕ) (hm : m i = m j)
    (p : MvPolynomial σ R) (hp : rename (Equiv.swap i j) p = -p) : coeff m p = 0 := by
  have he : m.mapDomain (Equiv.swap i j) = m := by
    ext k
    rw [Finsupp.mapDomain_equiv_apply]
    by_cases hki : k = i
    · subst k; simp [hm]
    by_cases hkj : k = j
    · subst k; simp [hm]
    simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hc := coeff_rename_mapDomain (Equiv.swap i j) (Equiv.swap i j).injective p m
  rw [he, hp, coeff_neg] at hc
  have : (2 : ℕ) • coeff m p = (2 : ℕ) • (0 : R) := by
    simp only [two_nsmul, add_zero]
    linear_combination -hc
  exact nsmul_right_injective (by decide : (2 : ℕ) ≠ 0) this

lemma x2611_16899_thm1_eq2_s1h1_s1h2_aux5
    (n : ℕ) (i j : Fin n) (hij : j.val = i.val + 1) (a b : Fin n) :
    (a < b ∧ (a,b) ≠ (i,j)) ↔
      ((Equiv.swap i j) a < (Equiv.swap i j) b ∧
        ((Equiv.swap i j) a, (Equiv.swap i j) b) ≠ (i,j)) := by
  have hf : ∀ a b : Fin n, a < b ∧ (a,b) ≠ (i,j) →
      (Equiv.swap i j) a < (Equiv.swap i j) b ∧
        ((Equiv.swap i j) a, (Equiv.swap i j) b) ≠ (i,j) := by
    intro a b h
    have hne : i ≠ j := by intro he; subst j; omega
    by_cases hai : a = i <;> by_cases haj : a = j <;>
      by_cases hbi : b = i <;> by_cases hbj : b = j <;>
      simp_all [Equiv.swap_apply_def, Prod.mk.injEq] <;> omega
  constructor
  · exact hf a b
  · intro h
    simpa using hf ((Equiv.swap i j) a) ((Equiv.swap i j) b) h

lemma x2611_16899_thm1_eq2_s1h1_s1h2_aux6
    (n N : ℕ) (t : RatFunc ℚ) (i j : Fin n) (hij : j.val = i.val + 1) :
    rename (Equiv.swap i j)
      (∏ ab : Fin n × Fin n, if ab.1 < ab.2 ∧ ab ≠ (i,j) then
        (X ab.2 - X ab.1) * ∑ k ∈ Finset.range (N+1),
          C (t^k) * X ab.1^k * X ab.2^(N-k) else 1) =
      (∏ ab : Fin n × Fin n, if ab.1 < ab.2 ∧ ab ≠ (i,j) then
        (X ab.2 - X ab.1) * ∑ k ∈ Finset.range (N+1),
          C (t^k) * X ab.1^k * X ab.2^(N-k) else 1) := by
  classical
  rw [map_prod]
  apply Fintype.prod_equiv (Equiv.prodCongr (Equiv.swap i j) (Equiv.swap i j))
  intro ab
  have hc := x2611_16899_thm1_eq2_s1h1_s1h2_aux5 n i j hij ab.1 ab.2
  by_cases h : ab.1 < ab.2 ∧ ab ≠ (i,j)
  · have hh := hc.mp h
    simp [h, hh, map_sum, Prod.map_def]
  · have hh := mt hc.mpr h
    simp only [map_one, Equiv.prodCongr_apply, Prod.map_def, if_neg h, if_neg hh]

lemma x2611_16899_thm1_eq2_s1h1_s1h2_aux7
    (n N : ℕ) (i : Fin n) :
    Finsupp.weight (fun b : Fin n => if b ≤ i then 1 else 0)
      (Finsupp.equivFunOnFinite.symm (fun b : Fin n => 1 + N * b.val)) =
      N * (∑ b : Fin n, if b ≤ i then b.val else 0) + (i.val + 1) := by
  classical
  rw [Finsupp.weight_eq_sum]
  simp only [Finsupp.coe_equivFunOnFinite_symm, smul_eq_mul]
  have he (b : Fin n) : (1 + N * b.val) * (if b ≤ i then 1 else 0) =
      N * (if b ≤ i then b.val else 0) + (if b ≤ i then 1 else 0) := by
    split_ifs <;> simp [Nat.add_comm]
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  simp only [mul_one, Nat.cast_id]
  have hf : Finset.univ.filter (fun b : Fin n => b ≤ i) = Finset.Iic i := by
    ext b; simp
  rw [hf]
  exact Fin.card_Iic i

lemma x2611_16899_thm1_eq2_s1h1_s1h2_aux8
    (n : ℕ) (t : RatFunc ℚ) (i j : Fin n) (hij : j.val = i.val + 1)
    (h : MvPolynomial (Fin n) (RatFunc ℚ)) :
    coeff (Finsupp.equivFunOnFinite.symm (fun b : Fin n => 1 + (n+1) * b.val))
      (X i ^ (n+1) *
        (∏ ab : Fin n × Fin n, if ab.1 < ab.2 ∧ ab ≠ (i,j) then
          (X ab.2 - X ab.1) * ∑ k ∈ Finset.range (n+1),
            C (t^k) * X ab.1^k * X ab.2^(n-k) else 1) * h) = 0 := by
  classical
  let w : Fin n → ℕ := fun b => if b ≤ i then 1 else 0
  let F : Fin n × Fin n → MvPolynomial (Fin n) (RatFunc ℚ) := fun ab =>
    (X ab.2 - X ab.1) * ∑ k ∈ Finset.range (n+1), C (t^k) * X ab.1^k * X ab.2^(n-k)
  let Q := ∏ ab : Fin n × Fin n, if ab.1 < ab.2 ∧ ab.2 ≤ i then F ab else 1
  let R := ∏ ab : Fin n × Fin n, if ab.1 < ab.2 ∧ ab ≠ (i,j) then F ab else 1
  let D := ∑ ab : Fin n × Fin n, if ab.1 < ab.2 ∧ ab.2 ≤ i then n+1 else 0
  have hQ : IsWeightedHomogeneous w Q D := by
    apply IsWeightedHomogeneous.prod
    intro ab hab
    split_ifs with hc
    · apply x2611_16899_thm1_eq2_s1h1_s1h2_aux2
      · simp [w, le_trans (le_of_lt hc.1) hc.2]
      · simp [w, hc.2]
    · exact isWeightedHomogeneous_one _ _
  have hdvd : Q ∣ R := by
    apply Finset.prod_dvd_prod_of_dvd
    intro ab hab
    dsimp
    split_ifs with hc hd
    · exact dvd_refl _
    · exfalso
      apply hd
      refine ⟨hc.1, ?_⟩
      intro he
      have : j ≤ i := by simpa [he] using hc.2
      omega
    · exact one_dvd _
    · exact one_dvd _
  obtain ⟨r, hr⟩ := hdvd
  change coeff _ (X i ^ (n+1) * R * h) = 0
  rw [hr]
  have hx : IsWeightedHomogeneous w (X i ^ (n+1) : MvPolynomial (Fin n) (RatFunc ℚ)) (n+1) := by
    simpa [w] using (isWeightedHomogeneous_X (R := RatFunc ℚ) w i).pow (n+1)
  rw [show X i ^ (n+1) * (Q * r) * h = (X i ^ (n+1) * Q) * (r*h) by ring]
  apply x2611_16899_thm1_eq2_s1h1_s1h2_aux1 w _ _ _ (hx.mul hQ)
  have hw := x2611_16899_thm1_eq2_s1h1_s1h2_aux7 n (n+1) i
  have hD := x2611_16899_thm1_eq2_s1h1_s1h2_aux3 n (n+1) i
  change _ < (n+1)+D
  change D = _ at hD
  change Finsupp.weight w _ = _ at hw
  rw [hw, hD]
  have := i.isLt
  omega

lemma x2611_16899_thm1_eq2_s1h1_s1h2_aux9
    (n : ℕ) (i j : Fin n) (hij : j.val = i.val + 1)
    (R f : MvPolynomial (Fin n) (RatFunc ℚ))
    (hR : rename (Equiv.swap i j) R = R) :
    coeff (Finsupp.equivFunOnFinite.symm (fun b : Fin n => 1 + (n+1) * b.val))
      (X j ^ (n+1) * R * (f - rename (Equiv.swap i j) f)) = 0 := by
  classical
  let m := Finsupp.equivFunOnFinite.symm (fun b : Fin n => 1 + (n+1) * b.val)
  have hne : i ≠ j := by intro he; subst j; omega
  have hs : Finsupp.single j (n+1) ≤ m := by
    rw [Finsupp.single_le_iff]
    change n+1 ≤ 1+(n+1)*j.val
    have : 1 ≤ j.val := by omega
    nlinarith
  have hm : (m - Finsupp.single j (n+1)) i = (m - Finsupp.single j (n+1)) j := by
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_of_ne hne,
      Finsupp.single_eq_same, Nat.sub_zero]
    change 1+(n+1)*i.val = 1+(n+1)*j.val-(n+1)
    rw [hij, Nat.mul_add]
    omega
  rw [mul_assoc, X_pow_eq_monomial, coeff_monomial_mul', if_pos hs, one_mul]
  apply x2611_16899_thm1_eq2_s1h1_s1h2_aux4 i j _ hm
  rw [map_mul, map_sub, hR, rename_rename]
  have he : (⇑(Equiv.swap i j) : Fin n → Fin n) ∘ (Equiv.swap i j) = id := by
    funext k; simp
  rw [he, rename_id_apply]
  ring

lemma x2611_16899_thm1_eq2_s1h1_s1h2_aux10
    {α M : Type*} [Fintype α] [DecidableEq α] [CommMonoid M] (c : α → Prop) [DecidablePred c]
    (F : α → M) (a : α) (ha : c a) :
    (∏ b, if c b then F b else 1) =
      F a * ∏ b, if c b ∧ b ≠ a then F b else 1 := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ (fun b => if c b then F b else 1)
    (Finset.mem_univ a), if_pos ha]
  congr 1
  rw [← Finset.prod_erase Finset.univ (a := a)
    (show (if c a ∧ a ≠ a then F a else 1) = 1 by simp)]
  apply Finset.prod_congr rfl
  intro b hb
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  simp [hba]

lemma x2611_16899_thm1_eq2_s1h1_s1h2_aux11
    {R : Type*} [CommRing R] (x y t : R) (N : ℕ) :
    (y-t*x) * (∑ k ∈ Finset.range (N+1), t^k*x^k*y^(N-k)) =
      y^(N+1) - t^(N+1)*x^(N+1) := by
  have hs : (∑ k ∈ Finset.range (N+1), t^k*x^k*y^(N-k)) =
      ∑ k ∈ Finset.range (N+1), (t*x)^k*y^((N+1)-1-k) := by
    simp [mul_pow]
  rw [hs]
  have hg := (Commute.all (t*x) y).mul_neg_geom_sum₂ (N+1)
  simpa [mul_pow] using hg


theorem x2611_16899_thm1_eq2_s1h1_s1h2 : ∀ (n : ℕ) (τ : RatFunc ℚ) (i j : Fin n) (f g : MvPolynomial (Fin n) (RatFunc ℚ)), (↑j : ℕ) = (↑i : ℕ) + 1 → f.totalDegree ≤ n → (MvPolynomial.X i - MvPolynomial.X j) * g = (MvPolynomial.C : RatFunc ℚ → MvPolynomial (Fin n) (RatFunc ℚ)) (1 - τ) * MvPolynomial.X j * (f - (MvPolynomial.rename (⇑(Equiv.swap i j) : Fin n → Fin n) : MvPolynomial (Fin n) (RatFunc ℚ) → MvPolynomial (Fin n) (RatFunc ℚ)) f) + (MvPolynomial.C : RatFunc ℚ → MvPolynomial (Fin n) (RatFunc ℚ)) τ * (MvPolynomial.X i - MvPolynomial.X j) * (MvPolynomial.rename (⇑(Equiv.swap i j) : Fin n → Fin n) : MvPolynomial (Fin n) (RatFunc ℚ) → MvPolynomial (Fin n) (RatFunc ℚ)) f → MvPolynomial.coeff ((Finsupp.equivFunOnFinite.symm : (Fin n → ℕ) → Fin n →₀ ℕ) fun (i : Fin n) => 1 + (n + 1) * (↑i : ℕ)) (g * ∏ ij : Fin n × Fin n, if ij.1 < ij.2 then (MvPolynomial.X ij.2 - MvPolynomial.X ij.1) * ∑ k ∈ Finset.range (n + 1), (MvPolynomial.C : RatFunc ℚ → MvPolynomial (Fin n) (RatFunc ℚ)) (τ ^ k) * MvPolynomial.X ij.1 ^ k * MvPolynomial.X ij.2 ^ (n - k) else 1) = τ * MvPolynomial.coeff ((Finsupp.equivFunOnFinite.symm : (Fin n → ℕ) → Fin n →₀ ℕ) fun (i : Fin n) => 1 + (n + 1) * (↑i : ℕ)) (f * ∏ ij : Fin n × Fin n, if ij.1 < ij.2 then (MvPolynomial.X ij.2 - MvPolynomial.X ij.1) * ∑ k ∈ Finset.range (n + 1), (MvPolynomial.C : RatFunc ℚ → MvPolynomial (Fin n) (RatFunc ℚ)) (τ ^ k) * MvPolynomial.X ij.1 ^ k * MvPolynomial.X ij.2 ^ (n - k) else 1) := by

  classical
  intro n τ i j f g hij hdegree hrel
  let m := Finsupp.equivFunOnFinite.symm (fun b : Fin n => 1 + (n+1)*b.val)
  let S : MvPolynomial (Fin n) (RatFunc ℚ) :=
    ∑ k ∈ Finset.range (n+1), C (τ^k) * X i^k * X j^(n-k)
  let R : MvPolynomial (Fin n) (RatFunc ℚ) :=
    ∏ ab : Fin n × Fin n, if ab.1 < ab.2 ∧ ab ≠ (i,j) then
      (X ab.2 - X ab.1) * ∑ k ∈ Finset.range (n+1),
        C (τ^k) * X ab.1^k * X ab.2^(n-k) else 1
  let P : MvPolynomial (Fin n) (RatFunc ℚ) :=
    ∏ ab : Fin n × Fin n, if ab.1 < ab.2 then
      (X ab.2 - X ab.1) * ∑ k ∈ Finset.range (n+1),
        C (τ^k) * X ab.1^k * X ab.2^(n-k) else 1
  let sf := rename (Equiv.swap i j) f
  let u := g - C τ * f
  have hlt : i < j := by omega
  have hP : P = (X j-X i)*S*R := by
    exact x2611_16899_thm1_eq2_s1h1_s1h2_aux10
      (fun ab : Fin n × Fin n => ab.1 < ab.2)
      (fun ab : Fin n × Fin n => (X ab.2-X ab.1) *
        ∑ k ∈ Finset.range (n+1), C (τ^k)*X ab.1^k*X ab.2^(n-k)) (i,j) hlt
  have hu : (X i-X j)*u = (X j-C τ*X i)*(f-sf) := by
    dsimp [u, sf]
    simp only [map_sub, map_one] at hrel
    linear_combination hrel
  have hgeom : (X j-C τ*X i)*S = X j^(n+1)-C (τ^(n+1))*X i^(n+1) := by
    dsimp only [S]
    simpa only [map_pow] using
      x2611_16899_thm1_eq2_s1h1_s1h2_aux11 (X i : MvPolynomial (Fin n) (RatFunc ℚ)) (X j) (C τ) n
  have hid : u*P = C (τ^(n+1))*(X i^(n+1)*R*(f-sf)) - X j^(n+1)*R*(f-sf) := by
    calc
      u*P = -((X i-X j)*u)*S*R := by rw [hP]; ring
      _ = -((X j-C τ*X i)*(f-sf))*S*R := by rw [hu]
      _ = -((X j-C τ*X i)*S)*R*(f-sf) := by ring
      _ = _ := by rw [hgeom]; ring
  have hR : rename (Equiv.swap i j) R = R :=
    x2611_16899_thm1_eq2_s1h1_s1h2_aux6 n n τ i j hij
  have hzero1 : coeff m (X i^(n+1)*R*(f-sf)) = 0 :=
    x2611_16899_thm1_eq2_s1h1_s1h2_aux8 n τ i j hij (f-sf)
  have hzero2 : coeff m (X j^(n+1)*R*(f-sf)) = 0 :=
    x2611_16899_thm1_eq2_s1h1_s1h2_aux9 n i j hij R f hR
  have hz : coeff m (u*P) = 0 := by
    rw [hid, coeff_sub, coeff_C_mul, hzero1, hzero2, mul_zero, sub_zero]
  change coeff m (g*P) = τ * coeff m (f*P)
  dsimp [u] at hz
  rw [sub_mul, mul_assoc, coeff_sub, coeff_C_mul] at hz
  exact sub_eq_zero.mp hz
end

end Mathlib2
