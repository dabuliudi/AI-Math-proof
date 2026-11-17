/- Mathlib2 分片 59（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0051
import Mathlib2.Shard.S0052
import Mathlib2.Shard.S0053
import Mathlib2.Shard.S0054
import Mathlib2.Shard.S0057
import Mathlib2.Shard.S0058
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry x2611_12360_lem2_3 kind=proved origin=paper
section
/- Lemma 2.3 -/
lemma x2611_12360_lem2_3_aux1 (p : ℕ) (A : Set (AddCircle (p : ℝ))) :
    0 ≤ x2611_12360_gap p A ∧ x2611_12360_gap p A ≤ p := by
  have hb : BddAbove {l : ℝ | 0 ≤ l ∧ l ≤ (p : ℝ) ∧
      ∃ a : ℝ, ∀ t : ℝ, a < t → t < a + l → (t : AddCircle (p : ℝ)) ∉ A} :=
    ⟨p, fun _ h => h.2.1⟩
  have hz : (0 : ℝ) ∈ {l : ℝ | 0 ≤ l ∧ l ≤ (p : ℝ) ∧
      ∃ a : ℝ, ∀ t : ℝ, a < t → t < a + l → (t : AddCircle (p : ℝ)) ∉ A} := by
    refine ⟨le_rfl, Nat.cast_nonneg p, 0, ?_⟩
    intro t ht ht'
    linarith
  exact ⟨le_csSup hb hz, csSup_le ⟨0, hz⟩ (fun _ h => h.2.1)⟩

lemma x2611_12360_lem2_3_aux2 {ι : Type*} (p : ℕ) (f g : ι → ℝ)
    (c d : ℝ) (hcd : c ≤ d) (h : ∀ i, c ≤ g i - f i ∧ g i - f i ≤ d) :
    x2611_12360_gap p (Set.range (fun i => (f i : AddCircle (p : ℝ)))) ≤
      x2611_12360_gap p (Set.range (fun i => (g i : AddCircle (p : ℝ)))) + (d - c) := by
  have hnon := (x2611_12360_lem2_3_aux1 p
    (Set.range (fun i => (g i : AddCircle (p : ℝ))))).1
  unfold x2611_12360_gap at hnon ⊢
  apply csSup_le
  · refine ⟨0, le_rfl, Nat.cast_nonneg p, 0, ?_⟩
    intro t ht ht'
    linarith
  · rintro l ⟨hl, hlp, a, ha⟩
    by_cases hd : l ≤ d - c
    · linarith
    · have hm : l - (d - c) ∈ {l : ℝ | 0 ≤ l ∧ l ≤ (p : ℝ) ∧
          ∃ a : ℝ, ∀ t : ℝ, a < t → t < a + l →
            (t : AddCircle (p : ℝ)) ∉ Set.range (fun i => (g i : AddCircle (p : ℝ)))} := by
        refine ⟨by linarith, by linarith, a + d, ?_⟩
        intro t ht ht' hmem
        rcases hmem with ⟨i, hi⟩
        have hi' : ((t - g i + f i : ℝ) : AddCircle (p : ℝ)) = (f i : AddCircle (p : ℝ)) := by
          rw [AddCircle.coe_add, AddCircle.coe_sub, ← hi, sub_self, zero_add]
        apply ha (t - g i + f i) (by linarith [(h i).2]) (by linarith [(h i).1])
        exact ⟨i, hi'.symm⟩
      have hb : BddAbove {l : ℝ | 0 ≤ l ∧ l ≤ (p : ℝ) ∧
          ∃ a : ℝ, ∀ t : ℝ, a < t → t < a + l →
            (t : AddCircle (p : ℝ)) ∉ Set.range (fun i => (g i : AddCircle (p : ℝ)))} :=
        ⟨p, fun _ h => h.2.1⟩
      have := le_csSup hb hm
      linarith

lemma x2611_12360_lem2_3_aux3 (p M : ℕ) (u : ℝ) :
    0 ≤ x2611_12360_G p M u ∧ x2611_12360_G p M u ≤ p := by
  have hb : BddAbove (Set.range (fun β : ℝ => x2611_12360_gap p
      (Set.range (fun k : Fin M => ((-u * (k.val : ℝ) ^ 2 - β * (k.val : ℝ) : ℝ) :
        AddCircle (p : ℝ)))))) :=
    ⟨p, by rintro _ ⟨β, rfl⟩; exact (x2611_12360_lem2_3_aux1 _ _).2⟩
  constructor
  · exact le_trans (x2611_12360_lem2_3_aux1 _ _).1 (le_csSup hb (Set.mem_range_self 0))
  · exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨β, rfl⟩; exact (x2611_12360_lem2_3_aux1 _ _).2)

lemma x2611_12360_lem2_3_aux4 (M k : ℕ) (hM : 1 ≤ M) (hk : k < M) :
    0 ≤ (k : ℝ) * ((M : ℝ) - 1 - k) ∧
    (k : ℝ) * ((M : ℝ) - 1 - k) ≤ ((⌊((M : ℝ) - 1) ^ 2 / 4⌋ : ℤ) : ℝ) := by
  have hkm : (k : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast (show k + 1 ≤ M by omega)
  have hk' : (k : ℝ) ≤ (M : ℝ) - 1 := by linarith
  have hnon : 0 ≤ (k : ℝ) * ((M : ℝ) - 1 - k) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith)
  refine ⟨hnon, ?_⟩
  have hs : (k : ℝ) * ((M : ℝ) - 1 - k) ≤ ((M : ℝ) - 1) ^ 2 / 4 := by
    nlinarith [sq_nonneg ((M : ℝ) - 1 - 2 * k)]
  have hz : ((k : ℤ) * ((M : ℤ) - 1 - k) : ℝ) = (k : ℝ) * ((M : ℝ) - 1 - k) := by push_cast; rfl
  have hzle : (k : ℤ) * ((M : ℤ) - 1 - k) ≤ ⌊((M : ℝ) - 1) ^ 2 / 4⌋ := by
    apply Int.le_floor.mpr
    simpa only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_one] using hs
  have hh := (Int.cast_le (R := ℝ)).mpr hzle
  simpa only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_one] using hh

lemma x2611_12360_lem2_3_aux5 {ι : Type*} (p : ℕ) (f g : ι → ℝ)
    (c d : ℝ) (hcd : c ≤ d) (h : ∀ i, c ≤ g i - f i ∧ g i - f i ≤ d) :
    |x2611_12360_gap p (Set.range (fun i => (f i : AddCircle (p : ℝ)))) -
      x2611_12360_gap p (Set.range (fun i => (g i : AddCircle (p : ℝ))))| ≤ d - c := by
  have h₁ := x2611_12360_lem2_3_aux2 p f g c d hcd h
  have h₂ := x2611_12360_lem2_3_aux2 p g f (-d) (-c) (by linarith)
    (fun i => by constructor <;> linarith [(h i).1, (h i).2])
  apply abs_le.mpr
  constructor <;> linarith

lemma x2611_12360_lem2_3_aux6 (p : ℕ) (k : ℕ) (u β : ℝ) :
    ((-(u + (p : ℝ) / 2) * (k : ℝ) ^ 2 - β * (k : ℝ) : ℝ) : AddCircle (p : ℝ)) =
      ((-u * (k : ℝ) ^ 2 - (β + (p : ℝ) / 2) * (k : ℝ) : ℝ) : AddCircle (p : ℝ)) := by
  rcases Int.even_mul_pred_self (k : ℤ) with ⟨z, hz⟩
  have hz' : (k : ℝ) * ((k : ℝ) - 1) = (z : ℝ) + z := by exact_mod_cast hz
  apply sub_eq_zero.mp
  rw [← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  refine ⟨-z, ?_⟩
  rw [zsmul_eq_mul]
  push_cast
  linear_combination (p : ℝ) / 2 * hz'

lemma x2611_12360_lem2_3_aux7 (p M : ℕ) (u : ℝ) :
    x2611_12360_G p M (u + (p : ℝ) / 2) = x2611_12360_G p M u := by
  unfold x2611_12360_G
  apply congrArg sSup
  ext y
  constructor
  · rintro ⟨β, rfl⟩
    refine ⟨β + (p : ℝ) / 2, ?_⟩
    apply congrArg (x2611_12360_gap p)
    apply congrArg Set.range
    funext k
    exact (x2611_12360_lem2_3_aux6 p k.val u β).symm
  · rintro ⟨β, rfl⟩
    refine ⟨β - (p : ℝ) / 2, ?_⟩
    apply congrArg (x2611_12360_gap p)
    apply congrArg Set.range
    funext k
    simpa only [sub_add_cancel] using x2611_12360_lem2_3_aux6 p k.val u (β - (p : ℝ) / 2)

lemma x2611_12360_lem2_3_aux8 (p M : ℕ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ k : Fin M, 0 ≤ (k.val : ℝ) * ((M : ℝ) - 1 - k.val) ∧
      (k.val : ℝ) * ((M : ℝ) - 1 - k.val) ≤ C)
    (u v : ℝ) (huv : u ≤ v) :
    x2611_12360_G p M u ≤ x2611_12360_G p M v + C * (v - u) ∧
    x2611_12360_G p M v ≤ x2611_12360_G p M u + C * (v - u) := by
  have hb (w : ℝ) : BddAbove (Set.range (fun β : ℝ => x2611_12360_gap p
      (Set.range (fun k : Fin M => ((-w * (k.val : ℝ) ^ 2 - β * (k.val : ℝ) : ℝ) :
        AddCircle (p : ℝ)))))) :=
    ⟨p, by rintro _ ⟨β, rfl⟩; exact (x2611_12360_lem2_3_aux1 _ _).2⟩
  have hpair (β : ℝ) :
      |x2611_12360_gap p (Set.range (fun k : Fin M =>
          ((-u * (k.val : ℝ) ^ 2 - β * (k.val : ℝ) : ℝ) : AddCircle (p : ℝ)))) -
        x2611_12360_gap p (Set.range (fun k : Fin M =>
          ((-v * (k.val : ℝ) ^ 2 - (β - ((M : ℝ) - 1) * (v - u)) * (k.val : ℝ) : ℝ) :
            AddCircle (p : ℝ))))| ≤ C * (v - u) := by
    calc
      _ ≤ C * (v - u) - 0 := by
        apply x2611_12360_lem2_3_aux5 p _ _ 0 (C * (v - u))
        · exact mul_nonneg hC0 (sub_nonneg.mpr huv)
        · intro k
          have he : (-v * (k.val : ℝ) ^ 2 - (β - ((M : ℝ) - 1) * (v - u)) * (k.val : ℝ)) -
              (-u * (k.val : ℝ) ^ 2 - β * (k.val : ℝ)) =
              (v - u) * ((k.val : ℝ) * ((M : ℝ) - 1 - k.val)) := by ring
          rw [he]
          constructor
          · exact mul_nonneg (sub_nonneg.mpr huv) (hC k).1
          · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hC k).2 (sub_nonneg.mpr huv)
      _ = _ := sub_zero _
  constructor
  · unfold x2611_12360_G
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨β, rfl⟩
    have h := (abs_le.mp (hpair β)).2
    have h' := le_csSup (hb v) (Set.mem_range_self (β - ((M : ℝ) - 1) * (v - u)))
    linarith
  · unfold x2611_12360_G
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨β, rfl⟩
    have h := (abs_le.mp (hpair (β + ((M : ℝ) - 1) * (v - u)))).1
    have he : β + ((M : ℝ) - 1) * (v - u) - ((M : ℝ) - 1) * (v - u) = β := by ring
    rw [he] at h
    have h' := le_csSup (hb u) (Set.mem_range_self (β + ((M : ℝ) - 1) * (v - u)))
    linarith

theorem x2611_12360_lem2_3 (p M : ℕ) (hp : 2 ≤ p) (hM : 2 ≤ M) (u v : ℝ) :
  x2611_12360_G p M (u + (p : ℝ) / 2) = x2611_12360_G p M u ∧
  |x2611_12360_G p M u - x2611_12360_G p M v| ≤
    ((⌊((M : ℝ) - 1) ^ 2 / 4⌋ : ℤ) : ℝ) * |u - v| := by
  refine ⟨x2611_12360_lem2_3_aux7 p M u, ?_⟩
  have hC (k : Fin M) := x2611_12360_lem2_3_aux4 M k.val (by omega) k.isLt
  have hC0 : 0 ≤ ((⌊((M : ℝ) - 1) ^ 2 / 4⌋ : ℤ) : ℝ) := by
    simpa using (hC ⟨0, by omega⟩).2
  rcases le_total u v with huv | hvu
  · have h := x2611_12360_lem2_3_aux8 p M _ hC0 hC u v huv
    rw [abs_of_nonpos (sub_nonpos.mpr huv)]
    apply abs_le.mpr
    constructor <;> linarith [h.1, h.2]
  · have h := x2611_12360_lem2_3_aux8 p M _ hC0 hC v u hvu
    rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
    apply abs_le.mpr
    constructor <;> linarith [h.1, h.2]
end

-- forge:entry x2611_15210_thm1_1_s1h1 kind=proved origin=decomposition
section
/- x2611_15210_thm1_1 的证明骨架中第 1 个空洞 -/
open Finset

lemma x2611_15210_thm1_1_s1h1_aux1
    (L : ℕ) (G : Type*) [AddCommMonoid G] [Fintype G]
    (hG : ∀ x : G, L • x = 0) :
    ∀ a : Fin (Fintype.card G * L) → G,
      ∃ I : Finset (Fin (Fintype.card G * L)), I.card = L ∧ ∑ i ∈ I, a i = 0 := by
  classical
  intro a
  obtain ⟨g, hg⟩ := Fintype.exists_le_card_fiber_of_mul_le_card a (n := L) (by simp)
  obtain ⟨I, hI, hc⟩ := Finset.exists_subset_card_eq hg
  refine ⟨I, hc, ?_⟩
  calc
    ∑ i ∈ I, a i = ∑ _i ∈ I, g := Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp (hI hi)).2)
    _ = 0 := by simp [hc, hG]

lemma x2611_15210_thm1_1_s1h1_aux2
    (L : ℕ) (G : Type*) [AddCommMonoid G] [Fintype G]
    (hG : ∀ x : G, L • x = 0)
    {α : Type*} (s : Finset α) (a : α → G)
    (hs : x2611_15210_s L G ≤ s.card) :
    ∃ I ⊆ s, I.card = L ∧ ∑ i ∈ I, a i = 0 := by
  classical
  have hne : {n : ℕ | ∀ a : Fin n → G, ∃ I : Finset (Fin n),
      I.card = L ∧ ∑ i ∈ I, a i = 0}.Nonempty :=
    ⟨_, x2611_15210_thm1_1_s1h1_aux1 L G hG⟩
  have hp : ∀ a : Fin (x2611_15210_s L G) → G,
      ∃ I : Finset (Fin (x2611_15210_s L G)), I.card = L ∧ ∑ i ∈ I, a i = 0 :=
    Nat.sInf_mem hne
  let e : Fin (x2611_15210_s L G) ↪ α :=
    (Fin.castLEEmb hs).trans s.equivFin.symm.toEmbedding |>.trans (Function.Embedding.subtype _)
  obtain ⟨I, hc, hz⟩ := hp (fun i => a (e i))
  refine ⟨I.map e, ?_, by rw [Finset.card_map]; exact hc, ?_⟩
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    exact (s.equivFin.symm (Fin.castLEEmb hs j)).property
  · rw [Finset.sum_map]; exact hz

lemma x2611_15210_thm1_1_s1h1_aux3
    {α : Type*} (P : Finset α → Prop) (c : ℕ)
    (hP : ∀ s : Finset α, c < s.card → ∃ b ⊆ s, b.card = 2 ∧ P b)
    (n : ℕ) (s : Finset α) (hs : 2 * n + c ≤ s.card + 1) :
    ∃ T : Finset (Finset α), T.card = n ∧
      (∀ b ∈ T, b ⊆ s ∧ b.card = 2 ∧ P b) ∧
      (T : Set (Finset α)).PairwiseDisjoint id := by
  classical
  induction n generalizing s with
  | zero => exact ⟨∅, by simp, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨b, hbs, hb, hPb⟩ := hP s (by omega)
    have hc : (s \ b).card + b.card = s.card := Finset.card_sdiff_add_card_eq_card hbs
    obtain ⟨T, hT, hTs, hTd⟩ := ih (s \ b) (by omega)
    have hdis : ∀ t ∈ T, Disjoint b t := by
      intro t ht
      exact Finset.disjoint_left.mpr (by
        intro x hxb hxt
        exact (Finset.mem_sdiff.mp ((hTs t ht).1 hxt)).2 hxb)
    have hbT : b ∉ T := by
      intro h
      have := hdis b h
      have : b = ∅ := disjoint_self.mp this
      simp [this] at hb
    refine ⟨insert b T, by simp [hbT, hT], ?_, ?_⟩
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact ⟨hbs, hb, hPb⟩
      · exact ⟨(hTs t ht).1.trans Finset.sdiff_subset, (hTs t ht).2⟩
    · simpa only [Finset.coe_insert, Set.pairwiseDisjoint_insert, id_eq] using ⟨hTd, fun t ht _ => hdis t ht⟩

lemma x2611_15210_thm1_1_s1h1_aux4
    (L : ℕ) (H G C : Type*) [AddCommMonoid H] [Fintype H]
    [AddCommMonoid G] [Fintype C]
    (hH : ∀ x : H, L • x = 0) (f : H →+ G) (color : G → C)
    (hc : 0 < Fintype.card C)
    (hp : ∀ x y : G, color x = color y → ∃ z : H, f z = x + y) :
    x2611_15210_s (2 * L) G + 1 ≤ 2 * x2611_15210_s L H + Fintype.card C := by
  classical
  let N := 2 * x2611_15210_s L H + Fintype.card C - 1
  have hprop : ∀ a : Fin N → G, ∃ I : Finset (Fin N),
      I.card = 2 * L ∧ ∑ i ∈ I, a i = 0 := by
    intro a
    have hpair : ∀ s : Finset (Fin N), Fintype.card C < s.card →
        ∃ b ⊆ s, b.card = 2 ∧ ∃ z : H, f z = ∑ i ∈ b, a i := by
      intro s hs
      obtain ⟨x, hx, y, hy, hxy, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
        (f := fun i => color (a i)) (t := Finset.univ) (by simpa using hs) (by simp)
      obtain ⟨z, hz⟩ := hp (a x) (a y) he
      refine ⟨{x, y}, ?_, by simp [hxy], z, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hx
        · exact (Finset.mem_singleton.mp hi) ▸ hy
      simpa [Finset.sum_pair hxy] using hz
    obtain ⟨T, hT, hTs, hTd⟩ := x2611_15210_thm1_1_s1h1_aux3
      (fun b => ∃ z : H, f z = ∑ i ∈ b, a i) (Fintype.card C) hpair
      (x2611_15210_s L H) Finset.univ (by simp only [Finset.card_univ, Fintype.card_fin]; dsimp [N]; omega)
    have hex : ∀ b : Finset (Fin N), ∃ z : H, b ∈ T → f z = ∑ i ∈ b, a i := by
      intro b
      by_cases hb : b ∈ T
      · obtain ⟨z, hz⟩ := (hTs b hb).2.2
        exact ⟨z, fun _ => hz⟩
      · exact ⟨0, fun h => (hb h).elim⟩
    choose g hg using hex
    obtain ⟨J, hJT, hJc, hJz⟩ := x2611_15210_thm1_1_s1h1_aux2 L H hH T g (by omega)
    have hd : (J : Set (Finset (Fin N))).PairwiseDisjoint id := by
      intro b hb c hc hbc
      exact hTd (hJT hb) (hJT hc) hbc
    refine ⟨J.biUnion id, ?_, ?_⟩
    · rw [Finset.card_biUnion hd]
      calc
        ∑ b ∈ J, b.card = ∑ _b ∈ J, 2 := Finset.sum_congr rfl (fun b hb => (hTs b (hJT hb)).2.1)
        _ = 2 * L := by simp [hJc, Nat.mul_comm]
    · rw [Finset.sum_biUnion hd]
      calc
        ∑ b ∈ J, ∑ i ∈ b, a i = ∑ b ∈ J, f (g b) :=
          Finset.sum_congr rfl (fun b hb => (hg b (hJT hb)).symm)
        _ = f (∑ b ∈ J, g b) := (map_sum f _ _).symm
        _ = 0 := by rw [hJz, map_zero]
  have hle : x2611_15210_s (2 * L) G ≤ N := Nat.sInf_le hprop
  dsimp [N] at hle
  omega

lemma x2611_15210_thm1_1_s1h1_aux5 (k : ℕ) :
    ∃ f : ZMod k →+ ZMod (2 * k), ∀ n : ℕ, f (n : ZMod k) = 2 * (n : ZMod (2 * k)) := by
  let g : ℤ →+ ZMod (2 * k) :=
    { toFun := fun z => 2 * (z : ZMod (2 * k))
      map_zero' := by simp
      map_add' := by intro a b; simp [mul_add] }
  have hg : g (k : ℤ) = 0 := by
    change (2 : ZMod (2 * k)) * ((k : ℤ) : ZMod (2 * k)) = 0
    simpa only [Int.cast_natCast, Nat.cast_mul, Nat.cast_ofNat] using (ZMod.natCast_self (2 * k))
  refine ⟨ZMod.lift k ⟨g, hg⟩, ?_⟩
  intro n
  simpa only [g, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Int.cast_natCast] using
    (ZMod.lift_coe k ⟨g, hg⟩ (n : ℤ))

lemma x2611_15210_thm1_1_s1h1_aux6 (k : ℕ) [NeZero (2 * k)]
    (f : ZMod k →+ ZMod (2 * k))
    (hf : ∀ n : ℕ, f (n : ZMod k) = 2 * (n : ZMod (2 * k)))
    (x y : ZMod (2 * k)) (he : x.val % 2 = y.val % 2) :
    ∃ z : ZMod k, f z = x + y := by
  have hsum : 2 * ((x.val + y.val) / 2) = x.val + y.val := by omega
  refine ⟨((x.val + y.val) / 2 : ℕ), ?_⟩
  rw [hf]
  calc
    (2 : ZMod (2 * k)) * (((x.val + y.val) / 2 : ℕ) : ZMod (2 * k)) =
        ((2 * ((x.val + y.val) / 2) : ℕ) : ZMod (2 * k)) := by simp
    _ = x + y := by rw [hsum, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

theorem x2611_15210_thm1_1_s1h1 : ∀ (k r : ℕ), 2 ≤ k →
    x2611_15210_s (2 * k) (Fin r → ZMod (2 * k)) + 1 ≤
      2 * x2611_15210_s k (Fin r → ZMod k) + 2 ^ r := by
  intro k r hk
  letI : NeZero k := ⟨by omega⟩
  letI : NeZero (2 * k) := ⟨by omega⟩
  obtain ⟨f, hf⟩ := x2611_15210_thm1_1_s1h1_aux5 k
  let F : (Fin r → ZMod k) →+ (Fin r → ZMod (2 * k)) :=
    { toFun := fun a i => f (a i)
      map_zero' := by ext i; exact map_zero f
      map_add' := by intro a b; ext i; exact map_add f (a i) (b i) }
  let color : (Fin r → ZMod (2 * k)) → (Fin r → Fin 2) :=
    fun a i => ⟨(a i).val % 2, Nat.mod_lt _ (by omega)⟩
  have hH : ∀ x : Fin r → ZMod k, k • x = 0 := by
    intro x
    ext i
    simp [nsmul_eq_mul]
  have hp : ∀ x y : Fin r → ZMod (2 * k), color x = color y →
      ∃ z : Fin r → ZMod k, F z = x + y := by
    intro x y he
    have hcoord : ∀ i : Fin r, ∃ z : ZMod k, f z = x i + y i := by
      intro i
      apply x2611_15210_thm1_1_s1h1_aux6 k f hf
      exact congrArg Fin.val (congrFun he i)
    choose z hz using hcoord
    exact ⟨z, funext hz⟩
  have h := x2611_15210_thm1_1_s1h1_aux4 k (Fin r → ZMod k)
    (Fin r → ZMod (2 * k)) (Fin r → Fin 2) hH F color (by simp) hp
  simpa only [Fintype.card_fun, Fintype.card_fin] using h
end

-- forge:entry x2611_10667_eq13_singular_point_count kind=proved origin=paper
section
/- After equation (13) (number of singular points on L1) -/
lemma x2611_10667_eq13_singular_point_count_aux1
    (q r : ℕ) (hr : r.Prime) (K : Type*) [Field K] [CharP K r] (z : K) :
    z ^ (q * r) = 1 ↔ z ^ q = 1 := by
  letI : Fact r.Prime := ⟨hr⟩
  constructor
  · intro hz
    apply frobenius_inj K r
    change (z ^ q) ^ r = (1 : K) ^ r
    simpa only [← pow_mul, one_pow] using hz
  · intro hz
    rw [pow_mul, hz, one_pow]

lemma x2611_10667_eq13_singular_point_count_aux2
    (q r : ℕ) (hq : 0 < q) (hr : r.Prime)
    (K : Type*) [Field K] [CharP K r]
    (ζ : K) (hζ : IsPrimitiveRoot ζ q) :
    Set.ncard {z : K | z ≠ 0 ∧
      Polynomial.IsRoot (Polynomial.X ^ (q * r) - 1 : Polynomial K) z ∧
      Polynomial.IsRoot (Polynomial.derivative
        (Polynomial.X ^ (q * r) - 1 : Polynomial K)) z} = q := by
  classical
  have hd : Polynomial.derivative
      (Polynomial.X ^ (q * r) - 1 : Polynomial K) = 0 := by
    simp [Polynomial.derivative_X_pow, Nat.cast_mul, CharP.cast_eq_zero K r]
  have hs : {z : K | z ≠ 0 ∧
      Polynomial.IsRoot (Polynomial.X ^ (q * r) - 1 : Polynomial K) z ∧
      Polynomial.IsRoot (Polynomial.derivative
        (Polynomial.X ^ (q * r) - 1 : Polynomial K)) z} =
      (Polynomial.nthRootsFinset q (1 : K) : Set K) := by
    ext z
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Polynomial.mem_nthRootsFinset hq,
      Polynomial.IsRoot, hd, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero, sub_eq_zero,
      and_true]
    rw [x2611_10667_eq13_singular_point_count_aux1 q r hr K z]
    constructor
    · exact And.right
    · intro hz
      refine ⟨?_, hz⟩
      intro hzero
      simpa [hzero, Nat.ne_of_gt hq] using hz
  rw [hs, Set.ncard_coe_finset]
  exact hζ.card_nthRootsFinset

theorem x2611_10667_eq13_singular_point_count
    (q r B C : ℕ) (hq : q.Prime) (hr : r.Prime) (hq2 : 2 < q) (hr2 : 2 < r)
    (hqr : q ≠ r) (m n : ℤ)
    (hm : IsCoprime m ((q * r : ℕ) : ℤ))
    (hn : IsCoprime n ((q * r : ℕ) : ℤ))
    (hbezout : n * (q : ℤ) - m * (r : ℤ) = 1)
    (hB : Int.ModEq ((q * r : ℕ) : ℤ) (B : ℤ) (-m * (r : ℤ) - n * (q : ℤ)))
    (hC : Int.ModEq ((q * r : ℕ) : ℤ) (C : ℤ) (m * (r : ℤ) + n * (q : ℤ)))
    (hB0 : 0 < B) (hC0 : 0 < C) (hBlt : B < q * r) (hClt : C < q * r)
    (hBC : B + C = q * r) (t : ℚ) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (ht : 2 + 2 / ((r : ℚ) - 1) < (padicValRat r (t - 1) : ℚ))
    (K : Type*) [Field K] [Finite K] [CharP K r]
    (ζ : K) (hζ : IsPrimitiveRoot ζ q) :
    Set.ncard {z : K | z ≠ 0 ∧
      Polynomial.IsRoot (Polynomial.X ^ (q * r) - 1 : Polynomial K) z ∧
      Polynomial.IsRoot (Polynomial.derivative
        (Polynomial.X ^ (q * r) - 1 : Polynomial K)) z} = q := by
  exact x2611_10667_eq13_singular_point_count_aux2 q r hq.pos hr K ζ hζ
end

-- forge:entry x2611_10667_table3_1 kind=proved origin=paper
section
/- Table 3.1 (all coefficient valuation rows) -/
open Polynomial

theorem x2611_10667_table3_1_aux1 (B C j : ℕ) (t : ℚ) (hj : j ≤ C + 1) :
    (x2611_10667_p B C t).coeff (B + j) =
      (-1 : ℚ) ^ B * ((1 - t) ^ ((C : ℤ) - (j : ℤ)) *
      (-t) ^ ((j : ℤ) - 1) *
      ((if j = 0 then 0 else (Nat.choose C (j - 1) : ℚ)) -
        t * (Nat.choose (C + 1) j : ℚ))) := by
  have hs : (-1 : Polynomial ℚ) ^ B = Polynomial.C ((-1 : ℚ) ^ B) := by simp
  rw [x2611_10667_p, neg_pow, hs, mul_assoc,
    coeff_C_mul, Nat.add_comm B j, coeff_X_pow_mul]
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b hb hbj
    simp [Ne.symm hbj]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (by omega)))

theorem x2611_10667_table3_1_aux2 (p : ℕ) [Fact p.Prime] (a b : ℚ)
    (ha : a ≠ 0) (hva : padicValRat p a = 0)
    (hb : b = 0 ∨ 0 < padicValRat p b) :
    a + b ≠ 0 ∧ padicValRat p (a + b) = 0 := by
  rcases hb with rfl | hb
  · simpa using And.intro ha hva
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb
  have hab : a + b ≠ 0 := by
    intro h
    have hab' : a = -b := eq_neg_of_add_eq_zero_left h
    rw [hab', padicValRat.neg] at hva
    omega
  exact ⟨hab, (padicValRat.add_eq_of_lt hab ha hb0 (by omega)).trans hva⟩

theorem x2611_10667_table3_1_aux3 (p : ℕ) [Fact p.Prime] (t : ℚ)
    (ht : 0 < padicValRat p (t - 1)) : padicValRat p t = 0 := by
  have h := x2611_10667_table3_1_aux2 p 1 (t - 1) one_ne_zero (by simp) (Or.inr ht)
  simpa using h.2

theorem x2611_10667_table3_1_aux4 (p : ℕ) [Fact p.Prime] (t : ℚ)
    (ht0 : t ≠ 0) (ht : padicValRat p t = 0) (a b : ℕ)
    (hab : (a : ℚ) - t * b ≠ 0) : 0 ≤ padicValRat p ((a : ℚ) - t * b) := by
  have hmul : 0 ≤ padicValRat p (t * (b : ℚ)) := by
    by_cases hb : b = 0
    · simp [hb]
    · rw [padicValRat.mul ht0 (by exact_mod_cast hb), ht, zero_add]
      exact zero_le_padicValRat_of_nat b
  have hh := padicValRat.min_le_padicValRat_add (p := p) (q := (a : ℚ))
    (r := -(t * b)) (by simpa [sub_eq_add_neg] using hab)
  simp only [padicValRat.neg, ← sub_eq_add_neg] at hh
  exact le_trans (le_min (zero_le_padicValRat_of_nat a) hmul) hh

theorem x2611_10667_table3_1_aux5 (p B C j : ℕ) [Fact p.Prime]
    (t : ℚ) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (ht : padicValRat p t = 0)
    (hj : j ≤ C + 1)
    (hbr : ((if j = 0 then 0 else (Nat.choose C (j - 1) : ℚ)) -
      t * (Nat.choose (C + 1) j : ℚ)) ≠ 0) :
    (x2611_10667_p B C t).coeff (B + j) ≠ 0 ∧
    padicValRat p ((x2611_10667_p B C t).coeff (B + j)) =
      ((C : ℤ) - (j : ℤ)) * padicValRat p (t - 1) +
      padicValRat p ((if j = 0 then 0 else (Nat.choose C (j - 1) : ℚ)) -
      t * (Nat.choose (C + 1) j : ℚ)) := by
  have hs : (-1 : ℚ) ^ B ≠ 0 := pow_ne_zero _ (by norm_num)
  have hx : (1 - t) ^ ((C : ℤ) - (j : ℤ)) ≠ 0 :=
    zpow_ne_zero _ (sub_ne_zero.mpr (Ne.symm ht1))
  have hy : (-t) ^ ((j : ℤ) - 1) ≠ 0 := zpow_ne_zero _ (neg_ne_zero.mpr ht0)
  have hv : padicValRat p (1 - t) = padicValRat p (t - 1) := by
    rw [show 1 - t = -(t - 1) by ring, padicValRat.neg]
  rw [x2611_10667_table3_1_aux1 B C j t hj]
  refine ⟨mul_ne_zero hs (mul_ne_zero (mul_ne_zero hx hy) hbr), ?_⟩
  rw [padicValRat.mul hs (mul_ne_zero (mul_ne_zero hx hy) hbr),
    padicValRat.mul (mul_ne_zero hx hy) hbr, padicValRat.mul hx hy]
  simp [padicValRat.pow, padicValRat.zpow, hv, ht]

theorem x2611_10667_table3_1_aux6 (p : ℕ) [Fact p.Prime] (t a : ℚ) (b : ℤ)
    (ha : a ≠ 0) (hva : padicValRat p a = 0)
    (ht : 0 < padicValRat p (t - 1)) :
    a + (b : ℚ) * (t - 1) ≠ 0 ∧
      padicValRat p (a + (b : ℚ) * (t - 1)) = 0 := by
  apply x2611_10667_table3_1_aux2 p _ _ ha hva
  by_cases hb : b = 0
  · exact Or.inl (by simp [hb])
  · right
    rw [padicValRat.mul (by exact_mod_cast hb) (sub_ne_zero.mpr (by
      intro h; simp [h] at ht))]
    have h : 0 ≤ padicValRat p (b : ℚ) := by simp
    omega

theorem x2611_10667_table3_1_aux7 (B C : ℕ) (t : ℚ) (ht0 : t ≠ 0) :
    (x2611_10667_p B C t).coeff B = (-1 : ℚ) ^ B * (1 - t) ^ C := by
  have h := x2611_10667_table3_1_aux1 B C 0 t (by omega)
  simpa [ht0, mul_assoc] using h

theorem x2611_10667_table3_1_aux8 (B C : ℕ) (t : ℚ) (ht1 : t ≠ 1) :
    (x2611_10667_p B C t).coeff (B + C + 1) = (-1 : ℚ) ^ B * (-t) ^ C := by
  have he1 : (C : ℤ) - ((C + 1 : ℕ) : ℤ) = -1 := by omega
  have he2 : ((C + 1 : ℕ) : ℤ) - 1 = C := by omega
  have h := x2611_10667_table3_1_aux1 B C (C + 1) t (by omega)
  simp only [he1, he2, zpow_natCast, zpow_neg_one, Nat.add_sub_cancel,
    Nat.choose_self, Nat.cast_one, mul_one, if_neg (by omega : C + 1 ≠ 0)] at h
  rw [← Nat.add_assoc] at h
  rw [h]
  have hn : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  field_simp

theorem x2611_10667_table3_1_aux9 (p B C : ℕ) [Fact p.Prime]
    (t : ℚ) (hC : 0 < C) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (ht : 0 < padicValRat p (t - 1)) :
    (x2611_10667_p B C t).coeff (B + C) ≠ 0 ∧
      padicValRat p ((x2611_10667_p B C t).coeff (B + C)) = 0 := by
  have hc : C.choose (C - 1) = C := by
    rw [Nat.choose_symm (by omega : 1 ≤ C)]
    simp
  have hbr : ((if C = 0 then 0 else (C.choose (C - 1) : ℚ)) -
      t * ((C + 1).choose C : ℚ)) = -1 + (-((C + 1 : ℕ) : ℤ) : ℚ) * (t - 1) := by
    simp only [if_neg (by omega : C ≠ 0), hc, Nat.choose_succ_self_right]
    push_cast
    ring
  have hu := x2611_10667_table3_1_aux6 p t (-1) (-((C + 1 : ℕ) : ℤ))
    (by norm_num) (by simp) ht
  simp only [Int.cast_neg, Int.cast_natCast] at hu hbr
  have h := x2611_10667_table3_1_aux5 p B C C t ht0 ht1
    (x2611_10667_table3_1_aux3 p t ht) (by omega) (by rw [hbr]; exact hu.1)
  simpa only [hbr, hu.2, sub_self, zero_mul, zero_add] using h

theorem x2611_10667_table3_1_aux10 (p B C : ℕ) [Fact p.Prime]
    (t : ℚ) (hC : 2 ≤ C) (hCp : ¬p ∣ C) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (ht : 0 < padicValRat p (t - 1)) :
    (x2611_10667_p B C t).coeff (B + C - 1) ≠ 0 ∧
      padicValRat p ((x2611_10667_p B C t).coeff (B + C - 1)) =
        padicValRat p (t - 1) := by
  have hc : C.choose (C - 1) = C := by
    rw [Nat.choose_symm (by omega : 1 ≤ C)]
    simp
  have hc' : (C + 1).choose (C - 1) = C.choose (C - 2) + C := by
    have h := Nat.choose_succ_succ C (C - 2)
    simpa only [Nat.succ_eq_add_one, show C - 2 + 1 = C - 1 by omega, hc] using h
  have hbr : ((if C - 1 = 0 then 0 else (C.choose (C - 1 - 1) : ℚ)) -
      t * ((C + 1).choose (C - 1) : ℚ)) =
      -(C : ℚ) + (-((C + 1).choose (C - 1) : ℤ) : ℚ) * (t - 1) := by
    simp only [if_neg (by omega : C - 1 ≠ 0), show C - 1 - 1 = C - 2 by omega, hc']
    push_cast
    ring
  have hvC : padicValRat p (-(C : ℚ)) = 0 := by
    simp [padicValNat.eq_zero_of_not_dvd hCp]
  have hu := x2611_10667_table3_1_aux6 p t (-(C : ℚ))
    (-((C + 1).choose (C - 1) : ℤ)) (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))) hvC ht
  simp only [Int.cast_neg, Int.cast_natCast] at hu hbr
  have h := x2611_10667_table3_1_aux5 p B C (C - 1) t ht0 ht1
    (x2611_10667_table3_1_aux3 p t ht) (by omega) (by rw [hbr]; exact hu.1)
  have he : (C : ℤ) - ((C - 1 : ℕ) : ℤ) = 1 := by omega
  simpa only [show B + (C - 1) = B + C - 1 by omega, hbr, hu.2, he, one_mul, add_zero] using h

theorem x2611_10667_table3_1_aux11 (p B C i : ℕ) [Fact p.Prime]
    (t : ℚ) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (ht : padicValRat p t = 0)
    (hiB : B ≤ i) (hiC : i ≤ B + C) :
    (x2611_10667_p B C t).coeff i = 0 ∨
      ((B + C : ℕ) - i : ℤ) * padicValRat p (t - 1) ≤
        padicValRat p ((x2611_10667_p B C t).coeff i) := by
  by_cases hz : (x2611_10667_p B C t).coeff i = 0
  · exact Or.inl hz
  right
  have hj : i - B ≤ C + 1 := by omega
  have hi : B + (i - B) = i := by omega
  have hbr : ((if i - B = 0 then 0 else (C.choose (i - B - 1) : ℚ)) -
      t * ((C + 1).choose (i - B) : ℚ)) ≠ 0 := by
    intro h
    rw [← hi, x2611_10667_table3_1_aux1 B C (i - B) t hj, h, mul_zero, mul_zero] at hz
    exact hz rfl
  have hv := (x2611_10667_table3_1_aux5 p B C (i - B) t ht0 ht1 ht hj hbr).2
  rw [hi] at hv
  have hnonneg : 0 ≤ padicValRat p
      ((if i - B = 0 then 0 else (C.choose (i - B - 1) : ℚ)) -
      t * ((C + 1).choose (i - B) : ℚ)) := by
    split_ifs at hbr ⊢ with h
    · exact x2611_10667_table3_1_aux4 p t ht0 ht 0 _ hbr
    · exact x2611_10667_table3_1_aux4 p t ht0 ht _ _ hbr
  rw [hv]
  have he : ((B + C : ℕ) - i : ℤ) = (C : ℤ) - ((i - B : ℕ) : ℤ) := by omega
  rw [he]
  omega

theorem x2611_10667_table3_1_aux12 (q r C : ℕ) (hq2 : 2 < q) (hr2 : 2 < r)
    (m n : ℤ) (hbezout : n * (q : ℤ) - m * (r : ℤ) = 1)
    (hC : Int.ModEq ((q * r : ℕ) : ℤ) (C : ℤ) (m * (r : ℤ) + n * (q : ℤ)))
    (hC0 : 0 < C) : 2 ≤ C ∧ ¬r ∣ C := by
  obtain ⟨k, hk⟩ := hC.dvd
  push_cast at hk
  have hrC : (r : ℤ) ∣ (C : ℤ) - 1 := by
    refine ⟨2 * m - (q : ℤ) * k, ?_⟩
    linear_combination -hk + hbezout
  have hqC : (q : ℤ) ∣ (C : ℤ) + 1 := by
    refine ⟨2 * n - (r : ℤ) * k, ?_⟩
    linear_combination -hk - hbezout
  constructor
  · by_contra h
    have hc1 : C = 1 := by omega
    rw [hc1] at hqC
    have hq : q ∣ 2 := by exact_mod_cast hqC
    have := Nat.le_of_dvd (by norm_num : 0 < 2) hq
    omega
  · intro hrC'
    have hd : (r : ℤ) ∣ (C : ℤ) := by exact_mod_cast hrC'
    have h1 : (r : ℤ) ∣ 1 := by
      simpa using dvd_sub hd hrC
    have h1' : r ∣ 1 := by exact_mod_cast h1
    have := Nat.le_of_dvd (by norm_num : 0 < 1) h1'
    omega

theorem x2611_10667_table3_1 (q r B C : ℕ) (hq : q.Prime) (hr : r.Prime) (hq2 : 2 < q) (hr2 : 2 < r) (hqr : q ≠ r) (m n : ℤ) (hm : IsCoprime m ((q * r : ℕ) : ℤ)) (hn : IsCoprime n ((q * r : ℕ) : ℤ)) (hbezout : n * (q : ℤ) - m * (r : ℤ) = 1) (hB : Int.ModEq ((q * r : ℕ) : ℤ) (B : ℤ) (-m * (r : ℤ) - n * (q : ℤ))) (hC : Int.ModEq ((q * r : ℕ) : ℤ) (C : ℤ) (m * (r : ℤ) + n * (q : ℤ))) (hB0 : 0 < B) (hC0 : 0 < C) (hBlt : B < q * r) (hClt : C < q * r) (hBC : B + C = q * r) (t : ℚ) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (ht : 2 + 2 / ((r : ℚ) - 1) < (padicValRat r (t - 1) : ℚ)) : ((r : ℤ) - 1) * padicValRat r (1 : ℚ) = 0 ∧ ((x2611_10667_p B C t).coeff (q * r) ≠ 0 ∧ ((r : ℤ) - 1) * padicValRat r ((x2611_10667_p B C t).coeff (q * r)) = 0) ∧ ((x2611_10667_p B C t).coeff (q * r + 1) ≠ 0 ∧ ((r : ℤ) - 1) * padicValRat r ((x2611_10667_p B C t).coeff (q * r + 1)) = 0) ∧ ((x2611_10667_p B C t).coeff B ≠ 0 ∧ ((r : ℤ) - 1) * padicValRat r ((x2611_10667_p B C t).coeff (B)) = (C : ℤ) * (((r : ℤ) - 1) * padicValRat r (t - 1))) ∧ ((x2611_10667_p B C t).coeff (q * r - 1) ≠ 0 ∧ ((r : ℤ) - 1) * padicValRat r ((x2611_10667_p B C t).coeff (q * r - 1)) = ((r : ℤ) - 1) * padicValRat r (t - 1)) ∧ (∀ i : ℕ, B ≤ i → i ≤ q * r - 2 → (x2611_10667_p B C t).coeff i = 0 ∨ ((q * r : ℕ) - i : ℤ) * (((r : ℤ) - 1) * padicValRat r (t - 1)) ≤ ((r : ℤ) - 1) * padicValRat r ((x2611_10667_p B C t).coeff (i))) := by
  letI : Fact r.Prime := ⟨hr⟩
  have hpos : 0 < padicValRat r (t - 1) := by
    have hrQ : (2 : ℚ) < r := by exact_mod_cast hr2
    have hdiv : (0 : ℚ) < 2 / ((r : ℚ) - 1) := div_pos (by norm_num) (by linarith)
    have hv : (0 : ℚ) < (padicValRat r (t - 1) : ℚ) := by linarith
    exact_mod_cast hv
  have htu := x2611_10667_table3_1_aux3 r t hpos
  obtain ⟨hC2, hCp⟩ := x2611_10667_table3_1_aux12 q r C hq2 hr2 m n hbezout hC hC0
  have hv : padicValRat r (1 - t) = padicValRat r (t - 1) := by
    rw [show 1 - t = -(t - 1) by ring, padicValRat.neg]
  have hs : (-1 : ℚ) ^ B ≠ 0 := pow_ne_zero _ (by norm_num)
  have hx : (1 - t) ^ C ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm ht1))
  have hy : (-t) ^ C ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr ht0)
  have hBval : padicValRat r ((x2611_10667_p B C t).coeff B) =
      (C : ℤ) * padicValRat r (t - 1) := by
    rw [x2611_10667_table3_1_aux7 B C t ht0, padicValRat.mul hs hx]
    simp [hv]
  have hBne : (x2611_10667_p B C t).coeff B ≠ 0 := by
    rw [x2611_10667_table3_1_aux7 B C t ht0]
    exact mul_ne_zero hs hx
  have htopne : (x2611_10667_p B C t).coeff (B + C + 1) ≠ 0 := by
    rw [x2611_10667_table3_1_aux8 B C t ht1]
    exact mul_ne_zero hs hy
  have htopval : padicValRat r ((x2611_10667_p B C t).coeff (B + C + 1)) = 0 := by
    rw [x2611_10667_table3_1_aux8 B C t ht1, padicValRat.mul hs hy]
    simp [htu]
  have hmid := x2611_10667_table3_1_aux9 r B C t hC0 ht0 ht1 hpos
  have hpred := x2611_10667_table3_1_aux10 r B C t hC2 hCp ht0 ht1 hpos
  rw [← hBC]
  refine ⟨by simp, ⟨hmid.1, by rw [hmid.2]; ring⟩,
    ⟨htopne, by rw [htopval]; ring⟩,
    ⟨hBne, by rw [hBval]; ring⟩,
    ⟨hpred.1, by rw [hpred.2]⟩, ?_⟩
  intro i hiB hiC
  have hbound := x2611_10667_table3_1_aux11 r B C i t ht0 ht1 htu hiB (by omega)
  rcases hbound with hzero | hbound
  · exact Or.inl hzero
  · right
    have hmul := mul_le_mul_of_nonneg_left hbound (show (0 : ℤ) ≤ (r : ℤ) - 1 by omega)
    simpa only [mul_left_comm] using hmul
end

-- forge:entry x2611_16923_lemma2_6 kind=proved origin=paper
section
/- Lemma 2.6 -/
open scoped BigOperators Classical

theorem x2611_16923_lemma2_6_aux1 {r : ℕ} (k : Fin r → ℕ)
    (L : List (Fin r)) (hL : L.Nodup) (weak : Bool) (lower : ℕ)
    (upper : Option ℕ) (e : Fin r →₀ ℕ) :
    x2611_16923_li r weak lower upper
        (L.map fun i => (k i, Finsupp.single i 1)) e =
      if (∀ i, i ∉ L → e i = 0) ∧ (∀ i ∈ L, lower ≤ e i) ∧
        (L.map e).Pairwise (fun a b => if weak then a ≤ b else a < b) ∧
        (∀ M ∈ upper, ∀ i ∈ L, e i < M) then
        (L.map fun i => (((e i : ℚ) ^ k i)⁻¹)).prod else 0 := by
  classical
  have hmap : L.map (fun i => (k i, Finsupp.single i 1)) =
      List.ofFn (fun i : Fin L.length => (k (L.get i), Finsupp.single (L.get i) 1)) := by
    simpa only [List.ofFn_get] using
      (List.ofFn_comp' L.get (fun i : Fin r => (k i, Finsupp.single i (1 : ℕ)))).symm
  rw [hmap, x2611_16923_lemma2_4_aux1]
  let ne : Fin L.length → Fin (e.sum (fun _ a => a) + 1) :=
    fun i => ⟨e (L.get i), x2611_16923_lemma2_4_aux2 e (L.get i)⟩
  have hs (n : Fin L.length → Fin (e.sum (fun _ a => a) + 1)) (i : Fin L.length) :
      (∑ j, (n j).val • Finsupp.single (L.get j) 1) (L.get i) = (n i).val := by
    simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.single_apply,
      smul_eq_mul]
    have hi (j : Fin L.length) : L.get j = L.get i ↔ j = i := hL.get_inj_iff
    simpa only [hi, mul_ite, mul_one, mul_zero, Finset.mem_univ, ↓reduceIte] using
      (Finset.sum_ite_eq' Finset.univ i (fun j : Fin L.length => (n j).val))
  have hz (n : Fin L.length → Fin (e.sum (fun _ a => a) + 1))
      (i : Fin r) (hi : i ∉ L) :
      (∑ j, (n j).val • Finsupp.single (L.get j) 1) i = 0 := by
    rw [Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro j _
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    have : L.get j ≠ i := by rintro rfl; exact hi (List.get_mem _ _)
    rw [if_neg this, mul_zero]
  have hsum : (∑ j, (ne j).val • Finsupp.single (L.get j) 1) = e ↔
      ∀ i, i ∉ L → e i = 0 := by
    constructor
    · intro h i hi
      rw [← h, hz ne i hi]
    · intro h
      ext i
      by_cases hi : i ∈ L
      · obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hi
        exact hs ne j
      · rw [hz ne i hi, h i hi]
  rw [Fintype.sum_eq_single ne]
  · have hm : List.ofFn (fun i : Fin L.length => e (L.get i)) = L.map e := by
      rw [List.ofFn_comp', List.ofFn_get]
    have hp : (∏ i : Fin L.length, (((e (L.get i) : ℚ) ^ k (L.get i))⁻¹)) =
        (L.map fun i => (((e i : ℚ) ^ k i)⁻¹)).prod := by
      rw [← List.prod_ofFn]
      congr 1
      simpa only [List.ofFn_get] using
        (List.ofFn_comp' L.get (fun i : Fin r => (((e i : ℚ) ^ k i)⁻¹)))
    change (if (∀ i : Fin L.length, lower ≤ e (L.get i)) ∧
      (List.ofFn (fun i : Fin L.length => e (L.get i))).Pairwise _ ∧
      (∀ M ∈ upper, ∀ i : Fin L.length, e (L.get i) < M) ∧ _ then _ else _) = _
    simp only [ne, hm, hsum, hp]
    congr 1
    simp only [List.forall_mem_iff_get]
    apply propext
    tauto
  · intro n hn
    apply if_neg
    rintro ⟨_, _, _, he⟩
    apply hn
    funext i
    apply Fin.ext
    have H := congrArg (fun v : Fin r →₀ ℕ => v (L.get i)) he
    rw [hs] at H
    exact H

theorem x2611_16923_lemma2_6_aux2 {σ : Type*} (f g : MvPowerSeries σ ℚ)
    (p : σ → Prop) (e : σ →₀ ℕ)
    (hf : ∀ d, f d ≠ 0 → ∀ i, ¬ p i → d i = 0)
    (hg : ∀ d, g d ≠ 0 → ∀ i, p i → d i = 0) :
    (f * g) e = f (e.filter p) * g (e.filter (fun i => ¬ p i)) := by
  classical
  change MvPowerSeries.coeff e (f * g) = _
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_single (e.filter p, e.filter (fun i => ¬ p i))
  · intro q hq hne
    change f q.1 * g q.2 = 0
    by_contra hzero
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hzero
    have he : q.1 + q.2 = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
    apply hne
    apply Prod.ext
    · ext i
      have hi := congrArg (fun d : σ →₀ ℕ => d i) he
      by_cases hp : p i
      · simpa [Finsupp.filter_apply, hp, hg q.2 h2 i hp] using hi
      · simp [Finsupp.filter_apply, hp, hf q.1 h1 i hp]
    · ext i
      have hi := congrArg (fun d : σ →₀ ℕ => d i) he
      by_cases hp : p i
      · simp [Finsupp.filter_apply, hp, hg q.2 h2 i hp]
      · simpa [Finsupp.filter_apply, hp, hf q.1 h1 i hp] using hi
  · intro h
    exact False.elim (h (Finset.HasAntidiagonal.mem_antidiagonal.mpr (Finsupp.filter_add_filter_not e p)))

theorem x2611_16923_lemma2_6_aux3 {r : ℕ} (k : Fin r → ℕ)
    (A B : List (Fin r)) (hAB : (A ++ B).Nodup) (N : ℕ) (e : Fin r →₀ ℕ) :
    (x2611_16923_li r false 1 none (A.map fun i => (k i, Finsupp.single i 1)) *
      x2611_16923_li r true N none (B.reverse.map fun i => (k i, Finsupp.single i 1))) e =
    if (∀ i, i ∉ A ++ B → e i = 0) ∧
      (∀ i ∈ A, 1 ≤ e i) ∧ (A.map e).Pairwise (· < ·) ∧
      (∀ i ∈ B, N ≤ e i) ∧ (B.map e).Pairwise (· ≥ ·) then
      ((A ++ B).map fun i => (((e i : ℚ) ^ k i)⁻¹)).prod else 0 := by
  classical
  obtain ⟨hA, hB, hd⟩ := List.nodup_append.mp hAB
  have hab (i : Fin r) (ha : i ∈ A) : i ∉ B := fun hb => hd i ha i hb rfl
  have hba (i : Fin r) (hb : i ∈ B) : i ∉ A := fun ha => hd i ha i hb rfl
  let f := x2611_16923_li r false 1 none (A.map fun i => (k i, Finsupp.single i 1))
  let g := x2611_16923_li r true N none (B.reverse.map fun i => (k i, Finsupp.single i 1))
  have hf : ∀ d, f d ≠ 0 → ∀ i, i ∉ A → d i = 0 := by
    intro d h
    dsimp [f] at h
    rw [x2611_16923_lemma2_6_aux1 k A hA] at h
    simp only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte] at h
    split_ifs at h with H
    · exact H.1
    · exact (h rfl).elim
  have hg : ∀ d, g d ≠ 0 → ∀ i, i ∈ A → d i = 0 := by
    intro d h
    dsimp [g] at h
    rw [x2611_16923_lemma2_6_aux1 k B.reverse (List.nodup_reverse.mpr hB)] at h
    simp only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte] at h
    split_ifs at h with H
    · intro i hi
      exact H.1 i (by simpa using hab i hi)
    · exact (h rfl).elim
  rw [x2611_16923_lemma2_6_aux2 f g (fun i => i ∈ A) e hf hg]
  dsimp [f, g]
  rw [x2611_16923_lemma2_6_aux1 k A hA,
    x2611_16923_lemma2_6_aux1 k B.reverse (List.nodup_reverse.mpr hB)]
  have hmA (u : ℕ → ℕ) : A.map (fun i => u ((e.filter (fun i => i ∈ A)) i)) =
      A.map (fun i => u (e i)) := by
    apply List.map_congr_left
    intro i hi
    simp [Finsupp.filter_apply, hi]
  have hAmap : A.map (e.filter (fun i => i ∈ A)) = A.map e := hmA id
  have hBmap : B.reverse.map (e.filter (fun i => i ∉ A)) = B.reverse.map e := by
    apply List.map_congr_left
    intro i hi
    simp [Finsupp.filter_apply, hba i (by simpa using hi)]
  have hpA : (A.map fun i => (((e.filter (fun i => i ∈ A)) i : ℚ) ^ k i)⁻¹) =
      A.map (fun i => (((e i : ℚ) ^ k i)⁻¹)) := by
    apply List.map_congr_left
    intro i hi
    simp [Finsupp.filter_apply, hi]
  have hpB : (B.reverse.map fun i => (((e.filter (fun i => i ∉ A)) i : ℚ) ^ k i)⁻¹) =
      B.reverse.map (fun i => (((e i : ℚ) ^ k i)⁻¹)) := by
    apply List.map_congr_left
    intro i hi
    simp [Finsupp.filter_apply, hba i (by simpa using hi)]
  have hsA : ∀ i, i ∉ A → (e.filter (fun i => i ∈ A)) i = 0 := by
    intro i hi; simp [Finsupp.filter_apply, hi]
  have hsB : (∀ i, i ∉ B.reverse → (e.filter (fun i => i ∉ A)) i = 0) ↔
      (∀ i, i ∉ A ++ B → e i = 0) := by
    constructor
    · intro h i hi
      have ha : i ∉ A := fun ha => hi (List.mem_append_left _ ha)
      have hb : i ∉ B.reverse := by
        simpa using (show i ∉ B from fun hb => hi (List.mem_append_right _ hb))
      simpa [Finsupp.filter_apply, ha] using h i hb
    · intro h i hi
      by_cases ha : i ∈ A
      · simp [Finsupp.filter_apply, ha]
      · simpa [Finsupp.filter_apply, ha] using h i (by simpa [ha] using hi)
  have hlA : (∀ i ∈ A, 1 ≤ (e.filter (fun i => i ∈ A)) i) ↔ ∀ i ∈ A, 1 ≤ e i := by
    constructor <;> intro h i hi
    · simpa only [Finsupp.filter_apply, if_pos hi] using h i hi
    · simpa only [Finsupp.filter_apply, if_pos hi] using h i hi
  have hlB : (∀ i ∈ B.reverse, N ≤ (e.filter (fun i => i ∉ A)) i) ↔
      ∀ i ∈ B, N ≤ e i := by
    simp only [List.mem_reverse]
    constructor <;> intro h i hi
    · simpa [Finsupp.filter_apply, hba i hi] using h i hi
    · simpa [Finsupp.filter_apply, hba i hi] using h i hi
  simp only [Finsupp.filter_eq_indicator] at hAmap hBmap hpA hpB hsA hsB hlA hlB ⊢
  rw [hAmap, hBmap, hpA, hpB]
  simp only [hsA, true_and, hsB, hlA, hlB,
    Bool.false_eq_true, Bool.true_eq, ↓reduceIte, Option.mem_def,
    reduceCtorEq, false_implies, forall_const, and_true,
    List.map_reverse, List.pairwise_reverse, List.prod_reverse,
    List.map_append, List.prod_append]
  split_ifs <;> simp_all <;> tauto

theorem x2611_16923_lemma2_6_aux4 : ∀ (L : List ℕ) (M : ℕ), 1 ≤ M → ∀ w : ℚ,
      (if (∀ a ∈ L, 1 ≤ a) ∧ L.Pairwise (· < ·) ∧ (∀ a ∈ L, a < M)
        then w else 0) =
      ∑ j ∈ Finset.range (L.length + 1), (-1 : ℚ) ^ (L.length - j) *
        (if (∀ a ∈ L.take j, 1 ≤ a) ∧ (L.take j).Pairwise (· < ·) ∧
          (∀ a ∈ L.drop j, M ≤ a) ∧ (L.drop j).Pairwise (· ≥ ·)
          then w else 0) := by

  intro L
  induction L using List.reverseRecOn with
  | nil => intro M hM w; simp
  | append_singleton L a ih =>
    intro M hM w
    let P (K : List ℕ) (b : ℕ) : ℚ :=
      if (∀ x ∈ K, 1 ≤ x) ∧ K.Pairwise (· < ·) ∧ (∀ x ∈ K, x < b) then w else 0
    let T (K : List ℕ) (b j : ℕ) : ℚ :=
      if (∀ x ∈ K.take j, 1 ≤ x) ∧ (K.take j).Pairwise (· < ·) ∧
        (∀ x ∈ K.drop j, b ≤ x) ∧ (K.drop j).Pairwise (· ≥ ·) then w else 0
    simp only [List.length_append, List.length_singleton]
    change P (L ++ [a]) M =
      ∑ j ∈ Finset.range ((L.length + 1) + 1),
        (-1 : ℚ) ^ (L.length + 1 - j) * T (L ++ [a]) M j
    have hlast : T (L ++ [a]) M (L.length + 1) =
        if (∀ x ∈ L ++ [a], 1 ≤ x) ∧ (L ++ [a]).Pairwise (· < ·) then w else 0 := by
      dsimp [T]
      rw [show L.length + 1 = (L ++ [a]).length by simp, List.take_length, List.drop_length]
      simp
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul, hlast]
    by_cases ha : a < M
    · have hzero (j : ℕ) (hj : j ∈ Finset.range (L.length + 1)) :
          T (L ++ [a]) M j = 0 := by
        have hj : j ≤ L.length := by simpa using hj
        dsimp [T]
        apply if_neg
        rintro ⟨_, _, h, _⟩
        have hmem : a ∈ (L ++ [a]).drop j := by
          rw [List.drop_append_of_le_length hj]
          simp
        have := h a hmem
        omega
      rw [Finset.sum_eq_zero (fun j hj => by rw [hzero j hj, mul_zero]), zero_add]
      dsimp [P]
      congr 1
      apply propext
      constructor
      · tauto
      · rintro ⟨hp, hs⟩
        refine ⟨hp, hs, ?_⟩
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · have hxa : x < a := (List.pairwise_append.mp hs).2.2 x hx a (by simp)
          omega
        · have hx : x = a := List.mem_singleton.mp hx
          simpa [hx] using ha
    · have ham : M ≤ a := by omega
      have ha1 : 1 ≤ a := le_trans hM ham
      have hpzero : P (L ++ [a]) M = 0 := by
        dsimp [P]
        apply if_neg
        rintro ⟨_, _, h⟩
        have := h a (by simp)
        omega
      have hfinal : (if (∀ x ∈ L ++ [a], 1 ≤ x) ∧ (L ++ [a]).Pairwise (· < ·)
          then w else 0) = P L a := by
        simp only [P, List.forall_mem_append, List.forall_mem_singleton,
          List.pairwise_append, List.pairwise_singleton, and_true, ha1]
        congr 1
        apply propext
        tauto
      have hterm (j : ℕ) (hj : j ∈ Finset.range (L.length + 1)) :
          T (L ++ [a]) M j = T L a j := by
        have hj : j ≤ L.length := by simpa using hj
        simp only [T, List.take_append_of_le_length hj, List.drop_append_of_le_length hj,
          List.forall_mem_append, List.forall_mem_singleton,
          List.pairwise_append, List.pairwise_singleton, and_true, true_and, ham]
        congr 1
        apply propext
        constructor
        · rintro ⟨hp, hs, hl, hd, hb⟩
          exact ⟨hp, hs, hb, hd⟩
        · rintro ⟨hp, hs, hb, hd⟩
          exact ⟨hp, hs, (fun x hx => le_trans ham (hb x hx)), hd, hb⟩
      have hsum : (∑ j ∈ Finset.range (L.length + 1),
          (-1 : ℚ) ^ (L.length + 1 - j) * T (L ++ [a]) M j) =
          -(∑ j ∈ Finset.range (L.length + 1), (-1 : ℚ) ^ (L.length - j) * T L a j) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j ≤ L.length := by simpa using hj
        rw [hterm j hj, show L.length + 1 - j = (L.length - j) + 1 by omega, pow_succ]
        ring
      rw [hpzero, hsum, hfinal]
      have hi := ih a ha1 w
      change P L a = ∑ j ∈ Finset.range (L.length + 1),
        (-1 : ℚ) ^ (L.length - j) * T L a j at hi
      rw [← hi]
      ring


theorem x2611_16923_lemma2_6 (N r : ℕ) (hN : 1 ≤ N) (k : Fin r → ℕ)
    (hk : ∀ i, 0 < k i) :
    x2611_16923_li r false 1 (some N) (x2611_16923_entries k) =
      ∑ j ∈ Finset.range (r + 1), (-1 : MvPowerSeries (Fin r) ℚ) ^ (r - j) *
        x2611_16923_li r false 1 none ((x2611_16923_entries k).take j) *
        x2611_16923_li r true N none ((x2611_16923_entries k).drop j).reverse := by
  classical
  have cancel := x2611_16923_lemma2_6_aux4
  let L := List.finRange r
  have hL : L.Nodup := List.nodup_finRange r
  have hlen : L.length = r := List.length_finRange
  have he : x2611_16923_entries k = L.map (fun i => (k i, Finsupp.single i 1)) := by
    unfold x2611_16923_entries L
    rw [← List.ofFn_id r, List.map_ofFn]
    rfl
  have hsign (n : ℕ) : (-1 : MvPowerSeries (Fin r) ℚ) ^ n =
      MvPowerSeries.C ((-1 : ℚ) ^ n) := by simp
  apply MvPowerSeries.ext
  intro e
  simp only [map_sum]
  rw [he]
  change x2611_16923_li r false 1 (some N) (L.map _) e =
    ∑ j ∈ Finset.range (r + 1), MvPowerSeries.coeff e
      ((-1 : MvPowerSeries (Fin r) ℚ) ^ (r-j) * _ * _)
  simp only [hsign, mul_assoc, MvPowerSeries.coeff_C_mul,
    ← List.map_take, ← List.map_drop, ← List.map_reverse]
  rw [x2611_16923_lemma2_6_aux1 k L hL]
  have hcut (j : ℕ) := x2611_16923_lemma2_6_aux3 k (L.take j) (L.drop j)
    (by simpa using hL) N e
  simp only [List.take_append_drop] at hcut
  simp_rw [show ∀ j, MvPowerSeries.coeff e
    (x2611_16923_li r false 1 none ((L.take j).map fun i => (k i, Finsupp.single i 1)) *
      x2611_16923_li r true N none ((L.drop j).reverse.map fun i => (k i, Finsupp.single i 1))) =
    (if (∀ i, i ∉ L → e i = 0) ∧
      (∀ i ∈ L.take j, 1 ≤ e i) ∧ ((L.take j).map e).Pairwise (· < ·) ∧
      (∀ i ∈ L.drop j, N ≤ e i) ∧ ((L.drop j).map e).Pairwise (· ≥ ·) then
      (L.map fun i => (((e i : ℚ) ^ k i)⁻¹)).prod else 0) from hcut]
  have hout : ∀ i, i ∉ L → e i = 0 := by simp [L]
  have houtiff : (∀ i, i ∉ L → e i = 0) ↔ True := iff_true_intro hout
  simp only [houtiff, true_and, Bool.false_eq_true, ↓reduceIte,
    Option.mem_def, Option.some.injEq, forall_eq']
  convert cancel (L.map e) N hN ((L.map fun i => (((e i : ℚ) ^ k i)⁻¹)).prod) using 1 <;>
    simp only [List.length_map, hlen, List.forall_mem_map,
      ← List.map_take, ← List.map_drop]
end

-- forge:entry x2611_15210_cor4_4_s1h1 kind=proved origin=decomposition
section
/- x2611_15210_cor4_4 的证明骨架中第 1 个空洞 -/
open scoped BigOperators

lemma x2611_15210_cor4_4_s1h1_aux1 {α : Type*} [Fintype α]
    (B : Finset (Finset α)) (hB : ∀ I ∈ B, I.Nonempty) :
    ∃ T : Finset α, Fintype.card α ≤ T.card + B.card ∧
      ∀ I ∈ B, ¬ I ⊆ T := by
  classical
  rcases B.eq_empty_or_nonempty with rfl | hne
  · exact ⟨Finset.univ, by simp, by simp⟩
  haveI : Nonempty α := ⟨(hB hne.choose hne.choose_spec).choose⟩
  let f : Finset α → α := fun I => if h : I ∈ B then (hB I h).choose else
    Classical.epsilon (fun _ => True)
  have hf : ∀ I ∈ B, f I ∈ I := by
    intro I hI
    simp only [f, dif_pos hI]
    exact (hB I hI).choose_spec
  let D := B.image f
  refine ⟨Finset.univ \ D, ?_, ?_⟩
  · have hd : D.card ≤ B.card := Finset.card_image_le
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
    simp only [Finset.card_univ] at hc
    omega
  · intro I hI hIT
    have h := hIT (hf I hI)
    have hm : f I ∈ D := Finset.mem_image_of_mem f hI
    simpa using (Finset.mem_sdiff.mp h).2 hm

lemma x2611_15210_cor4_4_s1h1_aux2 {α S : Type*} [Fintype α] [Fintype S]
    (I : Finset α) (P : (I → S) → Prop) :
    Nat.card {a : α → S // P (fun i => a i)} =
      Nat.card {a : I → S // P a} * (Fintype.card S) ^ (Fintype.card α - I.card) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun x : α => x ∈ I) (fun _ => S)
  let e' : {a : α → S // P (fun i => a i)} ≃
      {a : (I → S) × ({x : α // x ∉ I} → S) // P a.1} :=
    e.subtypeEquiv (fun _ => Iff.rfl)
  have h := Nat.card_congr (e'.trans Equiv.prodSubtypeFstEquivSubtypeProd)
  simpa [Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl] using h

lemma x2611_15210_cor4_4_s1h1_aux3 {α S G : Type*} [Fintype α] [Fintype S]
    [AddCommMonoid G] (I : Finset α) (L : ℕ) (hI : I.card = L) (p : S → G) :
    Nat.card {a : α → S // ∑ i ∈ I, p (a i) = 0} =
      Nat.card {v : Fin L → S // ∑ i, p (v i) = 0} *
        (Fintype.card S) ^ (Fintype.card α - L) := by
  classical
  have hc : Fintype.card I = L := by simpa using hI
  let e : I ≃ Fin L := Fintype.equivFinOfCardEq hc
  let e' : (I → S) ≃ (Fin L → S) := Equiv.arrowCongr e (Equiv.refl S)
  have he : ∀ a : I → S, (∑ i, p (a i)) = ∑ i, p (e' a i) := by
    intro a
    exact Fintype.sum_equiv e _ _ (by intro i; simp [e'])
  have hk : Nat.card {a : I → S // ∑ i, p (a i) = 0} =
      Nat.card {v : Fin L → S // ∑ i, p (v i) = 0} :=
    Nat.card_congr (e'.subtypeEquiv (by intro a; rw [he a]))
  have h := x2611_15210_cor4_4_s1h1_aux2 I (fun a : I → S => ∑ i, p (a i) = 0)
  have hs : ∀ a : α → S, (∑ i : I, p (a i)) = ∑ i ∈ I, p (a i) :=
    fun a => Finset.sum_coe_sort I (fun i => p (a i))
  simpa only [hs, hk, hI] using h

lemma x2611_15210_cor4_4_s1h1_aux4 (M L : ℕ) (S G : Type*) [Fintype S]
    [Nonempty S] [AddCommMonoid G] [DecidableEq G] (p : S → G) (θ : ℝ)
    (hθ : θ = (Nat.card {v : Fin L → S // ∑ i, p (v i) = 0} : ℝ) /
      (Fintype.card S : ℝ) ^ L) :
    ∃ a : Fin M → S,
      (((Finset.univ.powersetCard L).filter
        (fun I : Finset (Fin M) => ∑ i ∈ I, p (a i) = 0)).card : ℝ) ≤
        (M.choose L : ℝ) * θ := by
  classical
  let U : Finset (Finset (Fin M)) := Finset.univ.powersetCard L
  let B := fun a : Fin M → S => U.filter (fun I => ∑ i ∈ I, p (a i) = 0)
  have hs : ∑ a : Fin M → S, ((B a).card : ℝ) =
      ∑ I ∈ U, (Nat.card {a : Fin M → S // ∑ i ∈ I, p (a i) = 0} : ℝ) := by
    simp only [B, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [Finset.sum_comm]
  have hn : (0 : ℝ) < Fintype.card S := Nat.cast_pos.mpr Fintype.card_pos
  have he : ∀ I ∈ U,
      (Nat.card {a : Fin M → S // ∑ i ∈ I, p (a i) = 0} : ℝ) =
        θ * (Fintype.card S : ℝ) ^ M := by
    intro I hI
    have hIL := (Finset.mem_powersetCard.mp hI).2
    have hLM : L ≤ M := by
      have hh := Finset.card_le_card (Finset.subset_univ I)
      simpa [hIL] using hh
    have hc := x2611_15210_cor4_4_s1h1_aux3 I L hIL p
    rw [hc, Nat.cast_mul, Nat.cast_pow, hθ]
    simp only [Fintype.card_fin]
    rw [show (Fintype.card S : ℝ) ^ M =
      (Fintype.card S : ℝ) ^ (M - L) * (Fintype.card S : ℝ) ^ L by
        rw [← pow_add, Nat.sub_add_cancel hLM]]
    field_simp
  have hh : ∑ a : Fin M → S, ((B a).card : ℝ) ≤
      ∑ _a : Fin M → S, (M.choose L : ℝ) * θ := by
    rw [hs]
    rw [Finset.sum_congr rfl he]
    simp only [Finset.sum_const, nsmul_eq_mul, U, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin, Fintype.card_fun, Nat.cast_pow]
    ring_nf
    exact le_rfl
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_sum_le
    (s := Finset.univ) Finset.univ_nonempty hh
  exact ⟨a, ha⟩

lemma x2611_15210_cor4_4_s1h1_aux5 (M L : ℕ) (hL : 0 < L)
    (S G : Type*) [Fintype S] [Nonempty S] [AddCommMonoid G] [DecidableEq G]
    (p : S → G) (a : Fin M → S) (A : ℝ)
    (ha : (((Finset.univ.powersetCard L).filter
      (fun I : Finset (Fin M) => ∑ i ∈ I, p (a i) = 0)).card : ℝ) ≤ (M : ℝ) - A) :
    ∃ (N : ℕ) (b : Fin N → S), A ≤ (N : ℝ) ∧
      ∀ I : Finset (Fin N), I.card = L → ∑ i ∈ I, p (b i) ≠ 0 := by
  classical
  let B := (Finset.univ.powersetCard L).filter
      (fun I : Finset (Fin M) => ∑ i ∈ I, p (a i) = 0)
  have hB : ∀ I ∈ B, I.Nonempty := by
    intro I hI
    have hc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hI).1).2
    exact Finset.card_pos.mp (by omega)
  obtain ⟨T, hc, hT⟩ := x2611_15210_cor4_4_s1h1_aux1 B hB
  let e : Fin T.card ≃ T := (Fintype.equivFinOfCardEq (by simp)).symm
  let f : Fin T.card ↪ Fin M := e.toEmbedding.trans (Function.Embedding.subtype _)
  refine ⟨T.card, fun i => a (f i), ?_, ?_⟩
  · have hc' : (M : ℝ) ≤ (T.card : ℝ) + B.card := by exact_mod_cast (by simpa using hc : M ≤ T.card + B.card)
    change (B.card : ℝ) ≤ (M : ℝ) - A at ha
    linarith
  · intro I hI hz
    have hm : I.map f ∈ B := by
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by simpa using hI⟩
      · simpa only [Finset.sum_map] using hz
    apply hT (I.map f) hm
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact (e i).property

lemma x2611_15210_cor4_4_s1h1_aux6 (L : ℕ) (hL : 4 ≤ L) :
    2 * (3 * (L : ℝ) / (4 * Real.exp 1)) ^ (L - 1) ≤ (L.factorial : ℝ) := by
  have he : 0 < Real.exp 1 := Real.exp_pos _
  have hf : (0 : ℝ) < L.factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hl : (4 : ℝ) ≤ L := by exact_mod_cast hL
  have hfac : ((L : ℝ) / Real.exp 1) ^ L ≤ (L.factorial : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (L : ℝ) (by positivity) L
    have hexp : Real.exp (L : ℝ) = Real.exp 1 ^ L := by
      simpa using Real.exp_nat_mul (1 : ℝ) L
    rw [hexp, div_le_iff₀ hf] at h
    rw [div_pow, div_le_iff₀ (pow_pos he L)]
    nlinarith [h]
  have hb : (3 / 4 : ℝ) ^ (L - 1) ≤ (3 / 4 : ℝ) ^ 3 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hd : (1 : ℝ) ≤ (L : ℝ) / Real.exp 1 := by
    apply (le_div_iff₀ he).mpr
    have := Real.exp_one_lt_three
    linarith
  have hb' : 2 * (3 / 4 : ℝ) ^ (L - 1) ≤ (L : ℝ) / Real.exp 1 := by
    norm_num at hb
    linarith
  calc
    2 * (3 * (L : ℝ) / (4 * Real.exp 1)) ^ (L - 1) =
        (2 * (3 / 4 : ℝ) ^ (L - 1)) * ((L : ℝ) / Real.exp 1) ^ (L - 1) := by
      rw [show 3 * (L : ℝ) / (4 * Real.exp 1) =
        (3 / 4 : ℝ) * ((L : ℝ) / Real.exp 1) by ring, mul_pow]
      ring
    _ ≤ ((L : ℝ) / Real.exp 1) * ((L : ℝ) / Real.exp 1) ^ (L - 1) :=
      mul_le_mul_of_nonneg_right hb' (by positivity)
    _ = ((L : ℝ) / Real.exp 1) ^ L := by
      rw [← pow_succ']
      congr 1
      omega
    _ ≤ (L.factorial : ℝ) := hfac

lemma x2611_15210_cor4_4_s1h1_aux7 (L : ℕ) (hL : 4 ≤ L) (θ t : ℝ)
    (hθ : 0 < θ) (ht : 0 < t) (htθ : θ * t ^ (L - 1) = 1)
    (hA : 1 ≤ (L : ℝ) / (4 * Real.exp 1) * t) :
    ∃ M : ℕ, 2 * ((L : ℝ) / (4 * Real.exp 1) * t) ≤ (M : ℝ) ∧
      (M.choose L : ℝ) * θ ≤ (M : ℝ) / 2 := by
  let A := (L : ℝ) / (4 * Real.exp 1) * t
  let M := ⌈2 * A⌉₊
  have hMlo : 2 * A ≤ (M : ℝ) := Nat.le_ceil _
  have hMhi : (M : ℝ) ≤ 3 * A := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 2 * A by dsimp [A]; positivity)
    change (M : ℝ) < 2 * A + 1 at hc
    change 1 ≤ A at hA
    linarith
  refine ⟨M, hMlo, ?_⟩
  have hf : (0 : ℝ) < L.factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hpow : (M : ℝ) ^ (L - 1) * θ ≤
      (3 * (L : ℝ) / (4 * Real.exp 1)) ^ (L - 1) := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ M by positivity) hMhi (L - 1)
    have h' := mul_le_mul_of_nonneg_right h hθ.le
    have heq : 3 * A = (3 * (L : ℝ) / (4 * Real.exp 1)) * t := by dsimp [A]; ring
    rw [heq, mul_pow] at h'
    rw [mul_assoc, mul_comm (t ^ (L - 1)) θ, htθ, mul_one] at h'
    exact h'
  have hb := x2611_15210_cor4_4_s1h1_aux6 L hL
  have hhalf : ((M : ℝ) ^ (L - 1) * θ) / (L.factorial : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hf).mpr
    nlinarith
  calc
    (M.choose L : ℝ) * θ ≤ ((M : ℝ) ^ L / (L.factorial : ℝ)) * θ :=
      mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div L M) hθ.le
    _ = (M : ℝ) * (((M : ℝ) ^ (L - 1) * θ) / (L.factorial : ℝ)) := by
      have hp : (M : ℝ) ^ L = (M : ℝ) * (M : ℝ) ^ (L - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [hp]
      ring
    _ ≤ (M : ℝ) * (1 / 2) := mul_le_mul_of_nonneg_left hhalf (by positivity)
    _ = (M : ℝ) / 2 := by ring

theorem x2611_15210_cor4_4_s1h1 : ∀ (L : ℕ), 4 ≤ L →
    ∀ (S G : Type) [Fintype S] [Nonempty S] [inst : AddCommMonoid G]
      (p : S → G) (θ : ℝ), 0 < θ →
      θ = (↑(Nat.card {v : Fin L → S // ∑ i : Fin L, p (v i) = 0}) : ℝ) /
        (↑(Nat.card S) : ℝ) ^ L →
      ∃ (N : ℕ) (a : Fin N → S),
        (↑L : ℝ) / (4 * Real.exp 1) * θ ^ (-1 / ((↑L : ℝ) - 1)) ≤ (↑N : ℝ) ∧
        ∀ (I : Finset (Fin N)), I.card = L → ∑ i ∈ I, p (a i) ≠ 0 := by
  classical
  intro L hL S G _ _ _ p θ hθ hθeq
  let t := θ ^ (-1 / ((L : ℝ) - 1))
  let A := (L : ℝ) / (4 * Real.exp 1) * t
  have ht : 0 < t := Real.rpow_pos_of_pos hθ _
  have hLr : (0 : ℝ) < (L : ℝ) - 1 := by
    have : (4 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have htθ : θ * t ^ (L - 1) = 1 := by
    dsimp only [t]
    rw [← Real.rpow_mul_natCast hθ.le]
    have hc : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ L), Nat.cast_one]
    rw [hc, show (-1 / ((L : ℝ) - 1)) * ((L : ℝ) - 1) = -1 by
      field_simp, Real.rpow_neg_one]
    exact mul_inv_cancel₀ hθ.ne'
  by_cases hA : A ≤ ((L - 1 : ℕ) : ℝ)
  · refine ⟨L - 1, fun _ => Classical.choice (inferInstance : Nonempty S), hA, ?_⟩
    intro I hI
    have hc : I.card ≤ L - 1 := by simpa using Finset.card_le_univ I
    omega
  · have hA1 : 1 ≤ A := by
      have hc : (3 : ℝ) ≤ ((L - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ L - 1)
      linarith
    obtain ⟨M, hM, hb⟩ := x2611_15210_cor4_4_s1h1_aux7 L hL θ t hθ ht htθ hA1
    obtain ⟨a, ha⟩ := x2611_15210_cor4_4_s1h1_aux4 M L S G p θ
      (by simpa only [Nat.card_eq_fintype_card] using hθeq)
    apply x2611_15210_cor4_4_s1h1_aux5 M L (by omega) S G p a A
    change 2 * A ≤ (M : ℝ) at hM
    linarith
end

-- forge:entry x2611_12360_table1 kind=proved origin=paper
section
/- Table 1 -/

lemma x2611_12360_table1_aux1 (p x: ℝ) (n: ℤ) :
    ((x + (n: ℝ) * p: ℝ): AddCircle p) = (x: AddCircle p):= by
  rw [AddCircle.coe_add]
  have hn: (((n: ℝ) * p: ℝ): AddCircle p) = 0:= by
    rw [← zsmul_eq_mul,AddCircle.coe_zsmul,AddCircle.coe_period,smul_zero]
  rw [hn,add_zero]
lemma x2611_12360_table1_aux2 (p: ℕ) (hp: 0 < (p: ℝ))
    (A: Set (AddCircle (p: ℝ))) (g: ℝ) (x z: ℝ) (L: List ℝ)
    (hz: x + p ≤ z) (hzmem: z ∈ x :: L)
    (hmem: ∀ y ∈ x :: L,(y: AddCircle (p: ℝ)) ∈ A)
    (hchain: (x :: L).IsChain (fun a b => b - a ≤ g)) :
    x2611_12360_gap p A ≤ g:= by
  apply csSup_le
  · exact ⟨0,by exact ⟨le_rfl,hp.le,0,by intro t h1 h2; linarith⟩⟩
  rintro l ⟨hl,hlp,a,ha⟩
  by_contra hlg
  have hgl: g < l:= lt_of_not_ge hlg
  let n: ℤ:= ⌊(a - x) / (p: ℝ)⌋
  have hn1: x + (n: ℝ) * p ≤ a:= by
    have hh:= (le_div_iff₀ hp).mp (Int.floor_le ((a - x) / (p: ℝ)))
    dsimp [n]; linarith
  have hn2: a < x + (n: ℝ) * p + p:= by
    have hh:= (div_lt_iff₀ hp).mp (Int.lt_floor_add_one ((a - x) / (p: ℝ)))
    dsimp [n]; nlinarith
  have hc: (x :: L).IsChain (fun b c => b + (n: ℝ) * p ≤ a → c + (n: ℝ) * p ≤ a):= by
    apply hchain.imp_of_mem_imp
    intro b c hb hc hbc hbnd
    by_contra hcb
    have hca: a < c + (n: ℝ) * p:= lt_of_not_ge hcb
    have hcl: c + (n: ℝ) * p < a + l:= by linarith
    apply ha _ hca hcl
    rw [x2611_12360_table1_aux1]
    exact hmem c hc
  have hall: ∀ y ∈ x :: L,y + (n: ℝ) * p ≤ a :=
    hc.induction _ _ (fun {_ _} h h' => h h') (fun _ => hn1)
  have hh:= hall z hzmem
  linarith
lemma x2611_12360_table1_aux3 (p M: ℕ) (u b: ℝ) (k: ℕ) (n: ℤ) (hk: k < M) :
    ((-u * (k: ℝ)^2 - b * k + (n: ℝ) * p: ℝ): AddCircle (p: ℝ)) ∈
      Set.range (fun j: Fin M => ((-u * (j.val: ℝ)^2 - b * j.val: ℝ): AddCircle (p: ℝ))):= by
  rw [x2611_12360_table1_aux1]
  exact ⟨⟨k,hk⟩,rfl⟩
lemma x2611_12360_table1_aux4 (p M: ℕ) (u g: ℝ) (hp: 0 < (p: ℝ))
    (h: ∀ b: ℝ,0 ≤ b → b ≤ p →
      x2611_12360_gap p (Set.range (fun k: Fin M =>
        ((-u * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (p: ℝ)))) ≤ g) :
    x2611_12360_G p M u ≤ g:= by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨β,rfl⟩
  let n: ℤ:= ⌊β / (p: ℝ)⌋
  let b: ℝ:= β - (n: ℝ) * p
  have hb: 0 ≤ b:= by
    have hh:= (le_div_iff₀ hp).mp (Int.floor_le (β / (p: ℝ)))
    dsimp [b,n]; linarith
  have hb': b ≤ p:= by
    have hh:= (div_lt_iff₀ hp).mp (Int.lt_floor_add_one (β / (p: ℝ)))
    dsimp [b,n]; nlinarith
  have heq: (fun k: Fin M => ((-u * (k.val: ℝ)^2 - β * k.val: ℝ): AddCircle (p: ℝ))) =
      (fun k: Fin M => ((-u * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (p: ℝ))):= by
    funext k
    have he: -u * (k.val: ℝ)^2 - β * k.val =
        (-u * (k.val: ℝ)^2 - b * k.val) + ((-n * (k.val: ℤ): ℤ): ℝ) * p:= by
      dsimp [b]; push_cast; ring
    rw [he,x2611_12360_table1_aux1]
  change x2611_12360_gap p (Set.range (fun k: Fin M => ((-u * (k.val: ℝ)^2 - β * k.val: ℝ): AddCircle (p: ℝ)))) ≤ g
  rw [heq]
  exact h b hb hb'
lemma x2611_12360_table1_aux5 (p M: ℕ) (u g a b: ℝ)
    (hg: 0 ≤ g) (ha: 0 ≤ a) (hag: a + g ≤ p)
    (hw: ∀ k: Fin M,∃ n: ℤ,
      let r:= -u * (k.val: ℝ)^2 - b * k.val + (n: ℝ) * p
      0 ≤ r ∧ r < p ∧ (r ≤ a ∨ a + g ≤ r))
    (hu: x2611_12360_G p M u ≤ g): x2611_12360_G p M u = g:= by
  apply le_antisymm hu
  have hp: 0 ≤ (p: ℝ):= Nat.cast_nonneg p
  let A:= Set.range (fun k: Fin M => ((-u * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (p: ℝ)))
  have hgap: g ≤ x2611_12360_gap p A:= by
    apply le_csSup
    · exact ⟨p,fun l hl => hl.2.1⟩
    refine ⟨hg,by linarith,a,?_⟩
    intro t ht ht' hmem
    obtain ⟨k,hk⟩:= hmem
    obtain ⟨n,hn0,hnp,hn⟩:= hw k
    have heq: ((-u * (k.val: ℝ)^2 - b * k.val + (n: ℝ) * p: ℝ): AddCircle (p: ℝ)) = (t: AddCircle (p: ℝ)):= by
      rw [x2611_12360_table1_aux1]; exact hk
    letI: Fact (0 < (p: ℝ)):= ⟨by linarith⟩
    have hr: -u * (k.val: ℝ)^2 - b * k.val + (n: ℝ) * p = t :=
      (AddCircle.coe_eq_coe_iff_of_mem_Ico (a:= 0) ⟨hn0,by simpa using hnp⟩
        ⟨by linarith,by linarith⟩).mp heq
    rcases hn with hn | hn<;>linarith
  apply le_trans hgap
  apply le_csSup
  · refine ⟨p,?_⟩
    rintro _ ⟨β,rfl⟩
    apply csSup_le
    · exact ⟨0,⟨le_rfl,hp,0,by intro t h1 h2; linarith⟩⟩
    · intro l hl; exact hl.2.1
  · exact ⟨b,rfl⟩
lemma x2611_12360_table1_aux6 (p M: ℕ) (u b g: ℝ) (hp: 0 < (p: ℝ))
    (k: Fin M) (n m: ℤ) (L: List (Fin M × ℤ))
    (hnm: n + 1 ≤ m) (hlast: (k,m) ∈ (k,n) :: L)
    (hchain: (((k,n) :: L).map (fun q =>
      -u * (q.1.val: ℝ)^2 - b * q.1.val + (q.2: ℝ) * p)).IsChain
        (fun x y => y - x ≤ g)) :
    x2611_12360_gap p (Set.range (fun j: Fin M =>
      ((-u * (j.val: ℝ)^2 - b * j.val: ℝ): AddCircle (p: ℝ)))) ≤ g:= by
  apply x2611_12360_table1_aux2 p hp _ g
    (-u * (k.val: ℝ)^2 - b * k.val + (n: ℝ) * p)
    (-u * (k.val: ℝ)^2 - b * k.val + (m: ℝ) * p)
    (L.map (fun q => -u * (q.1.val: ℝ)^2 - b * q.1.val + (q.2: ℝ) * p))
  · have hh: (n: ℝ) + 1 ≤ m:= by exact_mod_cast hnm
    nlinarith
  · exact List.mem_map_of_mem (f:= fun q: Fin M × ℤ => -u * (q.1.val: ℝ)^2 - b * q.1.val + (q.2: ℝ) * p) hlast
  · intro y hy
    change y ∈ (((k,n) :: L).map (fun q => -u * (q.1.val: ℝ)^2 - b * q.1.val + (q.2: ℝ) * p)) at hy
    obtain ⟨⟨j,v⟩,hj,rfl⟩:= List.mem_map.mp hy
    exact x2611_12360_table1_aux3 p M u b j.val v j.isLt
  · exact hchain
lemma x2611_12360_table1_aux7 (b: ℝ) (hl: (0: ℝ) ≤ b) (hr: b ≤ (6: ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-(1: ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ (4: ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 (1) b (4) (by norm_num)
  by_cases hm: b ≤ ((25 / 7): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ (2: ℝ)
    · have hr:= hm
      by_cases hm: b ≤ (1: ℝ)
      · have hr:= hm
        apply H 7 0 1 [(8,1),(14,9),(12,6),(15,11),(16,13),(11,5),(13,8),(6,0),(7,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (1: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 0 0 1 [(5,2),(3,1),(6,3),(7,4),(2,1),(4,2),(1,1),(0,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: (2: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ (3: ℝ)
      · have hr:= hm
        apply H 6 0 1 [(7,1),(13,9),(11,6),(14,11),(15,13),(10,5),(12,8),(5,0),(6,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (3: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 5 0 1 [(7,2),(15,14),(21,28),(19,23),(12,9),(4,0),(2,-1),(5,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((25 / 7): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ (5: ℝ)
    · have hr:= hm
      by_cases hm: b ≤ (4: ℝ)
      · have hr:= hm
        apply H 6 0 1 [(1,-3),(3,-2),(0,-3),(4,-1),(9,4),(11,7),(6,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (4: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 5 0 1 [(6,1),(12,9),(10,6),(13,11),(14,13),(9,5),(11,8),(4,0),(5,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: (5: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((17 / 3): ℝ)
      · have hr:= hm
        apply H 20 0 1 [(18,-5),(21,3),(9,-22),(3,-28),(1,-29),(4,-27),(6,-25),(14,-13),(20,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((17 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 12 0 1 [(13,2),(14,4),(5,-9),(0,-12),(9,-4),(19,16),(12,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux8 (b: ℝ) (hl: (6: ℝ) ≤ b) (hr: b ≤ (14: ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-(1: ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ (4: ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 (1) b (4) (by norm_num)
  by_cases hm: b ≤ (10: ℝ)
  · have hr:= hm
    by_cases hm: b ≤ (8: ℝ)
    · have hr:= hm
      by_cases hm: b ≤ (7: ℝ)
      · have hr:= hm
        apply H 9 0 1 [(12,5),(13,7),(8,-1),(10,2),(3,-6),(4,-5),(5,-4),(11,4),(9,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (7: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 12 0 1 [(13,2),(19,16),(17,11),(20,19),(21,22),(16,9),(18,14),(11,-1),(12,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: (8: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ (9: ℝ)
      · have hr:= hm
        apply H 3 0 1 [(4,1),(10,9),(8,6),(11,11),(12,13),(7,5),(9,8),(2,0),(3,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (9: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 11 0 1 [(12,2),(18,16),(16,11),(19,19),(20,22),(15,9),(17,14),(10,-1),(11,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: (10: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ (12: ℝ)
    · have hr:= hm
      by_cases hm: b ≤ (11: ℝ)
      · have hr:= hm
        apply H 7 0 1 [(10,5),(11,7),(6,-1),(8,2),(1,-6),(2,-5),(3,-4),(9,4),(7,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (11: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 15 0 1 [(18,8),(19,11),(14,-2),(16,3),(9,-12),(10,-10),(11,-8),(17,6),(15,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: (12: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ (13: ℝ)
      · have hr:= hm
        apply H 1 0 1 [(2,1),(8,9),(6,6),(9,11),(10,13),(5,5),(7,8),(0,0),(1,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (13: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 9 0 1 [(10,2),(16,16),(14,11),(17,19),(18,22),(13,9),(15,14),(8,-1),(9,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux9 (b: ℝ) (hl: (14: ℝ) ≤ b) (hr: b ≤ (17: ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-(1: ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ (4: ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 (1) b (4) (by norm_num)
  by_cases hm: b ≤ (15: ℝ)
  · have hr:= hm
    apply H 1 0 1 [(7,8),(5,5),(8,10),(9,12),(4,4),(6,7),(3,3),(1,1)]
    · norm_num
    · simp
    · norm_num [List.isChain_cons,List.isChain_nil]
      all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: (15: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ (16: ℝ)
    · have hr:= hm
      apply H 8 0 1 [(9,2),(15,16),(13,11),(16,19),(17,22),(12,9),(14,14),(7,-1),(8,1)]
      · norm_num
      · simp
      · norm_num [List.isChain_cons,List.isChain_nil]
        all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: (16: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      apply H 0 0 1 [(6,8),(4,5),(7,10),(8,12),(3,4),(5,7),(2,3),(0,1)]
      · norm_num
      · simp
      · norm_num [List.isChain_cons,List.isChain_nil]
        all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux10: x2611_12360_G 17 22 (1: ℝ) ≤ (4: ℝ):= by
  apply x2611_12360_table1_aux4 17 22 (1) (4) (by norm_num)
  intro b hl hr
  norm_num at hr
  by_cases hm: b ≤ (6: ℝ)
  · have hr:= hm
    exact x2611_12360_table1_aux7 b (by linarith only[hl]) (by linarith only[hr])
  · have hl: (6: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ (14: ℝ)
    · have hr:= hm
      exact x2611_12360_table1_aux8 b (by linarith only[hl]) (by linarith only[hr])
    · have hl: (14: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      exact x2611_12360_table1_aux9 b (by linarith only[hl]) (by linarith only[hr])
lemma x2611_12360_table1_aux11: x2611_12360_G 17 22 (1: ℝ) = (4: ℝ):= by
  apply x2611_12360_table1_aux5 17 22 (1) (4) (4) (0)
  · norm_num
  · norm_num
  · norm_num
  · intro k
    fin_cases k
    · exact ⟨0,by norm_num⟩
    · exact ⟨1,by norm_num⟩
    · exact ⟨1,by norm_num⟩
    · exact ⟨1,by norm_num⟩
    · exact ⟨1,by norm_num⟩
    · exact ⟨2,by norm_num⟩
    · exact ⟨3,by norm_num⟩
    · exact ⟨3,by norm_num⟩
    · exact ⟨4,by norm_num⟩
    · exact ⟨5,by norm_num⟩
    · exact ⟨6,by norm_num⟩
    · exact ⟨8,by norm_num⟩
    · exact ⟨9,by norm_num⟩
    · exact ⟨10,by norm_num⟩
    · exact ⟨12,by norm_num⟩
    · exact ⟨14,by norm_num⟩
    · exact ⟨16,by norm_num⟩
    · exact ⟨17,by norm_num⟩
    · exact ⟨20,by norm_num⟩
    · exact ⟨22,by norm_num⟩
    · exact ⟨24,by norm_num⟩
    · exact ⟨26,by norm_num⟩
  · exact x2611_12360_table1_aux10
lemma x2611_12360_table1_aux12 (b: ℝ) (hl: (0: ℝ) ≤ b) (hr: b ≤ (3: ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-(2: ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ (4: ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 (2) b (4) (by norm_num)
  by_cases hm: b ≤ ((17 / 10): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ (1: ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((1 / 2): ℝ)
      · have hr:= hm
        apply H 12 0 1 [(1,-17),(4,-15),(7,-11),(8,-9),(2,-16),(6,-12),(14,7),(12,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((1 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 13 0 1 [(19,23),(10,-8),(4,-18),(8,-12),(11,-5),(14,4),(13,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: (1: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((3 / 2): ℝ)
      · have hr:= hm
        apply H 16 0 1 [(3,-30),(4,-29),(11,-16),(12,-13),(6,-26),(10,-18),(18,9),(16,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((3 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 12 0 1 [(15,10),(18,22),(17,18),(7,-11),(8,-9),(12,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((17 / 10): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((12 / 5): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ (2: ℝ)
      · have hr:= hm
        apply H 0 0 1 [(6,5),(2,1),(5,4),(8,9),(12,19),(15,29),(0,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (2: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 12 0 1 [(15,10),(16,14),(10,-5),(14,7),(9,-7),(12,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((12 / 5): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((17 / 6): ℝ)
      · have hr:= hm
        apply H 10 0 1 [(6,-8),(0,-13),(9,-2),(15,16),(16,20),(19,33),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((17 / 6): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 6 0 1 [(9,6),(12,14),(16,28),(19,41),(3,-3),(10,9),(6,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux13 (b: ℝ) (hl: (3: ℝ) ≤ b) (hr: b ≤ (6: ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-(2: ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ (4: ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 (2) b (4) (by norm_num)
  by_cases hm: b ≤ ((9 / 2): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((11 / 3): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((17 / 5): ℝ)
      · have hr:= hm
        apply H 18 0 1 [(13,-19),(16,-8),(19,5),(20,10),(2,-40),(3,-39),(10,-27),(18,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((17 / 5): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 3 0 1 [(6,4),(9,10),(8,8),(5,3),(10,13),(3,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((11 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ (4: ℝ)
      · have hr:= hm
        apply H 13 0 1 [(16,11),(9,-11),(7,-15),(14,4),(10,-8),(13,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (4: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 11 0 1 [(0,-17),(3,-15),(6,-11),(7,-9),(1,-16),(5,-12),(13,7),(11,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((9 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((11 / 2): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ (5: ℝ)
      · have hr:= hm
        apply H 12 0 1 [(18,23),(9,-8),(3,-18),(7,-12),(10,-5),(13,4),(12,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (5: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 15 0 1 [(2,-30),(3,-29),(10,-16),(11,-13),(5,-26),(9,-18),(17,9),(15,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((11 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((57 / 10): ℝ)
      · have hr:= hm
        apply H 14 0 1 [(17,12),(16,8),(6,-21),(7,-19),(11,-9),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((57 / 10): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 15 0 1 [(5,-27),(1,-31),(4,-28),(7,-23),(11,-13),(17,9),(15,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux14 (b: ℝ) (hl: (6: ℝ) ≤ b) (hr: b ≤ (9: ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-(2: ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ (4: ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 (2) b (4) (by norm_num)
  by_cases hm: b ≤ ((37 / 5): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((67 / 10): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((13 / 2): ℝ)
      · have hr:= hm
        apply H 19 0 1 [(1,-49),(7,-41),(14,-21),(15,-17),(9,-36),(13,-24),(21,11),(19,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((13 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 15 0 1 [(18,13),(21,28),(20,23),(10,-16),(11,-13),(15,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((67 / 10): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ (7: ℝ)
      · have hr:= hm
        apply H 5 0 1 [(8,6),(11,14),(15,28),(18,41),(2,-3),(9,9),(5,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (7: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 19 0 1 [(1,-50),(2,-49),(9,-37),(17,-9),(12,-28),(15,-17),(18,-4),(19,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((37 / 5): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ (8: ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((23 / 3): ℝ)
      · have hr:= hm
        apply H 5 0 1 [(8,6),(7,4),(4,-1),(9,9),(2,-3),(5,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((23 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 8 0 1 [(6,-4),(13,15),(9,3),(12,12),(15,23),(8,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: (8: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((17 / 2): ℝ)
      · have hr:= hm
        apply H 5 0 1 [(6,2),(0,-5),(4,-1),(12,18),(10,12),(1,-4),(2,-3),(5,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((17 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 8 0 1 [(2,-10),(6,-4),(9,3),(12,12),(11,9),(17,32),(8,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux15 (b: ℝ) (hl: (9: ℝ) ≤ b) (hr: b ≤ (12: ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-(2: ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ (4: ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 (2) b (4) (by norm_num)
  by_cases hm: b ≤ ((107 / 10): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ (10: ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((19 / 2): ℝ)
      · have hr:= hm
        apply H 9 0 1 [(10,3),(4,-10),(8,-2),(16,25),(14,17),(1,-13),(2,-12),(9,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((19 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 12 0 1 [(6,-16),(10,-6),(13,4),(16,16),(15,12),(21,41),(12,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: (10: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((21 / 2): ℝ)
      · have hr:= hm
        apply H 18 0 1 [(0,-49),(6,-41),(13,-21),(14,-17),(8,-36),(12,-24),(20,11),(18,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((21 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 17 0 1 [(20,15),(19,10),(9,-29),(10,-26),(14,-12),(17,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((107 / 10): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((57 / 5): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ (11: ℝ)
      · have hr:= hm
        apply H 4 0 1 [(7,6),(10,14),(14,28),(17,41),(1,-3),(8,9),(4,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (11: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 16 0 1 [(11,-19),(14,-8),(17,5),(18,10),(0,-40),(1,-39),(8,-27),(16,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((57 / 5): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((107 / 9): ℝ)
      · have hr:= hm
        apply H 1 0 1 [(4,4),(17,45),(18,50),(21,66),(12,25),(3,3),(0,0),(1,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((107 / 9): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 21 0 1 [(5,-60),(12,-41),(3,-63),(11,-44),(18,-15),(21,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux16 (b: ℝ) (hl: (12: ℝ) ≤ b) (hr: b ≤ (15: ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-(2: ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ (4: ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 (2) b (4) (by norm_num)
  by_cases hm: b ≤ ((27 / 2): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((127 / 10): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((62 / 5): ℝ)
      · have hr:= hm
        apply H 15 0 1 [(18,14),(21,30),(0,-37),(1,-36),(4,-32),(5,-30),(12,-11),(20,25),(15,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((62 / 5): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 8 0 1 [(11,9),(10,6),(0,-13),(4,-8),(5,-6),(8,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((127 / 10): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ (13: ℝ)
      · have hr:= hm
        apply H 15 0 1 [(18,14),(11,-15),(9,-21),(16,5),(12,-11),(15,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (13: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 13 0 1 [(0,-30),(1,-29),(8,-16),(9,-13),(3,-26),(7,-18),(15,9),(13,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((27 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((29 / 2): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ (14: ℝ)
      · have hr:= hm
        apply H 14 0 1 [(20,29),(11,-11),(5,-27),(9,-17),(12,-7),(15,5),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (14: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 17 0 1 [(4,-43),(5,-41),(12,-21),(13,-17),(7,-36),(11,-24),(19,11),(17,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((29 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((147 / 10): ℝ)
      · have hr:= hm
        apply H 13 0 1 [(16,13),(19,28),(18,23),(8,-16),(9,-13),(13,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((147 / 10): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 0 0 1 [(7,12),(3,4),(6,10),(9,18),(13,32),(16,45),(0,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux17 (b: ℝ) (hl: (15: ℝ) ≤ b) (hr: b ≤ (17: ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-(2: ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ (4: ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 (2) b (4) (by norm_num)
  by_cases hm: b ≤ (16: ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((77 / 5): ℝ)
    · have hr:= hm
      apply H 13 0 1 [(16,13),(17,18),(11,-7),(15,9),(10,-10),(13,1)]
      · norm_num
      · simp
      · norm_num [List.isChain_cons,List.isChain_nil]
        all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((77 / 5): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((95 / 6): ℝ)
      · have hr:= hm
        apply H 11 0 1 [(7,-12),(1,-23),(10,-3),(16,21),(17,26),(20,42),(11,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((95 / 6): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 7 0 1 [(10,9),(13,20),(17,38),(20,54),(4,-6),(11,13),(7,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: (16: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((82 / 5): ℝ)
    · have hr:= hm
      apply H 19 0 1 [(14,-24),(17,-10),(20,6),(21,12),(3,-56),(4,-54),(11,-35),(19,1)]
      · norm_num
      · simp
      · norm_num [List.isChain_cons,List.isChain_nil]
        all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((82 / 5): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((50 / 3): ℝ)
      · have hr:= hm
        apply H 4 0 1 [(7,7),(10,16),(9,13),(6,5),(11,20),(4,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((50 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 14 0 1 [(17,14),(10,-15),(8,-21),(15,5),(11,-11),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux18: x2611_12360_G 17 22 (2: ℝ) ≤ (4: ℝ):= by
  apply x2611_12360_table1_aux4 17 22 (2) (4) (by norm_num)
  intro b hl hr
  norm_num at hr
  by_cases hm: b ≤ (9: ℝ)
  · have hr:= hm
    by_cases hm: b ≤ (3: ℝ)
    · have hr:= hm
      exact x2611_12360_table1_aux12 b (by linarith only[hl]) (by linarith only[hr])
    · have hl: (3: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ (6: ℝ)
      · have hr:= hm
        exact x2611_12360_table1_aux13 b (by linarith only[hl]) (by linarith only[hr])
      · have hl: (6: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        exact x2611_12360_table1_aux14 b (by linarith only[hl]) (by linarith only[hr])
  · have hl: (9: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ (12: ℝ)
    · have hr:= hm
      exact x2611_12360_table1_aux15 b (by linarith only[hl]) (by linarith only[hr])
    · have hl: (12: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ (15: ℝ)
      · have hr:= hm
        exact x2611_12360_table1_aux16 b (by linarith only[hl]) (by linarith only[hr])
      · have hl: (15: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        exact x2611_12360_table1_aux17 b (by linarith only[hl]) (by linarith only[hr])
lemma x2611_12360_table1_aux19: x2611_12360_G 17 22 (2: ℝ) = (4: ℝ):= by
  apply x2611_12360_table1_aux5 17 22 (2) (4) (4) (0)
  · norm_num
  · norm_num
  · norm_num
  · intro k
    fin_cases k
    · exact ⟨0,by norm_num⟩
    · exact ⟨1,by norm_num⟩
    · exact ⟨1,by norm_num⟩
    · exact ⟨2,by norm_num⟩
    · exact ⟨2,by norm_num⟩
    · exact ⟨3,by norm_num⟩
    · exact ⟨5,by norm_num⟩
    · exact ⟨6,by norm_num⟩
    · exact ⟨8,by norm_num⟩
    · exact ⟨10,by norm_num⟩
    · exact ⟨12,by norm_num⟩
    · exact ⟨15,by norm_num⟩
    · exact ⟨17,by norm_num⟩
    · exact ⟨20,by norm_num⟩
    · exact ⟨24,by norm_num⟩
    · exact ⟨27,by norm_num⟩
    · exact ⟨31,by norm_num⟩
    · exact ⟨34,by norm_num⟩
    · exact ⟨39,by norm_num⟩
    · exact ⟨43,by norm_num⟩
    · exact ⟨48,by norm_num⟩
    · exact ⟨52,by norm_num⟩
  · exact x2611_12360_table1_aux18
lemma x2611_12360_table1_aux20 (b: ℝ) (hl: (0: ℝ) ≤ b) (hr: b ≤ ((31 / 6): ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-((1 / 2): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ (4: ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 ((1 / 2)) b (4) (by norm_num)
  by_cases hm: b ≤ ((19 / 6): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((3 / 2): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((1 / 2): ℝ)
      · have hr:= hm
        apply H 3 0 1 [(6,1),(8,2),(14,6),(15,7),(11,4),(7,2),(12,5),(3,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((1 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 10 0 1 [(8,-1),(11,1),(2,-3),(1,-3),(5,-2),(7,-1),(12,2),(13,3),(14,4),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((3 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((5 / 2): ℝ)
      · have hr:= hm
        apply H 9 0 1 [(7,-1),(10,1),(1,-3),(0,-3),(4,-2),(6,-1),(11,2),(12,3),(13,4),(9,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((5 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 5 0 1 [(10,3),(11,4),(12,5),(13,6),(6,1),(9,3),(3,0),(5,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((19 / 6): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((25 / 6): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((7 / 2): ℝ)
      · have hr:= hm
        apply H 3 0 1 [(11,5),(13,7),(19,14),(4,1),(9,4),(0,0),(3,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((7 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 10 0 1 [(11,1),(12,2),(5,-3),(8,-1),(2,-4),(4,-3),(9,0),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((25 / 6): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((9 / 2): ℝ)
      · have hr:= hm
        apply H 3 0 1 [(8,3),(17,12),(9,4),(10,5),(12,7),(18,14),(3,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((9 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 9 0 1 [(10,1),(11,2),(4,-3),(7,-1),(1,-4),(3,-3),(8,0),(9,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux21 (b: ℝ) (hl: ((31 / 6): ℝ) ≤ b) (hr: b ≤ ((161 / 18): ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-((1 / 2): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ (4: ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 ((1 / 2)) b (4) (by norm_num)
  by_cases hm: b ≤ ((125 / 18): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((37 / 6): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((11 / 2): ℝ)
      · have hr:= hm
        apply H 8 0 1 [(9,1),(11,3),(17,10),(2,-3),(7,0),(16,9),(8,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((11 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 8 0 1 [(9,1),(10,2),(3,-3),(6,-1),(0,-4),(2,-3),(7,0),(8,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((37 / 6): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((13 / 2): ℝ)
      · have hr:= hm
        apply H 7 0 1 [(8,1),(10,3),(16,10),(1,-3),(6,0),(15,9),(7,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((13 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 6 0 1 [(7,1),(8,2),(9,3),(16,11),(18,14),(15,10),(6,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((125 / 18): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((143 / 18): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((15 / 2): ℝ)
      · have hr:= hm
        apply H 15 0 1 [(21,9),(17,3),(14,-1),(6,-9),(7,-8),(8,-7),(9,-6),(18,5),(15,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((15 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 5 0 1 [(6,1),(7,2),(8,3),(15,11),(17,14),(14,10),(5,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((143 / 18): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((17 / 2): ℝ)
      · have hr:= hm
        apply H 7 0 1 [(8,1),(17,12),(14,8),(20,17),(16,11),(21,19),(5,-1),(6,0),(7,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((17 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 4 0 1 [(5,1),(6,2),(7,3),(14,11),(16,14),(13,10),(4,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux22 (b: ℝ) (hl: ((161 / 18): ℝ) ≤ b) (hr: b ≤ ((31 / 2): ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-((1 / 2): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ (4: ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 ((1 / 2)) b (4) (by norm_num)
  by_cases hm: b ≤ ((23 / 2): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((61 / 6): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((19 / 2): ℝ)
      · have hr:= hm
        apply H 16 0 1 [(13,-4),(19,5),(15,-1),(20,7),(4,-13),(5,-12),(6,-11),(7,-10),(16,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((19 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 20 0 1 [(21,2),(18,-3),(3,-21),(4,-20),(5,-19),(6,-18),(13,-10),(15,-7),(20,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((61 / 6): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((21 / 2): ℝ)
      · have hr:= hm
        apply H 3 0 1 [(4,1),(6,3),(12,10),(18,19),(14,13),(19,21),(3,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((21 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 2 0 1 [(3,1),(4,2),(5,3),(12,11),(14,14),(19,22),(20,24),(21,26),(17,19),(15,16),(18,21),(2,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((23 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((27 / 2): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((25 / 2): ℝ)
      · have hr:= hm
        apply H 1 0 1 [(2,1),(3,2),(4,3),(11,11),(13,14),(18,22),(19,24),(20,26),(16,19),(14,16),(17,21),(1,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((25 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 0 0 1 [(1,1),(2,2),(3,3),(10,11),(12,14),(17,22),(18,24),(19,26),(15,19),(13,16),(16,21),(0,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((27 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((29 / 2): ℝ)
      · have hr:= hm
        apply H 0 0 1 [(1,1),(2,2),(9,10),(11,13),(16,21),(17,23),(18,25),(14,18),(12,15),(15,20),(6,7),(0,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((29 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 13 0 1 [(11,-3),(14,2),(5,-11),(4,-12),(8,-7),(10,-4),(15,4),(16,6),(17,8),(13,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux23 (b: ℝ) (hl: ((31 / 2): ℝ) ≤ b) (hr: b ≤ (17: ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-((1 / 2): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ (4: ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 ((1 / 2)) b (4) (by norm_num)
  by_cases hm: b ≤ ((33 / 2): ℝ)
  · have hr:= hm
    apply H 12 0 1 [(10,-3),(13,2),(4,-11),(3,-12),(7,-7),(9,-4),(14,4),(15,6),(16,8),(12,1)]
    · norm_num
    · simp
    · norm_num [List.isChain_cons,List.isChain_nil]
      all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((33 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    apply H 6 0 1 [(8,3),(13,11),(14,13),(15,15),(9,5),(12,10),(6,1)]
    · norm_num
    · simp
    · norm_num [List.isChain_cons,List.isChain_nil]
      all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux24: x2611_12360_G 17 22 ((1 / 2): ℝ) ≤ (4: ℝ):= by
  apply x2611_12360_table1_aux4 17 22 ((1 / 2)) (4) (by norm_num)
  intro b hl hr
  norm_num at hr
  by_cases hm: b ≤ ((161 / 18): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((31 / 6): ℝ)
    · have hr:= hm
      exact x2611_12360_table1_aux20 b (by linarith only[hl]) (by linarith only[hr])
    · have hl: ((31 / 6): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      exact x2611_12360_table1_aux21 b (by linarith only[hl]) (by linarith only[hr])
  · have hl: ((161 / 18): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((31 / 2): ℝ)
    · have hr:= hm
      exact x2611_12360_table1_aux22 b (by linarith only[hl]) (by linarith only[hr])
    · have hl: ((31 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      exact x2611_12360_table1_aux23 b (by linarith only[hl]) (by linarith only[hr])
lemma x2611_12360_table1_aux25: x2611_12360_G 17 22 ((1 / 2): ℝ) = (4: ℝ):= by
  apply x2611_12360_table1_aux5 17 22 ((1 / 2)) (4) (0) ((9 / 2))
  · norm_num
  · norm_num
  · norm_num
  · intro k
    fin_cases k
    · exact ⟨0,by norm_num⟩
    · exact ⟨1,by norm_num⟩
    · exact ⟨1,by norm_num⟩
    · exact ⟨2,by norm_num⟩
    · exact ⟨2,by norm_num⟩
    · exact ⟨3,by norm_num⟩
    · exact ⟨3,by norm_num⟩
    · exact ⟨4,by norm_num⟩
    · exact ⟨4,by norm_num⟩
    · exact ⟨5,by norm_num⟩
    · exact ⟨6,by norm_num⟩
    · exact ⟨7,by norm_num⟩
    · exact ⟨8,by norm_num⟩
    · exact ⟨9,by norm_num⟩
    · exact ⟨10,by norm_num⟩
    · exact ⟨11,by norm_num⟩
    · exact ⟨12,by norm_num⟩
    · exact ⟨13,by norm_num⟩
    · exact ⟨15,by norm_num⟩
    · exact ⟨16,by norm_num⟩
    · exact ⟨18,by norm_num⟩
    · exact ⟨19,by norm_num⟩
  · exact x2611_12360_table1_aux24
lemma x2611_12360_table1_aux26 (b: ℝ) (hl: (0: ℝ) ≤ b) (hr: b ≤ ((202 / 91): ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-((2 / 3): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ ((133 / 39): ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 ((2 / 3)) b ((133 / 39)) (by norm_num)
  by_cases hm: b ≤ ((14 / 13): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((40 / 91): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((5 / 13): ℝ)
      · have hr:= hm
        apply H 8 0 1 [(17,9),(19,12),(3,-2),(9,1),(2,-2),(5,-1),(7,0),(11,3),(12,4),(4,-1),(8,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((5 / 13): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 2 0 1 [(5,1),(12,6),(17,12),(19,15),(6,2),(9,4),(2,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((40 / 91): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((367 / 429): ℝ)
      · have hr:= hm
        apply H 12 0 1 [(17,6),(19,9),(8,-3),(6,-4),(9,-2),(15,4),(10,-1),(11,0),(12,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((367 / 429): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 8 0 1 [(16,8),(20,14),(15,7),(14,6),(11,3),(2,-2),(1,-2),(8,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((14 / 13): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((67 / 39): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((55 / 39): ℝ)
      · have hr:= hm
        apply H 4 0 1 [(9,3),(10,4),(11,5),(7,2),(2,0),(1,0),(0,0),(4,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((55 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 7 0 1 [(16,9),(18,12),(21,17),(8,1),(1,-2),(4,-1),(6,0),(10,3),(11,4),(3,-1),(7,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((67 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((484 / 273): ℝ)
      · have hr:= hm
        apply H 1 0 1 [(4,1),(11,6),(16,12),(18,15),(21,20),(8,4),(1,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((484 / 273): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 3 0 1 [(5,1),(8,3),(14,9),(9,4),(10,5),(11,6),(16,12),(18,15),(21,20),(7,3),(3,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux27 (b: ℝ) (hl: ((202 / 91): ℝ) ≤ b) (hr: b ≤ ((57 / 13): ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-((2 / 3): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ ((133 / 39): ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 ((2 / 3)) b ((133 / 39)) (by norm_num)
  by_cases hm: b ≤ ((406 / 117): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((107 / 39): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((94 / 39): ℝ)
      · have hr:= hm
        apply H 13 0 1 [(16,4),(1,-8),(0,-8),(7,-5),(19,9),(14,2),(13,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((94 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 17 0 1 [(14,-4),(8,-10),(9,-9),(10,-8),(6,-11),(1,-13),(0,-13),(7,-10),(17,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((107 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((119 / 39): ℝ)
      · have hr:= hm
        apply H 6 0 1 [(15,9),(17,12),(20,17),(7,1),(0,-2),(3,-1),(5,0),(9,3),(10,4),(2,-1),(6,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((119 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 7 0 1 [(21,18),(18,13),(13,6),(8,1),(9,2),(10,3),(15,9),(17,12),(6,0),(4,-1),(7,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((406 / 117): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((352 / 91): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((146 / 39): ℝ)
      · have hr:= hm
        apply H 13 0 1 [(12,-1),(10,-3),(20,11),(21,13),(14,2),(18,8),(13,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((146 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 2 0 1 [(7,3),(8,4),(17,15),(21,22),(14,11),(18,17),(2,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((352 / 91): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((991 / 234): ℝ)
      · have hr:= hm
        apply H 5 0 1 [(3,-1),(14,9),(16,12),(13,8),(7,2),(8,3),(9,4),(5,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((991 / 234): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 13 0 1 [(20,11),(21,13),(8,-5),(9,-4),(1,-9),(3,-8),(6,-6),(13,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux28 (b: ℝ) (hl: ((57 / 13): ℝ) ≤ b) (hr: b ≤ ((262 / 39): ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-((2 / 3): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ ((133 / 39): ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 ((2 / 3)) b ((133 / 39)) (by norm_num)
  by_cases hm: b ≤ ((1303 / 234): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((66 / 13): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((1334 / 273): ℝ)
      · have hr:= hm
        apply H 5 0 1 [(1,-2),(3,-1),(6,1),(20,19),(21,21),(15,11),(12,7),(7,2),(8,3),(9,4),(14,10),(16,13),(19,18),(5,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((1334 / 273): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 17 0 1 [(12,-7),(11,-8),(14,-4),(19,4),(20,6),(21,8),(17,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((66 / 13): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((70 / 13): ℝ)
      · have hr:= hm
        apply H 21 0 1 [(13,-13),(17,-7),(15,-10),(12,-14),(6,-20),(7,-19),(16,-8),(20,-1),(21,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((70 / 13): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 12 0 1 [(6,-6),(7,-5),(8,-4),(4,-7),(13,2),(15,5),(12,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((1303 / 234): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((566 / 91): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((223 / 39): ℝ)
      · have hr:= hm
        apply H 12 0 1 [(19,11),(20,13),(21,15),(8,-4),(0,-9),(2,-8),(5,-6),(12,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((223 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 4 0 1 [(0,-2),(2,-1),(5,1),(19,19),(20,21),(14,11),(11,7),(6,2),(7,3),(8,4),(13,10),(15,13),(18,18),(4,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((566 / 91): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((250 / 39): ℝ)
      · have hr:= hm
        apply H 10 0 1 [(13,4),(18,12),(19,14),(20,16),(16,9),(11,2),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((250 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 20 0 1 [(12,-13),(16,-7),(14,-10),(11,-14),(5,-20),(6,-19),(15,-8),(19,-1),(20,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux29 (b: ℝ) (hl: ((262 / 39): ℝ) ≤ b) (hr: b ≤ ((346 / 39): ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-((2 / 3): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ ((133 / 39): ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 ((2 / 3)) b ((133 / 39)) (by norm_num)
  by_cases hm: b ≤ ((302 / 39): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((271 / 39): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((1615 / 234): ℝ)
      · have hr:= hm
        apply H 3 0 1 [(12,9),(14,12),(11,8),(5,2),(6,3),(7,4),(3,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((1615 / 234): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 3 0 1 [(12,9),(14,12),(11,8),(18,19),(19,21),(8,5),(3,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((271 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((98 / 13): ℝ)
      · have hr:= hm
        apply H 5 0 1 [(6,1),(8,3),(16,14),(12,8),(14,11),(17,16),(3,-1),(1,-2),(4,0),(18,18),(19,20),(20,22),(10,6),(5,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((98 / 13): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 15 0 1 [(10,-7),(9,-8),(12,-4),(17,4),(18,6),(19,8),(15,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((302 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((1927 / 234): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((314 / 39): ℝ)
      · have hr:= hm
        apply H 19 0 1 [(11,-13),(15,-7),(13,-10),(10,-14),(4,-20),(5,-19),(14,-8),(18,-1),(19,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((314 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 10 0 1 [(4,-6),(5,-5),(6,-4),(2,-7),(11,2),(13,5),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((1927 / 234): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((323 / 39): ℝ)
      · have hr:= hm
        apply H 7 0 1 [(2,-4),(11,5),(13,8),(10,4),(17,15),(18,17),(7,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((323 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 2 0 1 [(0,-1),(3,1),(17,19),(18,21),(19,23),(9,7),(4,2),(5,3),(7,5),(15,16),(11,10),(13,13),(16,18),(2,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux30 (b: ℝ) (hl: ((346 / 39): ℝ) ≤ b) (hr: b ≤ ((2551 / 234): ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-((2 / 3): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ ((133 / 39): ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 ((2 / 3)) b ((133 / 39)) (by norm_num)
  by_cases hm: b ≤ ((125 / 13): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((122 / 13): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((118 / 13): ℝ)
      · have hr:= hm
        apply H 8 0 1 [(11,4),(16,12),(17,14),(18,16),(14,9),(9,2),(8,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((118 / 13): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 18 0 1 [(10,-13),(14,-7),(12,-10),(9,-14),(3,-20),(4,-19),(13,-8),(17,-1),(18,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((122 / 13): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((2239 / 234): ℝ)
      · have hr:= hm
        apply H 1 0 1 [(10,9),(12,12),(9,8),(3,2),(4,3),(5,4),(1,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((2239 / 234): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 1 0 1 [(10,9),(12,12),(15,17),(21,29),(0,0),(4,3),(6,5),(1,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((125 / 13): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((406 / 39): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((131 / 13): ℝ)
      · have hr:= hm
        apply H 17 0 1 [(8,-14),(3,-19),(4,-18),(6,-16),(14,-5),(10,-11),(12,-8),(15,-3),(21,9),(20,7),(17,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((131 / 13): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 10 0 1 [(15,8),(16,10),(17,12),(13,5),(8,-2),(7,-3),(4,-6),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((406 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((418 / 39): ℝ)
      · have hr:= hm
        apply H 17 0 1 [(9,-13),(13,-7),(11,-10),(8,-14),(2,-20),(3,-19),(12,-8),(16,-1),(17,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((418 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 8 0 1 [(2,-6),(3,-5),(4,-4),(0,-7),(9,2),(11,5),(8,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux31 (b: ℝ) (hl: ((2551 / 234): ℝ) ≤ b) (hr: b ≤ ((170 / 13): ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-((2 / 3): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ ((133 / 39): ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 ((2 / 3)) b ((133 / 39)) (by norm_num)
  by_cases hm: b ≤ ((470 / 39): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((445 / 39): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((427 / 39): ℝ)
      · have hr:= hm
        apply H 14 0 1 [(20,12),(2,-15),(3,-14),(5,-12),(0,-16),(9,-7),(11,-4),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((427 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 7 0 1 [(2,-5),(3,-4),(5,-2),(13,9),(9,3),(11,6),(14,11),(20,23),(19,21),(16,15),(7,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((445 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((458 / 39): ℝ)
      · have hr:= hm
        apply H 14 0 1 [(15,2),(16,4),(12,-3),(7,-10),(6,-11),(3,-14),(9,-7),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((458 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 10 0 1 [(7,-4),(1,-10),(2,-9),(11,2),(15,9),(16,11),(8,-2),(12,4),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((470 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((4345 / 351): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((2863 / 234): ℝ)
      · have hr:= hm
        apply H 1 0 1 [(2,1),(16,21),(21,32),(8,8),(10,11),(7,7),(1,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((2863 / 234): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 19 0 1 [(14,-10),(15,-8),(16,-6),(21,5),(12,-13),(10,-16),(13,-11),(19,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((4345 / 351): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((497 / 39): ℝ)
      · have hr:= hm
        apply H 2 0 1 [(3,1),(12,13),(8,7),(10,10),(13,15),(19,27),(18,25),(15,19),(6,5),(1,0),(2,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((497 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 14 0 1 [(15,2),(11,-5),(6,-12),(5,-13),(2,-16),(8,-9),(13,-1),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux32 (b: ℝ) (hl: ((170 / 13): ℝ) ≤ b) (hr: b ≤ ((2172 / 143): ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-((2 / 3): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ ((133 / 39): ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 ((2 / 3)) b ((133 / 39)) (by norm_num)
  by_cases hm: b ≤ ((183 / 13): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((3175 / 234): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((174 / 13): ℝ)
      · have hr:= hm
        apply H 15 0 1 [(7,-13),(11,-7),(9,-10),(6,-14),(0,-20),(1,-19),(10,-8),(14,-1),(15,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((174 / 13): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 7 0 1 [(9,3),(6,-1),(0,-7),(1,-6),(15,14),(20,25),(7,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((3175 / 234): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((4813 / 351): ℝ)
      · have hr:= hm
        apply H 18 0 1 [(13,-10),(14,-8),(15,-6),(20,5),(11,-13),(9,-16),(12,-11),(18,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((4813 / 351): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 14 0 1 [(5,-14),(0,-19),(1,-18),(2,-17),(11,-5),(7,-11),(9,-8),(12,-3),(18,9),(17,7),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((183 / 13): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((574 / 39): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((562 / 39): ℝ)
      · have hr:= hm
        apply H 7 0 1 [(12,8),(13,10),(14,12),(10,5),(5,-2),(4,-3),(1,-6),(7,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((562 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 10 0 1 [(19,18),(21,23),(5,-7),(11,2),(4,-8),(7,-4),(9,-1),(13,6),(14,8),(6,-5),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((574 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((4033 / 273): ℝ)
      · have hr:= hm
        apply H 4 0 1 [(7,4),(14,16),(19,27),(21,32),(8,6),(11,11),(4,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((4033 / 273): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 14 0 1 [(19,11),(21,16),(10,-7),(8,-10),(11,-5),(17,7),(12,-3),(13,-1),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux33 (b: ℝ) (hl: ((2172 / 143): ℝ) ≤ b) (hr: b ≤ (17: ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-((2 / 3): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ ((133 / 39): ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 ((2 / 3)) b ((133 / 39)) (by norm_num)
  by_cases hm: b ≤ ((626 / 39): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((601 / 39): ℝ)
    · have hr:= hm
      apply H 10 0 1 [(6,-6),(8,-3),(17,14),(16,12),(13,6),(4,-8),(3,-9),(10,1)]
      · norm_num
      · simp
      · norm_num [List.isChain_cons,List.isChain_nil]
        all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((601 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((614 / 39): ℝ)
      · have hr:= hm
        apply H 6 0 1 [(11,8),(12,10),(13,12),(9,5),(4,-2),(3,-3),(0,-6),(6,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((614 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 9 0 1 [(18,18),(20,23),(4,-7),(10,2),(3,-8),(6,-4),(8,-1),(12,6),(13,8),(5,-5),(9,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((626 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((7088 / 429): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((4397 / 273): ℝ)
      · have hr:= hm
        apply H 3 0 1 [(6,4),(13,16),(18,27),(20,32),(7,6),(10,11),(3,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((4397 / 273): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 13 0 1 [(18,11),(20,16),(9,-7),(7,-10),(10,-5),(16,7),(11,-3),(12,-1),(13,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((7088 / 429): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((653 / 39): ℝ)
      · have hr:= hm
        apply H 9 0 1 [(17,16),(21,26),(16,14),(15,12),(12,6),(3,-8),(2,-9),(9,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((653 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 5 0 1 [(10,8),(11,10),(12,12),(8,5),(3,-2),(2,-3),(9,7),(5,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux34: x2611_12360_G 17 22 ((2 / 3): ℝ) ≤ ((133 / 39): ℝ):= by
  apply x2611_12360_table1_aux4 17 22 ((2 / 3)) ((133 / 39)) (by norm_num)
  intro b hl hr
  norm_num at hr
  by_cases hm: b ≤ ((346 / 39): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((57 / 13): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((202 / 91): ℝ)
      · have hr:= hm
        exact x2611_12360_table1_aux26 b (by linarith only[hl]) (by linarith only[hr])
      · have hl: ((202 / 91): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        exact x2611_12360_table1_aux27 b (by linarith only[hl]) (by linarith only[hr])
    · have hl: ((57 / 13): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((262 / 39): ℝ)
      · have hr:= hm
        exact x2611_12360_table1_aux28 b (by linarith only[hl]) (by linarith only[hr])
      · have hl: ((262 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        exact x2611_12360_table1_aux29 b (by linarith only[hl]) (by linarith only[hr])
  · have hl: ((346 / 39): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((170 / 13): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((2551 / 234): ℝ)
      · have hr:= hm
        exact x2611_12360_table1_aux30 b (by linarith only[hl]) (by linarith only[hr])
      · have hl: ((2551 / 234): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        exact x2611_12360_table1_aux31 b (by linarith only[hl]) (by linarith only[hr])
    · have hl: ((170 / 13): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((2172 / 143): ℝ)
      · have hr:= hm
        exact x2611_12360_table1_aux32 b (by linarith only[hl]) (by linarith only[hr])
      · have hl: ((2172 / 143): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        exact x2611_12360_table1_aux33 b (by linarith only[hl]) (by linarith only[hr])
lemma x2611_12360_table1_aux35: x2611_12360_G 17 22 ((2 / 3): ℝ) = ((133 / 39): ℝ):= by
  apply x2611_12360_table1_aux5 17 22 ((2 / 3)) ((133 / 39)) ((128 / 39)) ((574 / 39))
  · norm_num
  · norm_num
  · norm_num
  · intro k
    fin_cases k
    · exact ⟨0,by norm_num⟩
    · exact ⟨1,by norm_num⟩
    · exact ⟨2,by norm_num⟩
    · exact ⟨3,by norm_num⟩
    · exact ⟨5,by norm_num⟩
    · exact ⟨6,by norm_num⟩
    · exact ⟨7,by norm_num⟩
    · exact ⟨8,by norm_num⟩
    · exact ⟨10,by norm_num⟩
    · exact ⟨11,by norm_num⟩
    · exact ⟨13,by norm_num⟩
    · exact ⟨15,by norm_num⟩
    · exact ⟨17,by norm_num⟩
    · exact ⟨18,by norm_num⟩
    · exact ⟨20,by norm_num⟩
    · exact ⟨22,by norm_num⟩
    · exact ⟨24,by norm_num⟩
    · exact ⟨27,by norm_num⟩
    · exact ⟨29,by norm_num⟩
    · exact ⟨31,by norm_num⟩
    · exact ⟨34,by norm_num⟩
    · exact ⟨36,by norm_num⟩
  · exact x2611_12360_table1_aux34
lemma x2611_12360_table1_aux36 (b: ℝ) (hl: (0: ℝ) ≤ b) (hr: b ≤ ((87 / 20): ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-((3 / 5): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ ((39 / 10): ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 ((3 / 5)) b ((39 / 10)) (by norm_num)
  by_cases hm: b ≤ ((39 / 20): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((3 / 4): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((11 / 70): ℝ)
      · have hr:= hm
        apply H 13 0 1 [(19,7),(21,10),(18,6),(11,-1),(12,0),(13,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((11 / 70): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 4 0 1 [(11,4),(12,5),(3,0),(2,0),(9,3),(7,2),(10,4),(4,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((3 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((19 / 14): ℝ)
      · have hr:= hm
        apply H 12 0 1 [(4,-5),(6,-4),(3,-5),(18,7),(20,10),(17,6),(10,-1),(11,0),(12,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((19 / 14): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 3 0 1 [(10,4),(11,5),(2,0),(1,0),(8,3),(6,2),(9,4),(3,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((39 / 20): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((63 / 20): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((179 / 70): ℝ)
      · have hr:= hm
        apply H 11 0 1 [(3,-5),(5,-4),(2,-5),(17,7),(19,10),(16,6),(9,-1),(10,0),(11,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((179 / 70): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 1 0 1 [(0,0),(7,3),(5,2),(8,4),(2,1),(9,5),(10,6),(1,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((63 / 20): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((263 / 70): ℝ)
      · have hr:= hm
        apply H 10 0 1 [(2,-5),(4,-4),(1,-5),(16,7),(18,10),(15,6),(8,-1),(9,0),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((263 / 70): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 21 0 1 [(6,-18),(4,-19),(7,-17),(1,-20),(8,-16),(9,-15),(10,-14),(16,-7),(18,-4),(21,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux37 (b: ℝ) (hl: ((87 / 20): ℝ) ≤ b) (hr: b ≤ ((121 / 14): ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-((3 / 5): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ ((39 / 10): ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 ((3 / 5)) b ((39 / 10)) (by norm_num)
  by_cases hm: b ≤ ((437 / 70): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((111 / 20): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((347 / 70): ℝ)
      · have hr:= hm
        apply H 15 0 1 [(17,3),(14,-1),(7,-8),(8,-7),(9,-6),(1,-11),(3,-10),(0,-11),(15,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((347 / 70): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 20 0 1 [(5,-18),(3,-19),(6,-17),(0,-20),(7,-16),(8,-15),(9,-14),(15,-7),(17,-4),(20,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((111 / 20): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((431 / 70): ℝ)
      · have hr:= hm
        apply H 6 0 1 [(7,1),(8,2),(20,18),(21,20),(14,9),(16,12),(13,8),(6,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((431 / 70): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 12 0 1 [(15,4),(21,14),(14,3),(16,6),(19,11),(12,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((437 / 70): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((521 / 70): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((139 / 20): ℝ)
      · have hr:= hm
        apply H 16 0 1 [(19,5),(13,-4),(4,-13),(0,-15),(2,-14),(5,-12),(12,-5),(11,-6),(3,-13),(8,-9),(14,-2),(16,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((139 / 20): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 11 0 1 [(14,4),(19,12),(20,14),(13,3),(15,6),(12,2),(18,11),(11,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((521 / 70): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((161 / 20): ℝ)
      · have hr:= hm
        apply H 18 0 1 [(3,-18),(1,-19),(4,-17),(11,-10),(5,-16),(6,-15),(7,-14),(13,-7),(15,-4),(18,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((161 / 20): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 10 0 1 [(13,4),(18,12),(19,14),(21,18),(14,6),(11,2),(17,11),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux38 (b: ℝ) (hl: ((121 / 14): ℝ) ≤ b) (hr: b ≤ ((857 / 70): ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-((3 / 5): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ ((39 / 10): ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 ((3 / 5)) b ((39 / 10)) (by norm_num)
  by_cases hm: b ≤ ((211 / 20): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((689 / 70): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((37 / 4): ℝ)
      · have hr:= hm
        apply H 4 0 1 [(5,1),(6,2),(12,9),(14,12),(17,17),(2,-1),(0,-2),(3,0),(10,7),(4,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((37 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 9 0 1 [(12,4),(17,12),(18,14),(20,18),(13,6),(10,2),(16,11),(9,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((689 / 70): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((823 / 80): ℝ)
      · have hr:= hm
        apply H 16 0 1 [(10,-9),(2,-17),(9,-10),(18,4),(20,8),(0,-18),(5,-14),(11,-7),(13,-4),(16,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((823 / 80): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 16 0 1 [(10,-9),(14,-3),(2,-17),(3,-16),(5,-14),(16,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((211 / 20): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((919 / 80): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((773 / 70): ℝ)
      · have hr:= hm
        apply H 8 0 1 [(11,4),(16,12),(17,14),(19,18),(12,6),(9,2),(15,11),(8,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((773 / 70): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 10 0 1 [(12,3),(15,8),(9,-1),(1,-9),(8,-2),(2,-8),(3,-7),(4,-6),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((919 / 80): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((47 / 4): ℝ)
      · have hr:= hm
        apply H 2 0 1 [(4,2),(15,17),(9,8),(13,14),(1,0),(2,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((47 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 16 0 1 [(18,4),(11,-8),(8,-12),(14,-3),(7,-13),(10,-9),(15,-1),(16,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux39 (b: ℝ) (hl: ((857 / 70): ℝ) ≤ b) (hr: b ≤ ((1109 / 70): ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-((3 / 5): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ ((39 / 10): ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 ((3 / 5)) b ((39 / 10)) (by norm_num)
  by_cases hm: b ≤ ((283 / 20): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((133 / 10): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((203 / 16): ℝ)
      · have hr:= hm
        apply H 7 0 1 [(1,-6),(2,-5),(3,-4),(9,3),(11,6),(14,11),(8,2),(0,-6),(7,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((203 / 16): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 14 0 1 [(21,14),(20,12),(16,4),(10,-6),(7,-10),(0,-17),(1,-16),(3,-14),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((133 / 10): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((949 / 70): ℝ)
      · have hr:= hm
        apply H 8 0 1 [(10,3),(13,8),(21,24),(14,10),(15,12),(16,14),(8,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((949 / 70): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 10 0 1 [(13,5),(7,-4),(14,7),(15,9),(6,-5),(5,-6),(12,4),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((283 / 20): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((1033 / 70): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((205 / 14): ℝ)
      · have hr:= hm
        apply H 5 0 1 [(8,4),(13,12),(14,14),(16,18),(9,6),(6,2),(12,11),(5,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((205 / 14): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 9 0 1 [(12,5),(20,21),(13,7),(14,9),(15,11),(21,24),(9,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((1033 / 70): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((307 / 20): ℝ)
      · have hr:= hm
        apply H 12 0 1 [(6,-9),(13,2),(14,4),(5,-10),(4,-11),(11,-1),(9,-4),(12,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((307 / 20): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 4 0 1 [(7,4),(12,12),(13,14),(15,18),(8,6),(5,2),(11,11),(4,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux40 (b: ℝ) (hl: ((1109 / 70): ℝ) ≤ b) (hr: b ≤ (17: ℝ)) :
    x2611_12360_gap 17 (Set.range (fun k: Fin 22 => ((-((3 / 5): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (17: ℝ)))) ≤ ((39 / 10): ℝ):= by
  have H:= x2611_12360_table1_aux6 17 22 ((3 / 5)) b ((39 / 10)) (by norm_num)
  by_cases hm: b ≤ ((1117 / 70): ℝ)
  · have hr:= hm
    apply H 8 0 1 [(11,5),(19,21),(12,7),(13,9),(14,11),(20,24),(8,1)]
    · norm_num
    · simp
    · norm_num [List.isChain_cons,List.isChain_nil]
      all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((1117 / 70): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((331 / 20): ℝ)
    · have hr:= hm
      apply H 11 0 1 [(5,-9),(12,2),(13,4),(4,-10),(3,-11),(10,-1),(8,-4),(11,1)]
      · norm_num
      · simp
      · norm_num [List.isChain_cons,List.isChain_nil]
        all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((331 / 20): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      apply H 3 0 1 [(6,4),(11,12),(12,14),(14,18),(7,6),(4,2),(10,11),(3,1)]
      · norm_num
      · simp
      · norm_num [List.isChain_cons,List.isChain_nil]
        all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux41: x2611_12360_G 17 22 ((3 / 5): ℝ) ≤ ((39 / 10): ℝ):= by
  apply x2611_12360_table1_aux4 17 22 ((3 / 5)) ((39 / 10)) (by norm_num)
  intro b hl hr
  norm_num at hr
  by_cases hm: b ≤ ((121 / 14): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((87 / 20): ℝ)
    · have hr:= hm
      exact x2611_12360_table1_aux36 b (by linarith only[hl]) (by linarith only[hr])
    · have hl: ((87 / 20): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      exact x2611_12360_table1_aux37 b (by linarith only[hl]) (by linarith only[hr])
  · have hl: ((121 / 14): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((857 / 70): ℝ)
    · have hr:= hm
      exact x2611_12360_table1_aux38 b (by linarith only[hl]) (by linarith only[hr])
    · have hl: ((857 / 70): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((1109 / 70): ℝ)
      · have hr:= hm
        exact x2611_12360_table1_aux39 b (by linarith only[hl]) (by linarith only[hr])
      · have hl: ((1109 / 70): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        exact x2611_12360_table1_aux40 b (by linarith only[hl]) (by linarith only[hr])
lemma x2611_12360_table1_aux42: x2611_12360_G 17 22 ((3 / 5): ℝ) = ((39 / 10): ℝ):= by
  apply x2611_12360_table1_aux5 17 22 ((3 / 5)) ((39 / 10)) ((67 / 14)) ((437 / 70))
  · norm_num
  · norm_num
  · norm_num
  · intro k
    fin_cases k
    · exact ⟨0,by norm_num⟩
    · exact ⟨1,by norm_num⟩
    · exact ⟨1,by norm_num⟩
    · exact ⟨2,by norm_num⟩
    · exact ⟨3,by norm_num⟩
    · exact ⟨3,by norm_num⟩
    · exact ⟨4,by norm_num⟩
    · exact ⟨5,by norm_num⟩
    · exact ⟨6,by norm_num⟩
    · exact ⟨7,by norm_num⟩
    · exact ⟨8,by norm_num⟩
    · exact ⟨9,by norm_num⟩
    · exact ⟨10,by norm_num⟩
    · exact ⟨11,by norm_num⟩
    · exact ⟨13,by norm_num⟩
    · exact ⟨14,by norm_num⟩
    · exact ⟨15,by norm_num⟩
    · exact ⟨17,by norm_num⟩
    · exact ⟨19,by norm_num⟩
    · exact ⟨20,by norm_num⟩
    · exact ⟨22,by norm_num⟩
    · exact ⟨24,by norm_num⟩
  · exact x2611_12360_table1_aux41
lemma x2611_12360_table1_aux43 (b: ℝ) (hl: (0: ℝ) ≤ b) (hr: b ≤ (6: ℝ)) :
    x2611_12360_gap 29 (Set.range (fun k: Fin 22 => ((-(7: ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (29: ℝ)))) ≤ (6: ℝ):= by
  have H:= x2611_12360_table1_aux6 29 22 (7) b (6) (by norm_num)
  by_cases hm: b ≤ (4: ℝ)
  · have hr:= hm
    by_cases hm: b ≤ (2: ℝ)
    · have hr:= hm
      by_cases hm: b ≤ (1: ℝ)
      · have hr:= hm
        apply H 9 0 1 [(8,-4),(14,28),(11,10),(10,5),(1,-19),(5,-13),(7,-7),(6,-10),(9,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (1: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 11 0 1 [(10,-5),(16,33),(13,12),(12,6),(3,-27),(7,-17),(9,-9),(8,-13),(11,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: (2: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ (3: ℝ)
      · have hr:= hm
        apply H 13 0 1 [(12,-6),(18,38),(15,14),(14,7),(5,-35),(9,-21),(11,-11),(10,-16),(13,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (3: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 15 0 1 [(14,-7),(20,43),(17,16),(16,8),(7,-43),(11,-25),(13,-13),(12,-19),(15,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: (4: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ (5: ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((35 / 8): ℝ)
      · have hr:= hm
        apply H 16 0 1 [(0,-64),(7,-51),(13,-21),(15,-7),(1,-63),(2,-62),(17,9),(16,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((35 / 8): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 3 0 1 [(4,2),(17,70),(16,62),(19,88),(18,79),(9,19),(13,41),(15,55),(3,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: (5: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((17 / 3): ℝ)
      · have hr:= hm
        apply H 9 0 1 [(15,36),(17,52),(16,44),(19,70),(4,-16),(1,-20),(2,-19),(9,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((17 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 17 0 1 [(5,-66),(6,-63),(18,9),(21,38),(20,28),(11,-41),(15,-15),(17,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux44 (b: ℝ) (hl: (6: ℝ) ≤ b) (hr: b ≤ ((43 / 3): ℝ)) :
    x2611_12360_gap 29 (Set.range (fun k: Fin 22 => ((-(7: ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (29: ℝ)))) ≤ (6: ℝ):= by
  have H:= x2611_12360_table1_aux6 29 22 (7) b (6) (by norm_num)
  by_cases hm: b ≤ ((31 / 3): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((25 / 3): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((22 / 3): ℝ)
      · have hr:= hm
        apply H 10 0 1 [(8,-9),(5,-19),(6,-16),(0,-26),(3,-23),(4,-21),(11,6),(9,-4),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((22 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 10 0 1 [(7,-13),(8,-9),(2,-25),(5,-19),(6,-16),(13,18),(11,6),(12,12),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((25 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((28 / 3): ℝ)
      · have hr:= hm
        apply H 15 0 1 [(13,-14),(14,-7),(12,-20),(9,-36),(10,-31),(4,-53),(7,-44),(8,-40),(15,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((28 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 14 0 1 [(11,-19),(12,-13),(6,-41),(9,-29),(10,-24),(17,24),(15,8),(16,16),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((31 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((37 / 3): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((34 / 3): ℝ)
      · have hr:= hm
        apply H 16 0 1 [(13,-22),(14,-15),(8,-49),(11,-34),(12,-28),(19,27),(17,9),(18,18),(16,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((34 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 21 0 1 [(19,-20),(20,-10),(18,-29),(15,-54),(16,-46),(10,-86),(13,-68),(14,-61),(21,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((37 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((40 / 3): ℝ)
      · have hr:= hm
        apply H 18 0 1 [(12,-46),(15,-25),(0,-86),(2,-84),(1,-85),(4,-80),(9,-62),(14,-32),(20,20),(17,-8),(18,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((40 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 7 0 1 [(19,81),(20,91),(14,39),(17,63),(2,-13),(4,-9),(3,-11),(6,-3),(5,-6),(8,5),(7,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux45 (b: ℝ) (hl: ((43 / 3): ℝ) ≤ b) (hr: b ≤ ((62 / 3): ℝ)) :
    x2611_12360_gap 29 (Set.range (fun k: Fin 22 => ((-(7: ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (29: ℝ)))) ≤ (6: ℝ):= by
  have H:= x2611_12360_table1_aux6 29 22 (7) b (6) (by norm_num)
  by_cases hm: b ≤ (18: ℝ)
  · have hr:= hm
    by_cases hm: b ≤ (16: ℝ)
    · have hr:= hm
      by_cases hm: b ≤ (15: ℝ)
      · have hr:= hm
        apply H 4 0 1 [(6,6),(5,3),(8,14),(13,42),(10,24),(9,19),(0,-5),(4,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (15: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 8 0 1 [(7,-4),(10,10),(9,5),(15,43),(12,22),(11,16),(2,-17),(6,-7),(8,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: (16: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ (17: ℝ)
      · have hr:= hm
        apply H 12 0 1 [(11,-6),(17,38),(14,14),(13,7),(4,-35),(8,-21),(10,-11),(9,-16),(12,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (17: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 14 0 1 [(13,-7),(19,43),(16,16),(15,8),(6,-43),(10,-25),(12,-13),(11,-19),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: (18: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((59 / 3): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ (19: ℝ)
      · have hr:= hm
        apply H 16 0 1 [(15,-8),(21,48),(18,18),(17,9),(8,-51),(12,-29),(14,-15),(13,-22),(16,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (19: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 0 0 1 [(1,1),(8,21),(14,57),(16,73),(15,65),(18,91),(3,5),(0,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((59 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ (20: ℝ)
      · have hr:= hm
        apply H 16 0 1 [(4,-66),(5,-63),(17,9),(20,38),(19,28),(10,-41),(14,-15),(16,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (20: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 10 0 1 [(16,42),(18,60),(17,51),(20,80),(5,-21),(2,-28),(3,-26),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux46 (b: ℝ) (hl: ((62 / 3): ℝ) ≤ b) (hr: b ≤ ((85 / 3): ℝ)) :
    x2611_12360_gap 29 (Set.range (fun k: Fin 22 => ((-(7: ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (29: ℝ)))) ≤ (6: ℝ):= by
  have H:= x2611_12360_table1_aux6 29 22 (7) b (6) (by norm_num)
  by_cases hm: b ≤ ((73 / 3): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((67 / 3): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ (21: ℝ)
      · have hr:= hm
        apply H 12 0 1 [(16,30),(18,48),(6,-30),(7,-26),(4,-36),(5,-33),(21,79),(12,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (21: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 12 0 1 [(10,-12),(11,-6),(9,-17),(6,-30),(7,-26),(1,-42),(4,-36),(5,-33),(12,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((67 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((70 / 3): ℝ)
      · have hr:= hm
        apply H 11 0 1 [(8,-16),(9,-11),(3,-33),(6,-24),(7,-20),(14,21),(12,7),(13,14),(11,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((70 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 16 0 1 [(14,-16),(15,-8),(13,-23),(10,-42),(11,-36),(5,-64),(8,-52),(9,-47),(16,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((73 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((79 / 3): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((76 / 3): ℝ)
      · have hr:= hm
        apply H 10 0 1 [(11,6),(18,61),(16,43),(17,52),(15,35),(12,13),(13,20),(7,-14),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((76 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 17 0 1 [(14,-25),(15,-17),(9,-57),(12,-39),(13,-32),(20,30),(18,10),(19,20),(17,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((79 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((82 / 3): ℝ)
      · have hr:= hm
        apply H 14 0 1 [(6,-46),(1,-59),(0,-60),(3,-55),(8,-37),(13,-7),(19,45),(16,17),(17,26),(11,-20),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((82 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 16 0 1 [(1,-76),(3,-72),(2,-74),(5,-66),(10,-43),(15,-8),(21,50),(18,19),(19,29),(13,-23),(16,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux47 (b: ℝ) (hl: ((85 / 3): ℝ) ≤ b) (hr: b ≤ (29: ℝ)) :
    x2611_12360_gap 29 (Set.range (fun k: Fin 22 => ((-(7: ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (29: ℝ)))) ≤ (6: ℝ):= by
  have H:= x2611_12360_table1_aux6 29 22 (7) b (6) (by norm_num)
  apply H 5 0 1 [(4,-3),(7,8),(12,36),(9,18),(8,13),(1,-9),(3,-5),(5,1)]
  · norm_num
  · simp
  · norm_num [List.isChain_cons,List.isChain_nil]
    all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux48: x2611_12360_G 29 22 (7: ℝ) ≤ (6: ℝ):= by
  apply x2611_12360_table1_aux4 29 22 (7) (6) (by norm_num)
  intro b hl hr
  norm_num at hr
  by_cases hm: b ≤ ((43 / 3): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ (6: ℝ)
    · have hr:= hm
      exact x2611_12360_table1_aux43 b (by linarith only[hl]) (by linarith only[hr])
    · have hl: (6: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      exact x2611_12360_table1_aux44 b (by linarith only[hl]) (by linarith only[hr])
  · have hl: ((43 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((62 / 3): ℝ)
    · have hr:= hm
      exact x2611_12360_table1_aux45 b (by linarith only[hl]) (by linarith only[hr])
    · have hl: ((62 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((85 / 3): ℝ)
      · have hr:= hm
        exact x2611_12360_table1_aux46 b (by linarith only[hl]) (by linarith only[hr])
      · have hl: ((85 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        exact x2611_12360_table1_aux47 b (by linarith only[hl]) (by linarith only[hr])
lemma x2611_12360_table1_aux49: x2611_12360_G 29 22 (7: ℝ) = (6: ℝ):= by
  apply x2611_12360_table1_aux5 29 22 (7) (6) (0) (4)
  · norm_num
  · norm_num
  · norm_num
  · intro k
    fin_cases k
    · exact ⟨0,by norm_num⟩
    · exact ⟨1,by norm_num⟩
    · exact ⟨2,by norm_num⟩
    · exact ⟨3,by norm_num⟩
    · exact ⟨5,by norm_num⟩
    · exact ⟨7,by norm_num⟩
    · exact ⟨10,by norm_num⟩
    · exact ⟨13,by norm_num⟩
    · exact ⟨17,by norm_num⟩
    · exact ⟨21,by norm_num⟩
    · exact ⟨26,by norm_num⟩
    · exact ⟨31,by norm_num⟩
    · exact ⟨37,by norm_num⟩
    · exact ⟨43,by norm_num⟩
    · exact ⟨50,by norm_num⟩
    · exact ⟨57,by norm_num⟩
    · exact ⟨64,by norm_num⟩
    · exact ⟨73,by norm_num⟩
    · exact ⟨81,by norm_num⟩
    · exact ⟨90,by norm_num⟩
    · exact ⟨100,by norm_num⟩
    · exact ⟨110,by norm_num⟩
  · exact x2611_12360_table1_aux48
lemma x2611_12360_table1_aux50 (b: ℝ) (hl: (0: ℝ) ≤ b) (hr: b ≤ ((71 / 18): ℝ)) :
    x2611_12360_gap 29 (Set.range (fun k: Fin 22 => ((-(14: ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (29: ℝ)))) ≤ ((17 / 3): ℝ):= by
  have H:= x2611_12360_table1_aux6 29 22 (14) b ((17 / 3)) (by norm_num)
  by_cases hm: b ≤ ((5 / 3): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((2 / 3): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((1 / 6): ℝ)
      · have hr:= hm
        apply H 7 0 1 [(12,46),(18,133),(19,151),(20,170),(5,-11),(8,8),(4,-15),(7,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((1 / 6): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 10 0 1 [(9,-9),(5,-36),(8,-17),(2,-46),(4,-40),(7,-24),(18,109),(19,127),(20,146),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((2 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((7 / 6): ℝ)
      · have hr:= hm
        apply H 19 0 1 [(20,19),(21,39),(6,-157),(1,-174),(9,-135),(5,-162),(8,-143),(13,-92),(19,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((7 / 6): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 10 0 1 [(6,-31),(9,-9),(3,-44),(5,-36),(8,-17),(19,127),(20,146),(21,166),(11,11),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((5 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((8 / 3): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((13 / 6): ℝ)
      · have hr:= hm
        apply H 10 0 1 [(6,-31),(9,-9),(14,47),(20,146),(12,22),(11,11),(2,-46),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((13 / 6): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 12 0 1 [(11,-11),(7,-46),(10,-21),(0,-70),(6,-52),(9,-30),(20,125),(21,145),(8,-38),(12,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((8 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((19 / 6): ℝ)
      · have hr:= hm
        apply H 10 0 1 [(15,61),(21,166),(13,34),(12,22),(3,-44),(11,11),(7,-24),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((19 / 6): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 14 0 1 [(13,-13),(6,-78),(0,-96),(12,-25),(8,-64),(11,-36),(5,-83),(7,-71),(15,15),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux51 (b: ℝ) (hl: ((71 / 18): ℝ) ≤ b) (hr: b ≤ ((143 / 18): ℝ)) :
    x2611_12360_gap 29 (Set.range (fun k: Fin 22 => ((-(14: ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (29: ℝ)))) ≤ ((17 / 3): ℝ):= by
  have H:= x2611_12360_table1_aux6 29 22 (14) b ((17 / 3)) (by norm_num)
  by_cases hm: b ≤ ((107 / 18): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((89 / 18): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((25 / 6): ℝ)
      · have hr:= hm
        apply H 3 0 1 [(7,20),(14,92),(13,79),(4,4),(12,67),(8,28),(11,56),(16,122),(3,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((25 / 6): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 7 0 1 [(1,-24),(13,59),(9,16),(12,47),(6,-6),(8,8),(16,102),(15,87),(14,73),(7,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((89 / 18): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((31 / 6): ℝ)
      · have hr:= hm
        apply H 17 0 1 [(4,-134),(8,-110),(15,-31),(14,-45),(0,-142),(3,-137),(13,-58),(9,-101),(12,-70),(17,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((31 / 6): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 8 0 1 [(2,-30),(14,65),(10,18),(13,52),(7,-7),(9,9),(17,111),(16,95),(15,80),(8,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((107 / 18): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((125 / 18): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((37 / 6): ℝ)
      · have hr:= hm
        apply H 15 0 1 [(1,-111),(4,-103),(14,-14),(10,-61),(13,-27),(18,49),(5,-98),(9,-70),(16,16),(15,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((37 / 6): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 17 0 1 [(16,-16),(9,-102),(3,-138),(15,-31),(11,-82),(14,-45),(8,-110),(10,-92),(18,18),(17,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((125 / 18): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((43 / 6): ℝ)
      · have hr:= hm
        apply H 16 0 1 [(2,-125),(5,-114),(15,-15),(11,-66),(14,-29),(19,52),(6,-108),(10,-76),(17,17),(16,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((43 / 6): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 19 0 1 [(18,-18),(17,-35),(10,-128),(4,-170),(16,-51),(12,-106),(15,-66),(9,-137),(11,-117),(19,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux52 (b: ℝ) (hl: ((143 / 18): ℝ) ≤ b) (hr: b ≤ ((79 / 6): ℝ)) :
    x2611_12360_gap 29 (Set.range (fun k: Fin 22 => ((-(14: ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (29: ℝ)))) ≤ ((17 / 3): ℝ):= by
  have H:= x2611_12360_table1_aux6 29 22 (14) b ((17 / 3)) (by norm_num)
  by_cases hm: b ≤ ((32 / 3): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((55 / 6): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((26 / 3): ℝ)
      · have hr:= hm
        apply H 18 0 1 [(17,-17),(13,-76),(16,-33),(6,-142),(0,-161),(4,-152),(1,-160),(7,-135),(11,-99),(18,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((26 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 21 0 1 [(8,-186),(12,-146),(19,-39),(18,-57),(4,-210),(7,-193),(17,-74),(13,-133),(16,-90),(21,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((55 / 6): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((179 / 18): ℝ)
      · have hr:= hm
        apply H 12 0 1 [(6,-54),(18,89),(14,26),(17,72),(11,-11),(13,13),(21,147),(20,127),(19,108),(12,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((179 / 18): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 8 0 1 [(2,-31),(6,-14),(3,-28),(9,9),(13,53),(4,-24),(0,-33),(1,-32),(8,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((32 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((107 / 9): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((100 / 9): ℝ)
      · have hr:= hm
        apply H 6 0 1 [(9,23),(19,162),(15,95),(18,144),(12,55),(14,81),(1,-18),(2,-16),(6,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((100 / 9): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 10 0 1 [(14,48),(8,-18),(0,-52),(1,-51),(2,-49),(9,-9),(15,63),(3,-46),(7,-25),(4,-42),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((107 / 9): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((115 / 9): ℝ)
      · have hr:= hm
        apply H 8 0 1 [(5,-20),(11,29),(9,9),(1,-33),(2,-31),(3,-28),(7,-7),(10,19),(4,-24),(8,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((115 / 9): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 21 0 1 [(17,-75),(20,-20),(0,-222),(2,-219),(3,-216),(4,-212),(8,-187),(11,-158),(21,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux53 (b: ℝ) (hl: ((79 / 6): ℝ) ≤ b) (hr: b ≤ ((160 / 9): ℝ)) :
    x2611_12360_gap 29 (Set.range (fun k: Fin 22 => ((-(14: ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (29: ℝ)))) ≤ ((17 / 3): ℝ):= by
  have H:= x2611_12360_table1_aux6 29 22 (14) b ((17 / 3)) (by norm_num)
  by_cases hm: b ≤ ((142 / 9): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((133 / 9): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((125 / 9): ℝ)
      · have hr:= hm
        apply H 12 0 1 [(16,56),(10,-22),(2,-72),(3,-69),(4,-65),(11,-11),(17,73),(5,-60),(9,-31),(6,-54),(12,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((125 / 9): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 10 0 1 [(7,-26),(13,35),(17,95),(1,-52),(3,-47),(4,-43),(5,-38),(9,-9),(12,23),(6,-32),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((133 / 9): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((269 / 18): ℝ)
      · have hr:= hm
        apply H 2 0 1 [(4,7),(5,12),(6,18),(10,51),(17,146),(11,62),(2,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((269 / 18): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 13 0 1 [(7,-61),(11,-24),(8,-53),(14,14),(18,78),(2,-85),(4,-78),(5,-73),(6,-67),(13,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((142 / 9): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((151 / 9): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((287 / 18): ℝ)
      · have hr:= hm
        apply H 3 0 1 [(5,9),(6,15),(7,22),(11,59),(18,161),(12,71),(3,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((287 / 18): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 14 0 1 [(8,-67),(12,-26),(9,-58),(15,15),(19,83),(3,-96),(5,-87),(6,-81),(7,-74),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((151 / 9): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((305 / 18): ℝ)
      · have hr:= hm
        apply H 0 0 1 [(6,21),(7,28),(8,36),(12,77),(19,186),(13,90),(0,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((305 / 18): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 15 0 1 [(9,-73),(13,-28),(10,-63),(16,16),(20,88),(4,-107),(6,-96),(7,-89),(8,-81),(15,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux54 (b: ℝ) (hl: ((160 / 9): ℝ) ≤ b) (hr: b ≤ ((65 / 3): ℝ)) :
    x2611_12360_gap 29 (Set.range (fun k: Fin 22 => ((-(14: ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (29: ℝ)))) ≤ ((17 / 3): ℝ):= by
  have H:= x2611_12360_table1_aux6 29 22 (14) b ((17 / 3)) (by norm_num)
  by_cases hm: b ≤ ((178 / 9): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((169 / 9): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((323 / 18): ℝ)
      · have hr:= hm
        apply H 1 0 1 [(7,27),(8,35),(9,44),(13,89),(20,205),(14,103),(1,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((323 / 18): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 16 0 1 [(10,-79),(14,-30),(11,-68),(17,17),(21,93),(5,-118),(7,-105),(8,-97),(9,-88),(16,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((169 / 9): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((341 / 18): ℝ)
      · have hr:= hm
        apply H 2 0 1 [(8,33),(9,42),(10,52),(14,101),(21,224),(15,116),(2,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((341 / 18): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 17 0 1 [(11,-85),(15,-32),(12,-73),(18,18),(16,-16),(8,-114),(9,-105),(10,-95),(17,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((178 / 9): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((62 / 3): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((119 / 6): ℝ)
      · have hr:= hm
        apply H 3 0 1 [(9,39),(10,49),(11,60),(15,113),(18,163),(16,129),(3,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((119 / 6): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 18 0 1 [(12,-91),(16,-34),(13,-78),(6,-147),(7,-140),(9,-123),(10,-113),(11,-102),(15,-49),(18,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((62 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((125 / 6): ℝ)
      · have hr:= hm
        apply H 4 0 1 [(10,45),(11,56),(12,68),(16,125),(19,178),(17,142),(4,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((125 / 6): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 17 0 1 [(14,-47),(7,-123),(8,-115),(10,-96),(11,-85),(12,-73),(16,-16),(19,37),(13,-60),(17,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux55 (b: ℝ) (hl: ((65 / 3): ℝ) ≤ b) (hr: b ≤ ((77 / 3): ℝ)) :
    x2611_12360_gap 29 (Set.range (fun k: Fin 22 => ((-(14: ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (29: ℝ)))) ≤ ((17 / 3): ℝ):= by
  have H:= x2611_12360_table1_aux6 29 22 (14) b ((17 / 3)) (by norm_num)
  by_cases hm: b ≤ ((71 / 3): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((205 / 9): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((460 / 21): ℝ)
      · have hr:= hm
        apply H 0 0 1 [(5,16),(11,67),(12,79),(13,92),(17,153),(14,106),(0,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((460 / 21): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 20 0 1 [(14,-103),(18,-38),(15,-88),(21,21),(19,-19),(11,-141),(12,-129),(13,-116),(20,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((205 / 9): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((481 / 21): ℝ)
      · have hr:= hm
        apply H 1 0 1 [(6,21),(12,78),(13,91),(14,105),(18,170),(15,120),(1,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((481 / 21): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 13 0 1 [(14,14),(21,138),(15,29),(19,98),(16,45),(9,-45),(10,-35),(12,-12),(13,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((71 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((74 / 3): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((502 / 21): ℝ)
      · have hr:= hm
        apply H 2 0 1 [(7,26),(13,89),(14,103),(15,118),(19,187),(16,134),(2,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((502 / 21): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 14 0 1 [(15,15),(5,-90),(4,-95),(0,-106),(3,-99),(16,31),(20,104),(17,48),(10,-49),(11,-38),(13,-13),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((74 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((151 / 6): ℝ)
      · have hr:= hm
        apply H 15 0 1 [(16,16),(20,89),(17,33),(4,-110),(0,-121),(3,-114),(8,-83),(14,-14),(15,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((151 / 6): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 15 0 1 [(16,16),(6,-99),(5,-105),(17,33),(21,110),(18,51),(11,-53),(14,-14),(15,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux56 (b: ℝ) (hl: ((77 / 3): ℝ) ≤ b) (hr: b ≤ (29: ℝ)) :
    x2611_12360_gap 29 (Set.range (fun k: Fin 22 => ((-(14: ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (29: ℝ)))) ≤ ((17 / 3): ℝ):= by
  have H:= x2611_12360_table1_aux6 29 22 (14) b ((17 / 3)) (by norm_num)
  by_cases hm: b ≤ ((163 / 6): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((157 / 6): ℝ)
    · have hr:= hm
      apply H 16 0 1 [(17,17),(21,94),(18,35),(5,-121),(1,-136),(4,-126),(9,-90),(15,-15),(16,1)]
      · norm_num
      · simp
      · norm_num [List.isChain_cons,List.isChain_nil]
        all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((157 / 6): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((80 / 3): ℝ)
      · have hr:= hm
        apply H 17 0 1 [(7,-125),(6,-132),(2,-151),(5,-138),(19,37),(12,-74),(15,-32),(16,-16),(17,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((80 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 3 0 1 [(0,-7),(6,16),(2,-3),(5,10),(10,51),(16,132),(17,149),(18,167),(3,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((163 / 6): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((169 / 6): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((83 / 3): ℝ)
      · have hr:= hm
        apply H 8 0 1 [(7,-8),(3,-31),(6,-15),(0,-38),(2,-34),(5,-21),(16,101),(17,118),(18,136),(8,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((83 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 17 0 1 [(18,18),(19,37),(4,-144),(1,-154),(7,-125),(3,-148),(6,-132),(11,-86),(17,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((169 / 6): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((86 / 3): ℝ)
      · have hr:= hm
        apply H 8 0 1 [(4,-27),(7,-8),(1,-37),(3,-31),(6,-15),(17,118),(18,136),(19,155),(9,10),(8,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((86 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 7 0 1 [(12,51),(18,144),(19,163),(20,183),(0,-30),(8,9),(4,-18),(7,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux57: x2611_12360_G 29 22 (14: ℝ) ≤ ((17 / 3): ℝ):= by
  apply x2611_12360_table1_aux4 29 22 (14) ((17 / 3)) (by norm_num)
  intro b hl hr
  norm_num at hr
  by_cases hm: b ≤ ((79 / 6): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((71 / 18): ℝ)
    · have hr:= hm
      exact x2611_12360_table1_aux50 b (by linarith only[hl]) (by linarith only[hr])
    · have hl: ((71 / 18): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((143 / 18): ℝ)
      · have hr:= hm
        exact x2611_12360_table1_aux51 b (by linarith only[hl]) (by linarith only[hr])
      · have hl: ((143 / 18): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        exact x2611_12360_table1_aux52 b (by linarith only[hl]) (by linarith only[hr])
  · have hl: ((79 / 6): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((65 / 3): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((160 / 9): ℝ)
      · have hr:= hm
        exact x2611_12360_table1_aux53 b (by linarith only[hl]) (by linarith only[hr])
      · have hl: ((160 / 9): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        exact x2611_12360_table1_aux54 b (by linarith only[hl]) (by linarith only[hr])
    · have hl: ((65 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((77 / 3): ℝ)
      · have hr:= hm
        exact x2611_12360_table1_aux55 b (by linarith only[hl]) (by linarith only[hr])
      · have hl: ((77 / 3): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        exact x2611_12360_table1_aux56 b (by linarith only[hl]) (by linarith only[hr])
lemma x2611_12360_table1_aux58: x2611_12360_G 29 22 (14: ℝ) = ((17 / 3): ℝ):= by
  apply x2611_12360_table1_aux5 29 22 (14) ((17 / 3)) ((5 / 3)) ((1 / 6))
  · norm_num
  · norm_num
  · norm_num
  · intro k
    fin_cases k
    · exact ⟨0,by norm_num⟩
    · exact ⟨1,by norm_num⟩
    · exact ⟨2,by norm_num⟩
    · exact ⟨5,by norm_num⟩
    · exact ⟨8,by norm_num⟩
    · exact ⟨13,by norm_num⟩
    · exact ⟨18,by norm_num⟩
    · exact ⟨24,by norm_num⟩
    · exact ⟨31,by norm_num⟩
    · exact ⟨40,by norm_num⟩
    · exact ⟨49,by norm_num⟩
    · exact ⟨59,by norm_num⟩
    · exact ⟨70,by norm_num⟩
    · exact ⟨82,by norm_num⟩
    · exact ⟨95,by norm_num⟩
    · exact ⟨109,by norm_num⟩
    · exact ⟨124,by norm_num⟩
    · exact ⟨140,by norm_num⟩
    · exact ⟨157,by norm_num⟩
    · exact ⟨175,by norm_num⟩
    · exact ⟨194,by norm_num⟩
    · exact ⟨214,by norm_num⟩
  · exact x2611_12360_table1_aux57
lemma x2611_12360_table1_aux59 (b: ℝ) (hl: (0: ℝ) ≤ b) (hr: b ≤ ((13 / 2): ℝ)) :
    x2611_12360_gap 29 (Set.range (fun k: Fin 22 => ((-((1 / 4): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (29: ℝ)))) ≤ ((23 / 4): ℝ):= by
  have H:= x2611_12360_table1_aux6 29 22 ((1 / 4)) b ((23 / 4)) (by norm_num)
  by_cases hm: b ≤ ((143 / 32): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((79 / 32): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((47 / 32): ℝ)
      · have hr:= hm
        apply H 10 0 1 [(14,1),(17,2),(9,0),(8,0),(7,0),(6,0),(5,0),(4,0),(3,0),(1,0),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((47 / 32): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 7 0 1 [(6,0),(5,0),(4,0),(3,0),(2,0),(8,1),(12,2),(15,3),(7,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((79 / 32): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((111 / 32): ℝ)
      · have hr:= hm
        apply H 3 0 1 [(2,0),(7,1),(14,3),(19,5),(21,6),(16,4),(13,3),(5,1),(4,1),(3,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((111 / 32): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 0 0 1 [(5,1),(12,3),(17,5),(19,6),(14,4),(11,3),(3,1),(2,1),(1,1),(0,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((143 / 32): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((11 / 2): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ (5: ℝ)
      · have hr:= hm
        apply H 16 0 1 [(18,1),(13,-1),(10,-2),(15,0),(17,1),(9,-2),(5,-3),(14,0),(16,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (5: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 10 0 1 [(17,3),(12,1),(9,0),(14,2),(16,3),(8,0),(4,-1),(7,0),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((11 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ (6: ℝ)
      · have hr:= hm
        apply H 6 0 1 [(9,1),(16,4),(11,2),(8,1),(13,3),(15,4),(7,1),(3,0),(6,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (6: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 12 0 1 [(14,1),(6,-2),(2,-3),(5,-2),(8,-1),(15,2),(10,0),(7,-1),(12,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux60 (b: ℝ) (hl: ((13 / 2): ℝ) ≤ b) (hr: b ≤ ((19 / 2): ℝ)) :
    x2611_12360_gap 29 (Set.range (fun k: Fin 22 => ((-((1 / 4): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (29: ℝ)))) ≤ ((23 / 4): ℝ):= by
  have H:= x2611_12360_table1_aux6 29 22 ((1 / 4)) b ((23 / 4)) (by norm_num)
  by_cases hm: b ≤ (8: ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((15 / 2): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ (7: ℝ)
      · have hr:= hm
        apply H 7 0 1 [(14,3),(9,1),(6,0),(11,2),(13,3),(5,0),(1,-1),(4,0),(7,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (7: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 6 0 1 [(13,3),(8,1),(5,0),(10,2),(12,3),(4,0),(0,-1),(3,0),(6,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((15 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((383 / 48): ℝ)
      · have hr:= hm
        apply H 11 0 1 [(13,1),(20,5),(8,-1),(10,0),(12,1),(7,-1),(4,-2),(9,0),(11,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((383 / 48): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 3 0 1 [(8,2),(10,3),(12,4),(7,2),(9,3),(11,4),(3,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: (8: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((17 / 2): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((407 / 48): ℝ)
      · have hr:= hm
        apply H 10 0 1 [(12,1),(19,5),(7,-1),(9,0),(11,1),(6,-1),(3,-2),(8,0),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((407 / 48): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 6 0 1 [(8,1),(10,2),(2,-1),(7,1),(9,2),(11,3),(6,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((17 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ (9: ℝ)
      · have hr:= hm
        apply H 10 0 1 [(5,-2),(2,-3),(7,-1),(9,0),(11,1),(18,5),(21,7),(6,-1),(8,0),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (9: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 20 0 1 [(5,-8),(7,-7),(9,-6),(4,-8),(1,-9),(6,-7),(8,-6),(10,-5),(17,-1),(20,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux61 (b: ℝ) (hl: ((19 / 2): ℝ) ≤ b) (hr: b ≤ ((229 / 18): ℝ)) :
    x2611_12360_gap 29 (Set.range (fun k: Fin 22 => ((-((1 / 4): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (29: ℝ)))) ≤ ((23 / 4): ℝ):= by
  have H:= x2611_12360_table1_aux6 29 22 ((1 / 4)) b ((23 / 4)) (by norm_num)
  by_cases hm: b ≤ ((54 / 5): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((103 / 10): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ (10: ℝ)
      · have hr:= hm
        apply H 19 0 1 [(4,-8),(6,-7),(8,-6),(3,-8),(0,-9),(5,-7),(7,-6),(9,-5),(16,-1),(19,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (10: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 15 0 1 [(18,2),(0,-7),(7,-4),(19,3),(14,0),(17,2),(8,-3),(15,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((103 / 10): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((21 / 2): ℝ)
      · have hr:= hm
        apply H 2 0 1 [(4,1),(6,2),(15,7),(18,9),(3,1),(5,2),(7,3),(2,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((21 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 13 0 1 [(16,2),(7,-3),(14,1),(17,3),(4,-4),(6,-3),(18,4),(13,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((54 / 5): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((211 / 18): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ (11: ℝ)
      · have hr:= hm
        apply H 14 0 1 [(17,2),(2,-6),(4,-5),(6,-4),(1,-6),(3,-5),(5,-4),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (11: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 4 0 1 [(6,1),(13,5),(16,7),(11,4),(20,10),(17,8),(21,11),(12,5),(15,7),(2,0),(4,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((211 / 18): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((110 / 9): ℝ)
      · have hr:= hm
        apply H 10 0 1 [(13,2),(20,7),(11,1),(14,3),(1,-4),(3,-3),(12,2),(15,4),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((110 / 9): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 2 0 1 [(11,5),(14,7),(9,4),(12,6),(19,11),(10,5),(13,7),(0,0),(2,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux62 (b: ℝ) (hl: ((229 / 18): ℝ) ≤ b) (hr: b ≤ ((807 / 40): ℝ)) :
    x2611_12360_gap 29 (Set.range (fun k: Fin 22 => ((-((1 / 4): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (29: ℝ)))) ≤ ((23 / 4): ℝ):= by
  have H:= x2611_12360_table1_aux6 29 22 ((1 / 4)) b ((23 / 4)) (by norm_num)
  by_cases hm: b ≤ ((151 / 10): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((247 / 18): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((119 / 9): ℝ)
      · have hr:= hm
        apply H 8 0 1 [(11,2),(18,7),(9,1),(7,0),(1,-3),(10,2),(13,4),(8,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((119 / 9): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 21 0 1 [(10,-8),(17,-3),(8,-9),(6,-10),(0,-13),(9,-8),(12,-6),(20,0),(21,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((247 / 18): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((128 / 9): ℝ)
      · have hr:= hm
        apply H 16 0 1 [(7,-6),(5,-7),(1,-9),(8,-5),(11,-3),(19,3),(20,4),(21,5),(16,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((128 / 9): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 16 0 1 [(9,-5),(4,-8),(2,-9),(7,-6),(10,-4),(18,2),(19,3),(20,4),(21,5),(16,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((151 / 10): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((563 / 32): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((163 / 10): ℝ)
      · have hr:= hm
        apply H 5 0 1 [(8,2),(16,8),(17,9),(18,10),(19,11),(20,12),(21,13),(10,4),(7,2),(2,-1),(0,-2),(5,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((163 / 10): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 19 0 1 [(21,2),(13,-5),(9,-8),(14,-4),(15,-3),(16,-2),(17,-1),(18,0),(19,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((563 / 32): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ (19: ℝ)
      · have hr:= hm
        apply H 6 0 1 [(3,-2),(11,4),(12,5),(13,6),(14,7),(15,8),(16,9),(17,10),(18,11),(10,4),(6,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (19: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 14 0 1 [(15,1),(18,4),(8,-5),(9,-4),(10,-3),(11,-2),(12,-1),(13,0),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux63 (b: ℝ) (hl: ((807 / 40): ℝ) ≤ b) (hr: b ≤ ((911 / 32): ℝ)) :
    x2611_12360_gap 29 (Set.range (fun k: Fin 22 => ((-((1 / 4): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (29: ℝ)))) ≤ ((23 / 4): ℝ):= by
  have H:= x2611_12360_table1_aux6 29 22 ((1 / 4)) b ((23 / 4)) (by norm_num)
  by_cases hm: b ≤ ((967 / 40): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((887 / 40): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((847 / 40): ℝ)
      · have hr:= hm
        apply H 9 0 1 [(10,1),(11,2),(13,4),(16,7),(6,-2),(7,-1),(8,0),(9,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((847 / 40): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 7 0 1 [(8,1),(9,2),(11,4),(14,7),(4,-2),(5,-1),(6,0),(7,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((887 / 40): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((927 / 40): ℝ)
      · have hr:= hm
        apply H 5 0 1 [(6,1),(7,2),(9,4),(12,7),(2,-2),(3,-1),(4,0),(5,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((927 / 40): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 3 0 1 [(4,1),(5,2),(7,4),(10,7),(0,-2),(1,-1),(2,0),(3,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((967 / 40): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ (26: ℝ)
    · have hr:= hm
      by_cases hm: b ≤ (25: ℝ)
      · have hr:= hm
        apply H 19 0 1 [(18,-1),(17,-2),(0,-19),(1,-18),(2,-17),(3,-16),(4,-15),(6,-13),(20,2),(19,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: (25: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 13 0 1 [(0,-13),(1,-12),(2,-11),(3,-10),(6,-7),(18,6),(17,5),(16,4),(15,3),(14,2),(13,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: (26: ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((136 / 5): ℝ)
      · have hr:= hm
        apply H 8 0 1 [(16,9),(20,14),(15,8),(14,7),(13,6),(12,5),(11,4),(10,3),(8,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((136 / 5): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 21 0 1 [(13,-10),(12,-11),(11,-12),(10,-13),(9,-14),(8,-15),(7,-16),(14,-8),(18,-3),(21,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux64 (b: ℝ) (hl: ((911 / 32): ℝ) ≤ b) (hr: b ≤ (29: ℝ)) :
    x2611_12360_gap 29 (Set.range (fun k: Fin 22 => ((-((1 / 4): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (29: ℝ)))) ≤ ((23 / 4): ℝ):= by
  have H:= x2611_12360_table1_aux6 29 22 ((1 / 4)) b ((23 / 4)) (by norm_num)
  apply H 9 0 1 [(8,-1),(13,5),(6,-3),(12,4),(11,3),(10,2),(9,1)]
  · norm_num
  · simp
  · norm_num [List.isChain_cons,List.isChain_nil]
    all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux65: x2611_12360_G 29 22 ((1 / 4): ℝ) ≤ ((23 / 4): ℝ):= by
  apply x2611_12360_table1_aux4 29 22 ((1 / 4)) ((23 / 4)) (by norm_num)
  intro b hl hr
  norm_num at hr
  by_cases hm: b ≤ ((229 / 18): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((13 / 2): ℝ)
    · have hr:= hm
      exact x2611_12360_table1_aux59 b (by linarith only[hl]) (by linarith only[hr])
    · have hl: ((13 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((19 / 2): ℝ)
      · have hr:= hm
        exact x2611_12360_table1_aux60 b (by linarith only[hl]) (by linarith only[hr])
      · have hl: ((19 / 2): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        exact x2611_12360_table1_aux61 b (by linarith only[hl]) (by linarith only[hr])
  · have hl: ((229 / 18): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((807 / 40): ℝ)
    · have hr:= hm
      exact x2611_12360_table1_aux62 b (by linarith only[hl]) (by linarith only[hr])
    · have hl: ((807 / 40): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((911 / 32): ℝ)
      · have hr:= hm
        exact x2611_12360_table1_aux63 b (by linarith only[hl]) (by linarith only[hr])
      · have hl: ((911 / 32): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        exact x2611_12360_table1_aux64 b (by linarith only[hl]) (by linarith only[hr])
lemma x2611_12360_table1_aux66: x2611_12360_G 29 22 ((1 / 4): ℝ) = ((23 / 4): ℝ):= by
  apply x2611_12360_table1_aux5 29 22 ((1 / 4)) ((23 / 4)) ((41 / 4)) ((19 / 2))
  · norm_num
  · norm_num
  · norm_num
  · intro k
    fin_cases k
    · exact ⟨0,by norm_num⟩
    · exact ⟨1,by norm_num⟩
    · exact ⟨1,by norm_num⟩
    · exact ⟨2,by norm_num⟩
    · exact ⟨2,by norm_num⟩
    · exact ⟨2,by norm_num⟩
    · exact ⟨3,by norm_num⟩
    · exact ⟨3,by norm_num⟩
    · exact ⟨4,by norm_num⟩
    · exact ⟨4,by norm_num⟩
    · exact ⟨5,by norm_num⟩
    · exact ⟨5,by norm_num⟩
    · exact ⟨6,by norm_num⟩
    · exact ⟨6,by norm_num⟩
    · exact ⟨7,by norm_num⟩
    · exact ⟨7,by norm_num⟩
    · exact ⟨8,by norm_num⟩
    · exact ⟨9,by norm_num⟩
    · exact ⟨9,by norm_num⟩
    · exact ⟨10,by norm_num⟩
    · exact ⟨10,by norm_num⟩
    · exact ⟨11,by norm_num⟩
  · exact x2611_12360_table1_aux65
lemma x2611_12360_table1_aux67 (b: ℝ) (hl: (0: ℝ) ≤ b) (hr: b ≤ ((601 / 168): ℝ)) :
    x2611_12360_gap 29 (Set.range (fun k: Fin 22 => ((-((157 / 11): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (29: ℝ)))) ≤ ((731 / 132): ℝ):= by
  have H:= x2611_12360_table1_aux6 29 22 ((157 / 11)) b ((731 / 132)) (by norm_num)
  by_cases hm: b ≤ ((983 / 528): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((1235 / 1056): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((755 / 1056): ℝ)
      · have hr:= hm
        apply H 5 0 1 [(7,12),(16,114),(20,185),(12,59),(15,99),(4,-4),(6,6),(11,48),(8,20),(1,-11),(5,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((755 / 1056): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 7 0 1 [(12,47),(9,16),(18,136),(0,-24),(6,-6),(8,8),(21,194),(13,60),(16,103),(5,-11),(7,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((1235 / 1056): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((743 / 528): ℝ)
      · have hr:= hm
        apply H 13 0 1 [(10,-34),(19,95),(7,-59),(9,-43),(18,77),(14,14),(17,60),(8,-51),(13,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((743 / 528): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 19 0 1 [(15,-67),(18,-18),(9,-138),(14,-81),(11,-118),(2,-176),(8,-146),(10,-128),(19,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((983 / 528): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((133 / 48): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((1223 / 528): ℝ)
      · have hr:= hm
        apply H 10 0 1 [(15,62),(12,22),(3,-45),(9,-9),(11,11),(20,149),(16,78),(19,130),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((1223 / 528): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 21 0 1 [(17,-75),(20,-20),(11,-158),(16,-91),(13,-134),(4,-210),(10,-168),(12,-146),(21,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((133 / 48): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((401 / 132): ℝ)
      · have hr:= hm
        apply H 6 0 1 [(10,32),(12,54),(17,126),(5,-5),(11,43),(13,67),(6,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((401 / 132): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 21 0 1 [(10,-169),(12,-147),(17,-75),(14,-121),(0,-219),(5,-206),(11,-158),(13,-134),(18,-57),(21,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux68 (b: ℝ) (hl: ((601 / 168): ℝ) ≤ b) (hr: b ≤ ((89 / 12): ℝ)) :
    x2611_12360_gap 29 (Set.range (fun k: Fin 22 => ((-((157 / 11): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (29: ℝ)))) ≤ ((731 / 132): ℝ):= by
  have H:= x2611_12360_table1_aux6 29 22 ((157 / 11)) b ((731 / 132)) (by norm_num)
  by_cases hm: b ≤ ((739 / 132): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((8291 / 1848): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((7451 / 1848): ℝ)
      · have hr:= hm
        apply H 15 0 1 [(1,-112),(6,-94),(12,-40),(14,-14),(19,68),(16,16),(11,-51),(13,-27),(18,50),(15,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((7451 / 1848): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 17 0 1 [(12,-72),(14,-46),(19,36),(16,-16),(2,-142),(7,-119),(13,-59),(15,-31),(20,56),(17,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((8291 / 1848): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((679 / 132): ℝ)
      · have hr:= hm
        apply H 18 0 1 [(11,-101),(7,-137),(5,-149),(0,-162),(3,-157),(8,-129),(14,-63),(16,-33),(21,59),(18,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((679 / 132): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 6 0 1 [(1,-18),(4,-10),(15,95),(17,127),(2,-16),(5,-5),(12,55),(16,111),(18,145),(6,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((739 / 132): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((859 / 132): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((799 / 132): ℝ)
      · have hr:= hm
        apply H 19 0 1 [(7,-156),(2,-179),(5,-168),(16,-52),(18,-18),(3,-176),(6,-162),(13,-95),(17,-35),(19,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((799 / 132): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 19 0 1 [(4,-173),(7,-156),(14,-82),(18,-18),(20,20),(8,-148),(3,-176),(6,-162),(17,-35),(19,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((859 / 132): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((919 / 132): ℝ)
      · have hr:= hm
        apply H 9 0 1 [(4,-33),(7,-16),(18,122),(20,160),(5,-28),(8,-8),(15,73),(19,141),(21,181),(9,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((919 / 132): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 16 0 1 [(7,-104),(10,-78),(5,-116),(8,-96),(19,53),(21,93),(6,-110),(9,-87),(16,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux69 (b: ℝ) (hl: ((89 / 12): ℝ) ≤ b) (hr: b ≤ ((1459 / 132): ℝ)) :
    x2611_12360_gap 29 (Set.range (fun k: Fin 22 => ((-((157 / 11): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (29: ℝ)))) ≤ ((731 / 132): ℝ):= by
  have H:= x2611_12360_table1_aux6 29 22 ((157 / 11)) b ((731 / 132)) (by norm_num)
  by_cases hm: b ≤ ((1219 / 132): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((1099 / 132): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((1039 / 132): ℝ)
      · have hr:= hm
        apply H 17 0 1 [(8,-113),(11,-84),(6,-127),(9,-104),(14,-46),(12,-72),(4,-137),(10,-94),(17,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((1039 / 132): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 10 0 1 [(15,63),(13,35),(5,-38),(11,11),(18,113),(9,-9),(12,23),(7,-25),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((1099 / 132): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((1159 / 132): ℝ)
      · have hr:= hm
        apply H 8 0 1 [(11,29),(16,97),(14,67),(6,-14),(12,41),(19,150),(10,19),(13,54),(8,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((1159 / 132): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 9 0 1 [(12,32),(17,105),(15,73),(7,-16),(13,45),(20,161),(11,21),(14,59),(9,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((1219 / 132): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((1339 / 132): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((1279 / 132): ℝ)
      · have hr:= hm
        apply H 10 0 1 [(13,35),(18,113),(16,79),(8,-18),(0,-52),(1,-51),(6,-32),(15,64),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((1279 / 132): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 2 0 1 [(7,24),(16,129),(11,61),(14,99),(19,182),(17,146),(0,-2),(1,-1),(2,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((1339 / 132): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((1399 / 132): ℝ)
      · have hr:= hm
        apply H 12 0 1 [(15,41),(20,129),(0,-75),(1,-74),(2,-72),(3,-69),(8,-40),(17,74),(12,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((1399 / 132): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 13 0 1 [(16,44),(21,137),(1,-87),(2,-85),(3,-82),(4,-78),(9,-44),(18,79),(13,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux70 (b: ℝ) (hl: ((1459 / 132): ℝ) ≤ b) (hr: b ≤ ((25043 / 1320): ℝ)) :
    x2611_12360_gap 29 (Set.range (fun k: Fin 22 => ((-((157 / 11): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (29: ℝ)))) ≤ ((731 / 132): ℝ):= by
  have H:= x2611_12360_table1_aux6 29 22 ((157 / 11)) b ((731 / 132)) (by norm_num)
  by_cases hm: b ≤ ((8159 / 528): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((6959 / 528): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((9467 / 792): ℝ)
      · have hr:= hm
        apply H 3 0 1 [(4,4),(5,9),(10,48),(6,15),(0,-5),(1,-4),(2,-2),(3,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((9467 / 792): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 7 0 1 [(12,49),(8,8),(1,-26),(2,-24),(3,-21),(4,-17),(5,-12),(6,-6),(7,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((6959 / 528): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((15107 / 1056): ℝ)
      · have hr:= hm
        apply H 2 0 1 [(4,7),(5,12),(6,18),(7,25),(8,33),(9,42),(14,101),(18,166),(10,52),(0,-2),(2,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((15107 / 1056): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 17 0 1 [(13,-61),(6,-130),(7,-123),(8,-115),(9,-106),(10,-96),(11,-85),(12,-73),(17,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((8159 / 528): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((829 / 48): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((8639 / 528): ℝ)
      · have hr:= hm
        apply H 14 0 1 [(19,84),(15,15),(7,-76),(9,-59),(10,-49),(11,-38),(12,-26),(13,-13),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((8639 / 528): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 16 0 1 [(21,94),(17,17),(9,-90),(11,-69),(12,-57),(13,-44),(14,-30),(15,-15),(16,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((829 / 48): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((23843 / 1320): ℝ)
      · have hr:= hm
        apply H 14 0 1 [(15,15),(16,31),(17,48),(18,66),(8,-68),(11,-38),(13,-13),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((23843 / 1320): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 18 0 1 [(19,19),(20,39),(10,-115),(12,-92),(14,-65),(15,-50),(16,-34),(17,-17),(18,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux71 (b: ℝ) (hl: ((25043 / 1320): ℝ) ≤ b) (hr: b ≤ ((13895 / 528): ℝ)) :
    x2611_12360_gap 29 (Set.range (fun k: Fin 22 => ((-((157 / 11): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (29: ℝ)))) ≤ ((731 / 132): ℝ):= by
  have H:= x2611_12360_table1_aux6 29 22 ((157 / 11)) b ((731 / 132)) (by norm_num)
  by_cases hm: b ≤ ((265 / 12): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((2675 / 132): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((25643 / 1320): ℝ)
      · have hr:= hm
        apply H 17 0 1 [(18,18),(19,37),(20,57),(21,78),(11,-86),(14,-47),(16,-16),(17,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((25643 / 1320): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 2 0 1 [(1,-2),(0,-3),(8,34),(15,118),(17,151),(18,169),(19,188),(20,208),(4,8),(3,4),(2,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((2675 / 132): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((2795 / 132): ℝ)
      · have hr:= hm
        apply H 10 0 1 [(17,98),(19,135),(20,155),(21,176),(7,-27),(6,-34),(5,-40),(4,-45),(3,-49),(2,-52),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((2795 / 132): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 9 0 1 [(8,-9),(7,-17),(6,-24),(5,-30),(4,-35),(12,34),(10,11),(9,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((265 / 12): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((12695 / 528): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((3035 / 132): ℝ)
      · have hr:= hm
        apply H 11 0 1 [(10,-11),(9,-21),(8,-30),(7,-38),(6,-45),(1,-66),(5,-51),(11,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((3035 / 132): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 10 0 1 [(9,-10),(4,-46),(0,-57),(8,-19),(16,82),(14,51),(13,37),(12,24),(11,12),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((12695 / 528): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((3335 / 132): ℝ)
      · have hr:= hm
        apply H 14 0 1 [(13,-14),(12,-27),(11,-39),(6,-85),(10,-50),(17,49),(16,32),(15,16),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((3335 / 132): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 18 0 1 [(17,-18),(16,-35),(15,-51),(14,-66),(9,-127),(5,-158),(13,-80),(21,61),(19,20),(18,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux72 (b: ℝ) (hl: ((13895 / 528): ℝ) ≤ b) (hr: b ≤ (29: ℝ)) :
    x2611_12360_gap 29 (Set.range (fun k: Fin 22 => ((-((157 / 11): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (29: ℝ)))) ≤ ((731 / 132): ℝ):= by
  have H:= x2611_12360_table1_aux6 29 22 ((157 / 11)) b ((731 / 132)) (by norm_num)
  by_cases hm: b ≤ ((29459 / 1056): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((28979 / 1056): ℝ)
    · have hr:= hm
      apply H 20 0 1 [(19,-20),(18,-39),(17,-57),(16,-74),(11,-145),(15,-90),(7,-184),(10,-156),(14,-105),(20,1)]
      · norm_num
      · simp
      · norm_num [List.isChain_cons,List.isChain_nil]
        all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((28979 / 1056): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      apply H 17 0 1 [(1,-157),(3,-151),(16,-17),(8,-119),(11,-88),(0,-158),(2,-154),(10,-99),(18,19),(17,1)]
      · norm_num
      · simp
      · norm_num [List.isChain_cons,List.isChain_nil]
        all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((29459 / 1056): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((29939 / 1056): ℝ)
    · have hr:= hm
      apply H 1 0 1 [(3,6),(11,69),(19,195),(18,176),(2,3),(4,11),(17,158),(9,48),(12,82),(1,1)]
      · norm_num
      · simp
      · norm_num [List.isChain_cons,List.isChain_nil]
        all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((29939 / 1056): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((30419 / 1056): ℝ)
      · have hr:= hm
        apply H 19 0 1 [(3,-189),(5,-179),(18,-19),(10,-137),(13,-100),(2,-192),(4,-184),(12,-113),(20,21),(19,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((30419 / 1056): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 1 0 1 [(3,6),(5,16),(13,95),(21,237),(4,11),(6,23),(19,196),(1,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux73: x2611_12360_G 29 22 ((157 / 11): ℝ) ≤ ((731 / 132): ℝ):= by
  apply x2611_12360_table1_aux4 29 22 ((157 / 11)) ((731 / 132)) (by norm_num)
  intro b hl hr
  norm_num at hr
  by_cases hm: b ≤ ((1459 / 132): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((601 / 168): ℝ)
    · have hr:= hm
      exact x2611_12360_table1_aux67 b (by linarith only[hl]) (by linarith only[hr])
    · have hl: ((601 / 168): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((89 / 12): ℝ)
      · have hr:= hm
        exact x2611_12360_table1_aux68 b (by linarith only[hl]) (by linarith only[hr])
      · have hl: ((89 / 12): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        exact x2611_12360_table1_aux69 b (by linarith only[hl]) (by linarith only[hr])
  · have hl: ((1459 / 132): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((25043 / 1320): ℝ)
    · have hr:= hm
      exact x2611_12360_table1_aux70 b (by linarith only[hl]) (by linarith only[hr])
    · have hl: ((25043 / 1320): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((13895 / 528): ℝ)
      · have hr:= hm
        exact x2611_12360_table1_aux71 b (by linarith only[hl]) (by linarith only[hr])
      · have hl: ((13895 / 528): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        exact x2611_12360_table1_aux72 b (by linarith only[hl]) (by linarith only[hr])
lemma x2611_12360_table1_aux74: x2611_12360_G 29 22 ((157 / 11): ℝ) = ((731 / 132): ℝ):= by
  apply x2611_12360_table1_aux5 29 22 ((157 / 11)) ((731 / 132)) ((676 / 33)) ((859 / 132))
  · norm_num
  · norm_num
  · norm_num
  · intro k
    fin_cases k
    · exact ⟨0,by norm_num⟩
    · exact ⟨1,by norm_num⟩
    · exact ⟨3,by norm_num⟩
    · exact ⟨6,by norm_num⟩
    · exact ⟨9,by norm_num⟩
    · exact ⟨14,by norm_num⟩
    · exact ⟨20,by norm_num⟩
    · exact ⟨26,by norm_num⟩
    · exact ⟨34,by norm_num⟩
    · exact ⟨42,by norm_num⟩
    · exact ⟨52,by norm_num⟩
    · exact ⟨63,by norm_num⟩
    · exact ⟨74,by norm_num⟩
    · exact ⟨87,by norm_num⟩
    · exact ⟨100,by norm_num⟩
    · exact ⟨115,by norm_num⟩
    · exact ⟨130,by norm_num⟩
    · exact ⟨147,by norm_num⟩
    · exact ⟨164,by norm_num⟩
    · exact ⟨182,by norm_num⟩
    · exact ⟨202,by norm_num⟩
    · exact ⟨222,by norm_num⟩
  · exact x2611_12360_table1_aux73
lemma x2611_12360_table1_aux75 (b: ℝ) (hl: (0: ℝ) ≤ b) (hr: b ≤ ((29 / 4): ℝ)) :
    x2611_12360_gap 33 (Set.range (fun k: Fin 22 => ((-((15 / 4): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (33: ℝ)))) ≤ ((15 / 2): ℝ):= by
  have H:= x2611_12360_table1_aux6 33 22 ((15 / 4)) b ((15 / 2)) (by norm_num)
  by_cases hm: b ≤ ((13 / 4): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((63 / 44): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((15 / 16): ℝ)
      · have hr:= hm
        apply H 11 0 1 [(15,12),(7,-8),(10,-2),(9,-4),(6,-9),(3,-12),(4,-11),(11,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((15 / 16): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 4 0 1 [(7,4),(16,28),(17,32),(6,3),(11,13),(15,25),(4,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((63 / 44): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((9 / 4): ℝ)
      · have hr:= hm
        apply H 21 0 1 [(19,-9),(4,-49),(10,-39),(8,-43),(2,-50),(6,-46),(11,-36),(21,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((9 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 17 0 1 [(20,13),(7,-28),(8,-26),(15,-7),(11,-19),(19,9),(16,-3),(17,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((13 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((21 / 4): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((17 / 4): ℝ)
      · have hr:= hm
        apply H 8 0 1 [(11,7),(14,16),(13,13),(10,5),(7,-1),(8,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((17 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 2 0 1 [(5,3),(8,8),(14,24),(12,18),(6,5),(10,13),(2,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((21 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((25 / 4): ℝ)
      · have hr:= hm
        apply H 2 0 1 [(5,3),(11,15),(12,18),(19,44),(15,28),(6,5),(0,0),(2,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((25 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 12 0 1 [(15,10),(18,22),(17,18),(14,7),(11,-2),(12,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux76 (b: ℝ) (hl: ((29 / 4): ℝ) ≤ b) (hr: b ≤ ((111 / 8): ℝ)) :
    x2611_12360_gap 33 (Set.range (fun k: Fin 22 => ((-((15 / 4): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (33: ℝ)))) ≤ ((15 / 2): ℝ):= by
  have H:= x2611_12360_table1_aux6 33 22 ((15 / 4)) b ((15 / 2)) (by norm_num)
  by_cases hm: b ≤ ((43 / 4): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((393 / 44): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((135 / 16): ℝ)
      · have hr:= hm
        apply H 14 0 1 [(6,-20),(9,-14),(8,-16),(5,-21),(2,-24),(3,-23),(10,-11),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((135 / 16): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 3 0 1 [(6,4),(15,28),(16,32),(5,3),(10,13),(14,25),(3,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((393 / 44): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((39 / 4): ℝ)
      · have hr:= hm
        apply H 20 0 1 [(18,-9),(3,-49),(9,-39),(7,-43),(1,-50),(5,-46),(10,-36),(20,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((39 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 16 0 1 [(19,13),(6,-28),(7,-26),(14,-7),(10,-19),(18,9),(15,-3),(16,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((43 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((51 / 4): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((47 / 4): ℝ)
      · have hr:= hm
        apply H 7 0 1 [(10,7),(13,16),(12,13),(9,5),(6,-1),(7,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((47 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 5 0 1 [(9,8),(1,-4),(4,-1),(7,4),(13,20),(11,14),(5,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((51 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((207 / 16): ℝ)
      · have hr:= hm
        apply H 10 0 1 [(11,3),(18,29),(9,-2),(1,-14),(4,-11),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((207 / 16): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 18 0 1 [(14,-16),(9,-31),(17,-4),(20,10),(8,-33),(10,-28),(11,-25),(18,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux77 (b: ℝ) (hl: ((111 / 8): ℝ) ≤ b) (hr: b ≤ ((85 / 4): ℝ)) :
    x2611_12360_gap 33 (Set.range (fun k: Fin 22 => ((-((15 / 4): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (33: ℝ)))) ≤ ((15 / 2): ℝ):= by
  have H:= x2611_12360_table1_aux6 33 22 ((15 / 4)) b ((15 / 2)) (by norm_num)
  by_cases hm: b ≤ ((69 / 4): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((255 / 16): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((59 / 4): ℝ)
      · have hr:= hm
        apply H 14 0 1 [(17,12),(16,8),(13,-3),(10,-12),(11,-9),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((59 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 13 0 1 [(5,-20),(8,-14),(7,-16),(4,-21),(1,-24),(2,-23),(9,-11),(13,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((255 / 16): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((723 / 44): ℝ)
      · have hr:= hm
        apply H 5 0 1 [(14,24),(15,28),(4,-1),(9,9),(13,21),(2,-3),(5,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((723 / 44): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 0 0 1 [(4,4),(9,14),(19,51),(17,42),(2,2),(8,12),(6,8),(0,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((69 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((77 / 4): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((73 / 4): ℝ)
      · have hr:= hm
        apply H 5 0 1 [(6,2),(13,21),(9,9),(17,37),(14,25),(15,29),(18,42),(5,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((73 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 9 0 1 [(12,9),(11,6),(8,-2),(5,-8),(6,-6),(9,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((77 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((81 / 4): ℝ)
      · have hr:= hm
        apply H 4 0 1 [(8,8),(0,-4),(3,-1),(6,4),(12,20),(10,14),(4,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((81 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 19 0 1 [(5,-47),(9,-38),(10,-35),(17,-9),(13,-25),(21,11),(18,-4),(19,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux78 (b: ℝ) (hl: ((85 / 4): ℝ) ≤ b) (hr: b ≤ ((111 / 4): ℝ)) :
    x2611_12360_gap 33 (Set.range (fun k: Fin 22 => ((-((15 / 4): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (33: ℝ)))) ≤ ((15 / 2): ℝ):= by
  have H:= x2611_12360_table1_aux6 33 22 ((15 / 4)) b ((15 / 2)) (by norm_num)
  by_cases hm: b ≤ ((101 / 4): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((375 / 16): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((89 / 4): ℝ)
      · have hr:= hm
        apply H 10 0 1 [(13,10),(16,22),(15,18),(12,7),(9,-2),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((89 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 12 0 1 [(4,-20),(7,-14),(6,-16),(3,-21),(0,-24),(1,-23),(8,-11),(12,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((375 / 16): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((195 / 8): ℝ)
      · have hr:= hm
        apply H 1 0 1 [(4,4),(13,28),(14,32),(21,65),(17,45),(8,13),(0,0),(1,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((195 / 8): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 14 0 1 [(17,13),(20,28),(19,23),(16,9),(13,-3),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((101 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((1185 / 44): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((423 / 16): ℝ)
      · have hr:= hm
        apply H 8 0 1 [(11,9),(10,6),(7,-2),(0,-13),(1,-12),(5,-6),(12,13),(16,29),(8,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((423 / 16): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 5 0 1 [(8,7),(17,40),(18,45),(7,5),(12,20),(16,36),(5,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((1185 / 44): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((441 / 16): ℝ)
      · have hr:= hm
        apply H 9 0 1 [(3,-13),(7,-5),(12,10),(4,-11),(5,-9),(11,7),(9,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((441 / 16): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 3 0 1 [(12,23),(20,59),(5,4),(18,49),(21,65),(3,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux79 (b: ℝ) (hl: ((111 / 4): ℝ) ≤ b) (hr: b ≤ (33: ℝ)) :
    x2611_12360_gap 33 (Set.range (fun k: Fin 22 => ((-((15 / 4): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (33: ℝ)))) ≤ ((15 / 2): ℝ):= by
  have H:= x2611_12360_table1_aux6 33 22 ((15 / 4)) b ((15 / 2)) (by norm_num)
  by_cases hm: b ≤ ((123 / 4): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((115 / 4): ℝ)
    · have hr:= hm
      apply H 18 0 1 [(21,16),(8,-38),(9,-35),(16,-9),(12,-25),(20,11),(17,-4),(18,1)]
      · norm_num
      · simp
      · norm_num [List.isChain_cons,List.isChain_nil]
        all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((115 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((119 / 4): ℝ)
      · have hr:= hm
        apply H 9 0 1 [(12,10),(15,22),(14,18),(11,7),(8,-2),(9,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((119 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 3 0 1 [(6,6),(9,14),(15,36),(13,28),(7,9),(11,21),(3,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((123 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((127 / 4): ℝ)
    · have hr:= hm
      apply H 3 0 1 [(6,6),(12,24),(13,28),(20,61),(16,41),(7,9),(1,-2),(3,1)]
      · norm_num
      · simp
      · norm_num [List.isChain_cons,List.isChain_nil]
        all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((127 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((131 / 4): ℝ)
      · have hr:= hm
        apply H 13 0 1 [(16,13),(19,28),(18,23),(15,9),(12,-3),(13,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((131 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 4 0 1 [(11,19),(15,35),(20,60),(8,10),(13,27),(19,55),(4,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux80: x2611_12360_G 33 22 ((15 / 4): ℝ) ≤ ((15 / 2): ℝ):= by
  apply x2611_12360_table1_aux4 33 22 ((15 / 4)) ((15 / 2)) (by norm_num)
  intro b hl hr
  norm_num at hr
  by_cases hm: b ≤ ((111 / 8): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((29 / 4): ℝ)
    · have hr:= hm
      exact x2611_12360_table1_aux75 b (by linarith only[hl]) (by linarith only[hr])
    · have hl: ((29 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      exact x2611_12360_table1_aux76 b (by linarith only[hl]) (by linarith only[hr])
  · have hl: ((111 / 8): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((85 / 4): ℝ)
    · have hr:= hm
      exact x2611_12360_table1_aux77 b (by linarith only[hl]) (by linarith only[hr])
    · have hl: ((85 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((111 / 4): ℝ)
      · have hr:= hm
        exact x2611_12360_table1_aux78 b (by linarith only[hl]) (by linarith only[hr])
      · have hl: ((111 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        exact x2611_12360_table1_aux79 b (by linarith only[hl]) (by linarith only[hr])
lemma x2611_12360_table1_aux81: x2611_12360_G 33 22 ((15 / 4): ℝ) = ((15 / 2): ℝ):= by
  apply x2611_12360_table1_aux5 33 22 ((15 / 4)) ((15 / 2)) (12) ((39 / 4))
  · norm_num
  · norm_num
  · norm_num
  · intro k
    fin_cases k
    · exact ⟨0,by norm_num⟩
    · exact ⟨1,by norm_num⟩
    · exact ⟨2,by norm_num⟩
    · exact ⟨2,by norm_num⟩
    · exact ⟨3,by norm_num⟩
    · exact ⟨5,by norm_num⟩
    · exact ⟨6,by norm_num⟩
    · exact ⟨8,by norm_num⟩
    · exact ⟨10,by norm_num⟩
    · exact ⟨12,by norm_num⟩
    · exact ⟨15,by norm_num⟩
    · exact ⟨17,by norm_num⟩
    · exact ⟨20,by norm_num⟩
    · exact ⟨24,by norm_num⟩
    · exact ⟨27,by norm_num⟩
    · exact ⟨30,by norm_num⟩
    · exact ⟨34,by norm_num⟩
    · exact ⟨38,by norm_num⟩
    · exact ⟨43,by norm_num⟩
    · exact ⟨47,by norm_num⟩
    · exact ⟨52,by norm_num⟩
    · exact ⟨57,by norm_num⟩
  · exact x2611_12360_table1_aux80
lemma x2611_12360_table1_aux82 (b: ℝ) (hl: (0: ℝ) ≤ b) (hr: b ≤ ((45 / 4): ℝ)) :
    x2611_12360_gap 33 (Set.range (fun k: Fin 22 => ((-((23 / 4): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (33: ℝ)))) ≤ (8: ℝ):= by
  have H:= x2611_12360_table1_aux6 33 22 ((23 / 4)) b (8) (by norm_num)
  by_cases hm: b ≤ ((23 / 4): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((11 / 4): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((5 / 4): ℝ)
      · have hr:= hm
        apply H 20 0 1 [(16,-25),(18,-13),(13,-40),(15,-30),(5,-65),(9,-55),(19,-6),(20,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((5 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 15 0 1 [(19,24),(20,31),(4,-37),(0,-40),(2,-39),(3,-38),(8,-28),(16,6),(17,12),(13,-9),(15,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((11 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((17 / 4): ℝ)
      · have hr:= hm
        apply H 17 0 1 [(21,27),(19,13),(13,-21),(14,-16),(10,-33),(12,-25),(16,-5),(17,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((17 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 17 0 1 [(19,13),(11,-30),(7,-43),(9,-37),(13,-21),(14,-16),(18,7),(21,28),(17,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((23 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((35 / 4): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((29 / 4): ℝ)
      · have hr:= hm
        apply H 14 0 1 [(16,11),(8,-24),(4,-33),(6,-29),(10,-17),(11,-13),(15,6),(18,24),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((29 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 8 0 1 [(12,15),(15,30),(11,11),(13,20),(5,-7),(1,-12),(3,-10),(7,-2),(8,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((35 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((39 / 4): ℝ)
      · have hr:= hm
        apply H 13 0 1 [(6,-25),(5,-27),(9,-16),(12,-4),(15,11),(19,36),(13,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((39 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 2 0 1 [(6,7),(4,3),(5,5),(7,10),(10,20),(3,2),(2,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux83 (b: ℝ) (hl: ((45 / 4): ℝ) ≤ b) (hr: b ≤ ((91 / 4): ℝ)) :
    x2611_12360_gap 33 (Set.range (fun k: Fin 22 => ((-((23 / 4): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (33: ℝ)))) ≤ (8: ℝ):= by
  have H:= x2611_12360_table1_aux6 33 22 ((23 / 4)) b (8) (by norm_num)
  by_cases hm: b ≤ ((69 / 4): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((57 / 4): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((51 / 4): ℝ)
      · have hr:= hm
        apply H 19 0 1 [(15,-25),(17,-13),(3,-67),(1,-69),(2,-68),(4,-65),(5,-63),(10,-48),(18,-6),(19,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((51 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 14 0 1 [(13,-5),(11,-14),(1,-39),(2,-38),(7,-28),(15,6),(16,12),(12,-9),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((57 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((63 / 4): ℝ)
      · have hr:= hm
        apply H 15 0 1 [(16,6),(20,33),(18,19),(19,26),(21,41),(13,-10),(9,-27),(11,-19),(15,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((63 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 13 0 1 [(17,23),(20,44),(16,17),(18,30),(10,-13),(6,-26),(8,-20),(12,-4),(13,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((69 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((81 / 4): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((75 / 4): ℝ)
      · have hr:= hm
        apply H 10 0 1 [(14,19),(17,37),(13,14),(15,25),(7,-10),(3,-19),(5,-15),(9,-3),(10,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((75 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 14 0 1 [(10,-19),(12,-10),(4,-37),(0,-42),(2,-40),(6,-32),(7,-29),(11,-14),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((81 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((85 / 4): ℝ)
      · have hr:= hm
        apply H 5 0 1 [(4,-2),(8,9),(11,21),(14,36),(18,61),(12,26),(5,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((85 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 5 0 1 [(3,-4),(4,-2),(6,3),(7,6),(12,26),(20,76),(21,84),(17,55),(19,69),(5,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux84 (b: ℝ) (hl: ((91 / 4): ℝ) ≤ b) (hr: b ≤ (33: ℝ)) :
    x2611_12360_gap 33 (Set.range (fun k: Fin 22 => ((-((23 / 4): ℝ) * (k.val: ℝ)^2 - b * k.val: ℝ): AddCircle (33: ℝ)))) ≤ (8: ℝ):= by
  have H:= x2611_12360_table1_aux6 33 22 ((23 / 4)) b (8) (by norm_num)
  by_cases hm: b ≤ ((115 / 4): ℝ)
  · have hr:= hm
    by_cases hm: b ≤ ((103 / 4): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((97 / 4): ℝ)
      · have hr:= hm
        apply H 16 0 1 [(20,28),(21,36),(5,-48),(1,-55),(3,-52),(4,-50),(9,-35),(17,7),(18,14),(14,-11),(16,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((97 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 13 0 1 [(12,-5),(10,-14),(0,-39),(1,-38),(6,-28),(14,6),(15,12),(11,-9),(13,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((103 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((109 / 4): ℝ)
      · have hr:= hm
        apply H 18 0 1 [(20,15),(12,-36),(8,-53),(10,-45),(14,-25),(15,-19),(19,8),(17,-6),(18,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((109 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 15 0 1 [(17,13),(9,-30),(5,-43),(7,-37),(11,-21),(12,-16),(16,7),(19,28),(15,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
  · have hl: ((115 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((125 / 4): ℝ)
    · have hr:= hm
      by_cases hm: b ≤ ((121 / 4): ℝ)
      · have hr:= hm
        apply H 9 0 1 [(13,19),(16,37),(12,14),(14,25),(6,-10),(2,-19),(4,-15),(8,-3),(9,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((121 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 14 0 1 [(7,-32),(6,-35),(10,-20),(13,-5),(16,13),(20,42),(14,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
    · have hl: ((125 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      by_cases hm: b ≤ ((131 / 4): ℝ)
      · have hr:= hm
        apply H 4 0 1 [(3,-2),(7,9),(5,3),(6,6),(8,13),(11,26),(4,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
      · have hl: ((131 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
        apply H 11 0 1 [(19,50),(20,58),(3,-27),(5,-22),(6,-19),(11,1)]
        · norm_num
        · simp
        · norm_num [List.isChain_cons,List.isChain_nil]
          all_goals (repeat' constructor)<;>first | linarith only[hl,hr] | simp
lemma x2611_12360_table1_aux85: x2611_12360_G 33 22 ((23 / 4): ℝ) ≤ (8: ℝ):= by
  apply x2611_12360_table1_aux4 33 22 ((23 / 4)) (8) (by norm_num)
  intro b hl hr
  norm_num at hr
  by_cases hm: b ≤ ((45 / 4): ℝ)
  · have hr:= hm
    exact x2611_12360_table1_aux82 b (by linarith only[hl]) (by linarith only[hr])
  · have hl: ((45 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
    by_cases hm: b ≤ ((91 / 4): ℝ)
    · have hr:= hm
      exact x2611_12360_table1_aux83 b (by linarith only[hl]) (by linarith only[hr])
    · have hl: ((91 / 4): ℝ) ≤ b:= le_of_lt (lt_of_not_ge hm)
      exact x2611_12360_table1_aux84 b (by linarith only[hl]) (by linarith only[hr])
lemma x2611_12360_table1_aux86: x2611_12360_G 33 22 ((23 / 4): ℝ) = (8: ℝ):= by
  apply x2611_12360_table1_aux5 33 22 ((23 / 4)) (8) (0) ((131 / 4))
  · norm_num
  · norm_num
  · norm_num
  · intro k
    fin_cases k
    · exact ⟨0,by norm_num⟩
    · exact ⟨2,by norm_num⟩
    · exact ⟨3,by norm_num⟩
    · exact ⟨5,by norm_num⟩
    · exact ⟨7,by norm_num⟩
    · exact ⟨10,by norm_num⟩
    · exact ⟨13,by norm_num⟩
    · exact ⟨16,by norm_num⟩
    · exact ⟨20,by norm_num⟩
    · exact ⟨24,by norm_num⟩
    · exact ⟨28,by norm_num⟩
    · exact ⟨32,by norm_num⟩
    · exact ⟨37,by norm_num⟩
    · exact ⟨43,by norm_num⟩
    · exact ⟨49,by norm_num⟩
    · exact ⟨55,by norm_num⟩
    · exact ⟨61,by norm_num⟩
    · exact ⟨68,by norm_num⟩
    · exact ⟨75,by norm_num⟩
    · exact ⟨82,by norm_num⟩
    · exact ⟨90,by norm_num⟩
    · exact ⟨98,by norm_num⟩
  · exact x2611_12360_table1_aux85
theorem x2611_12360_table1 :
  x2611_12360_G 17 22 (1: ℝ) = (4: ℝ) ∧
  x2611_12360_G 17 22 (2: ℝ) = (4: ℝ) ∧
  x2611_12360_G 17 22 ((1 / 2): ℝ) = (4: ℝ) ∧
  x2611_12360_G 17 22 ((2 / 3): ℝ) = ((133 / 39): ℝ) ∧
  x2611_12360_G 17 22 ((3 / 5): ℝ) = ((39 / 10): ℝ) ∧
  x2611_12360_G 29 22 (7: ℝ) = (6: ℝ) ∧
  x2611_12360_G 29 22 (14: ℝ) = ((17 / 3): ℝ) ∧
  x2611_12360_G 29 22 ((1 / 4): ℝ) = ((23 / 4): ℝ) ∧
  x2611_12360_G 29 22 ((157 / 11): ℝ) = ((731 / 132): ℝ) ∧
  x2611_12360_G 33 22 ((15 / 4): ℝ) = ((15 / 2): ℝ) ∧
  x2611_12360_G 33 22 ((23 / 4): ℝ) = (8: ℝ):= by
  exact ⟨x2611_12360_table1_aux11,x2611_12360_table1_aux19,x2611_12360_table1_aux25,x2611_12360_table1_aux35,x2611_12360_table1_aux42,x2611_12360_table1_aux49,x2611_12360_table1_aux58,x2611_12360_table1_aux66,x2611_12360_table1_aux74,x2611_12360_table1_aux81,x2611_12360_table1_aux86⟩
end

-- forge:entry x2611_11287_thm2_1 kind=proved origin=paper
section
/- Theorem 2.1 -/
open scoped BigOperators

lemma x2611_11287_thm2_1_aux1 (n H : ℕ)
    (S : Submodule ℤ (Matrix (Fin n) (Fin n) ℤ)) :
    Function.Injective (fun x : {A : Matrix (Fin n) (Fin n) ℤ //
        A ∈ S ∧ ∀ i j, |A i j| ≤ (H : ℤ)} =>
      ModN.mkQ (2 * H + 1) (⟨x.val, x.property.1⟩ : S)) := by
  intro x y h
  have hm : (⟨x.val, x.property.1⟩ : S) - ⟨y.val, y.property.1⟩ ∈
      LinearMap.range (LinearMap.lsmul ℤ S (2 * H + 1 : ℕ)) :=
    (Submodule.Quotient.eq _).mp h
  obtain ⟨z, hz⟩ := hm
  apply Subtype.ext
  ext i j
  have hd : (2 * H + 1 : ℤ) ∣ x.val i j - y.val i j := by
    refine ⟨z.val i j, ?_⟩
    have hh := congrArg (fun w : S => w.val i j) hz
    change ((2 * H + 1 : ℕ) : ℤ) * z.val i j = x.val i j - y.val i j at hh
    exact hh.symm
  have hb : |x.val i j - y.val i j| < (2 * H + 1 : ℤ) := by
    calc
      _ ≤ |x.val i j| + |y.val i j| := abs_sub _ _
      _ < (2 * H + 1 : ℤ) := by
        have hx := x.property.2 i j
        have hy := y.property.2 i j
        omega
  apply sub_eq_zero.mp
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd
  have hb' : |x.val i j - y.val i j| < |(2 * H + 1 : ℤ)| := by
    simpa only [abs_of_nonneg (by omega : (0 : ℤ) ≤ 2 * H + 1)] using hb
  simpa only [Int.abs_eq_natAbs, Nat.cast_lt] using hb'

lemma x2611_11287_thm2_1_aux2 (n H : ℕ)
    (S : Submodule ℤ (Matrix (Fin n) (Fin n) ℤ)) :
    {A : Matrix (Fin n) (Fin n) ℤ | A ∈ S ∧ ∀ i j, |A i j| ≤ (H : ℤ)}.Finite ∧
      x2611_11287_lattice_count S (H : ℤ) ≤ (2 * H + 1) ^ Module.finrank ℤ S := by
  letI : NeZero (2 * H + 1) := ⟨by omega⟩
  have hi := x2611_11287_thm2_1_aux1 n H S
  letI : Finite {A : Matrix (Fin n) (Fin n) ℤ //
    A ∈ S ∧ ∀ i j, |A i j| ≤ (H : ℤ)} := Finite.of_injective _ hi
  constructor
  · change Finite {A : Matrix (Fin n) (Fin n) ℤ //
      A ∈ S ∧ ∀ i j, |A i j| ≤ (H : ℤ)}
    infer_instance
  · change Nat.card {A : Matrix (Fin n) (Fin n) ℤ //
      A ∈ S ∧ ∀ i j, |A i j| ≤ (H : ℤ)} ≤ _
    simpa only [ModN.natCard_eq] using Nat.card_le_card_of_injective _ hi

lemma x2611_11287_thm2_1_aux3 (n k M L H : ℕ)
    (S : Submodule ℤ (Matrix (Fin n) (Fin n) ℤ)) (b : Module.Basis (Fin k) ℤ S)
    (hb : ∀ t i j, ((b t).val i j).natAbs ≤ M) (hH : k * L * M ≤ H) :
    (L + 1) ^ k ≤ x2611_11287_lattice_count S (H : ℤ) := by
  classical
  let f : (Fin k → Fin (L + 1)) → S :=
    fun v => b.equivFun.symm (fun t => ((v t).val : ℤ))
  have hf : ∀ v i j, |(f v).val i j| ≤ (H : ℤ) := by
    intro v i j
    have he : (f v).val i j = ∑ t, ((v t).val : ℤ) * (b t).val i j := by
      simp only [f, Module.Basis.equivFun_symm_apply, Submodule.coe_sum,
        Submodule.coe_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [he]
    calc
      _ ≤ ∑ t, |((v t).val : ℤ) * (b t).val i j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t : Fin k, (L : ℤ) * M := by
        apply Finset.sum_le_sum
        intro t ht
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (v t).val)]
        apply mul_le_mul
        · exact_mod_cast (show (v t).val ≤ L by omega)
        · simpa only [Int.natCast_natAbs] using
            (show (((b t).val i j).natAbs : ℤ) ≤ (M : ℤ) by exact_mod_cast hb t i j)
        · exact abs_nonneg _
        · positivity
      _ = (k * L * M : ℕ) := by simp; ring
      _ ≤ (H : ℤ) := by exact_mod_cast hH
  let g : (Fin k → Fin (L + 1)) → {A : Matrix (Fin n) (Fin n) ℤ //
      A ∈ S ∧ ∀ i j, |A i j| ≤ (H : ℤ)} :=
    fun v => ⟨(f v).val, (f v).property, hf v⟩
  have hg : Function.Injective g := by
    intro v w h
    have hv : (g v).val = (g w).val := congrArg (fun z => z.val) h
    change (f v).val = (f w).val at hv
    have he : f v = f w := Subtype.ext hv
    have hh := b.equivFun.symm.injective he
    funext t
    apply Fin.ext
    have ht := congrFun hh t
    exact_mod_cast ht
  letI : Finite {A : Matrix (Fin n) (Fin n) ℤ //
    A ∈ S ∧ ∀ i j, |A i j| ≤ (H : ℤ)} := (x2611_11287_thm2_1_aux2 n H S).1.to_subtype
  have hcard := Nat.card_le_card_of_injective g hg
  change (L + 1) ^ k ≤ Nat.card {A : Matrix (Fin n) (Fin n) ℤ //
    A ∈ S ∧ ∀ i j, |A i j| ≤ (H : ℤ)}
  simpa only [Nat.card_fun, Nat.card_fin] using hcard

lemma x2611_11287_thm2_1_aux4 (n k : ℕ)
    (S : Submodule ℤ (Matrix (Fin n) (Fin n) ℤ)) (b : Module.Basis (Fin k) ℤ S) :
    ∃ C : ℕ, 0 < C ∧ ∀ H : ℕ,
      (H / C + 1) ^ k ≤ x2611_11287_lattice_count S (H : ℤ) := by
  obtain ⟨M, hM⟩ := Finite.exists_le (fun p : Fin k × Fin n × Fin n =>
    ((b p.1).val p.2.1 p.2.2).natAbs)
  refine ⟨k * M + 1, by omega, fun H => ?_⟩
  apply x2611_11287_thm2_1_aux3 n k M (H / (k * M + 1)) H S b
  · intro t i j
    exact hM (t, i, j)
  · calc
      k * (H / (k * M + 1)) * M = (H / (k * M + 1)) * (k * M) := by ring
      _ ≤ (H / (k * M + 1)) * (k * M + 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ H := Nat.div_mul_le_self _ _

theorem x2611_11287_thm2_1 (n k : ℕ)
    (S : Submodule ℤ (Matrix (Fin n) (Fin n) ℤ))
    (hdim : Module.finrank ℤ S = k) :
    Asymptotics.IsTheta Filter.atTop
      (fun H : ℕ => (x2611_11287_lattice_count S (H : ℤ) : ℝ))
      (fun H : ℕ => (H : ℝ) ^ k) := by
  obtain ⟨C, hC, hlow⟩ := x2611_11287_thm2_1_aux4 n k S
    (Module.finBasisOfFinrankEq ℤ S hdim)
  constructor
  · apply Asymptotics.IsBigO.of_bound ((3 : ℝ) ^ k)
    filter_upwards [Filter.eventually_ge_atTop 1] with H hH
    simp only [norm_pow, Real.norm_natCast]
    have hu := (x2611_11287_thm2_1_aux2 n H S).2
    rw [hdim] at hu
    have hpow : (2 * H + 1) ^ k ≤ (3 * H) ^ k := Nat.pow_le_pow_left (by omega) k
    have hh := hu.trans hpow
    exact_mod_cast (show x2611_11287_lattice_count S (H : ℤ) ≤ 3 ^ k * H ^ k by
      simpa only [mul_pow] using hh)
  · apply Asymptotics.IsBigO.of_bound ((C : ℝ) ^ k)
    apply Filter.Eventually.of_forall
    intro H
    simp only [norm_pow, Real.norm_natCast]
    have hH : H ≤ C * (H / C + 1) := by
      have hm := Nat.mod_lt H hC
      have he := Nat.div_add_mod H C
      nlinarith
    have hp := Nat.pow_le_pow_left hH k
    rw [mul_pow] at hp
    exact_mod_cast hp.trans (Nat.mul_le_mul_left (C ^ k) (hlow H))
end

-- forge:entry x2611_10200_lem4_1 kind=proved origin=paper
section
/- Lemma 4.1 -/
lemma x2611_10200_lem4_1_aux1
    (f : ℤ → ℤ) (L : ℕ) (N c : ℤ)
    (hL : 3 ≤ L) (hN : 0 < N) (hc : 0 < N + c)
    (hinit : ∀ m : ℤ, m < (L : ℤ) → 0 ≤ f m)
    (hpos : ∀ m : ℤ, 0 ≤ m → m < (L : ℤ) - 1 → 0 < f m)
    (hzero : f 0 = 1) (hone : c < 0 → 3 ≤ f 1)
    (hrec : ∀ m : ℤ, (L : ℤ) ≤ m →
      f m = f (m - 1) + N * f (m - (L : ℤ)) + c) :
    (∀ m : ℤ, 0 ≤ f m) ∧ ∀ m : ℤ, (L : ℤ) ≤ m → 0 < f m := by
  have H : ∀ n : ℕ, 0 ≤ f (n : ℤ) ∧
      ((L : ℤ) ≤ (n : ℤ) → 0 < f (n : ℤ)) ∧
      (L + 1 ≤ n → n < 2 * L - 1 → c < 0 → -c < f (n : ℤ)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < L
      · exact ⟨hinit n (by omega), by omega, by omega⟩
      have hLn : (L : ℤ) ≤ (n : ℤ) := by omega
      have hp : ∀ m : ℤ, m < (n : ℤ) → 0 ≤ f m := by
        intro m hm
        by_cases hm0 : m < 0
        · exact hinit m (by omega)
        · simpa only [Int.toNat_of_nonneg (by omega : 0 ≤ m)] using
            (ih m.toNat (by omega)).1
      have hr := hrec (n : ℤ) hLn
      have ht : 0 < f (n : ℤ) ∧
          (L + 1 ≤ n → n < 2 * L - 1 → c < 0 → -c < f (n : ℤ)) := by
        by_cases he : n = L
        · subst n
          rw [sub_self, hzero, mul_one] at hr
          have hprev := hp ((L : ℤ) - 1) (by omega)
          exact ⟨by omega, by omega⟩
        have hprev : 0 < f ((n : ℤ) - 1) := by
          have hh := (ih (n - 1) (by omega)).2.1 (by omega)
          have heq : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
          simpa only [heq] using hh
        have hd0 := hp ((n : ℤ) - L) (by omega)
        have hmul0 : 0 ≤ N * f ((n : ℤ) - L) := mul_nonneg (by omega) hd0
        by_cases hcn : 0 ≤ c
        · exact ⟨by omega, by omega⟩
        have hcneg : c < 0 := by omega
        by_cases he1 : n = L + 1
        · have heq : (n : ℤ) - L = 1 := by omega
          rw [heq] at hr
          have hmul := mul_le_mul_of_nonneg_left (hone hcneg) (le_of_lt hN)
          constructor <;> intros <;> nlinarith
        by_cases he2 : n = 2 * L - 1
        · have hbound : -c < f ((n : ℤ) - 1) := by
            have hh := (ih (n - 1) (by omega)).2.2 (by omega) (by omega) hcneg
            have heq : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
            simpa only [heq] using hh
          exact ⟨by omega, by omega⟩
        have hdpos : 0 < f ((n : ℤ) - L) := by
          by_cases hd : (n : ℤ) - L < (L : ℤ)
          · exact hpos _ (by omega) (by omega)
          · have hh := (ih (n - L) (by omega)).2.1 (by omega)
            have heq : ((n - L : ℕ) : ℤ) = (n : ℤ) - L := by omega
            simpa only [heq] using hh
        have hmul : N ≤ N * f ((n : ℤ) - L) := by
          simpa using mul_le_mul_of_nonneg_left (by omega : 1 ≤ f ((n : ℤ) - L))
            (le_of_lt hN)
        refine ⟨by omega, ?_⟩
        intro hlow hupp _
        have hbound : -c < f ((n : ℤ) - 1) := by
          have hh := (ih (n - 1) (by omega)).2.2 (by omega) (by omega) hcneg
          have heq : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
          simpa only [heq] using hh
        omega
      exact ⟨le_of_lt ht.1, fun _ => ht.1, ht.2⟩
  constructor
  · intro m
    by_cases hm : m < 0
    · exact hinit m (by omega)
    · simpa only [Int.toNat_of_nonneg (by omega : 0 ≤ m)] using (H m.toNat).1
  · intro m hm
    have hm0 : 0 ≤ m := by omega
    simpa only [Int.toNat_of_nonneg hm0] using
      (H m.toNat).2.1 (by simpa only [Int.toNat_of_nonneg hm0] using hm)

theorem x2611_10200_lem4_1 (k N : ℕ) (hk : 1 ≤ k) (hN : 1 ≤ N)
    (hM : (N : ℝ) ≤ x2611_10200_M 1 k) :
    (∀ m : ℤ, 0 ≤ x2611_10200_f 1 k N m) ∧
      ∀ m : ℤ, ((k + 2 : ℕ) : ℤ) ≤ m → 0 < x2611_10200_f 1 k N m := by
  obtain ⟨har, hap⟩ := x2611_10200_coeff_recurrence_initial 1 (by omega)
  obtain ⟨hbelow, hmiddle⟩ := x2611_10200_lem3_1_s1h3 1 k N (by omega) hk hN
  obtain ⟨hanon, hapos⟩ := x2611_10200_lem3_1_aux2 (x2611_10200_a 1) 1 (by omega)
    (by intro m hm; simp [x2611_10200_a, hm]) har
  have hMb : (N : ℤ) * (2 : ℤ) ^ 1 ≤ x2611_10200_a 1 ((k + 1 : ℕ) : ℤ) + 1 := by
    unfold x2611_10200_M at hM
    have hh := (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ (1 : ℕ))).mp hM
    have hh' : (N : ℤ) * (2 : ℤ) ^ 1 ≤ x2611_10200_a 1 ((1 + k : ℕ) : ℤ) + 1 := by
      exact_mod_cast hh
    simpa only [Nat.add_comm 1 k] using hh'
  obtain ⟨hb, hstrict⟩ := x2611_10200_lem3_1_aux3 (x2611_10200_a 1) 1 k (N : ℤ)
    (by omega) hk hanon (hapos _ (by omega)) har hMb
  have ha0 : x2611_10200_a 1 0 = 1 := by simpa using hap 0 (by omega)
  have ha1 : x2611_10200_a 1 1 = 3 := by simpa using hap 1 (by omega)
  have hblock : ∀ m : ℤ, m < ((k + 2 : ℕ) : ℤ) → 0 ≤ x2611_10200_f 1 k N m := by
    intro m hm
    by_cases hm0 : m < 0
    · simp [x2611_10200_f, hm0]
    by_cases hmk : m < (k : ℤ)
    · rw [hbelow m (by omega) hmk]
      exact hanon m
    let r : ℕ := (m - (k : ℤ)).toNat
    have hr : r ≤ 1 := by dsimp [r]; omega
    have heq : m = ((k + r : ℕ) : ℤ) := by dsimp [r]; omega
    rw [heq, hmiddle r hr]
    have hh := hb r hr
    omega
  have hpos : ∀ m : ℤ, 0 ≤ m → m < ((k + 2 : ℕ) : ℤ) - 1 →
      0 < x2611_10200_f 1 k N m := by
    intro m hm hmk
    by_cases hmk' : m < (k : ℤ)
    · rw [hbelow m hm hmk']
      exact hapos m hm
    have heq : m = (k : ℤ) := by omega
    rw [heq]
    have hh := hmiddle 0 (by omega)
    simp only [Nat.add_zero, pow_zero, mul_one] at hh
    omega
  have hzero : x2611_10200_f 1 k N 0 = 1 := by
    rw [hbelow 0 (by omega) (by omega), ha0]
  have hone : (k : ℤ) + 2 - (N : ℤ) < 0 → 3 ≤ x2611_10200_f 1 k N 1 := by
    intro hc
    have hk2 : 2 ≤ k := by
      by_contra hn
      have hk1 : k = 1 := by omega
      subst k
      simp only [Nat.cast_one, ha1] at hstrict
      omega
    rw [hbelow 1 (by omega) (by omega), ha1]
  apply x2611_10200_lem4_1_aux1 (x2611_10200_f 1 k N) (k + 2)
    (N : ℤ) ((k : ℤ) + 2 - (N : ℤ)) (by omega) (by omega) (by omega)
    hblock hpos hzero hone
  intro m hm
  have hr := x2611_10200_gap_recurrence 1 k N (by omega) hk hN m (by omega)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr
end

-- forge:entry x2611_15210_cor4_4_s1h2 kind=proved origin=decomposition
section
/- x2611_15210_cor4_4 的证明骨架中第 2 个空洞 -/
open scoped BigOperators

theorem x2611_15210_cor4_4_s1h2_aux1 (m n : ℕ) (hm : 0 < m)
    (hn : n ≤ 2 * m) (h : m ∣ n) : n = 0 ∨ n = m ∨ n = 2 * m := by
  obtain ⟨k, rfl⟩ := h
  have hk : k ≤ 2 := by nlinarith
  interval_cases k <;> simp_all <;> omega

theorem x2611_15210_cor4_4_s1h2_aux2 (m : ℕ) (hm : 0 < m) (n : Fin 7 → ℕ)
    (hs : ∑ a, n a = 2 * m)
    (h0 : m ∣ n 5 + n 6) (h1 : m ∣ n 3 + n 4)
    (h2 : m ∣ n 1 + n 2 + n 4 + n 5 + n 6)
    (h3 : m ∣ n 1 + n 2 + n 3 + n 4 + n 6)
    (h4 : m ∣ n 2 + n 4) : ∀ a, m ∣ n a := by
  simp [Fin.sum_univ_succ] at hs
  have h0' := x2611_15210_cor4_4_s1h2_aux1 m _ hm (by omega) h0
  have h1' := x2611_15210_cor4_4_s1h2_aux1 m _ hm (by omega) h1
  have h2' := x2611_15210_cor4_4_s1h2_aux1 m _ hm (by omega) h2
  have h3' := x2611_15210_cor4_4_s1h2_aux1 m _ hm (by omega) h3
  have h4' := x2611_15210_cor4_4_s1h2_aux1 m _ hm (by omega) h4
  have ha0 : n 0 = 0 ∨ n 0 = m ∨ n 0 = 2 * m := by omega
  have ha1 : n 1 = 0 ∨ n 1 = m ∨ n 1 = 2 * m := by omega
  have ha2 : n 2 = 0 ∨ n 2 = m ∨ n 2 = 2 * m := by omega
  have ha3 : n 3 = 0 ∨ n 3 = m ∨ n 3 = 2 * m := by omega
  have ha4 : n 4 = 0 ∨ n 4 = m ∨ n 4 = 2 * m := by omega
  have ha5 : n 5 = 0 ∨ n 5 = m ∨ n 5 = 2 * m := by omega
  have ha6 : n 6 = 0 ∨ n 6 = m ∨ n 6 = 2 * m := by omega
  have ha : ∀ a, n a = 0 ∨ n a = m ∨ n a = 2 * m := by
    intro a
    fin_cases a <;> first
      | exact ha0
      | exact ha1
      | exact ha2
      | exact ha3
      | exact ha4
      | exact ha5
      | exact ha6
  intro a
  rcases ha a with h | h | h <;> rw [h] <;> simp

theorem x2611_15210_cor4_4_s1h2_aux3 {A B R : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] [AddCommMonoid R] (v : A → B) (p : B → R) :
    ∑ i, p (v i) = ∑ a, (Finset.univ.filter (fun i => v i = a)).card • p a := by
  classical
  symm
  calc
    _ = ∑ a, ∑ i ∈ Finset.univ.filter (fun i => v i = a), p (v i) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [Finset.sum_filter]
      rw [← Finset.sum_filter]
      rw [Finset.sum_congr rfl (fun i hi => congrArg p (Finset.mem_filter.mp hi).2)]
      simp
    _ = _ := by exact Finset.sum_fiberwise _ _ _

theorem x2611_15210_cor4_4_s1h2_aux4 (m : ℕ) (hm : 0 < m)
    (s : Finset (Fin (2 * m))) (hs : s.card = m) :
    (∃ i, i ∈ s) ∧ (∃ i, i ∉ s) := by
  constructor
  · exact Finset.card_pos.mp (by omega)
  · have hc : sᶜ.card = m := by simp [Finset.card_compl, hs]; omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < sᶜ.card by omega)
    exact ⟨i, by simpa using hi⟩

theorem x2611_15210_cor4_4_s1h2_aux5 (m k : ℕ) (hm : 0 < m) :
    Function.Injective
      (fun d : Fin k ⊕ ({q : Fin k × Fin k // q.1 < q.2} ×
        {s : Finset (Fin (2 * m)) // s.card = m}) =>
        Sum.elim (fun a _ => a) (fun q i => if i ∈ q.2.val then q.1.val.1 else q.1.val.2) d) := by
  classical
  intro x y h
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      have h0 := congrFun h ⟨0, by omega⟩
      exact congrArg Sum.inl h0
    | inr q =>
      obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := x2611_15210_cor4_4_s1h2_aux4 m hm q.2.val q.2.property
      have hia := congrFun h i
      have hjb := congrFun h j
      simp only [Sum.elim_inl, Sum.elim_inr, if_pos hi, if_neg hj] at hia hjb
      have := q.1.property
      simp_all
  | inr p =>
    cases y with
    | inl b =>
      obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := x2611_15210_cor4_4_s1h2_aux4 m hm p.2.val p.2.property
      have hia := congrFun h i
      have hjb := congrFun h j
      simp only [Sum.elim_inl, Sum.elim_inr, if_pos hi, if_neg hj] at hia hjb
      have := p.1.property
      simp_all
    | inr q =>
      obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := x2611_15210_cor4_4_s1h2_aux4 m hm p.2.val p.2.property
      obtain ⟨⟨u, hu⟩, ⟨w, hw⟩⟩ := x2611_15210_cor4_4_s1h2_aux4 m hm q.2.val q.2.property
      have hia := congrFun h i
      have hjb := congrFun h j
      have hua := congrFun h u
      have hwb := congrFun h w
      simp only [Sum.elim_inr, if_pos hi, if_neg hj, if_pos hu, if_neg hw] at hia hjb hua hwb
      have hp := p.1.property
      have hq := q.1.property
      have ha : p.1.val.1 = q.1.val.1 := by split_ifs at hia hjb hua hwb <;> omega
      have hb : p.1.val.2 = q.1.val.2 := by split_ifs at hia hjb hua hwb <;> omega
      have hs : p.2 = q.2 := by
        apply Subtype.ext
        ext z
        have hz := congrFun h z
        simp only [Sum.elim_inr, ha, hb] at hz
        by_cases hpz : z ∈ p.2.val <;> by_cases hqz : z ∈ q.2.val <;>
          simp only [hpz, hqz, if_true, if_false] at hz ⊢ <;> omega
      have hpq : p.1 = q.1 := Subtype.ext (Prod.ext ha hb)
      exact congrArg Sum.inr (Prod.ext hpq hs)

theorem x2611_15210_cor4_4_s1h2_aux6 (m k : ℕ) (hm : 0 < m)
    (v : Fin (2 * m) → Fin k)
    (hv : ∀ a, m ∣ (Finset.univ.filter (fun i => v i = a)).card) :
    ∃ d : Fin k ⊕ ({q : Fin k × Fin k // q.1 < q.2} ×
        {s : Finset (Fin (2 * m)) // s.card = m}),
      Sum.elim (fun a _ => a) (fun q i => if i ∈ q.2.val then q.1.val.1 else q.1.val.2) d = v := by
  classical
  by_cases hc : ∃ a, ∀ i, v i = a
  · obtain ⟨a, ha⟩ := hc
    exact ⟨Sum.inl a, funext (fun i => (ha i).symm)⟩
  have hn (a : Fin k) : (Finset.univ.filter (fun i => v i = a)).card ≠ 2 * m := by
    intro h
    have he := Finset.eq_univ_of_card (Finset.univ.filter (fun i => v i = a)) (by simpa using h)
    apply hc
    refine ⟨a, fun i => ?_⟩
    have : i ∈ Finset.univ.filter (fun i => v i = a) := by rw [he]; simp
    exact (Finset.mem_filter.mp this).2
  have hcount (i : Fin (2 * m)) : (Finset.univ.filter (fun j => v j = v i)).card = m := by
    have hp : 0 < (Finset.univ.filter (fun j => v j = v i)).card :=
      Finset.card_pos.mpr ⟨i, by simp⟩
    have hb : (Finset.univ.filter (fun j => v j = v i)).card ≤ 2 * m :=
      by simpa using (Finset.card_le_card (Finset.filter_subset (fun j => v j = v i) Finset.univ))
    rcases x2611_15210_cor4_4_s1h2_aux1 m _ hm hb (hv (v i)) with h | h | h
    · omega
    · exact h
    · exact False.elim (hn (v i) h)
  let i : Fin (2 * m) := ⟨0, by omega⟩
  let a := v i
  let s := Finset.univ.filter (fun j => v j = a)
  have hs : s.card = m := hcount i
  obtain ⟨_, j, hj⟩ := x2611_15210_cor4_4_s1h2_aux4 m hm s hs
  let b := v j
  have hab : a ≠ b := by
    intro h
    apply hj
    simp [s, b, h]
  let r := Finset.univ.filter (fun j => v j = b)
  have hr : r.card = m := hcount j
  have hd : Disjoint s r := by
    apply Finset.disjoint_left.mpr
    intro x hxs hxr
    exact hab ((Finset.mem_filter.mp hxs).2.symm.trans (Finset.mem_filter.mp hxr).2)
  have hu : s ∪ r = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hd, hs, hr]
    simp; omega
  have hvab : ∀ z, v z = a ∨ v z = b := by
    intro z
    have hz : z ∈ s ∪ r := by rw [hu]; simp
    simpa [s, r] using hz
  rcases lt_or_gt_of_ne hab with hab | hba
  · refine ⟨Sum.inr (⟨(a, b), hab⟩, ⟨s, hs⟩), ?_⟩
    funext z
    dsimp
    by_cases hz : z ∈ s
    · simpa [hz] using (Finset.mem_filter.mp hz).2.symm
    · simp only [hz, if_false]
      exact (hvab z).resolve_left (by simpa [s] using hz) |>.symm
  · refine ⟨Sum.inr (⟨(b, a), hba⟩, ⟨r, hr⟩), ?_⟩
    funext z
    dsimp
    by_cases hz : z ∈ r
    · simpa [hz] using (Finset.mem_filter.mp hz).2.symm
    · simp only [hz, if_false]
      exact (hvab z).resolve_right (by simpa [r] using hz) |>.symm

theorem x2611_15210_cor4_4_s1h2_aux7 (m k : ℕ) (hm : 0 < m)
    {G : Type*} [AddCommMonoid G] (hz : ∀ x : G, m • x = 0) (p : Fin k → G)
    (hc : ∀ v : Fin (2 * m) → Fin k, (∑ i, p (v i)) = 0 →
      ∀ a, m ∣ (Finset.univ.filter (fun i => v i = a)).card) :
    Nat.card {v : Fin (2 * m) → Fin k // ∑ i, p (v i) = 0} =
      k + k.choose 2 * (2 * m).choose m := by
  classical
  let D := Fin k ⊕ ({q : Fin k × Fin k // q.1 < q.2} ×
        {s : Finset (Fin (2 * m)) // s.card = m})
  let e : D → (Fin (2 * m) → Fin k) :=
    fun d => Sum.elim (fun a _ => a)
      (fun q i => if i ∈ q.2.val then q.1.val.1 else q.1.val.2) d
  have he (d : D) : ∑ i, p (e d i) = 0 := by
    cases d with
    | inl a => simp [e, mul_smul, hz]
    | inr q =>
      have hcomp : q.2.valᶜ.card = m := by
        simp [Finset.card_compl, q.2.property]; omega
      simp only [e, Sum.elim_inr, apply_ite p]
      rw [Finset.sum_ite]
      have hh : Finset.univ.filter (fun i => i ∈ q.2.val) = q.2.val := by ext; simp
      have hh' : Finset.univ.filter (fun i => i ∉ q.2.val) = q.2.valᶜ := by ext; simp
      rw [hh, hh']
      simp [q.2.property, hcomp, hz]
  let f : D → {v : Fin (2 * m) → Fin k // ∑ i, p (v i) = 0} := fun d => ⟨e d, he d⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact x2611_15210_cor4_4_s1h2_aux5 m k hm (congrArg Subtype.val h)
    · intro v
      obtain ⟨d, hd⟩ := x2611_15210_cor4_4_s1h2_aux6 m k hm v.val (hc v.val v.property)
      exact ⟨d, Subtype.ext hd⟩
  rw [← Nat.card_eq_of_bijective f hf]
  dsimp [D]
  simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin, Fintype.card_prod,
    Fintype.card_finset_len]
  congr 2
  rw [Fintype.card_subtype]
  simpa using (Fintype.card_product_filter_lt (α := Fin k))

theorem x2611_15210_cor4_4_s1h2_aux8 (m : ℕ) (hm : 0 < m) :
    ∃ p : Fin 7 → Fin 5 → ZMod m,
      (∀ a j, p a j = 0 ∨ p a j = 1) ∧
      Nat.card {v : Fin (2 * m) → Fin 7 // ∑ i, p (v i) = 0} =
        7 + 21 * (2 * m).choose m := by
  classical
  let b : Fin 7 → Fin 5 → ℕ :=
    ![![0,0,0,0,0], ![0,0,1,1,0], ![0,0,1,1,1],
      ![0,1,0,1,0], ![0,1,1,1,1], ![1,0,1,0,0], ![1,0,1,1,0]]
  let p : Fin 7 → Fin 5 → ZMod m := fun a j => b a j
  refine ⟨p, ?_, ?_⟩
  · intro a j
    fin_cases a <;> fin_cases j <;> norm_num [p, b]
  · have hz : ∀ x : Fin 5 → ZMod m, m • x = 0 := by
      intro x
      ext j
      simp [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self]
    have hcard := x2611_15210_cor4_4_s1h2_aux7 m 7 hm hz p ?_
    · simpa only [show Nat.choose 7 2 = 21 by decide] using hcard
    intro v hv
    let n : Fin 7 → ℕ := fun a => (Finset.univ.filter (fun i => v i = a)).card
    have hs : ∑ a, n a = 2 * m := by
      simpa [n] using Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset (Fin (2 * m))) (Finset.univ : Finset (Fin 7)) v
    rw [x2611_15210_cor4_4_s1h2_aux3 v p] at hv
    have hd : ∀ j, m ∣ ∑ a, n a * b a j := by
      intro j
      rw [← ZMod.natCast_eq_zero_iff]
      simpa [p, n, Nat.cast_sum, Nat.cast_mul, Finset.sum_apply, Pi.smul_apply,
        nsmul_eq_mul] using congrFun hv j
    apply x2611_15210_cor4_4_s1h2_aux2 m hm n hs
    · simpa [b, Fin.sum_univ_succ] using hd 0
    · simpa [b, Fin.sum_univ_succ] using hd 1
    · simpa [b, Fin.sum_univ_succ, add_assoc] using hd 2
    · simpa [b, Fin.sum_univ_succ, add_assoc] using hd 3
    · simpa [b, Fin.sum_univ_succ] using hd 4

theorem x2611_15210_cor4_4_s1h2 : ∀ (m : ℕ), 2 ≤ m → ∀ (t : ℕ),
    ∃ (p : (Fin t → Fin 7) → Fin (5 * t) → ZMod m),
      (∀ (a : Fin t → Fin 7) (j : Fin (5 * t)), p a j = 0 ∨ p a j = 1) ∧
      Nat.card {v : Fin (2 * m) → Fin t → Fin 7 // ∑ i : Fin (2 * m), p (v i) = 0} =
        (7 + 21 * (2 * m).choose m) ^ t := by
  intro m hm t
  classical
  obtain ⟨b, hb, hc⟩ := x2611_15210_cor4_4_s1h2_aux8 m (by omega)
  let e : Fin (5 * t) ≃ Fin 5 × Fin t := finProdFinEquiv.symm
  let p : (Fin t → Fin 7) → Fin (5 * t) → ZMod m := fun a j => b (a (e j).2) (e j).1
  refine ⟨p, fun a j => hb _ _, ?_⟩
  let E : {v : Fin (2 * m) → Fin t → Fin 7 // ∑ i, p (v i) = 0} ≃
      (Fin t → {v : Fin (2 * m) → Fin 7 // ∑ i, b (v i) = 0}) :=
    { toFun := fun v j => ⟨fun i => v.val i j, by
        ext k
        have h := congrFun v.property (e.symm (k, j))
        simpa [p, Finset.sum_apply] using h⟩
      invFun := fun w => ⟨fun i j => (w j).val i, by
        ext u
        have h := congrFun (w (e u).2).property (e u).1
        simpa [p, Finset.sum_apply] using h⟩
      left_inv := fun v => by apply Subtype.ext; rfl
      right_inv := fun w => by funext j; apply Subtype.ext; rfl }
  rw [Nat.card_congr E, Nat.card_fun, hc]
  simp
end

-- forge:entry x2611_10200_two_unit_formulas kind=proved origin=paper
section
/- Section 6, two leading units and Equation (6.1) -/
lemma x2611_10200_two_unit_formulas_aux1 (m : ℕ) :
    x2611_10200_a 2 (m : ℤ) = (Nat.fib (m + 5) : ℤ) - (m : ℤ) - 4 := by
  have hr := x2611_10200_coeff_recurrence_initial 2 (by omega)
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m ≤ 2
    · have ha := hr.2 m hm
      interval_cases m <;> norm_num [Nat.fib] at ha ⊢ <;> exact ha
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 3 := ⟨m - 3, by omega⟩
      have h := hr.1 ((n + 3 : ℕ) : ℤ) (by omega)
      have h0 := ih n (by omega)
      have h2 := ih (n + 2) (by omega)
      have hidx1 : ((n + 3 : ℕ) : ℤ) - 1 = ((n + 2 : ℕ) : ℤ) := by omega
      have hidx2 : ((n + 3 : ℕ) : ℤ) - (2 : ℤ) - 1 = (n : ℤ) := by omega
      norm_num only at h
      rw [hidx1, hidx2, h0, h2] at h
      have hf1 : (Nat.fib (n + 8) : ℤ) =
          (Nat.fib (n + 6) : ℤ) + (Nat.fib (n + 7) : ℤ) := by
        exact_mod_cast (Nat.fib_add_two (n := n + 6))
      have hf2 : (Nat.fib (n + 7) : ℤ) =
          (Nat.fib (n + 5) : ℤ) + (Nat.fib (n + 6) : ℤ) := by
        exact_mod_cast (Nat.fib_add_two (n := n + 5))
      simp only [Nat.add_assoc, Nat.cast_add, Nat.cast_ofNat] at h ⊢
      linarith

theorem x2611_10200_two_unit_formulas (k : ℕ) (hk : 1 ≤ k) :
    (∀ m : ℕ, x2611_10200_a 2 (m : ℤ) =
      (Nat.fib (m + 5) : ℤ) - (m : ℤ) - 4) ∧
    Int.floor (x2611_10200_M 2 k) =
      Int.floor (((Nat.fib (k + 7) : ℝ) - (k : ℝ) - 5) / 4) := by
  refine ⟨x2611_10200_two_unit_formulas_aux1, ?_⟩
  congr 1
  rw [x2611_10200_M, x2611_10200_two_unit_formulas_aux1]
  push_cast
  congr 1 <;> ring
end

-- forge:entry x2611_10200_lem2_1 kind=proved origin=paper
section
/- Lemma 2.1 (Initial block) -/
open scoped BigOperators

lemma x2611_10200_lem2_1_aux1 (g k N : ℕ) (hg : 1 ≤ g) (hk : 1 ≤ k)
    (hN : 1 ≤ N) (H : ℕ → ℤ) (hH : x2611_10200_standard g k N H) :
    (∀ n : ℕ, 1 ≤ n → 1 ≤ H n) ∧ Monotone (fun n : ℕ => H (n + 1)) := by
  have hp : ∀ n : ℕ, 1 ≤ n → 1 ≤ H n ∧ (2 ≤ n → H (n - 1) ≤ H n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hn1 : n = 1
      · subst n
        exact ⟨by rw [hH.1], by omega⟩
      have hn2 : 2 ≤ n := by omega
      have hprev : 1 ≤ H (n - 1) := (ih (n - 1) (by omega) (by omega)).1
      by_cases hnl : n ≤ g + k + 1
      · have hr := hH.2.1 n hn2 hnl
        have hs : H (n - 1) ≤
            (Finset.Icc 1 (min g (n - 1))).sum (fun j => H (n - j)) := by
          apply Finset.single_le_sum (f := fun j => H (n - j)) (a := 1)
          · intro j hj
            have hj' := Finset.mem_Icc.mp hj
            exact le_trans (by norm_num : (0 : ℤ) ≤ 1)
              (ih (n - j) (by omega) (by omega)).1
          · simp only [Finset.mem_Icc, le_min_iff]
            omega
        exact ⟨by omega, by omega⟩
      · have hr := hH.2.2 n (by omega)
        have hs : H (n - 1) ≤ (Finset.Icc 1 g).sum (fun j => H (n - j)) := by
          apply Finset.single_le_sum (f := fun j => H (n - j)) (a := 1)
          · intro j hj
            have hj' := Finset.mem_Icc.mp hj
            exact le_trans (by norm_num : (0 : ℤ) ≤ 1)
              (ih (n - j) (by omega) (by omega)).1
          · simp only [Finset.mem_Icc]
            omega
        have ht : 0 ≤ (N : ℤ) * H (n - (g + k + 1)) := by
          have hh := (ih (n - (g + k + 1)) (by omega) (by omega)).1
          positivity
        exact ⟨by omega, by omega⟩
  refine ⟨fun n hn => (hp n hn).1, ?_⟩
  apply monotone_nat_of_le_succ
  intro n
  simpa using (hp (n + 2) (by omega)).2 (by omega)

lemma x2611_10200_lem2_1_aux2 (H : ℕ → ℤ)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 ≤ H n)
    (hmono : Monotone (fun n : ℕ => H (n + 1)))
    (hc : x2611_10200_complete H) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ x2611_10200_B H n := by
  classical
  have hs : 0 ≤ (Finset.Icc 1 (n - 1)).sum H := by
    apply Finset.sum_nonneg
    intro i hi
    exact hpos i (Finset.mem_Icc.mp hi).1
  obtain ⟨S, hS, he⟩ := hc (1 + (Finset.Icc 1 (n - 1)).sum H) (by omega)
  by_contra hb
  have hlt : 1 + (Finset.Icc 1 (n - 1)).sum H < H n := by
    unfold x2611_10200_B at hb
    omega
  have hsub : S ⊆ Finset.Icc 1 (n - 1) := by
    intro i hi
    have hi1 := hS i hi
    have hin : i < n := by
      by_contra hni
      have hmon := hmono (show n - 1 ≤ i - 1 by omega)
      have hni' : H n ≤ H i := by
        simpa only [Nat.sub_add_cancel hn, Nat.sub_add_cancel hi1] using hmon
      have hsum : H i ≤ S.sum H := Finset.single_le_sum (fun j hj => hpos j (hS j hj)) hi
      omega
    exact Finset.mem_Icc.mpr ⟨hi1, by omega⟩
  have hsum : S.sum H ≤ (Finset.Icc 1 (n - 1)).sum H := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro i hi _
    exact hpos i (Finset.mem_Icc.mp hi).1
  omega

theorem x2611_10200_lem2_1 (g k N : ℕ) (hg : 1 ≤ g) (hk : 1 ≤ k) (hN : 1 ≤ N) :
    (∀ m : ℤ, 0 ≤ m → m < (k : ℤ) → x2611_10200_f g k N m = x2611_10200_a g m) ∧
    (∀ r : ℕ, r ≤ g → x2611_10200_f g k N ((k + r : ℕ) : ℤ) =
      x2611_10200_a g ((k + r : ℕ) : ℤ) + 1 - (N : ℤ) * 2 ^ r) ∧
    ((N : ℝ) ≤ x2611_10200_M g k → ∀ m : ℤ, m < ((g + k + 1 : ℕ) : ℤ) →
      0 ≤ x2611_10200_f g k N m) ∧
    (∀ H : ℕ → ℤ, x2611_10200_standard g k N H → x2611_10200_complete H →
      (N : ℝ) ≤ x2611_10200_M g k) := by
  obtain ⟨hbelow, hmiddle⟩ := x2611_10200_lem3_1_s1h3 g k N hg hk hN
  refine ⟨hbelow, hmiddle, ?_, ?_⟩
  · intro hM
    obtain ⟨har, _⟩ := x2611_10200_coeff_recurrence_initial g hg
    obtain ⟨hanon, hapos⟩ := x2611_10200_lem3_1_aux2 (x2611_10200_a g) g hg
      (by intro m hm; simp [x2611_10200_a, hm]) har
    have hMb : (N : ℤ) * (2 : ℤ) ^ g ≤ x2611_10200_a g ((k + g : ℕ) : ℤ) + 1 := by
      unfold x2611_10200_M at hM
      have hh := (le_div_iff₀ (show 0 < (2 : ℝ) ^ g by positivity)).mp hM
      have hh' : (N : ℤ) * (2 : ℤ) ^ g ≤ x2611_10200_a g ((g + k : ℕ) : ℤ) + 1 := by
        exact_mod_cast hh
      simpa only [Nat.add_comm g k] using hh'
    obtain ⟨hb, _⟩ := x2611_10200_lem3_1_aux3 (x2611_10200_a g) g k (N : ℤ)
      hg hk hanon (hapos _ (by omega)) har hMb
    intro m hm
    by_cases hm0 : m < 0
    · simp [x2611_10200_f, hm0]
    by_cases hmk : m < (k : ℤ)
    · rw [hbelow m (by omega) hmk]
      exact hanon m
    let r : ℕ := (m - (k : ℤ)).toNat
    have hr : r ≤ g := by dsimp [r]; omega
    have heq : m = ((k + r : ℕ) : ℤ) := by dsimp [r]; omega
    rw [heq, hmiddle r hr]
    have hh := hb r hr
    omega
  · intro H hH hc
    obtain ⟨hpos, hmono⟩ := x2611_10200_lem2_1_aux1 g k N hg hk hN H hH
    have hb := x2611_10200_lem2_1_aux2 H
      (fun n hn => le_trans (by norm_num) (hpos n hn)) hmono hc (k + g + g + 2) (by omega)
    have hgap := (x2611_10200_brown_gap_coefficients g k N hg hk hN H hH).2 (k + g)
    rw [hgap, hmiddle g le_rfl] at hb
    unfold x2611_10200_M
    apply (le_div_iff₀ (show 0 < (2 : ℝ) ^ g by positivity)).mpr
    have hi : (N : ℤ) * 2 ^ g ≤ x2611_10200_a g ((g + k : ℕ) : ℤ) + 1 := by
      simpa only [Nat.add_comm g k] using (show (N : ℤ) * 2 ^ g ≤
        x2611_10200_a g ((k + g : ℕ) : ℤ) + 1 by omega)
    exact_mod_cast hi
end

-- forge:entry x2611_15210_cor4_4 kind=proved origin=paper
section
/- Corollary 4.4 -/

open Filter
open scoped Topology


lemma x2611_15210_cor4_4_aux1 (L : ℕ) (hL : 0 < L)
    (G : Type*) [AddCommMonoid G] [Fintype G] (hz : ∀ g : G, L • g = 0) :
    Set.Nonempty {s : ℕ | ∀ a : Fin s → G,
      ∃ I : Finset (Fin s), I.card = L ∧ ∑ i ∈ I, a i = 0} := by
  classical
  refine ⟨Fintype.card G * (L - 1) + 1, ?_⟩
  intro a
  obtain ⟨g, -, hg⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (f := a) (n := L - 1)
    (by simp) (by simp)
  obtain ⟨I, hI, hcard⟩ := Finset.exists_subset_card_eq (by omega :
    L ≤ (Finset.univ.filter (fun i => a i = g)).card)
  refine ⟨I, hcard, ?_⟩
  calc
    ∑ i ∈ I, a i = ∑ _i ∈ I, g := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (Finset.mem_filter.mp (hI hi)).2
    _ = L • g := by simp [hcard]
    _ = 0 := hz g

lemma x2611_15210_cor4_4_aux2 (L : ℕ) (hL : 0 < L)
    (G : Type*) [AddCommMonoid G] [Fintype G] (hz : ∀ g : G, L • g = 0)
    (N : ℕ) (a : Fin N → G)
    (ha : ∀ I : Finset (Fin N), I.card = L → ∑ i ∈ I, a i ≠ 0) :
    N ≤ x2611_15210_A L G := by
  classical
  have hs : ∀ b : Fin (x2611_15210_s L G) → G,
      ∃ I : Finset (Fin (x2611_15210_s L G)), I.card = L ∧ ∑ i ∈ I, b i = 0 :=
    Nat.sInf_mem (x2611_15210_cor4_4_aux1 L hL G hz)
  have hlt : N < x2611_15210_s L G := by
    by_contra h
    have hn : x2611_15210_s L G ≤ N := by omega
    let e : Fin (x2611_15210_s L G) ↪ Fin N :=
      ⟨Fin.castLE hn, Fin.castLE_injective hn⟩
    obtain ⟨I, hI, hsum⟩ := hs (a ∘ e)
    apply ha (I.map e) (by simpa using hI)
    simpa only [Finset.sum_map, Function.comp_apply] using hsum
  unfold x2611_15210_A
  omega

lemma x2611_15210_cor4_4_aux3 (m r : ℕ) (hm : 0 < m) (B : ℝ)
    (h : x2611_15210_binary_witness m r (2 * m) B) :
    B ≤ (x2611_15210_A (2 * m) (Fin r → ZMod m) : ℝ) := by
  letI : NeZero m := ⟨by omega⟩
  obtain ⟨N, a, hN, -, ha⟩ := h
  have hbound := x2611_15210_cor4_4_aux2 (2 * m) (by omega)
    (Fin r → ZMod m) (by
      intro g
      ext j
      simp [nsmul_eq_mul, Nat.cast_mul]) N a ha
  exact hN.trans (by exact_mod_cast hbound)

lemma x2611_15210_cor4_4_aux4 (m r L : ℕ) (hL : 0 < L) (B : ℝ)
    (hB : B ≤ ((L - 1 : ℕ) : ℝ)) : x2611_15210_binary_witness m r L B := by
  refine ⟨L - 1, fun _ _ => 0, hB, by simp, ?_⟩
  intro I hI
  have hcard := Finset.card_le_univ I
  simp only [Fintype.card_fin] at hcard
  omega

lemma x2611_15210_cor4_4_aux5 :
    Tendsto (fun m : ℕ => Real.log (m.centralBinom : ℝ) / (m : ℝ))
      atTop (nhds (Real.log 4)) := by
  have hlog : Tendsto (fun m : ℕ => Real.log (2 * (m : ℝ)) / (m : ℝ))
      atTop (nhds 0) := by
    have ht := (Real.tendsto_pow_log_div_mul_add_atTop (1 / 2) 0 1
      (by norm_num)).comp
      ((tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop).const_mul_atTop
        (by norm_num : (0 : ℝ) < 2))
    simpa [Function.comp_def, ← mul_assoc] using ht
  have hlower : Tendsto
      (fun m : ℕ => Real.log 4 - Real.log (2 * (m : ℝ)) / (m : ℝ))
      atTop (nhds (Real.log 4)) := by
    simpa using tendsto_const_nhds.sub hlog
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    have hcb : 0 < (m.centralBinom : ℝ) := by exact_mod_cast m.centralBinom_pos
    have hb : (4 : ℝ) ^ m ≤ 2 * (m : ℝ) * (m.centralBinom : ℝ) := by
      exact_mod_cast Nat.four_pow_le_two_mul_self_mul_centralBinom m (by omega)
    have hh := Real.log_le_log (by positivity : 0 < (4 : ℝ) ^ m) hb
    rw [Real.log_pow, Real.log_mul (by positivity) (ne_of_gt hcb)] at hh
    apply (le_div_iff₀ hm0).mpr
    have hmne := ne_of_gt hm0
    field_simp
    nlinarith
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    have hcb : 0 < (m.centralBinom : ℝ) := by exact_mod_cast m.centralBinom_pos
    have hb : (m.centralBinom : ℝ) ≤ (4 : ℝ) ^ m := by
      exact_mod_cast Nat.centralBinom_le_four_pow m
    have hh := Real.log_le_log hcb hb
    rw [Real.log_pow] at hh
    exact (div_le_iff₀ hm0).mpr (by nlinarith)

lemma x2611_15210_cor4_4_aux6 :
    Tendsto (fun m : ℕ => Real.log (7 + 21 * (m.centralBinom : ℝ)) / (m : ℝ))
      atTop (nhds (Real.log 4)) := by
  have hinv : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hsmall (c : ℝ) : Tendsto (fun m : ℕ => c / (m : ℝ)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hinv
  have hlow := (hsmall (Real.log 21)).add x2611_15210_cor4_4_aux5
  have hupp := (hsmall (Real.log 28)).add x2611_15210_cor4_4_aux5
  simp only [zero_add] at hlow hupp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    have hcb : 0 < (m.centralBinom : ℝ) := by exact_mod_cast m.centralBinom_pos
    have hh := Real.log_le_log (by positivity : 0 < 21 * (m.centralBinom : ℝ))
      (by linarith : 21 * (m.centralBinom : ℝ) ≤ 7 + 21 * (m.centralBinom : ℝ))
    rw [Real.log_mul (by norm_num) (ne_of_gt hcb)] at hh
    simpa only [add_div] using (div_le_div_of_nonneg_right hh hm0.le)
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    have hcb : 1 ≤ (m.centralBinom : ℝ) := by
      exact_mod_cast m.centralBinom_pos
    have hh := Real.log_le_log (by positivity : 0 < 7 + 21 * (m.centralBinom : ℝ))
      (by linarith : 7 + 21 * (m.centralBinom : ℝ) ≤ 28 * (m.centralBinom : ℝ))
    rw [Real.log_mul (by norm_num) (by linarith)] at hh
    simpa only [add_div] using (div_le_div_of_nonneg_right hh hm0.le)

lemma x2611_15210_cor4_4_aux7 :
    Tendsto x2611_15210_rho_prime atTop (nhds ((7 / 2 : ℝ) ^ ((1 : ℝ) / 5))) := by
  have hinv : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun m : ℕ =>
      (2 * Real.log 7 - Real.log (7 + 21 * (m.centralBinom : ℝ)) / (m : ℝ)) /
        (5 * (2 - (m : ℝ)⁻¹))) atTop (nhds ((2 * Real.log 7 - Real.log 4) / 10)) := by
    convert ((tendsto_const_nhds (x := 2 * Real.log 7)).sub
      x2611_15210_cor4_4_aux6).div
      ((tendsto_const_nhds (x := (5 : ℝ))).mul
        ((tendsto_const_nhds (x := (2 : ℝ))).sub hinv)) (by norm_num) using 1
    · funext m
      rfl
    · norm_num
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp ht
  have hlim : Real.exp ((2 * Real.log 7 - Real.log 4) / 10) =
      (7 / 2 : ℝ) ^ ((1 : ℝ) / 5) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    rw [Real.log_div (by norm_num) (by norm_num)]
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.cast_ofNat] using
        Real.log_pow (2 : ℝ) 2
    rw [h4]
    ring
  rw [hlim] at hexp
  apply hexp.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hd : 0 < 7 + 21 * (m.centralBinom : ℝ) := by positivity
  have hbase : 0 < (7 : ℝ) ^ (2 * m) / (7 + 21 * (m.centralBinom : ℝ)) := by positivity
  simp only [Function.comp_apply]
  unfold x2611_15210_rho_prime
  rw [← Nat.centralBinom_eq_two_mul_choose, Real.rpow_def_of_pos hbase,
    Real.log_div (by positivity) (ne_of_gt hd), Real.log_pow]
  congr 1
  push_cast
  field_simp [ne_of_gt hm0]
  <;> ring

lemma x2611_15210_cor4_4_aux8 (m r s L : ℕ) (hrs : r ≤ s) (B : ℝ)
    (h : x2611_15210_binary_witness m r L B) :
    x2611_15210_binary_witness m s L B := by
  classical
  obtain ⟨N, a, hN, hb, ha⟩ := h
  let a' : Fin N → Fin s → ZMod m := fun i j =>
    if h : j.val < r then a i ⟨j.val, h⟩ else 0
  refine ⟨N, a', hN, ?_, ?_⟩
  · intro i j
    dsimp [a']
    split_ifs with h
    · exact hb i ⟨j.val, h⟩
    · exact Or.inl rfl
  · intro I hI hz
    apply ha I hI
    ext j
    have hj := congrFun hz ⟨j.val, lt_of_lt_of_le j.isLt hrs⟩
    simpa [a', Finset.sum_apply, j.isLt] using hj

lemma x2611_15210_cor4_4_aux9 (m r L : ℕ) (B C : ℝ) (hBC : B ≤ C)
    (h : x2611_15210_binary_witness m r L C) :
    x2611_15210_binary_witness m r L B := by
  obtain ⟨N, a, hN, hb, ha⟩ := h
  exact ⟨N, a, hBC.trans hN, hb, ha⟩

lemma x2611_15210_cor4_4_aux10 (m : ℕ) (hm : 1 ≤ m) :
    0 ≤ x2611_15210_rho_prime m ∧ x2611_15210_rho_prime m ≤ (3 / 2 : ℝ) := by
  have hmcast : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hden : 0 < 5 * (2 * (m : ℝ) - 1) := by linarith
  have hcast : ((2 * m - 1 : ℕ) : ℝ) = 2 * (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hbase : (7 : ℝ) ^ (2 * m) / (7 + 21 * ((2 * m).choose m : ℝ)) ≤
      (7 : ℝ) ^ (2 * m - 1) := by
    apply (div_le_iff₀ (by positivity)).mpr
    rw [show (7 : ℝ) ^ (2 * m) = 7 ^ (2 * m - 1) * 7 by
      rw [← pow_succ]
      congr 1
      omega]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 7) (2 * m - 1),
      show (0 : ℝ) ≤ ((2 * m).choose m : ℝ) by positivity]
  have hroot : ((7 : ℝ) ^ (2 * m - 1)) ^ (1 / (5 * (2 * (m : ℝ) - 1))) =
      (7 : ℝ) ^ ((1 : ℝ) / 5) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), hcast]
    congr 1
    field_simp [show 2 * (m : ℝ) - 1 ≠ 0 by linarith]
    <;> ring
  have hupper : x2611_15210_rho_prime m ≤ (7 : ℝ) ^ ((1 : ℝ) / 5) := by
    unfold x2611_15210_rho_prime
    exact (Real.rpow_le_rpow (by positivity) hbase (by positivity)).trans_eq hroot
  have hseven : ((7 : ℝ) ^ ((1 : ℝ) / 5)) ^ 5 = 7 := by
    simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (x := (7 : ℝ))
      (n := 5) (by norm_num) (by decide)
  refine ⟨Real.rpow_nonneg (by positivity) _, hupper.trans ?_⟩
  apply le_of_pow_le_pow_left₀ (n := 5) (by decide) (by norm_num)
  rw [hseven]
  norm_num

lemma x2611_15210_cor4_4_aux11 (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ (3 / 2 : ℝ))
    (u : ℕ) (hu : u ≤ 4) : x ^ u ≤ 6 := by
  apply (pow_le_pow_left₀ hx hx' u).trans
  interval_cases u <;> norm_num

lemma x2611_15210_cor4_4_aux12 (x a : ℝ) (hx : 0 < x) (ha : a ≠ 0) (t : ℕ) :
    ((x⁻¹) ^ t) ^ (-(1 : ℝ) / a) =
      (x ^ ((1 : ℝ) / (5 * a))) ^ (5 * t) := by
  rw [Real.rpow_def_of_pos (pow_pos (inv_pos.mpr hx) t), Real.log_pow, Real.log_inv,
    ← Real.rpow_natCast, ← Real.rpow_mul hx.le, Real.rpow_def_of_pos hx]
  congr 1
  push_cast
  field_simp
  <;> ring

lemma x2611_15210_cor4_4_aux13 (m : ℕ) (hm : 2 ≤ m)
    (hblock : ∀ t : ℕ, x2611_15210_binary_witness m (5 * t) (2 * m)
      (((m : ℝ) / (2 * Real.exp 1)) * x2611_15210_rho_prime m ^ (5 * t))) :
    ∀ r : ℕ, x2611_15210_binary_witness m r (2 * m)
      (((m : ℝ) / (12 * Real.exp 1)) * x2611_15210_rho_prime m ^ r) := by
  intro r
  obtain ⟨hρ0, hρ⟩ := x2611_15210_cor4_4_aux10 m (by omega)
  have hu : r % 5 ≤ 4 := by omega
  have hpow := x2611_15210_cor4_4_aux11 _ hρ0 hρ (r % 5) hu
  have hr : r = 5 * (r / 5) + r % 5 := by omega
  have hB : ((m : ℝ) / (12 * Real.exp 1)) * x2611_15210_rho_prime m ^ r ≤
      ((m : ℝ) / (2 * Real.exp 1)) * x2611_15210_rho_prime m ^ (5 * (r / 5)) := by
    calc
      _ = (((m : ℝ) / (12 * Real.exp 1)) * x2611_15210_rho_prime m ^ (r % 5)) *
          x2611_15210_rho_prime m ^ (5 * (r / 5)) := by
        conv_lhs => rw [hr, pow_add]
        ring
      _ ≤ (((m : ℝ) / (12 * Real.exp 1)) * 6) *
          x2611_15210_rho_prime m ^ (5 * (r / 5)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity))
          (pow_nonneg hρ0 _)
      _ = _ := by field_simp; ring
  exact x2611_15210_cor4_4_aux9 m r (2 * m) _ _ hB
    (x2611_15210_cor4_4_aux8 m (5 * (r / 5)) r (2 * m) (by omega) _ (hblock (r / 5)))


theorem x2611_15210_cor4_4 (m : ℕ) (hm : 2 ≤ m) :
    (∀ r : ℕ,
      ((m : ℝ) / (12 * Real.exp 1)) * x2611_15210_rho_prime m ^ r ≤
          (x2611_15210_A (2 * m) (Fin r → ZMod m) : ℝ) ∧
        x2611_15210_binary_witness m r (2 * m)
          (((m : ℝ) / (12 * Real.exp 1)) * x2611_15210_rho_prime m ^ r)) ∧
      Filter.Tendsto x2611_15210_rho_prime Filter.atTop
        (nhds ((7 / 2 : ℝ) ^ ((1 : ℝ) / 5))) := by
  have alteration := x2611_15210_cor4_4_s1h1
  have count := x2611_15210_cor4_4_s1h2
  have hblock : ∀ t : ℕ, x2611_15210_binary_witness m (5 * t) (2 * m)
      (((m : ℝ) / (2 * Real.exp 1)) * x2611_15210_rho_prime m ^ (5 * t)) := by
    intro t
    obtain ⟨p, hp, hcount⟩ := count m hm t
    let x : ℝ := (7 : ℝ) ^ (2 * m) / (7 + 21 * ((2 * m).choose m : ℝ))
    have hx : 0 < x := by dsimp [x]; positivity
    have hθ : (x⁻¹) ^ t =
        (Nat.card {v : Fin (2 * m) → (Fin t → Fin 7) //
          (∑ i : Fin (2 * m), p (v i)) = 0} : ℝ) /
            (Nat.card (Fin t → Fin 7) : ℝ) ^ (2 * m) := by
      rw [hcount]
      simp only [Nat.card_fun, Nat.card_fin, Nat.cast_pow, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat]
      dsimp [x]
      rw [inv_div, div_pow]
      congr 1
      rw [← pow_mul, ← pow_mul, Nat.mul_comm t (2 * m)]
    obtain ⟨N, a, hN, ha⟩ := alteration (2 * m) (by omega)
      (Fin t → Fin 7) (Fin (5 * t) → ZMod m) p ((x⁻¹) ^ t) (by positivity) hθ
    have hrpow : ((x⁻¹) ^ t) ^ (-(1 : ℝ) / ((2 * m : ℕ) - 1 : ℝ)) =
        x2611_15210_rho_prime m ^ (5 * t) := by
      have hmcast : 2 ≤ (m : ℝ) := by exact_mod_cast hm
      convert x2611_15210_cor4_4_aux12 x (2 * (m : ℝ) - 1) hx (by linarith) t using 1 <;>
        simp only [Nat.cast_mul, Nat.cast_ofNat, x2611_15210_rho_prime, x]
    rw [hrpow] at hN
    have hc : ((2 * m : ℕ) : ℝ) / (4 * Real.exp 1) = (m : ℝ) / (2 * Real.exp 1) := by
      push_cast
      field_simp
      <;> ring
    rw [hc] at hN
    exact ⟨N, fun i => p (a i), hN, fun i j => hp (a i) j, ha⟩
  have hw := x2611_15210_cor4_4_aux13 m hm hblock
  refine ⟨?_, x2611_15210_cor4_4_aux7⟩
  intro r
  exact ⟨x2611_15210_cor4_4_aux3 m r (by omega) _ (hw r), hw r⟩
end

-- forge:entry x2611_15210_rem4_3 kind=proved origin=paper
section
/- Remark 4.3 (exact comparisons and nonmonotonicity) -/
open Filter

lemma x2611_15210_rem4_3_aux1 :
    Tendsto (fun m : ℕ => Real.log (m.centralBinom : ℝ) / (m : ℝ))
      atTop (nhds (Real.log 4)) := by
  have hlog : Tendsto (fun m : ℕ => Real.log (2 * (m : ℝ)) / (m : ℝ))
      atTop (nhds 0) := by
    have ht := (Real.tendsto_pow_log_div_mul_add_atTop (1 / 2) 0 1
      (by norm_num)).comp
      ((tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop).const_mul_atTop
        (by norm_num : (0 : ℝ) < 2))
    simpa [Function.comp_def, ← mul_assoc] using ht
  have hlower : Tendsto
      (fun m : ℕ => Real.log 4 - Real.log (2 * (m : ℝ)) / (m : ℝ))
      atTop (nhds (Real.log 4)) := by
    simpa using tendsto_const_nhds.sub hlog
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    have hcb : 0 < (m.centralBinom : ℝ) := by exact_mod_cast m.centralBinom_pos
    have hb : (4 : ℝ) ^ m ≤ 2 * (m : ℝ) * (m.centralBinom : ℝ) := by
      exact_mod_cast Nat.four_pow_le_two_mul_self_mul_centralBinom m (by omega)
    have hh := Real.log_le_log (by positivity : 0 < (4 : ℝ) ^ m) hb
    rw [Real.log_pow, Real.log_mul (by positivity) (ne_of_gt hcb)] at hh
    apply (le_div_iff₀ hm0).mpr
    have hmne := ne_of_gt hm0
    field_simp
    nlinarith
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    have hcb : 0 < (m.centralBinom : ℝ) := by exact_mod_cast m.centralBinom_pos
    have hb : (m.centralBinom : ℝ) ≤ (4 : ℝ) ^ m := by
      exact_mod_cast Nat.centralBinom_le_four_pow m
    have hh := Real.log_le_log hcb hb
    rw [Real.log_pow] at hh
    exact (div_le_iff₀ hm0).mpr (by nlinarith)

lemma x2611_15210_rem4_3_aux2 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    Tendsto (fun m : ℕ => Real.log (a + b * (m.centralBinom : ℝ)) / (m : ℝ))
      atTop (nhds (Real.log 4)) := by
  have hinv : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hsmall (c : ℝ) : Tendsto (fun m : ℕ => c / (m : ℝ)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hinv
  have hlow := (hsmall (Real.log b)).add x2611_15210_rem4_3_aux1
  have hupp := (hsmall (Real.log (a + b))).add x2611_15210_rem4_3_aux1
  simp only [zero_add] at hlow hupp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    have hcb : 0 < (m.centralBinom : ℝ) := by exact_mod_cast m.centralBinom_pos
    have hh := Real.log_le_log (by positivity : 0 < b * (m.centralBinom : ℝ))
      (by linarith : b * (m.centralBinom : ℝ) ≤ a + b * (m.centralBinom : ℝ))
    rw [Real.log_mul (ne_of_gt hb) (ne_of_gt hcb)] at hh
    simpa only [add_div] using (div_le_div_of_nonneg_right hh hm0.le)
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    have hcb : 1 ≤ (m.centralBinom : ℝ) := by exact_mod_cast m.centralBinom_pos
    have hh := Real.log_le_log (by positivity : 0 < a + b * (m.centralBinom : ℝ))
      (by nlinarith : a + b * (m.centralBinom : ℝ) ≤ (a + b) * (m.centralBinom : ℝ))
    rw [Real.log_mul (by positivity) (by linarith)] at hh
    simpa only [add_div] using (div_le_div_of_nonneg_right hh hm0.le)

lemma x2611_15210_rem4_3_aux3 :
    Tendsto x2611_15210_rho atTop (nhds ((9 / 2 : ℝ) ^ ((1 : ℝ) / 5))) := by
  have hinv : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun m : ℕ =>
      (2 * Real.log 9 - Real.log (9 + 36 * (m.centralBinom : ℝ)) / (m : ℝ)) /
        (5 * (2 - (m : ℝ)⁻¹))) atTop (nhds ((2 * Real.log 9 - Real.log 4) / 10)) := by
    convert ((tendsto_const_nhds (x := 2 * Real.log 9)).sub
      (x2611_15210_rem4_3_aux2 9 36 (by norm_num) (by norm_num))).div
      ((tendsto_const_nhds (x := (5 : ℝ))).mul
        ((tendsto_const_nhds (x := (2 : ℝ))).sub hinv)) (by norm_num) using 1
    · funext m
      rfl
    · norm_num
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp ht
  have hlim : Real.exp ((2 * Real.log 9 - Real.log 4) / 10) =
      (9 / 2 : ℝ) ^ ((1 : ℝ) / 5) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    rw [Real.log_div (by norm_num) (by norm_num)]
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.cast_ofNat] using
        Real.log_pow (2 : ℝ) 2
    rw [h4]
    ring
  rw [hlim] at hexp
  apply hexp.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hd : 0 < 9 + 36 * (m.centralBinom : ℝ) := by positivity
  have hbase : 0 < (9 : ℝ) ^ (2 * m) / (9 + 36 * (m.centralBinom : ℝ)) := by positivity
  simp only [Function.comp_apply]
  unfold x2611_15210_rho
  rw [← Nat.centralBinom_eq_two_mul_choose, Real.rpow_def_of_pos hbase,
    Real.log_div (by positivity) (ne_of_gt hd), Real.log_pow]
  congr 1
  push_cast
  field_simp [ne_of_gt hm0]
  <;> ring

theorem x2611_15210_rem4_3 :
    x2611_15210_rho 3 < ((9 / 2 : ℝ) ^ ((1 : ℝ) / 5)) ∧
    ((9 / 2 : ℝ) ^ ((1 : ℝ) / 5)) < x2611_15210_rho 21 ∧
    (¬ Monotone (fun k : ℕ => x2611_15210_rho (2 * k + 3))) ∧
    (¬ Antitone (fun k : ℕ => x2611_15210_rho (2 * k + 3))) ∧
    Tendsto (fun k : ℕ => x2611_15210_rho (2 * k + 1)) atTop
      (nhds ((9 / 2 : ℝ) ^ ((1 : ℝ) / 5))) := by
  have h3 : x2611_15210_rho 3 < (9 / 2 : ℝ) ^ ((1 : ℝ) / 5) := by
    have he : (9 / 2 : ℝ) ^ ((1 : ℝ) / 5) =
        ((9 / 2 : ℝ) ^ (5 : ℕ)) ^ ((1 : ℝ) / 25) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [he]
    norm_num [x2611_15210_rho, Nat.choose]
    exact Real.rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
  have h21 : (9 / 2 : ℝ) ^ ((1 : ℝ) / 5) < x2611_15210_rho 21 := by
    have hc : (42 : ℕ).choose 21 = 538257874440 := by
      rw [Nat.choose_eq_factorial_div_factorial (by norm_num)]
      norm_num [Nat.factorial]
    have he : (9 / 2 : ℝ) ^ ((1 : ℝ) / 5) =
        ((9 / 2 : ℝ) ^ (41 : ℕ)) ^ ((1 : ℝ) / 205) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [he]
    norm_num [x2611_15210_rho, hc]
    exact Real.rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
  have hseq : Tendsto (fun k : ℕ => x2611_15210_rho (2 * k + 3)) atTop
      (nhds ((9 / 2 : ℝ) ^ ((1 : ℝ) / 5))) := by
    apply x2611_15210_rem4_3_aux3.comp
    exact tendsto_atTop_mono (fun k => by omega : ∀ k : ℕ, k ≤ 2 * k + 3) tendsto_id
  refine ⟨h3, h21, ?_, ?_, ?_⟩
  · intro hm
    have hh := hm.ge_of_tendsto hseq 9
    norm_num at hh
    exact (not_le_of_gt h21) hh
  · intro ha
    have hh := ha.le_of_tendsto hseq 0
    norm_num at hh
    exact (not_le_of_gt h3) hh
  · apply x2611_15210_rem4_3_aux3.comp
    exact tendsto_atTop_mono (fun k => by omega : ∀ k : ℕ, k ≤ 2 * k + 1) tendsto_id
end

-- forge:entry x2611_14160_remark3_4 kind=proved origin=paper
section
/- Remark 3.4 (Odd prime moduli) -/
open Finset

lemma x2611_14160_remark3_4_aux1 {A B W R : Type*} [Fintype A] [Fintype B]
    [AddCommMonoid R] (w : Sym2 W → R) (f : A ⊕ B ↪ W) :
    x2611_14160_copyWeight (completeBipartiteGraph A B) w f =
      ∑ a : A, ∑ b : B, w (Sym2.mk (f (.inl a)) (f (.inr b))) := by
  classical
  have he : (completeBipartiteGraph A B).edgeFinset =
      (univ : Finset (A × B)).image (fun x => Sym2.mk (.inl x.1) (.inr x.2)) := by
    ext e
    simp [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_completeBipartiteGraph,
      Set.mem_range, Finset.mem_image]
  rw [x2611_14160_copyWeight, he, Finset.sum_image]
  · simp [Fintype.sum_prod_type, Sym2.map_mk]
  · intro x _ y _ h
    have hh : x.1 = y.1 ∧ x.2 = y.2 := by simpa using h
    exact Prod.ext hh.1 hh.2

lemma x2611_14160_remark3_4_aux2 (p : ℕ) (hp : 0 < p) :
    ∃ N, x2611_14160_zeroSumForces (completeBipartiteGraph (Fin p) (Fin p)) p N := by
  classical
  letI : NeZero p := ⟨Nat.ne_of_gt hp⟩
  let K := p ^ p * p
  refine ⟨p + K, ?_⟩
  intro w
  let e : Fin p ⊕ Fin K ≃ Fin (p + K) := finSumFinEquiv
  let q : Fin K → (Fin p → ZMod p) := fun j i => w (Sym2.mk (e (.inl i)) (e (.inr j)))
  have hc : Fintype.card (Fin p → ZMod p) * p ≤ Fintype.card (Fin K) := by
    simp [K, Fintype.card_fun, ZMod.card p]
  obtain ⟨c, hc⟩ := Fintype.exists_le_card_fiber_of_mul_le_card q hc
  have hf : Fintype.card (Fin p) ≤ Fintype.card {j : Fin K // q j = c} := by
    simpa [Fintype.card_subtype] using hc
  let b : Fin p ↪ {j : Fin K // q j = c} := Classical.choice (Function.Embedding.nonempty_of_card_le hf)
  let b' : Fin p ↪ Fin K := b.trans (Function.Embedding.subtype _)
  let f : Fin p ⊕ Fin p ↪ Fin (p + K) :=
    (Function.Embedding.sumMap (Function.Embedding.refl _) b').trans e.toEmbedding
  refine ⟨f, ?_⟩
  rw [x2611_14160_remark3_4_aux1]
  have hw (i j : Fin p) : w (Sym2.mk (f (.inl i)) (f (.inr j))) = c i := by
    exact congrFun (b j).property i
  simp_rw [hw]
  simp [nsmul_eq_mul, ZMod.natCast_self]

lemma x2611_14160_remark3_4_aux3 {V : Type*} [Fintype V]
    (G : SimpleGraph V) (m : ℕ) {N M : ℕ} (hNM : N ≤ M)
    (h : x2611_14160_zeroSumForces G m N) : x2611_14160_zeroSumForces G m M := by
  intro w
  let e : Fin N ↪ Fin M := Fin.castLEEmb hNM
  obtain ⟨f, hf⟩ := h (fun x => w (Sym2.map e x))
  refine ⟨f.trans e, ?_⟩
  simpa [x2611_14160_copyWeight, Sym2.map_map, Function.comp_def] using hf

lemma x2611_14160_remark3_4_aux4 {ι : Type*} [Fintype ι] (p : ℕ)
    (hcard : Fintype.card ι = p) (P : ι → Prop) [DecidablePred P]
    (h : (∑ i, if P i then (1 : ZMod p) else 0) = 0) :
    (∀ i, P i) ∨ (∀ i, ¬ P i) := by
  classical
  let s := (univ : Finset ι).filter P
  have hc : s.card ≤ p := by simpa [hcard] using Finset.card_le_card (filter_subset P univ)
  have hz : (s.card : ZMod p) = 0 := by simpa [s] using h
  have hd := (ZMod.natCast_eq_zero_iff s.card p).mp hz
  have he : s.card = 0 ∨ s.card = p := by
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · exact Or.inl h0
    · exact Or.inr (le_antisymm hc (Nat.le_of_dvd hpos hd))
  rcases he with he | he
  · right
    simpa [s, Finset.card_filter_eq_zero_iff] using he
  · left
    have he' : s.card = (univ : Finset ι).card := by simpa [hcard] using he
    have hall := (Finset.card_filter_eq_iff).mp he'
    simpa using hall

lemma x2611_14160_remark3_4_aux5 {A B W R : Type*} [Fintype A] [Fintype B]
    [AddCommMonoid R] [DecidableEq W] (f : A ⊕ B ↪ W) (x y : A ⊕ B) (t : R) :
    (∑ i : A, ∑ j : B, if Sym2.mk (f (.inl i)) (f (.inr j)) =
      Sym2.mk (f x) (f y) then t else 0) =
      if x.isLeft = y.isLeft then 0 else t := by
  classical
  cases x <;> cases y <;>
    simp [Sym2.eq_iff, f.injective.eq_iff, ite_and, and_comm]

lemma x2611_14160_remark3_4_aux6 (p : ℕ) (hp : Nat.Prime p)
    (t : ZMod p) (ht : ¬ IsSquare t) :
    ∃ w : Sym2 (Fin p ⊕ Fin p) → ZMod p,
      ∀ f : Fin p ⊕ Fin p ↪ Fin p ⊕ Fin p,
        x2611_14160_copyWeight (completeBipartiteGraph (Fin p) (Fin p)) w f ≠ 0 := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  let u : Fin p ⊕ Fin p := .inl 0
  let v : Fin p ⊕ Fin p := .inr 0
  let w : Sym2 (Fin p ⊕ Fin p) → ZMod p := Sym2.lift
    ⟨fun x y => (if x.isLeft ∧ y.isLeft then 1 else 0) +
      (if Sym2.mk x y = Sym2.mk u v then t else 0), by
      intro x y
      simp [and_comm, Sym2.eq_swap]⟩
  refine ⟨w, ?_⟩
  intro f hzero
  have hsurj : Function.Surjective f := Finite.surjective_of_injective f.injective
  obtain ⟨x, hx⟩ := hsurj u
  obtain ⟨y, hy⟩ := hsurj v
  let a : ZMod p := ∑ i : Fin p, if (f (.inl i)).isLeft then 1 else 0
  let b : ZMod p := ∑ j : Fin p, if (f (.inr j)).isLeft then 1 else 0
  have hab : a + b = 0 := by
    have he := Equiv.sum_comp (Equiv.ofBijective f ⟨f.injective, hsurj⟩)
      (fun z : Fin p ⊕ Fin p => if z.isLeft then (1 : ZMod p) else 0)
    change (∑ z : Fin p ⊕ Fin p, if (f z).isLeft then (1 : ZMod p) else 0) =
      (∑ z : Fin p ⊕ Fin p, if z.isLeft then (1 : ZMod p) else 0) at he
    simp only [Fintype.sum_sum_type] at he
    simpa [a, b] using he
  have hprod : (∑ i : Fin p, ∑ j : Fin p,
      if (f (.inl i)).isLeft ∧ (f (.inr j)).isLeft then (1 : ZMod p) else 0) = a * b := by
    dsimp only [a, b]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hi' : (f (.inl i)).isLeft <;>
      by_cases hj' : (f (.inr j)).isLeft <;> simp [hi', hj']
  have hz : a * b + (if x.isLeft = y.isLeft then 0 else t) = 0 := by
    rw [x2611_14160_remark3_4_aux1] at hzero
    simp only [w, Sym2.lift_mk, Finset.sum_add_distrib] at hzero
    rw [hprod] at hzero
    have he := x2611_14160_remark3_4_aux5 f x y t
    rw [hx, hy] at he
    rwa [he] at hzero
  by_cases hxy : x.isLeft = y.isLeft
  · simp only [hxy, ite_true, add_zero] at hz
    have ha : a = 0 := by
      rcases mul_eq_zero.mp hz with ha | hb
      · exact ha
      · simpa [hb] using hab
    have hb : b = 0 := by simpa [ha] using hab
    cases x with
    | inl i =>
      cases y with
      | inl j =>
        obtain hh | hh := x2611_14160_remark3_4_aux4 p (Fintype.card_fin p)
          (fun i : Fin p => (f (.inl i)).isLeft) ha
        · have := hh j
          simpa [hy, v] using this
        · have := hh i
          simpa [hx, u] using this
      | inr j => simp at hxy
    | inr i =>
      cases y with
      | inl j => simp at hxy
      | inr j =>
        obtain hh | hh := x2611_14160_remark3_4_aux4 p (Fintype.card_fin p)
          (fun j : Fin p => (f (.inr j)).isLeft) hb
        · have := hh j
          simpa [hy, v] using this
        · have := hh i
          simpa [hx, u] using this
  · simp only [hxy, ite_false] at hz
    apply ht
    refine ⟨a, ?_⟩
    have hb : b = -a := eq_neg_of_add_eq_zero_right hab
    rw [hb] at hz
    linear_combination hz

lemma x2611_14160_remark3_4_aux7 (p : ℕ) (hp : Nat.Prime p) (hodd : Odd p) :
    ¬ x2611_14160_zeroSumForces (completeBipartiteGraph (Fin p) (Fin p)) p (2*p) := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hodd
  obtain ⟨t, ht⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by simpa only [ZMod.ringChar_zmod_n] using hp2)
  obtain ⟨w, hw⟩ := x2611_14160_remark3_4_aux6 p hp t ht
  let e : Fin p ⊕ Fin p ≃ Fin (2*p) :=
    finSumFinEquiv.trans (finCongr (by omega))
  intro h
  obtain ⟨f, hf⟩ := h (fun x => w (Sym2.map e.symm x))
  apply hw (f.trans e.symm.toEmbedding)
  simpa [x2611_14160_copyWeight, Sym2.map_map, Function.comp_def] using hf

theorem x2611_14160_remark3_4 (p : ℕ) (hp : Nat.Prime p) (hodd : Odd p) :
  2*p+1 ≤ x2611_14160_zeroSumRamsey (completeBipartiteGraph (Fin p) (Fin p)) p := by
  have hex := x2611_14160_remark3_4_aux2 p hp.pos
  apply le_csInf hex
  intro N hN
  by_contra hsmall
  have hNle : N ≤ 2*p := by omega
  exact x2611_14160_remark3_4_aux7 p hp hodd
    (x2611_14160_remark3_4_aux3 _ p hNle hN)
end

-- forge:entry x2611_15210_lem2_1 kind=proved origin=paper
section
/- Lemma 2.1 -/
open scoped BigOperators

lemma x2611_15210_lem2_1_aux1 {α G : Type*} [Fintype α] [Fintype G] [DecidableEq α] [DecidableEq G]
    (μ : G → ℝ) (hμ : ∑ g, μ g = 1) :
    (∑ a : α → G, ∏ i, μ (a i)) = 1 := by
  classical
  rw [← Fintype.prod_sum]
  simp [hμ]

lemma x2611_15210_lem2_1_aux2 {α G : Type*} [Fintype α] [Fintype G] [DecidableEq α] [DecidableEq G]
    (μ : G → ℝ) (hμ : ∑ g, μ g = 1) (I : Finset α)
    (P : (I → G) → Prop) [DecidablePred P] :
    (∑ a : α → G, if P (fun i => a i) then ∏ i, μ (a i) else 0) =
      ∑ a : I → G, if P a then ∏ i, μ (a i) else 0 := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun x : α => x ∈ I) (fun _ => G)
  calc
    _ = ∑ a : (I → G) × ({x : α // x ∉ I} → G),
        (if P a.1 then ∏ i, μ (a.1 i) else 0) * ∏ i, μ (a.2 i) := by
      apply Fintype.sum_equiv e
      intro a
      change (if P (fun i => a i) then ∏ i, μ (a i) else 0) =
        (if P (fun i => a i) then ∏ i : I, μ (a i) else 0) *
          ∏ i : {x : α // x ∉ I}, μ (a i)
      by_cases hP : P (fun i => a i)
      · rw [if_pos hP, if_pos hP]
        convert (Fintype.prod_subtype_mul_prod_subtype (fun x : α => x ∈ I)
          (fun i => μ (a i))).symm using 1
        congr 2 <;> ext i <;> simp
      · simp only [if_neg hP, zero_mul]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [x2611_15210_lem2_1_aux1 μ hμ]
      simp

lemma x2611_15210_lem2_1_aux3 {α G : Type*} [Fintype α] [Fintype G] [DecidableEq α] [DecidableEq G]
    [AddCommMonoid G] (μ : G → ℝ) (hμ : ∑ g, μ g = 1)
    (L : ℕ) (I : Finset α) (hI : I.card = L) :
    (∑ a : α → G, if (∑ i ∈ I, a i) = 0 then ∏ i, μ (a i) else 0) =
      ∑ a : Fin L → G, if (∑ i, a i) = 0 then ∏ i, μ (a i) else 0 := by
  classical
  have hs : ∀ a : α → G, (∑ i : I, a i) = ∑ i ∈ I, a i :=
    fun a => Finset.sum_coe_sort I (fun i => a i)
  have h := x2611_15210_lem2_1_aux2 μ hμ I (fun a => ∑ i, a i = 0)
  simp only [hs] at h
  rw [h]
  let e : I ≃ Fin L := Fintype.equivFinOfCardEq (by simpa using hI)
  let e' : (I → G) ≃ (Fin L → G) := Equiv.arrowCongr e (Equiv.refl G)
  apply Fintype.sum_equiv e'
  intro a
  have hs' : (∑ i, a i) = ∑ i, e' a i :=
    Fintype.sum_equiv e _ _ (by intro i; simp [e'])
  have hp : (∏ i, μ (a i)) = ∏ i, μ (e' a i) :=
    Fintype.prod_equiv e _ _ (by intro i; simp [e'])
  rw [hs', hp]

lemma x2611_15210_lem2_1_aux4 (M L : ℕ) (G : Type*) [Fintype G]
    [AddCommMonoid G] [DecidableEq G] (μ : G → ℝ)
    (hμ : ∀ g, 0 ≤ μ g) (hμsum : ∑ g, μ g = 1) (θ : ℝ)
    (hθ : (∑ a : Fin L → G, if (∑ i, a i) = 0 then ∏ i, μ (a i) else 0) = θ) :
    ∃ a : Fin M → G,
      (((Finset.univ.powersetCard L).filter
        (fun I : Finset (Fin M) => ∑ i ∈ I, a i = 0)).card : ℝ) ≤
        (M.choose L : ℝ) * θ := by
  classical
  let U : Finset (Finset (Fin M)) := Finset.univ.powersetCard L
  let B := fun a : Fin M → G => U.filter (fun I => ∑ i ∈ I, a i = 0)
  let w := fun a : Fin M → G => ∏ i, μ (a i)
  have hw : ∀ a, 0 ≤ w a := fun a => Finset.prod_nonneg (fun i _ => hμ (a i))
  have hws : ∑ a, w a = 1 := x2611_15210_lem2_1_aux1 μ hμsum
  have hs : ∑ a : Fin M → G, w a * ((B a).card : ℝ) =
      ∑ I ∈ U, ∑ a : Fin M → G,
        if (∑ i ∈ I, a i) = 0 then w a else 0 := by
    simp only [B, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs <;> simp
  have he : ∑ a : Fin M → G, w a * ((B a).card : ℝ) = (M.choose L : ℝ) * θ := by
    rw [hs]
    have hi : ∀ I ∈ U, (∑ a : Fin M → G,
        if (∑ i ∈ I, a i) = 0 then w a else 0) = θ := by
      intro I hI
      rw [x2611_15210_lem2_1_aux3 μ hμsum L I
        (Finset.mem_powersetCard.mp hI).2, hθ]
    rw [Finset.sum_congr rfl hi]
    simp [U]
  by_contra hn
  push_neg at hn
  have hx : ∃ a, 0 < w a := by
    by_contra hn'
    push_neg at hn'
    have hz : ∑ a, w a = 0 := Finset.sum_eq_zero (fun a _ => le_antisymm (hn' a) (hw a))
    linarith
  obtain ⟨a, ha⟩ := hx
  have hlt : ∑ a, w a * ((M.choose L : ℝ) * θ) <
      ∑ a, w a * ((B a).card : ℝ) := by
    apply Finset.sum_lt_sum
    · intro b hb
      exact mul_le_mul_of_nonneg_left (hn b).le (hw b)
    · exact ⟨a, Finset.mem_univ _, mul_lt_mul_of_pos_left (hn a) ha⟩
  rw [← Finset.sum_mul, hws, one_mul, he] at hlt
  exact (lt_irrefl _ hlt)

lemma x2611_15210_lem2_1_aux5 (L : ℕ) (G : Type*) [AddCommMonoid G]
    [Fintype G] (hG : ∀ g : G, L • g = 0) (n : ℕ) (a : Fin n → G)
    (ha : ∀ I : Finset (Fin n), I.card = L → ∑ i ∈ I, a i ≠ 0) :
    n ≤ x2611_15210_A L G := by
  classical
  have hs : n < x2611_15210_s L G := by
    by_contra hh
    obtain ⟨I, _, hI, hz⟩ := x2611_15210_thm1_1_s1h1_aux2 L G hG
      Finset.univ a (by simpa using (not_lt.mp hh))
    exact ha I hI hz
  simp only [x2611_15210_A]
  omega

lemma x2611_15210_lem2_1_aux6 (L : ℕ) (hL : 0 < L) (G : Type*)
    [AddCommMonoid G] [Fintype G] [DecidableEq G]
    (hG : ∀ g : G, L • g = 0) (μ : G → ℝ)
    (hμ : ∀ g, 0 ≤ μ g) (hμsum : ∑ g, μ g = 1) (θ : ℝ)
    (hθ : (∑ a : Fin L → G, if (∑ i, a i) = 0 then ∏ i, μ (a i) else 0) = θ)
    (M : ℕ) (A : ℝ) (hA : (M.choose L : ℝ) * θ ≤ (M : ℝ) - A) :
    A ≤ (x2611_15210_A L G : ℝ) := by
  obtain ⟨a, ha⟩ := x2611_15210_lem2_1_aux4 M L G μ hμ hμsum θ hθ
  obtain ⟨n, b, hn, hb⟩ := x2611_15210_cor4_4_s1h1_aux5 M L hL G G
    (fun x => x) a A (ha.trans hA)
  exact hn.trans (by exact_mod_cast x2611_15210_lem2_1_aux5 L G hG n b hb)

lemma x2611_15210_lem2_1_aux7 (L : ℕ) (hL : 2 ≤ L) (θ : ℝ) (hθ : 0 < θ) :
    θ * (θ ^ (-1 / ((L : ℝ) - 1))) ^ (L - 1) = 1 := by
  have hl : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  rw [← Real.rpow_mul_natCast hθ.le]
  have hc : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ L), Nat.cast_one]
  rw [hc, show (-1 / ((L : ℝ) - 1)) * ((L : ℝ) - 1) = -1 by
    field_simp [ne_of_gt (sub_pos.mpr hl)], Real.rpow_neg_one]
  exact mul_inv_cancel₀ hθ.ne'

lemma x2611_15210_lem2_1_aux8 (L : ℕ) (hL : 2 ≤ L) (θ D : ℝ)
    (hθ : 0 < θ) (hD : D = ((L - 1).factorial : ℝ) ^ (1 / ((L : ℝ) - 1)))
    (N : ℕ) (hN : N = ⌊D * θ ^ (-1 / ((L : ℝ) - 1))⌋₊) :
    (N.choose L : ℝ) * θ ≤ (N : ℝ) / L := by
  let t := θ ^ (-1 / ((L : ℝ) - 1))
  have ht : 0 < t := Real.rpow_pos_of_pos hθ _
  have hDpos : 0 < D := by rw [hD]; positivity
  have hLr : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hl : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hc : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ L), Nat.cast_one]
  have hDp : D ^ (L - 1) = ((L - 1).factorial : ℝ) := by
    rw [hD, ← Real.rpow_mul_natCast (by positivity), hc,
      show (1 / ((L : ℝ) - 1)) * ((L : ℝ) - 1) = 1 by field_simp [ne_of_gt (sub_pos.mpr hl)],
      Real.rpow_one]
  have htθ : θ * t ^ (L - 1) = 1 := x2611_15210_lem2_1_aux7 L hL θ hθ
  have hn : (N : ℝ) ≤ D * t := by
    rw [hN]
    exact Nat.floor_le (by positivity)
  have hpow : (N : ℝ) ^ (L - 1) * θ ≤ ((L - 1).factorial : ℝ) := by
    have h := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (show (0 : ℝ) ≤ N by positivity) hn (L - 1)) hθ.le
    rw [mul_pow, hDp] at h
    nlinarith [htθ]
  have hf : (0 : ℝ) < L.factorial := by positivity
  have hfac : (L.factorial : ℝ) = (L : ℝ) * ((L - 1).factorial : ℝ) := by
    have he : L = (L - 1) + 1 := by omega
    conv_lhs => rw [he, Nat.factorial_succ]
    push_cast
    rw [hc]
    ring
  have hnp : (N : ℝ) ^ L = (N : ℝ) * (N : ℝ) ^ (L - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hratio : ((N : ℝ) ^ (L - 1) * θ) / (L.factorial : ℝ) ≤ 1 / L := by
    apply (div_le_div_iff₀ hf hLr).mpr
    rw [hfac, one_mul]
    simpa only [mul_comm (L : ℝ)] using mul_le_mul_of_nonneg_right hpow hLr.le
  calc
    (N.choose L : ℝ) * θ ≤ ((N : ℝ) ^ L / (L.factorial : ℝ)) * θ :=
      mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div L N) hθ.le
    _ = (N : ℝ) * (((N : ℝ) ^ (L - 1) * θ) / (L.factorial : ℝ)) := by
      rw [hnp]
      ring
    _ ≤ (N : ℝ) * (1 / L) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = (N : ℝ) / L := by ring


theorem x2611_15210_lem2_1 (L : ℕ) (hL : 2 ≤ L) (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] (hexp : AddMonoid.exponent G ∣ L) (μ : G → ℝ) (hμ : ∀ g, 0 ≤ μ g) (hμsum : ∑ g, μ g = 1) (θ : ℝ) (hθpos : 0 < θ) (hθ : (∑ a : Fin L → G, if (∑ i, a i) = 0 then ∏ i, μ (a i) else 0) = θ) (D : ℝ) (hD : D = ((L - 1).factorial : ℝ) ^ (1 / ((L : ℝ) - 1))) (N : ℕ) (hN : N = ⌊D * θ ^ (-1 / ((L : ℝ) - 1))⌋₊) : (1 - 1 / (L : ℝ)) * (N : ℝ) ≤ (x2611_15210_A (L) (G) : ℝ) ∧ (4 ≤ L → ((L : ℝ) / (4 * Real.exp 1)) * θ ^ (-1 / ((L : ℝ) - 1)) ≤ (x2611_15210_A (L) (G) : ℝ)) := by
  classical
  have hG : ∀ g : G, L • g = 0 := by
    intro g
    obtain ⟨k, hk⟩ := hexp
    rw [hk, mul_nsmul, AddMonoid.exponent_nsmul_eq_zero, nsmul_zero]
  constructor
  · apply x2611_15210_lem2_1_aux6 L (by omega) G hG μ hμ hμsum θ hθ N
    have hb := x2611_15210_lem2_1_aux8 L hL θ D hθpos hD N hN
    convert hb using 1 <;> ring
  · intro h4
    let t := θ ^ (-1 / ((L : ℝ) - 1))
    let A := (L : ℝ) / (4 * Real.exp 1) * t
    have ht : 0 < t := Real.rpow_pos_of_pos hθpos _
    have htθ : θ * t ^ (L - 1) = 1 := x2611_15210_lem2_1_aux7 L hL θ hθpos
    change A ≤ (x2611_15210_A L G : ℝ)
    by_cases hA : A ≤ ((L - 1 : ℕ) : ℝ)
    · apply hA.trans
      exact_mod_cast x2611_15210_lem2_1_aux5 L G hG (L - 1) (fun _ => 0)
        (by
          intro I hI
          have hh : I.card ≤ L - 1 := by simpa using Finset.card_le_univ I
          omega)
    · have hA1 : 1 ≤ A := by
        have hc : (3 : ℝ) ≤ ((L - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ L - 1)
        linarith
      obtain ⟨M, hM, hb⟩ := x2611_15210_cor4_4_s1h1_aux7 L h4 θ t hθpos ht htθ hA1
      apply x2611_15210_lem2_1_aux6 L (by omega) G hG μ hμ hμsum θ hθ M A
      change 2 * A ≤ (M : ℝ) at hM
      linarith
end

-- forge:entry x2611_15210_lem2_2 kind=proved origin=paper
section
/- Lemma 2.2 -/
lemma x2611_15210_lem2_2_aux1 (L : ℕ) (hL : 0 < L)
    (G : Type*) [AddCommMonoid G] [Fintype G] (hz : ∀ g : G, L • g = 0) :
    Set.Nonempty {s : ℕ | ∀ a : Fin s → G,
      ∃ I : Finset (Fin s), I.card = L ∧ ∑ i ∈ I, a i = 0} := by
  classical
  refine ⟨Fintype.card G * (L - 1) + 1, ?_⟩
  intro a
  obtain ⟨g, -, hg⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (f := a) (n := L - 1)
    (by simp) (by simp)
  obtain ⟨I, hI, hcard⟩ := Finset.exists_subset_card_eq (by omega :
    L ≤ (Finset.univ.filter (fun i => a i = g)).card)
  refine ⟨I, hcard, ?_⟩
  calc
    ∑ i ∈ I, a i = ∑ _i ∈ I, g := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (Finset.mem_filter.mp (hI hi)).2
    _ = L • g := by simp [hcard]
    _ = 0 := hz g

lemma x2611_15210_lem2_2_aux2 (L : ℕ) (hL : 0 < L)
    (G : Type*) [AddCommMonoid G] [Fintype G] (hz : ∀ g : G, L • g = 0)
    (N : ℕ) (a : Fin N → G)
    (ha : ∀ I : Finset (Fin N), I.card = L → ∑ i ∈ I, a i ≠ 0) :
    N ≤ x2611_15210_A L G := by
  classical
  have hs : ∀ b : Fin (x2611_15210_s L G) → G,
      ∃ I : Finset (Fin (x2611_15210_s L G)), I.card = L ∧ ∑ i ∈ I, b i = 0 :=
    Nat.sInf_mem (x2611_15210_lem2_2_aux1 L hL G hz)
  have hlt : N < x2611_15210_s L G := by
    by_contra h
    have hn : x2611_15210_s L G ≤ N := by omega
    let e : Fin (x2611_15210_s L G) ↪ Fin N :=
      ⟨Fin.castLE hn, Fin.castLE_injective hn⟩
    obtain ⟨I, hI, hsum⟩ := hs (a ∘ e)
    apply ha (I.map e) (by simpa using hI)
    simpa only [Finset.sum_map, Function.comp_apply] using hsum
  unfold x2611_15210_A
  omega

lemma x2611_15210_lem2_2_aux3 (L : ℕ) (hL : 0 < L)
    (G : Type*) [AddCommMonoid G] [Fintype G] (hz : ∀ g : G, L • g = 0) :
    ∃ a : Fin (x2611_15210_A L G) → G,
      ∀ I : Finset (Fin (x2611_15210_A L G)), I.card = L → ∑ i ∈ I, a i ≠ 0 := by
  classical
  have hs : ∀ b : Fin (x2611_15210_s L G) → G,
      ∃ I : Finset (Fin (x2611_15210_s L G)), I.card = L ∧ ∑ i ∈ I, b i = 0 :=
    Nat.sInf_mem (x2611_15210_lem2_2_aux1 L hL G hz)
  have hpos : 0 < x2611_15210_s L G := by
    obtain ⟨I, hI, -⟩ := hs (fun _ => 0)
    have := Finset.card_le_univ I
    simp only [Fintype.card_fin] at this
    omega
  have hbad : ¬ ∀ a : Fin (x2611_15210_A L G) → G,
      ∃ I : Finset (Fin (x2611_15210_A L G)), I.card = L ∧ ∑ i ∈ I, a i = 0 := by
    intro h
    have hh : x2611_15210_s L G ≤ x2611_15210_A L G := Nat.sInf_le h
    unfold x2611_15210_A at hh
    omega
  push Not at hbad
  exact hbad

lemma x2611_15210_lem2_2_aux4 (n : ℕ) (α : Type*) (I : Finset α)
    (f : α → Bool) (hcard : I.card = n)
    (hs : ∑ i ∈ I, (if f i then (1 : ZMod n) else 0) = 0) :
    ∀ i ∈ I, ∀ j ∈ I, f i = f j := by
  classical
  let J := I.filter (fun i => f i = true)
  have hcast : (J.card : ZMod n) = 0 := by
    simpa [J, Finset.sum_filter] using hs
  have hdiv : n ∣ J.card := (ZMod.natCast_eq_zero_iff _ _).mp hcast
  by_cases hz : J.card = 0
  · have hf : ∀ i ∈ I, ¬ f i = true := Finset.card_filter_eq_zero_iff.mp hz
    intro i hi j hj
    have hfi : f i = false := by simpa using hf i hi
    have hfj : f j = false := by simpa using hf j hj
    exact hfi.trans hfj.symm
  · have heq : J.card = I.card := le_antisymm (Finset.card_filter_le _ _)
      (by rw [hcard]; exact Nat.le_of_dvd (Nat.pos_of_ne_zero hz) hdiv)
    have hf : ∀ i ∈ I, f i = true := Finset.card_filter_eq_iff.mp heq
    intro i hi j hj
    exact (hf i hi).trans (hf j hj).symm

lemma x2611_15210_lem2_2_aux5 (L : ℕ) (hL : 0 < L)
    (G : Type*) [AddCommMonoid G] [Fintype G] (hz : ∀ g : G, L • g = 0)
    (α : Type*) [Fintype α] (a : α → G)
    (ha : ∀ I : Finset α, I.card = L → ∑ i ∈ I, a i ≠ 0) :
    Fintype.card α ≤ x2611_15210_A L G := by
  classical
  let e := (Fintype.equivFin α).symm
  apply x2611_15210_lem2_2_aux2 L hL G hz (Fintype.card α) (a ∘ e)
  intro I hI hs
  apply ha (I.map e.toEmbedding) (by simpa using hI)
  simpa only [Finset.sum_map, Function.comp_apply, Equiv.toEmbedding_apply] using hs

lemma x2611_15210_lem2_2_aux6 (L : ℕ) (hL : 0 < L)
    (G H : Type*) [AddCommMonoid G] [Fintype G] [AddCommMonoid H] [Fintype H]
    (hzG : ∀ g : G, L • g = 0) (hzH : ∀ h : H, L • h = 0) :
    x2611_15210_A L G ≤ x2611_15210_A L (G × H) := by
  classical
  obtain ⟨a, ha⟩ := x2611_15210_lem2_2_aux3 L hL G hzG
  apply x2611_15210_lem2_2_aux2 L hL (G × H)
    (fun x => Prod.ext (hzG x.1) (hzH x.2)) (x2611_15210_A L G)
    (fun i => (a i, 0))
  intro I hI hs
  apply ha I hI
  simpa [Prod.fst_sum] using congrArg Prod.fst hs

lemma x2611_15210_lem2_2_aux7 (n : ℕ) (hn : 0 < n)
    (G : Type*) [AddCommMonoid G] [Fintype G] (hzG : ∀ g : G, n • g = 0)
    (d : ℕ) :
    2 ^ d * x2611_15210_A n G ≤ x2611_15210_A n (G × (Fin d → ZMod n)) := by
  classical
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨a, ha⟩ := x2611_15210_lem2_2_aux3 n hn G hzG
  let α := Fin (x2611_15210_A n G) × (Fin d → Bool)
  let b : α → G × (Fin d → ZMod n) :=
    fun p => (a p.1, fun j => if p.2 j then 1 else 0)
  have hz : ∀ x : G × (Fin d → ZMod n), n • x = 0 := by
    intro x
    apply Prod.ext (hzG x.1)
    ext j
    simp [nsmul_eq_mul]
  have hb : Fintype.card α ≤ x2611_15210_A n (G × (Fin d → ZMod n)) := by
    apply x2611_15210_lem2_2_aux5 n hn _ hz α b
    intro I hI hs
    have hbit (j : Fin d) : ∀ p ∈ I, ∀ q ∈ I, p.2 j = q.2 j := by
      apply x2611_15210_lem2_2_aux4 n α I (fun p => p.2 j) hI
      simpa [b, Prod.snd_sum, Finset.sum_apply] using congrArg (fun x : G × (Fin d → ZMod n) => x.2 j) hs
    have hinj : Set.InjOn (fun p : α => p.1) (↑I : Set α) := by
      intro p hp q hq hpq
      apply Prod.ext hpq
      funext j
      exact hbit j p hp q hq
    apply ha (I.image (fun p => p.1)) (by rw [Finset.card_image_of_injOn hinj, hI])
    rw [Finset.sum_image hinj]
    simpa [b, Prod.fst_sum] using congrArg (fun x : G × (Fin d → ZMod n) => x.1) hs
  simpa [α, Fintype.card_prod, Fintype.card_fun, Nat.mul_comm] using hb

theorem x2611_15210_lem2_2 (n : ℕ) (hn : 2 ≤ n)
    (G H : Type*) [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]
    (hG : AddMonoid.exponent G ∣ n) (hH : AddMonoid.exponent H ∣ n) (d : ℕ) :
    2 ^ d * x2611_15210_A n G ≤ x2611_15210_A n (G × (Fin d → ZMod n)) ∧
    x2611_15210_A n G ≤ x2611_15210_A n (G × H) := by
  have hzG : ∀ g : G, n • g = 0 := AddMonoid.exponent_dvd_iff_forall_nsmul_eq_zero.mp hG
  have hzH : ∀ h : H, n • h = 0 := AddMonoid.exponent_dvd_iff_forall_nsmul_eq_zero.mp hH
  exact ⟨x2611_15210_lem2_2_aux7 n (by omega) G hzG d,
    x2611_15210_lem2_2_aux6 n (by omega) G H hzG hzH⟩
end

-- forge:entry x2611_16338_lemma2_1 kind=proved origin=paper
section
/- Lemma 2.1 (Admissibility) -/
open Finset

lemma x2611_16338_lemma2_1_aux1 {α : Type*} (A : Finset α) :
    ∃ f : α → ℕ, (∀ x ∈ A, f x < A.card) ∧ Set.InjOn f A := by
  classical
  let f : α → ℕ := fun x => if h : x ∈ A then (A.equivFin ⟨x, h⟩).val else 0
  refine ⟨f, ?_, ?_⟩
  · intro x hx
    simpa [f, hx] using (A.equivFin ⟨x, hx⟩).isLt
  · intro x hx y hy h
    change x ∈ A at hx
    change y ∈ A at hy
    have hh : A.equivFin ⟨x, hx⟩ = A.equivFin ⟨y, hy⟩ := by
      apply Fin.ext
      simpa [f, hx, hy] using h
    exact congrArg Subtype.val (A.equivFin.injective hh)

lemma x2611_16338_lemma2_1_aux2 {α : Type*} (A : Finset α) (f : α → ℕ)
    (l u : ℕ) (hf : Set.InjOn f A)
    (hb : ∀ x ∈ A, l ≤ f x ∧ f x ≤ u) : A.card ≤ u + 1 - l := by
  classical
  have h := Finset.card_le_card_of_injOn (s := A) (t := Finset.Icc l u) f
    (fun x hx => Finset.mem_Icc.mpr (hb x hx)) hf
  simpa using h

lemma x2611_16338_lemma2_1_aux3 {α : Type*} [DecidableEq α]
    (A B C : Finset α) (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C) (p q r : ℕ)
    (hpq : p + A.card ≤ q) (hqr : q + B.card ≤ r) :
    ∃ w : α → ℕ,
      (∀ x ∈ A, p ≤ w x ∧ w x < p + A.card) ∧
      (∀ x ∈ B, q ≤ w x ∧ w x < q + B.card) ∧
      (∀ x ∈ C, r ≤ w x ∧ w x < r + C.card) ∧
      Set.InjOn w (↑(A ∪ B ∪ C) : Set α) := by
  classical
  obtain ⟨f, hf, hfi⟩ := x2611_16338_lemma2_1_aux1 A
  obtain ⟨g, hg, hgi⟩ := x2611_16338_lemma2_1_aux1 B
  obtain ⟨k, hk, hki⟩ := x2611_16338_lemma2_1_aux1 C
  let w : α → ℕ := fun x => if x ∈ A then p + f x else if x ∈ B then q + g x else r + k x
  have hBA (x) (hx : x ∈ B) : x ∉ A := fun ha => Finset.disjoint_left.mp hAB ha hx
  have hCA (x) (hx : x ∈ C) : x ∉ A := fun ha => Finset.disjoint_left.mp hAC ha hx
  have hCB (x) (hx : x ∈ C) : x ∉ B := fun hb => Finset.disjoint_left.mp hBC hb hx
  have hwa (x) (hx : x ∈ A) : w x = p + f x := by simp [w, hx]
  have hwb (x) (hx : x ∈ B) : w x = q + g x := by simp [w, hBA x hx, hx]
  have hwc (x) (hx : x ∈ C) : w x = r + k x := by simp [w, hCA x hx, hCB x hx]
  have ba : ∀ x ∈ A, p ≤ w x ∧ w x < p + A.card := by
    intro x hx
    rw [hwa x hx]
    have := hf x hx
    omega
  have bb : ∀ x ∈ B, q ≤ w x ∧ w x < q + B.card := by
    intro x hx
    rw [hwb x hx]
    have := hg x hx
    omega
  have bc : ∀ x ∈ C, r ≤ w x ∧ w x < r + C.card := by
    intro x hx
    rw [hwc x hx]
    have := hk x hx
    omega
  refine ⟨w, ba, bb, bc, ?_⟩
  intro x hx y hy he
  simp only [Finset.mem_coe, Finset.mem_union] at hx hy
  rcases hx with (hx | hx) | hx <;> rcases hy with (hy | hy) | hy
  · apply hfi hx hy
    rw [hwa x hx, hwa y hy] at he
    omega
  · have := ba x hx; have := bb y hy; omega
  · have := ba x hx; have := bc y hy; omega
  · have := bb x hx; have := ba y hy; omega
  · apply hgi hx hy
    rw [hwb x hx, hwb y hy] at he
    omega
  · have := bb x hx; have := bc y hy; omega
  · have := bc x hx; have := ba y hy; omega
  · have := bc x hx; have := bb y hy; omega
  · apply hki hx hy
    rw [hwc x hx, hwc y hy] at he
    omega

lemma x2611_16338_lemma2_1_aux4 {α : Type*} [DecidableEq α]
    (A B C : Finset α) (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C) (s : ℕ) (hs : 3 ≤ s) :
    (∃ w : α → ℕ,
      (∀ x ∈ A, 3 ≤ w x ∧ w x ≤ s + 2) ∧
      (∀ x ∈ B, s + 2 ≤ w x ∧ w x ≤ 2 * s + 1) ∧
      (∀ x ∈ C, 2 * s + 1 ≤ w x ∧ w x ≤ 3 * s) ∧
      Set.InjOn w (↑(A ∪ B ∪ C) : Set α)) ↔
      (A.card ≤ s ∧ B.card ≤ s ∧ C.card ≤ s ∧
        A.card + B.card ≤ 2 * s - 1 ∧ B.card + C.card ≤ 2 * s - 1 ∧
        A.card + B.card + C.card ≤ 3 * s - 2) := by
  classical
  constructor
  · rintro ⟨w, ha, hb, hc, hi⟩
    have ia : Set.InjOn w A := hi.mono (by intro x hx; simp [hx])
    have ib : Set.InjOn w B := hi.mono (by intro x hx; simp [hx])
    have ic : Set.InjOn w C := hi.mono (by intro x hx; simp [hx])
    have iab : Set.InjOn w (↑(A ∪ B) : Set α) :=
      hi.mono (by intro x hx; exact Finset.mem_union_left C hx)
    have ibc : Set.InjOn w (↑(B ∪ C) : Set α) := hi.mono (by intro x hx; simp only [Finset.mem_coe, Finset.mem_union] at hx ⊢; tauto)
    have h1 := x2611_16338_lemma2_1_aux2 A w 3 (s + 2) ia ha
    have h2 := x2611_16338_lemma2_1_aux2 B w (s + 2) (2 * s + 1) ib hb
    have h3 := x2611_16338_lemma2_1_aux2 C w (2 * s + 1) (3 * s) ic hc
    have h4 := x2611_16338_lemma2_1_aux2 (A ∪ B) w 3 (2 * s + 1) iab (by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · have := ha x hx; omega
      · have := hb x hx; omega)
    have h5 := x2611_16338_lemma2_1_aux2 (B ∪ C) w (s + 2) (3 * s) ibc (by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · have := hb x hx; omega
      · have := hc x hx; omega)
    have h6 := x2611_16338_lemma2_1_aux2 (A ∪ B ∪ C) w 3 (3 * s) hi (by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_union.mp hx with hx | hx
        · have := ha x hx; omega
        · have := hb x hx; omega
      · have := hc x hx; omega)
    rw [Finset.card_union_of_disjoint hAB] at h4
    rw [Finset.card_union_of_disjoint hBC] at h5
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩),
      Finset.card_union_of_disjoint hAB] at h6
    omega
  · rintro ⟨ha, hb, hc, hab, hbc, habc⟩
    let q := max (s + 2) (3 + A.card)
    let r := max (2 * s + 1) (q + B.card)
    have hpq : 3 + A.card ≤ q := le_max_right _ _
    have hqr : q + B.card ≤ r := le_max_right _ _
    have hq : s + 2 ≤ q := le_max_left _ _
    have hr : 2 * s + 1 ≤ r := le_max_left _ _
    have hqb : q + B.card ≤ 2 * s + 2 := by
      dsimp [q]
      omega
    have hrc : r + C.card ≤ 3 * s + 1 := by
      dsimp [r, q]
      omega
    obtain ⟨w, hwa, hwb, hwc, hi⟩ :=
      x2611_16338_lemma2_1_aux3 A B C hAB hAC hBC 3 q r hpq hqr
    refine ⟨w, ?_, ?_, ?_, hi⟩
    · intro x hx
      have := hwa x hx
      omega
    · intro x hx
      have := hwb x hx
      omega
    · intro x hx
      have := hwc x hx
      omega

theorem x2611_16338_lemma2_1 (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) (hs : 3 ≤ s)
    (φ : V → ℕ) (hφ : ∀ v, φ v = 1 ∨ φ v = s) (a b c : ℕ)
    (ha : a = (x2611_16338_edgeClass G φ 2).ncard)
    (hb : b = (x2611_16338_edgeClass G φ (s + 1)).ncard)
    (hc : c = (x2611_16338_edgeClass G φ (2 * s)).ncard) :
    (∃ ψ : Sym2 V → ℕ, x2611_16338_totalLabeling G s φ ψ) ↔
      (a ≤ s ∧ b ≤ s ∧ c ≤ s ∧ a + b ≤ 2 * s - 1 ∧
        b + c ≤ 2 * s - 1 ∧ a + b + c ≤ 3 * s - 2) := by
  classical
  let E := G.edgeFinset
  let A := E.filter (fun e => x2611_16338_vertexSum φ e = 2)
  let B := E.filter (fun e => x2611_16338_vertexSum φ e = s + 1)
  let C := E.filter (fun e => x2611_16338_vertexSum φ e = 2 * s)
  have hsum (e : Sym2 V) : x2611_16338_vertexSum φ e = 2 ∨
      x2611_16338_vertexSum φ e = s + 1 ∨ x2611_16338_vertexSum φ e = 2 * s := by
    induction e using Sym2.inductionOn with
    | _ u v =>
      change φ u + φ v = 2 ∨ φ u + φ v = s + 1 ∨ φ u + φ v = 2 * s
      rcases hφ u with hu | hu <;> rcases hφ v with hv | hv <;> omega
  have hA (e) : e ∈ A ↔ e ∈ G.edgeSet ∧ x2611_16338_vertexSum φ e = 2 := by
    simp [A, E]
  have hB (e) : e ∈ B ↔ e ∈ G.edgeSet ∧ x2611_16338_vertexSum φ e = s + 1 := by
    simp [B, E]
  have hC (e) : e ∈ C ↔ e ∈ G.edgeSet ∧ x2611_16338_vertexSum φ e = 2 * s := by
    simp [C, E]
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    have := (hA e).mp he
    have := (hB e).mp hf
    omega
  have hAC : Disjoint A C := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    have := (hA e).mp he
    have := (hC e).mp hf
    omega
  have hBC : Disjoint B C := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    have := (hB e).mp he
    have := (hC e).mp hf
    omega
  have hE : A ∪ B ∪ C = E := by
    ext e
    simp only [Finset.mem_union, hA, hB, hC, E, SimpleGraph.mem_edgeFinset]
    have := hsum e
    tauto
  have hcard (r : ℕ) : (x2611_16338_edgeClass G φ r).ncard =
      (E.filter (fun e => x2611_16338_vertexSum φ e = r)).card := by
    have heq : x2611_16338_edgeClass G φ r =
        (↑(E.filter (fun e => x2611_16338_vertexSum φ e = r)) : Set (Sym2 V)) := by
      ext e
      simp [x2611_16338_edgeClass, E]
    rw [heq, Set.ncard_coe_finset]
  have hca : A.card = a := by simpa [A] using (ha.trans (hcard 2)).symm
  have hcb : B.card = b := by simpa [B] using (hb.trans (hcard (s + 1))).symm
  have hcc : C.card = c := by simpa [C] using (hc.trans (hcard (2 * s))).symm
  rw [← hca, ← hcb, ← hcc,
    ← x2611_16338_lemma2_1_aux4 A B C hAB hAC hBC s hs]
  constructor
  · rintro ⟨ψ, hv, hψ, hi⟩
    refine ⟨fun e => x2611_16338_vertexSum φ e + ψ e, ?_, ?_, ?_, ?_⟩
    · intro e he
      obtain ⟨he, hr⟩ := (hA e).mp he
      have := hψ e he
      dsimp
      omega
    · intro e he
      obtain ⟨he, hr⟩ := (hB e).mp he
      have := hψ e he
      dsimp
      omega
    · intro e he
      obtain ⟨he, hr⟩ := (hC e).mp he
      have := hψ e he
      dsimp
      omega
    · simpa only [hE, E, SimpleGraph.coe_edgeFinset] using hi
  · rintro ⟨w, hwa, hwb, hwc, hi⟩
    have hw (e) (he : e ∈ G.edgeSet) :
        x2611_16338_vertexSum φ e + 1 ≤ w e ∧
        w e ≤ x2611_16338_vertexSum φ e + s := by
      rcases hsum e with hr | hr | hr
      · have := hwa e ((hA e).mpr ⟨he, hr⟩)
        omega
      · have := hwb e ((hB e).mpr ⟨he, hr⟩)
        omega
      · have := hwc e ((hC e).mpr ⟨he, hr⟩)
        omega
    refine ⟨fun e => w e - x2611_16338_vertexSum φ e, ?_, ?_, ?_⟩
    · intro v
      rcases hφ v with h | h <;> omega
    · intro e he
      have := hw e he
      dsimp
      omega
    · intro e he f hf hef
      have hwe := hw e he
      have hwf := hw f hf
      apply hi
      · simpa only [hE, E, Finset.mem_coe, SimpleGraph.mem_edgeFinset] using he
      · simpa only [hE, E, Finset.mem_coe, SimpleGraph.mem_edgeFinset] using hf
      · dsimp at hef
        omega
end

-- forge:entry x2611_16338_lower_bound kind=proved origin=paper
section
/- Equation (1) -/
lemma x2611_16338_lower_bound_aux1 {V : Type*} (G : SimpleGraph V) (s : ℕ)
    (φ : V → ℕ) (ψ : Sym2 V → ℕ)
    (h : x2611_16338_totalLabeling G s φ ψ) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    3 ≤ x2611_16338_vertexSum φ e + ψ e ∧
      x2611_16338_vertexSum φ e + ψ e ≤ 3 * s := by
  rcases h with ⟨hφ, hψ, hinj⟩
  revert he
  refine Sym2.inductionOn e (fun u v => ?_)
  intro he
  have hu := hφ u
  have hv := hφ v
  have hw := hψ _ he
  change 3 ≤ φ u + φ v + ψ s(u, v) ∧ φ u + φ v + ψ s(u, v) ≤ 3 * s
  omega

lemma x2611_16338_lower_bound_aux2 {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ s : ℕ, 0 < s ∧ ∃ (φ : V → ℕ) (ψ : Sym2 V → ℕ),
      x2611_16338_totalLabeling G s φ ψ := by
  classical
  let q := Fintype.equivFin (Sym2 V)
  have hc : ∀ e : Sym2 V, x2611_16338_vertexSum (fun _ : V => 1) e = 2 := by
    intro e
    exact Sym2.inductionOn e (fun _ _ => rfl)
  refine ⟨Fintype.card (Sym2 V) + 1, by omega, (fun _ => 1),
    (fun e => (q e).val + 1), ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro v
    change 1 ≤ 1 ∧ 1 ≤ Fintype.card (Sym2 V) + 1
    omega
  · intro e he
    have heq := (q e).isLt
    change 1 ≤ (q e).val + 1 ∧ (q e).val + 1 ≤ Fintype.card (Sym2 V) + 1
    omega
  · intro e he f hf hef
    simp only [hc] at hef
    apply q.injective
    apply Fin.ext
    omega

lemma x2611_16338_lower_bound_aux3 {V : Type*} [Fintype V] (G : SimpleGraph V)
    (s : ℕ) (hs : 0 < s) (φ : V → ℕ) (ψ : Sym2 V → ℕ)
    (h : x2611_16338_totalLabeling G s φ ψ) :
    G.edgeSet.ncard + 2 ≤ 3 * s := by
  classical
  have hc := Set.ncard_le_ncard_of_injOn
    (s := G.edgeSet) (t := (↑(Finset.Icc 3 (3 * s)) : Set ℕ))
    (fun e => x2611_16338_vertexSum φ e + ψ e)
    (by
      intro e he
      simpa only [Finset.mem_coe, Finset.mem_Icc] using
        x2611_16338_lower_bound_aux1 G s φ ψ h e he)
    h.2.2
  simp only [Set.ncard_coe_finset, Nat.card_Icc] at hc
  omega

lemma x2611_16338_lower_bound_aux4 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 0 < s) (φ : V → ℕ) (ψ : Sym2 V → ℕ)
    (h : x2611_16338_totalLabeling G s φ ψ) :
    G.maxDegree + 1 ≤ 2 * s := by
  classical
  have hd : ∀ v, G.degree v ≤ 2 * s - 1 := by
    intro v
    have hc := Set.ncard_le_ncard_of_injOn
      (s := G.neighborSet v) (t := (↑(Finset.Icc 2 (2 * s)) : Set ℕ))
      (fun w => φ w + ψ s(v, w))
      (by
        intro w hw
        have hp := h.1 w
        have he := h.2.1 s(v, w) (by simpa using hw)
        simp only [Finset.mem_coe, Finset.mem_Icc]
        omega)
      (by
        intro u hu w hw huw
        change φ u + ψ s(v, u) = φ w + ψ s(v, w) at huw
        have he : s(v, u) = s(v, w) := h.2.2
          (by simpa using hu) (by simpa using hw) (by
            change φ v + φ u + ψ s(v, u) = φ v + φ w + ψ s(v, w)
            omega)
        exact (Sym2.mkEmbedding v).injective he)
    have hn : (G.neighborSet v).ncard = G.degree v := by
      rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
      exact G.card_neighborSet_eq_degree v
    rw [hn] at hc
    simp only [Set.ncard_coe_finset, Nat.card_Icc] at hc
    omega
  have hm := G.maxDegree_le_of_forall_degree_le (2 * s - 1) hd
  omega

theorem x2611_16338_lower_bound (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hE : G.edgeSet.Nonempty) :
    max ((G.edgeSet.ncard + 4) / 3) ((G.maxDegree + 2) / 2) ≤ x2611_16338_tes G := by
  unfold x2611_16338_tes
  apply le_csInf
  · obtain ⟨s, hs⟩ := x2611_16338_lower_bound_aux2 G
    exact ⟨s, hs⟩
  · intro s hs
    obtain ⟨hs, φ, ψ, h⟩ := hs
    have hm := x2611_16338_lower_bound_aux3 G s hs φ ψ h
    have hd := x2611_16338_lower_bound_aux4 G s hs φ ψ h
    omega
end

-- forge:entry x2611_15210_thm4_2 kind=proved origin=paper
section
/- Theorem 4.2 -/
open scoped BigOperators

lemma x2611_15210_thm4_2_aux1 (m : ℕ) (hm : 0 < m) (ho : Odd m)
    (n : Fin 9 → ℕ) (hs : ∑ a, n a = 2 * m)
    (h0 : m ∣ n 6 + n 7 + n 8) (h1 : m ∣ n 3 + n 4 + n 5)
    (h2 : m ∣ n 1 + n 2 + n 4 + n 5 + n 7 + n 8)
    (h3 : m ∣ n 1 + n 2 + n 3 + n 5 + n 6 + n 8)
    (h4 : m ∣ n 2 + n 5 + n 6) : ∀ a, m ∣ n a := by
  simp [Fin.sum_univ_succ] at hs
  have h0' := x2611_15210_cor4_4_s1h2_aux1 m _ hm (by omega) h0
  have h1' := x2611_15210_cor4_4_s1h2_aux1 m _ hm (by omega) h1
  have h2' := x2611_15210_cor4_4_s1h2_aux1 m _ hm (by omega) h2
  have h3' := x2611_15210_cor4_4_s1h2_aux1 m _ hm (by omega) h3
  have h4' := x2611_15210_cor4_4_s1h2_aux1 m _ hm (by omega) h4
  have ha1' : n 1 = 0 ∨ n 1 = m ∨ n 1 = 2 * m ∨ 2 * n 1 = m := by omega
  obtain ⟨k, hk⟩ := ho
  have ha1 : n 1 = 0 ∨ n 1 = m ∨ n 1 = 2 * m := by
    rcases ha1' with h | h | h | h <;> omega
  have ha2 : n 2 = 0 ∨ n 2 = m ∨ n 2 = 2 * m := by omega
  have ha3 : n 3 = 0 ∨ n 3 = m ∨ n 3 = 2 * m := by omega
  have ha4 : n 4 = 0 ∨ n 4 = m ∨ n 4 = 2 * m := by omega
  have ha5 : n 5 = 0 ∨ n 5 = m ∨ n 5 = 2 * m := by omega
  have ha6 : n 6 = 0 ∨ n 6 = m ∨ n 6 = 2 * m := by omega
  have ha7 : n 7 = 0 ∨ n 7 = m ∨ n 7 = 2 * m := by omega
  have ha8 : n 8 = 0 ∨ n 8 = m ∨ n 8 = 2 * m := by omega
  have ha0 : n 0 = 0 ∨ n 0 = m ∨ n 0 = 2 * m := by omega
  have ha : ∀ a, n a = 0 ∨ n a = m ∨ n a = 2 * m := by
    intro a
    fin_cases a <;> first
      | exact ha0
      | exact ha1
      | exact ha2
      | exact ha3
      | exact ha4
      | exact ha5
      | exact ha6
      | exact ha7
      | exact ha8
  intro a
  rcases ha a with h | h | h <;> rw [h] <;> simp

lemma x2611_15210_thm4_2_aux2 (m : ℕ) (hm : 0 < m) (ho : Odd m) :
    ∃ p : Fin 9 → Fin 5 → ZMod m,
      (∀ a j, p a j = 0 ∨ p a j = 1) ∧
      Nat.card {v : Fin (2 * m) → Fin 9 // ∑ i, p (v i) = 0} =
        9 + 36 * (2 * m).choose m := by
  classical
  let b := x2611_15210_P
  let p : Fin 9 → Fin 5 → ZMod m := fun a j => b a j
  refine ⟨p, ?_, ?_⟩
  · intro a j
    fin_cases a <;> fin_cases j <;> norm_num [p, b, x2611_15210_P]
  · have hz : ∀ x : Fin 5 → ZMod m, m • x = 0 := by
      intro x
      ext j
      simp [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self]
    have hcard := x2611_15210_cor4_4_s1h2_aux7 m 9 hm hz p ?_
    · simpa only [show Nat.choose 9 2 = 36 by decide] using hcard
    intro v hv
    let n : Fin 9 → ℕ := fun a => (Finset.univ.filter (fun i => v i = a)).card
    have hs : ∑ a, n a = 2 * m := by
      simpa [n] using Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset (Fin (2 * m))) (Finset.univ : Finset (Fin 9)) v
    rw [x2611_15210_cor4_4_s1h2_aux3 v p] at hv
    have hd : ∀ j, m ∣ ∑ a, n a * b a j := by
      intro j
      rw [← ZMod.natCast_eq_zero_iff]
      simpa [p, n, Nat.cast_sum, Nat.cast_mul, Finset.sum_apply, Pi.smul_apply,
        nsmul_eq_mul] using congrFun hv j
    apply x2611_15210_thm4_2_aux1 m hm ho n hs
    · simpa [b, x2611_15210_P, Fin.sum_univ_succ, add_assoc] using hd 0
    · simpa [b, x2611_15210_P, Fin.sum_univ_succ, add_assoc] using hd 1
    · simpa [b, x2611_15210_P, Fin.sum_univ_succ, add_assoc] using hd 2
    · simpa [b, x2611_15210_P, Fin.sum_univ_succ, add_assoc] using hd 3
    · simpa [b, x2611_15210_P, Fin.sum_univ_succ, add_assoc] using hd 4

lemma x2611_15210_thm4_2_aux3 : ∀ (m : ℕ), 0 < m → Odd m → ∀ (t : ℕ),
    ∃ (p : (Fin t → Fin 9) → Fin (5 * t) → ZMod m),
      (∀ (a : Fin t → Fin 9) (j : Fin (5 * t)), p a j = 0 ∨ p a j = 1) ∧
      Nat.card {v : Fin (2 * m) → Fin t → Fin 9 // ∑ i : Fin (2 * m), p (v i) = 0} =
        (9 + 36 * (2 * m).choose m) ^ t := by
  intro m hm ho t
  classical
  obtain ⟨b, hb, hc⟩ := x2611_15210_thm4_2_aux2 m hm ho
  let e : Fin (5 * t) ≃ Fin 5 × Fin t := finProdFinEquiv.symm
  let p : (Fin t → Fin 9) → Fin (5 * t) → ZMod m := fun a j => b (a (e j).2) (e j).1
  refine ⟨p, fun a j => hb _ _, ?_⟩
  let E : {v : Fin (2 * m) → Fin t → Fin 9 // ∑ i, p (v i) = 0} ≃
      (Fin t → {v : Fin (2 * m) → Fin 9 // ∑ i, b (v i) = 0}) :=
    { toFun := fun v j => ⟨fun i => v.val i j, by
        ext k
        have h := congrFun v.property (e.symm (k, j))
        simpa [p, Finset.sum_apply] using h⟩
      invFun := fun w => ⟨fun i j => (w j).val i, by
        ext u
        have h := congrFun (w (e u).2).property (e u).1
        simpa [p, Finset.sum_apply] using h⟩
      left_inv := fun v => by apply Subtype.ext; rfl
      right_inv := fun w => by funext j; apply Subtype.ext; rfl }
  rw [Nat.card_congr E, Nat.card_fun, hc]
  simp


-- The denominator grows by at most a factor of four at each step.
theorem x2611_15210_thm4_2_aux4 (m : ℕ) :
    ((2 * (m + 1)).choose (m + 1) : ℝ) ≤ 4 * ((2 * m).choose m : ℝ) := by
  have h := Nat.succ_mul_centralBinom_succ m
  have h' : ((m : ℝ) + 1) * ((2 * (m + 1)).choose (m + 1) : ℝ) =
      2 * (2 * (m : ℝ) + 1) * ((2 * m).choose m : ℝ) := by
    exact_mod_cast h
  have hc : (0 : ℝ) ≤ ((2 * m).choose m : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem x2611_15210_thm4_2_aux5 (m : ℕ) (hm : 3 ≤ m) :
    x2611_15210_rho 3 ≤ x2611_15210_rho m := by
  let q : ℝ := (729 : ℝ) ^ (1 / 25 : ℝ)
  have hq : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq25 : q ^ 25 = 729 := by
    dsimp [q]
    norm_num [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 729)]
  have hq10 : q ^ 10 ≤ 81 / 4 := by
    apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ q ^ 10)
      (by norm_num : (0 : ℝ) ≤ 81 / 4) (by norm_num : (5 : ℕ) ≠ 0)).mp
    have he : (q ^ 10) ^ 5 = 729 ^ 2 := by
      rw [← pow_mul, show 10 * 5 = 25 * 2 by norm_num, pow_mul, hq25]
    rw [he]
    norm_num
  have hb : ∀ n : ℕ, q ^ (10 * n + 25) *
      (9 + 36 * ((2 * (n + 3)).choose (n + 3) : ℝ)) ≤ (9 : ℝ) ^ (2 * (n + 3)) := by
    intro n
    induction n with
    | zero => norm_num [hq25, Nat.choose]
    | succ n ih =>
      have hc := x2611_15210_thm4_2_aux4 (n + 3)
      have hd : 9 + 36 * ((2 * (n + 1 + 3)).choose (n + 1 + 3) : ℝ) ≤
          4 * (9 + 36 * ((2 * (n + 3)).choose (n + 3) : ℝ)) := by
        convert (show 9 + 36 * ((2 * (n + 3 + 1)).choose (n + 3 + 1) : ℝ) ≤
          4 * (9 + 36 * ((2 * (n + 3)).choose (n + 3) : ℝ)) from by linarith) using 1 <;> congr 3 <;> omega
      have hp : q ^ (10 * (n + 1) + 25) = q ^ (10 * n + 25) * q ^ 10 := by
        rw [← pow_add]
        congr 1
      have hn : (9 : ℝ) ^ (2 * (n + 1 + 3)) = 81 * 9 ^ (2 * (n + 3)) := by
        rw [show 2 * (n + 1 + 3) = 2 * (n + 3) + 2 by omega, pow_add]
        ring
      rw [hp, hn]
      calc
        q ^ (10 * n + 25) * q ^ 10 * (9 + 36 * ((2 * (n + 1 + 3)).choose (n + 1 + 3) : ℝ))
          ≤ q ^ (10 * n + 25) * (81 / 4) * (4 * (9 + 36 * ((2 * (n + 3)).choose (n + 3) : ℝ))) := by
              gcongr
        _ = 81 * (q ^ (10 * n + 25) * (9 + 36 * ((2 * (n + 3)).choose (n + 3) : ℝ))) := by ring
        _ ≤ 81 * 9 ^ (2 * (n + 3)) := by gcongr
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hrho3 : x2611_15210_rho 3 = q := by
    norm_num [x2611_15210_rho, Nat.choose, q]
  rw [hrho3]
  have hn : 0 < 5 * (2 * ((3 + n : ℕ) : ℝ) - 1) := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  unfold x2611_15210_rho
  rw [one_div, Real.le_rpow_inv_iff_of_pos hq.le (by positivity) hn]
  have he : 5 * (2 * ((3 + n : ℕ) : ℝ) - 1) = ((10 * n + 25 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [he, Real.rpow_natCast]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 9 + 36 * ((2 * (3 + n)).choose (3 + n) : ℝ))).mpr
  simpa [Nat.add_comm] using hb n

lemma x2611_15210_thm4_2_aux6 (m : ℕ) (hm : 1 ≤ m) :
    0 ≤ x2611_15210_rho m ∧ x2611_15210_rho m ≤ (9 : ℝ) ^ ((1 : ℝ) / 5) := by
  have hmcast : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hden : 0 < 5 * (2 * (m : ℝ) - 1) := by linarith
  have hcast : ((2 * m - 1 : ℕ) : ℝ) = 2 * (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hbase : (9 : ℝ) ^ (2 * m) / (9 + 36 * ((2 * m).choose m : ℝ)) ≤
      (9 : ℝ) ^ (2 * m - 1) := by
    apply (div_le_iff₀ (by positivity)).mpr
    rw [show (9 : ℝ) ^ (2 * m) = 9 ^ (2 * m - 1) * 9 by
      rw [← pow_succ]
      congr 1
      omega]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 9) (2 * m - 1),
      show (0 : ℝ) ≤ ((2 * m).choose m : ℝ) by positivity]
  have hroot : ((9 : ℝ) ^ (2 * m - 1)) ^ (1 / (5 * (2 * (m : ℝ) - 1))) =
      (9 : ℝ) ^ ((1 : ℝ) / 5) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), hcast]
    congr 1
    field_simp [show 2 * (m : ℝ) - 1 ≠ 0 by linarith]
    <;> ring
  have hupper : x2611_15210_rho m ≤ (9 : ℝ) ^ ((1 : ℝ) / 5) := by
    unfold x2611_15210_rho
    exact (Real.rpow_le_rpow (by positivity) hbase (by positivity)).trans_eq hroot
  exact ⟨Real.rpow_nonneg (by positivity) _, hupper⟩



lemma x2611_15210_thm4_2_aux7 (L : ℕ) (hL : 2 ≤ L)
    (S G : Type*) [Fintype S] [Nonempty S] [AddCommMonoid G] [DecidableEq G]
    (p : S → G) (θ : ℝ) (hθ : 0 < θ)
    (hθeq : θ = (Nat.card {v : Fin L → S // ∑ i, p (v i) = 0} : ℝ) /
      (Nat.card S : ℝ) ^ L) :
    ∃ (N : ℕ) (a : Fin N → S),
      (1 - 1 / (L : ℝ)) *
        (⌊((L - 1).factorial : ℝ) ^ (1 / ((L : ℝ) - 1)) *
          θ ^ (-1 / ((L : ℝ) - 1))⌋₊ : ℝ) ≤ (N : ℝ) ∧
      ∀ I : Finset (Fin N), I.card = L → ∑ i ∈ I, p (a i) ≠ 0 := by
  classical
  let D : ℝ := ((L - 1).factorial : ℝ) ^ (1 / ((L : ℝ) - 1))
  let M : ℕ := ⌊D * θ ^ (-1 / ((L : ℝ) - 1))⌋₊
  obtain ⟨a, ha⟩ := x2611_15210_cor4_4_s1h1_aux4 M L S G p θ
    (by simpa only [Nat.card_eq_fintype_card] using hθeq)
  have hc := x2611_15210_lem2_1_aux8 L hL θ D hθ rfl M rfl
  apply x2611_15210_cor4_4_s1h1_aux5 M L (by omega) S G p a
  calc
    _ ≤ (M.choose L : ℝ) * θ := ha
    _ ≤ (M : ℝ) / L := hc
    _ = (M : ℝ) - (1 - 1 / (L : ℝ)) * M := by ring

lemma x2611_15210_thm4_2_aux8 (m : ℕ) (hm : 3 ≤ m) (ho : Odd m) (t : ℕ) :
    x2611_15210_binary_witness m (5 * t) (2 * m)
      ((1 - 1 / (2 * (m : ℝ))) *
        (⌊((2 * m - 1).factorial : ℝ) ^ (1 / (2 * (m : ℝ) - 1)) *
          x2611_15210_rho m ^ (5 * t)⌋₊ : ℝ)) ∧
    x2611_15210_binary_witness m (5 * t) (2 * m)
      (((m : ℝ) / (2 * Real.exp 1)) * x2611_15210_rho m ^ (5 * t)) := by
  classical
  obtain ⟨p, hp, hcount⟩ := x2611_15210_thm4_2_aux3 m (by omega) ho t
  let x : ℝ := (9 : ℝ) ^ (2 * m) / (9 + 36 * ((2 * m).choose m : ℝ))
  have hx : 0 < x := by dsimp [x]; positivity
  have hθ : (x⁻¹) ^ t =
      (Nat.card {v : Fin (2 * m) → (Fin t → Fin 9) //
        (∑ i : Fin (2 * m), p (v i)) = 0} : ℝ) /
          (Nat.card (Fin t → Fin 9) : ℝ) ^ (2 * m) := by
    rw [hcount]
    simp only [Nat.card_fun, Nat.card_fin, Nat.cast_pow, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat]
    dsimp [x]
    rw [inv_div, div_pow]
    congr 1
    rw [← pow_mul, ← pow_mul, Nat.mul_comm t (2 * m)]
  have hrpow : ((x⁻¹) ^ t) ^ (-(1 : ℝ) / ((2 * m : ℕ) - 1 : ℝ)) =
      x2611_15210_rho m ^ (5 * t) := by
    have hmcast : 3 ≤ (m : ℝ) := by exact_mod_cast hm
    convert x2611_15210_cor4_4_aux12 x (2 * (m : ℝ) - 1) hx (by linarith) t using 1 <;>
      simp only [Nat.cast_mul, Nat.cast_ofNat, x2611_15210_rho, x]
  constructor
  · obtain ⟨N, a, hN, ha⟩ := x2611_15210_thm4_2_aux7 (2 * m) (by omega)
      (Fin t → Fin 9) (Fin (5 * t) → ZMod m) p ((x⁻¹) ^ t) (by positivity) hθ
    rw [hrpow] at hN
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hN
    exact ⟨N, fun i => p (a i), hN, fun i j => hp (a i) j, ha⟩
  · obtain ⟨N, a, hN, ha⟩ := x2611_15210_cor4_4_s1h1 (2 * m) (by omega)
      (Fin t → Fin 9) (Fin (5 * t) → ZMod m) p ((x⁻¹) ^ t) (by positivity) hθ
    rw [hrpow] at hN
    have hc : ((2 * m : ℕ) : ℝ) / (4 * Real.exp 1) = (m : ℝ) / (2 * Real.exp 1) := by
      push_cast
      field_simp
      <;> ring
    rw [hc] at hN
    exact ⟨N, fun i => p (a i), hN, fun i j => hp (a i) j, ha⟩

lemma x2611_15210_thm4_2_aux9 (x : ℝ) (hx : 0 ≤ x)
    (hupper : x ≤ (9 : ℝ) ^ ((1 : ℝ) / 5)) (u : ℕ) (hu : u ≤ 4) : x ^ u ≤ 6 := by
  have hroot : (9 : ℝ) ^ ((1 : ℝ) / 5) ≤ 14 / 9 := by
    have hfive : ((9 : ℝ) ^ ((1 : ℝ) / 5)) ^ 5 = 9 := by
      simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow
        (x := (9 : ℝ)) (n := 5) (by norm_num) (by decide)
    apply le_of_pow_le_pow_left₀ (n := 5) (by decide) (by norm_num)
    rw [hfive]
    norm_num
  apply (pow_le_pow_left₀ hx (hupper.trans hroot) u).trans
  interval_cases u <;> norm_num

lemma x2611_15210_thm4_2_aux10 (m : ℕ) (hm : 2 ≤ m)
    (hblock : ∀ t : ℕ, x2611_15210_binary_witness m (5 * t) (2 * m)
      (((m : ℝ) / (2 * Real.exp 1)) * x2611_15210_rho m ^ (5 * t))) :
    ∀ r : ℕ, x2611_15210_binary_witness m r (2 * m)
      (((m : ℝ) / (12 * Real.exp 1)) * x2611_15210_rho m ^ r) := by
  intro r
  obtain ⟨hρ0, hρ⟩ := x2611_15210_thm4_2_aux6 m (by omega)
  have hu : r % 5 ≤ 4 := by omega
  have hpow := x2611_15210_thm4_2_aux9 _ hρ0 hρ (r % 5) hu
  have hr : r = 5 * (r / 5) + r % 5 := by omega
  have hB : ((m : ℝ) / (12 * Real.exp 1)) * x2611_15210_rho m ^ r ≤
      ((m : ℝ) / (2 * Real.exp 1)) * x2611_15210_rho m ^ (5 * (r / 5)) := by
    calc
      _ = (((m : ℝ) / (12 * Real.exp 1)) * x2611_15210_rho m ^ (r % 5)) *
          x2611_15210_rho m ^ (5 * (r / 5)) := by
        conv_lhs => rw [hr, pow_add]
        ring
      _ ≤ (((m : ℝ) / (12 * Real.exp 1)) * 6) *
          x2611_15210_rho m ^ (5 * (r / 5)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity))
          (pow_nonneg hρ0 _)
      _ = _ := by field_simp; ring
  exact x2611_15210_cor4_4_aux9 m r (2 * m) _ _ hB
    (x2611_15210_cor4_4_aux8 m (5 * (r / 5)) r (2 * m) (by omega) _ (hblock (r / 5)))


theorem x2611_15210_thm4_2 (m : ℕ) (hm : 3 ≤ m) (hodd : Odd m) : (∀ t u : ℕ, 1 ≤ t → u ≤ 4 → ((1 - 1 / (2 * (m : ℝ))) * (⌊((2 * m - 1).factorial : ℝ) ^ (1 / (2 * (m : ℝ) - 1)) * x2611_15210_rho m ^ (5 * t)⌋₊ : ℝ) ≤ (x2611_15210_A (2 * m) (Fin (5 * t + u) → ZMod (m)) : ℝ)) ∧ x2611_15210_binary_witness m (5 * t + u) (2 * m) ((1 - 1 / (2 * (m : ℝ))) * (⌊((2 * m - 1).factorial : ℝ) ^ (1 / (2 * (m : ℝ) - 1)) * x2611_15210_rho m ^ (5 * t)⌋₊ : ℝ))) ∧ (∀ r : ℕ, ((m : ℝ) / (12 * Real.exp 1)) * x2611_15210_rho m ^ r ≤ (x2611_15210_A (2 * m) (Fin (r) → ZMod (m)) : ℝ) ∧ ((m : ℝ) / (12 * Real.exp 1)) * (3 : ℝ) ^ ((6 * (r : ℝ)) / 25) ≤ ((m : ℝ) / (12 * Real.exp 1)) * x2611_15210_rho m ^ r ∧ x2611_15210_binary_witness m r (2 * m) (((m : ℝ) / (12 * Real.exp 1)) * x2611_15210_rho m ^ r)) ∧ (3 : ℝ) ^ ((6 : ℝ) / 25) = x2611_15210_rho 3 ∧ x2611_15210_rho 3 ≤ x2611_15210_rho m ∧ x2611_15210_rho m ≤ (9 : ℝ) ^ ((1 : ℝ) / 5) ∧ Filter.Tendsto (fun k : ℕ => x2611_15210_rho (2 * k + 1)) Filter.atTop (nhds ((9 / 2 : ℝ) ^ ((1 : ℝ) / 5))) := by
  have h3 : (3 : ℝ) ^ ((6 : ℝ) / 25) = x2611_15210_rho 3 := by
    norm_num [x2611_15210_rho, Nat.choose]
    rw [show (729 : ℝ) = (3 : ℝ) ^ (6 : ℕ) by norm_num,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hmin := x2611_15210_thm4_2_aux5 m hm
  have hupper := x2611_15210_thm4_2_aux6 m (by omega)
  have hw := x2611_15210_thm4_2_aux10 m (by omega)
    (fun t => (x2611_15210_thm4_2_aux8 m hm hodd t).2)
  refine ⟨?_, ?_, h3, hmin, hupper.2, x2611_15210_rem4_3.2.2.2.2⟩
  · intro t u ht hu
    have hb := x2611_15210_cor4_4_aux8 m (5 * t) (5 * t + u) (2 * m)
      (by omega) _ (x2611_15210_thm4_2_aux8 m hm hodd t).1
    exact ⟨x2611_15210_cor4_4_aux3 m _ (by omega) _ hb, hb⟩
  · intro r
    have hpow : (3 : ℝ) ^ ((6 * (r : ℝ)) / 25) ≤ x2611_15210_rho m ^ r := by
      calc
        _ = ((3 : ℝ) ^ ((6 : ℝ) / 25)) ^ r := by
          rw [← Real.rpow_mul_natCast (by norm_num)]
          congr 1
          ring
        _ ≤ _ := pow_le_pow_left₀ (by positivity) (h3.trans_le hmin) r
    exact ⟨x2611_15210_cor4_4_aux3 m r (by omega) _ (hw r),
      mul_le_mul_of_nonneg_left hpow (by positivity), hw r⟩
end

end Mathlib2
