/- Mathlib2 分片 58（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0057
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry x2611_14160_cutWeight kind=definition origin=definition
section
noncomputable def x2611_14160_cutWeight {V Γ : Type*} [Fintype V]
    [AddCommMonoid Γ] (G : SimpleGraph V) (w : Sym2 V → Γ) (A : Finset V) : Γ := by
  classical
  exact ∑ u ∈ A, ∑ v ∈ Finset.univ \ A,
    if G.Adj u v then w (Sym2.mk u v) else 0
end

-- forge:entry x2611_14160_twoGroupD kind=definition origin=definition
section
def x2611_14160_twoGroupD {ι : Type*} [Fintype ι] (a : ι → ℕ) : ℕ :=
  1 + ∑ i, (2 ^ a i - 1)
end

-- forge:entry x2611_14160_twoGroupCondition kind=definition origin=definition
section
def x2611_14160_twoGroupCondition (Γ : Type*) [AddCommGroup Γ] (q : ℕ) : Prop :=
  ∃ (s : ℕ) (a : Fin s → ℕ), (∀ i, 1 ≤ a i) ∧
    Nonempty (Γ ≃+ ((i : Fin s) → ZMod (2 ^ a i))) ∧
    x2611_14160_twoGroupD a ≤ q
end

-- forge:entry x2611_14160_obstructionLabel kind=definition origin=definition
section
noncomputable def x2611_14160_obstructionLabel (a s m : ℕ) :
    Sym2 (Fin (2 * (a - 1) + s)) → ZMod m := by
  classical
  exact fun e =>
    if ∃ v ∈ e.toFinset, 2 * (a - 1) ≤ v.val then 1
    else if (∃ v ∈ e.toFinset, v.val < a - 1) ∧
      (∃ v ∈ e.toFinset, a - 1 ≤ v.val ∧ v.val < 2 * (a - 1))
    then -1 else 0
end

-- forge:entry x2611_14160_forestRatios kind=definition origin=definition
section
def x2611_14160_forestRatios (m : ℕ) : Set ℝ :=
  {r | ∃ (n : ℕ) (F : SimpleGraph (Fin n)), F.IsAcyclic ∧
    Nat.card F.edgeSet = m ∧
    r = (x2611_14160_zeroSumRamsey F m : ℝ) / (x2611_14160_ramsey F 2 : ℝ)}
end

-- forge:entry x2611_14160_defect kind=definition origin=definition
section
noncomputable def x2611_14160_defect {V : Type*} [Fintype V]
    (G : SimpleGraph V) (t : ℕ) : ℕ :=
  sInf {d : ℕ | ∀ w : Sym2 (Fin (2 * Fintype.card V)) → ZMod t,
    (∀ f : V ↪ Fin (2 * Fintype.card V),
      ∃ g : V ↪ Fin (2 * Fintype.card V),
        Disjoint (Set.range f) (Set.range g) ∧
        x2611_14160_copyWeight G w f = x2611_14160_copyWeight G w g) ∨
    (∃ S : Finset (Fin (2 * Fintype.card V)), S.card ≤ Fintype.card V + d ∧
      ∃ f g : V ↪ Fin (2 * Fintype.card V),
        Set.range f ⊆ (S : Set (Fin (2 * Fintype.card V))) ∧
        Set.range g ⊆ (S : Set (Fin (2 * Fintype.card V))) ∧
        x2611_14160_copyWeight G w f ≠ x2611_14160_copyWeight G w g)}
end

-- forge:entry x2611_11972_sharp_example kind=proved origin=paper
section
/- Example following (1.2) -/
theorem x2611_11972_sharp_example_aux1
    {α : Type*} [LinearOrder α] (f : (Fin 2 → α) → ℝ) (hf : Summable f) :
    (∑' n : Fin 2 → α, if Monotone n then
      (2 : ℝ) ^ (Finset.univ.image n).card * f n else 0) =
    4 * (∑' n : Fin 2 → α, if StrictMono n then f n else 0) +
      2 * ∑' a : α, f (fun _ => a) := by
  classical
  have hm (n : Fin 2 → α) : Monotone n ↔ n 0 ≤ n 1 := by
    simp [Fin.monotone_iff_le_succ, Fin.forall_fin_one]
  have hs (n : Fin 2 → α) : StrictMono n ↔ n 0 < n 1 := by
    simp [Fin.strictMono_iff_lt_succ, Fin.forall_fin_one]
  have hd : (∑' n : Fin 2 → α, if n 0 = n 1 then f n else 0) =
      ∑' a : α, f (fun _ => a) := by
    have hi : Function.Injective (fun a : α => (fun _ : Fin 2 => a)) := by
      intro a b h
      exact congrFun h 0
    have he := hi.tsum_eq (f := fun n : Fin 2 → α => if n 0 = n 1 then f n else 0) (by
      intro n hn
      have hn' : n 0 = n 1 := by
        by_contra h
        simp [Function.mem_support, h] at hn
      refine ⟨n 0, ?_⟩
      funext i
      fin_cases i
      · rfl
      · exact hn')
    simpa using he.symm
  have hss : Summable (fun n : Fin 2 → α => if StrictMono n then f n else 0) := by
    exact (hf.indicator {n | StrictMono n}).congr (fun n => by simp only [Set.indicator_apply, Set.mem_ofPred_eq])
  have hds : Summable (fun n : Fin 2 → α => if n 0 = n 1 then f n else 0) := by
    exact (hf.indicator {n | n 0 = n 1}).congr (fun n => by simp only [Set.indicator_apply, Set.mem_ofPred_eq])
  calc
    _ = ∑' n : Fin 2 → α,
        (4 * (if StrictMono n then f n else 0) +
          2 * (if n 0 = n 1 then f n else 0)) := by
      apply tsum_congr
      intro n
      rcases lt_trichotomy (n 0) (n 1) with h | h | h
      · norm_num [hm, hs, Finset.univ_fin2, h, h.le, h.ne, h.ne.symm]
      · simp [hm, hs, Finset.univ_fin2, h]
      · simp [hm, hs, h.not_ge, h.ne.symm, not_lt_of_gt h]
    _ = _ := by
      rw [(hss.mul_left 4).tsum_add (hds.mul_left 2), tsum_mul_left, tsum_mul_left, hd]

theorem x2611_11972_sharp_example_aux2
    (p : ℕ) (hp : 1 < p) (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ 1) :
    Summable (fun n : ℕ => c n / ((n + 1 : ℕ) : ℝ) ^ p) := by
  have h : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ p) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr hp)
  apply h.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_nonneg (show (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by positivity)]
  exact div_le_div_of_nonneg_right (hc n) (by positivity)

theorem x2611_11972_sharp_example :
    x2611_11972_sharp [2, -3] =
      4 * x2611_11972_euler [2, -3] + 2 * x2611_11972_euler [-5] := by
  classical
  let f : (Fin 2 → ℕ) → ℝ := fun n =>
    (1 / ((n 0 + 1 : ℕ) : ℝ) ^ 2) *
      ((-1 : ℝ) ^ (n 1 + 1) / ((n 1 + 1 : ℕ) : ℝ) ^ 3)
  have h2 : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) :=
    x2611_11972_sharp_example_aux2 2 (by norm_num) (fun _ => 1) (by simp)
  have h3 : Summable (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 3) :=
    x2611_11972_sharp_example_aux2 3 (by norm_num) (fun n => (-1) ^ (n + 1))
      (by intro n; simp [abs_pow])
  have hf : Summable f := by
    exact (finTwoArrowEquiv ℕ).summable_iff.mpr
      (summable_mul_of_summable_norm h2.norm h3.norm)
  have hsharp : x2611_11972_sharp [2, -3] =
      ∑' n : Fin 2 → ℕ, if Monotone n then
        (2 : ℝ) ^ (Finset.univ.image n).card * f n else 0 := by
    unfold x2611_11972_sharp
    apply tsum_congr
    intro n
    simp [Fin.prod_univ_two, f, div_eq_mul_inv, mul_comm]
  have heuler : x2611_11972_euler [2, -3] =
      ∑' n : Fin 2 → ℕ, if StrictMono n then f n else 0 := by
    unfold x2611_11972_euler
    apply tsum_congr
    intro n
    simp [Fin.prod_univ_two, f, div_eq_mul_inv, mul_comm]
  have hsingle : x2611_11972_euler [-5] =
      ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 5 := by
    unfold x2611_11972_euler
    simp only [List.length_cons, List.length_nil]
    rw [← (Equiv.funUnique (Fin 1) ℕ).symm.tsum_eq]
    apply tsum_congr
    intro n
    simp [Equiv.funUnique, Subsingleton.strictMono]
  rw [hsharp, x2611_11972_sharp_example_aux1 f hf, heuler, hsingle]
  congr 1
  congr 1
  apply tsum_congr
  intro n
  dsimp [f]
  rw [div_mul_div_comm, one_mul, ← pow_add]
end

-- forge:entry x2611_10200_coeff_recurrence_initial kind=proved origin=paper
section
/- Equations (2.1)–(2.2) -/
lemma x2611_10200_coeff_recurrence_initial_aux1
    {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    (1 - x) * (1 - ∑ j ∈ Finset.Icc 1 n, x ^ j) =
      1 - 2 * x + x ^ (n + 1) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    rw [show 1 - ((∑ j ∈ Finset.Icc 1 n, x ^ j) + x ^ (n + 1)) =
      (1 - ∑ j ∈ Finset.Icc 1 n, x ^ j) - x ^ (n + 1) by ring]
    rw [mul_sub, ih, pow_succ]
    ring

lemma x2611_10200_coeff_recurrence_initial_aux2
    (F : PowerSeries ℤ) (hF : (1 - PowerSeries.X) * F = 1) (n : ℕ) :
    PowerSeries.coeff n F = 1 := by
  induction n with
  | zero =>
    have h := congrArg (PowerSeries.coeff 0) hF
    simpa [sub_mul] using h
  | succ n ih =>
    have h := congrArg (PowerSeries.coeff (n + 1)) hF
    simp [sub_mul] at h
    omega

lemma x2611_10200_coeff_recurrence_initial_aux3
    (F : PowerSeries ℤ) (m : ℤ) (hm : 0 ≤ m) (d : ℕ) :
    PowerSeries.coeff m.toNat (PowerSeries.X ^ d * F) =
      if m - (d : ℤ) < 0 then 0 else PowerSeries.coeff (m - (d : ℤ)).toNat F := by
  rw [PowerSeries.coeff_X_pow_mul']
  have hm' : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm
  by_cases hd : d ≤ m.toNat
  · have hmd : ¬ m - (d : ℤ) < 0 := by omega
    rw [if_pos hd, if_neg hmd]
    have hidx : m.toNat - d = (m - (d : ℤ)).toNat := by omega
    rw [hidx]
  · have hmd : m - (d : ℤ) < 0 := by omega
    rw [if_neg hd, if_pos hmd]

lemma x2611_10200_coeff_recurrence_initial_aux4
    (g : ℕ) :
    ∀ m : ℤ, 0 ≤ m →
      x2611_10200_a g m - 2 * x2611_10200_a g (m - 1) +
        x2611_10200_a g (m - (g : ℤ) - 1) = 1 := by
  let D : PowerSeries ℤ := (1 - PowerSeries.X) ^ 2 * x2611_10200_Q g
  let A := PowerSeries.invOfUnit D 1
  let B : PowerSeries ℤ := 1 - 2 * PowerSeries.X + PowerSeries.X ^ (g + 1)
  have hQ : (1 - PowerSeries.X) * x2611_10200_Q g = B := by
    exact x2611_10200_coeff_recurrence_initial_aux1 PowerSeries.X g
  have hD : D = (1 - PowerSeries.X) * B := by
    dsimp [D]
    rw [← hQ]
    ring
  have hconst : PowerSeries.constantCoeff D = (1 : ℤˣ) := by
    rw [hD]
    simp [B]
  have hinv : D * A = 1 := PowerSeries.mul_invOfUnit D 1 hconst
  have hBA : (1 - PowerSeries.X) * (B * A) = 1 := by
    rw [← mul_assoc, ← hD]
    exact hinv
  intro m hm
  have hcoeff := x2611_10200_coeff_recurrence_initial_aux2 (B * A) hBA m.toNat
  have hshift (d : ℕ) :
      PowerSeries.coeff m.toNat (PowerSeries.X ^ d * A) =
        x2611_10200_a g (m - (d : ℤ)) := by
    rw [x2611_10200_coeff_recurrence_initial_aux3 A m hm d]
    rfl
  have hzero : PowerSeries.coeff m.toNat A = x2611_10200_a g m := by
    simp [x2611_10200_a, not_lt.mpr hm, A, D]
  dsimp [B] at hcoeff
  simp only [two_mul, add_mul, sub_mul, one_mul, map_add, map_sub] at hcoeff
  have hshift1 : PowerSeries.coeff m.toNat (PowerSeries.X * A) =
      x2611_10200_a g (m - 1) := by simpa using hshift 1
  rw [hzero, hshift1, hshift (g + 1)] at hcoeff
  norm_num only [Nat.cast_add, Nat.cast_one] at hcoeff
  have heq : m - ((g : ℤ) + 1) = m - (g : ℤ) - 1 := by omega
  rw [heq] at hcoeff
  linarith

theorem x2611_10200_coeff_recurrence_initial (g : ℕ) (hg : 1 ≤ g) :
    (∀ m : ℤ, 0 ≤ m → x2611_10200_a g m - 2 * x2611_10200_a g (m - 1) +
      x2611_10200_a g (m - (g : ℤ) - 1) = 1) ∧
    ∀ r : ℕ, r ≤ g → x2611_10200_a g (r : ℤ) = (2 : ℤ) ^ (r + 1) - 1 := by
  have hrec := x2611_10200_coeff_recurrence_initial_aux4 g
  refine ⟨hrec, ?_⟩
  intro r
  induction r with
  | zero =>
    intro hr
    have h := hrec 0 (by omega)
    have hneg : -(g : ℤ) - 1 < 0 := by omega
    simp [x2611_10200_a, hneg] at h ⊢
  | succ r ih =>
    intro hr
    have hi := ih (by omega)
    have h := hrec (r + 1) (by omega)
    have hneg : (r : ℤ) + 1 - (g : ℤ) - 1 < 0 := by omega
    have hz : x2611_10200_a g ((r : ℤ) + 1 - (g : ℤ) - 1) = 0 := by
      simp [x2611_10200_a, hneg]
    rw [hz] at h
    have heq : (r : ℤ) + 1 - 1 = r := by omega
    rw [heq, hi] at h
    push_cast
    rw [pow_succ]
    linarith
end

-- forge:entry x2611_10200_brown_gap_coefficients kind=proved origin=paper
section
/- Equation (2.7) -/
lemma x2611_10200_brown_gap_coefficients_aux1
    (H : ℕ → ℤ) (g n : ℕ) :
    PowerSeries.coeff n
      (((Finset.Icc 1 g).sum (fun j => (PowerSeries.X : PowerSeries ℤ) ^ j)) *
        PowerSeries.mk (fun r => H (r + 1))) =
      (Finset.Icc 1 (min g n)).sum (fun j => H (n + 1 - j)) := by
  rw [Finset.sum_mul, map_sum]
  calc
    _ = ∑ j ∈ Finset.Icc 1 (min g n),
        PowerSeries.coeff n (PowerSeries.X ^ j * PowerSeries.mk (fun r => H (r + 1))) := by
      symm
      apply Finset.sum_subset
      · intro j hj
        simp only [Finset.mem_Icc] at hj ⊢
        omega
      · intro j hj hj'
        have hjn : ¬ j ≤ n := by
          simp only [Finset.mem_Icc] at hj hj'
          omega
        simp [PowerSeries.coeff_X_pow_mul', hjn]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2.trans (min_le_right _ _)
      rw [PowerSeries.coeff_X_pow_mul', if_pos hjn, PowerSeries.coeff_mk]
      congr 1
      omega

lemma x2611_10200_brown_gap_coefficients_aux2
    (g k N : ℕ) (hk : 1 ≤ k) (H : ℕ → ℤ)
    (hH : x2611_10200_standard g k N H) :
    (x2611_10200_Q g - PowerSeries.C (N : ℤ) * PowerSeries.X ^ (g + k + 1)) *
      PowerSeries.mk (fun r => H (r + 1)) =
      PowerSeries.mk (fun r => if r < g + k + 1 then (1 : ℤ) else 0) := by
  ext n
  rw [sub_mul, x2611_10200_Q, sub_mul, one_mul]
  rw [map_sub, map_sub, PowerSeries.coeff_mk,
    x2611_10200_brown_gap_coefficients_aux1, mul_assoc,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk]
  simp only [PowerSeries.coeff_mk]
  by_cases hn : n < g + k + 1
  · rw [if_pos hn, if_neg (by omega : ¬ g + k + 1 ≤ n)]
    cases n with
    | zero => simpa using hH.1
    | succ n =>
      have h := hH.2.1 (n + 1 + 1) (by omega) (by omega)
      have he : n + 1 + 1 - 1 = n + 1 := by omega
      rw [he] at h
      linarith
  · rw [if_neg hn, if_pos (by omega : g + k + 1 ≤ n)]
    have h := hH.2.2 (n + 1) (by omega)
    have hmin : min g n = g := min_eq_left (by omega)
    have he : n - (g + k + 1) + 1 = n + 1 - (g + k + 1) := by omega
    rw [hmin, he]
    linarith

lemma x2611_10200_brown_gap_coefficients_aux3
    (L : ℕ) (hL : 1 ≤ L) :
    (1 - PowerSeries.X) *
      PowerSeries.mk (fun r => if r < L then (1 : ℤ) else 0) =
      1 - PowerSeries.X ^ L := by
  ext n
  cases n with
  | zero => simp [sub_mul, show 0 < L by omega, show L ≠ 0 by omega]
  | succ n =>
    simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_mk,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
    simp only [Nat.succ_ne_zero, if_false]
    split_ifs <;> omega

lemma x2611_10200_brown_gap_coefficients_aux4
    (H : ℕ → ℤ) :
    (1 - PowerSeries.X) * PowerSeries.mk (fun n => x2611_10200_B H (n + 1)) =
      1 + (2 * PowerSeries.X - 1) * PowerSeries.mk (fun n => H (n + 1)) := by
  ext n
  cases n with
  | zero => simp [x2611_10200_B, sub_mul, sub_eq_add_neg]
  | succ n =>
    simp only [sub_mul, one_mul, map_sub, map_add,
      PowerSeries.coeff_mk, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_one, Nat.succ_ne_zero, if_false]
    rw [show 2 * PowerSeries.X * PowerSeries.mk (fun n => H (n + 1)) =
      PowerSeries.X * PowerSeries.mk (fun n => H (n + 1)) +
      PowerSeries.X * PowerSeries.mk (fun n => H (n + 1)) by ring]
    simp only [map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
    simp only [x2611_10200_B, Nat.add_sub_cancel]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    ring

lemma x2611_10200_brown_gap_coefficients_aux5
    (g k N : ℕ) (hk : 1 ≤ k) (H : ℕ → ℤ)
    (hH : x2611_10200_standard g k N H) :
    PowerSeries.mk (fun n => x2611_10200_B H (n + 1)) =
      PowerSeries.X ^ (g + 1) *
        ((1 - PowerSeries.C ((N : ℤ) - 1) * PowerSeries.X ^ k +
            PowerSeries.C ((N : ℤ) - 2) * PowerSeries.X ^ (k + 1)) *
          PowerSeries.invOfUnit
            (((1 - PowerSeries.X) ^ 2 : PowerSeries ℤ) *
              (x2611_10200_Q g - PowerSeries.C (N : ℤ) *
                PowerSeries.X ^ (g + k + 1))) 1) := by
  let X : PowerSeries ℤ := PowerSeries.X
  let L := g + k + 1
  let R := x2611_10200_Q g - PowerSeries.C (N : ℤ) * X ^ L
  let S := PowerSeries.mk (fun n => H (n + 1))
  let T := PowerSeries.mk (fun n => x2611_10200_B H (n + 1))
  let P := (1 - PowerSeries.C ((N : ℤ) - 1) * X ^ k +
      PowerSeries.C ((N : ℤ) - 2) * X ^ (k + 1))
  let D := (1 - X) ^ 2 * R
  have hS : (1 - X) * R * S = 1 - X ^ L := by
    rw [mul_assoc]
    change (1 - PowerSeries.X) *
      ((x2611_10200_Q g - PowerSeries.C (N : ℤ) * PowerSeries.X ^ (g + k + 1)) *
        PowerSeries.mk (fun n => H (n + 1))) = _
    rw [x2611_10200_brown_gap_coefficients_aux2 g k N hk H hH]
    exact x2611_10200_brown_gap_coefficients_aux3 L (by dsimp [L]; omega)
  have hT : (1 - X) * T = 1 + (2 * X - 1) * S :=
    x2611_10200_brown_gap_coefficients_aux4 H
  have hQ : (1 - X) * x2611_10200_Q g = 1 - 2 * X + X ^ (g + 1) :=
    x2611_10200_coeff_recurrence_initial_aux1 X g
  have hpow : X ^ L = X ^ (g + 1) * X ^ k := by
    rw [← pow_add]
    congr 1
    dsimp [L]
    omega
  have hpoly : (1 - X) * R + (2 * X - 1) * (1 - X ^ L) = X ^ (g + 1) * P := by
    dsimp only [R, P]
    rw [mul_sub, hQ, hpow, pow_succ]
    simp only [map_sub, map_one, map_ofNat]
    ring
  have hDT : D * T = X ^ (g + 1) * P := by
    calc
      D * T = ((1 - X) * R) * ((1 - X) * T) := by dsimp [D]; ring
      _ = ((1 - X) * R) * (1 + (2 * X - 1) * S) := by rw [hT]
      _ = (1 - X) * R + (2 * X - 1) * ((1 - X) * R * S) := by ring
      _ = (1 - X) * R + (2 * X - 1) * (1 - X ^ L) := by rw [hS]
      _ = X ^ (g + 1) * P := hpoly
  have hconst : PowerSeries.constantCoeff D = (1 : ℤˣ) := by
    dsimp [D, R, X, L, x2611_10200_Q]
    simp only [map_mul, map_pow, map_sub, map_one,
      PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C, map_sum]
    have hz : (∑ j ∈ Finset.Icc 1 g, (0 : ℤ) ^ j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
      simp [hj0]
    rw [hz]
    simp
  have hinv : PowerSeries.invOfUnit D 1 * D = 1 :=
    PowerSeries.invOfUnit_mul D 1 hconst
  change T = X ^ (g + 1) * (P * PowerSeries.invOfUnit D 1)
  calc
    T = (PowerSeries.invOfUnit D 1 * D) * T := by rw [hinv, one_mul]
    _ = PowerSeries.invOfUnit D 1 * (D * T) := by ring
    _ = PowerSeries.invOfUnit D 1 * (X ^ (g + 1) * P) := by rw [hDT]
    _ = X ^ (g + 1) * (P * PowerSeries.invOfUnit D 1) := by ring

theorem x2611_10200_brown_gap_coefficients
    (g k N : ℕ) (hg : 1 ≤ g) (hk : 1 ≤ k) (hN : 1 ≤ N)
    (H : ℕ → ℤ) (hH : x2611_10200_standard g k N H) :
    (∀ n : ℕ, 1 ≤ n → n ≤ g + 1 → x2611_10200_B H n = 0) ∧
      ∀ m : ℕ, x2611_10200_B H (m + g + 2) = x2611_10200_f g k N (m : ℤ) := by
  have h := x2611_10200_brown_gap_coefficients_aux5 g k N hk H hH
  constructor
  · intro n hn hng
    have hc := congrArg (PowerSeries.coeff (n - 1)) h
    rw [PowerSeries.coeff_mk, show n - 1 + 1 = n by omega,
      PowerSeries.coeff_X_pow_mul', if_neg (by omega : ¬ g + 1 ≤ n - 1)] at hc
    exact hc
  · intro m
    have hc := congrArg (PowerSeries.coeff (m + (g + 1))) h
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul] at hc
    simpa [x2611_10200_f, show ¬ (m : ℤ) < 0 by omega,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hc
end

-- forge:entry x2611_10200_gap_recurrence kind=proved origin=paper
section
/- Equation (2.9) -/
lemma x2611_10200_gap_recurrence_aux1
    (F : PowerSeries ℤ) (hF : (1 - PowerSeries.X) ^ 2 * F = 1) (n : ℕ) :
    PowerSeries.coeff n F = (n : ℤ) + 1 := by
  have hG : (1 - PowerSeries.X) * ((1 - PowerSeries.X) * F) = 1 := by
    simpa [pow_two, mul_assoc] using hF
  induction n with
  | zero =>
    have h := x2611_10200_coeff_recurrence_initial_aux2
      ((1 - PowerSeries.X) * F) hG 0
    simpa [sub_mul] using h
  | succ n ih =>
    have h := x2611_10200_coeff_recurrence_initial_aux2
      ((1 - PowerSeries.X) * F) hG (n + 1)
    simp [sub_mul] at h
    rw [ih] at h
    push_cast
    linarith

lemma x2611_10200_gap_recurrence_aux2
    (F : PowerSeries ℤ) (hF : (1 - PowerSeries.X) ^ 2 * F = 1)
    (m : ℤ) (hm : 0 ≤ m) (d : ℕ) (hd : (d : ℤ) ≤ m + 1) :
    PowerSeries.coeff m.toNat (PowerSeries.X ^ d * F) = m + 1 - (d : ℤ) := by
  rw [x2611_10200_coeff_recurrence_initial_aux3 F m hm d]
  split_ifs with hneg
  · omega
  · rw [x2611_10200_gap_recurrence_aux1 F hF]
    have hcast := Int.toNat_of_nonneg (by omega : 0 ≤ m - (d : ℤ))
    omega

theorem x2611_10200_gap_recurrence
    (g k N : ℕ) (hg : 1 ≤ g) (hk : 1 ≤ k) (hN : 1 ≤ N)
    (m : ℤ) (hm : (k : ℤ) ≤ m) :
    x2611_10200_f g k N m =
      (Finset.Icc 1 g).sum (fun j => x2611_10200_f g k N (m - (j : ℤ))) +
      (N : ℤ) * x2611_10200_f g k N (m - ((g + k + 1 : ℕ) : ℤ)) +
      ((k : ℤ) + 2 - (N : ℤ)) := by
  let R : PowerSeries ℤ := x2611_10200_Q g -
    PowerSeries.C (N : ℤ) * PowerSeries.X ^ (g + k + 1)
  let P : PowerSeries ℤ := 1 - PowerSeries.C ((N : ℤ) - 1) * PowerSeries.X ^ k +
    PowerSeries.C ((N : ℤ) - 2) * PowerSeries.X ^ (k + 1)
  let D : PowerSeries ℤ := (1 - PowerSeries.X) ^ 2 * R
  let A := PowerSeries.invOfUnit D 1
  let F := P * A
  let B := R * A
  have hconst : PowerSeries.constantCoeff D = (1 : ℤˣ) := by
    dsimp [D, R, x2611_10200_Q]
    simp only [map_mul, map_pow, map_sub, map_one,
      PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C, map_sum]
    have hz : (∑ j ∈ Finset.Icc 1 g, (0 : ℤ) ^ j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
      simp [hj0]
    rw [hz]
    simp
  have hinv : D * A = 1 := PowerSeries.mul_invOfUnit D 1 hconst
  have hB : (1 - PowerSeries.X) ^ 2 * B = 1 := by
    change (1 - PowerSeries.X) ^ 2 * (R * A) = 1
    rw [← mul_assoc]
    exact hinv
  have hRF : R * F = P * B := by dsimp [F, B]; ring
  have hm0 : 0 ≤ m := by omega
  have hshift (d : ℕ) :
      PowerSeries.coeff m.toNat (PowerSeries.X ^ d * F) =
        x2611_10200_f g k N (m - (d : ℤ)) := by
    rw [x2611_10200_coeff_recurrence_initial_aux3 F m hm0 d]
    rfl
  have hzero : PowerSeries.coeff m.toNat F = x2611_10200_f g k N m := by
    simp [x2611_10200_f, not_lt.mpr hm0, F, P, A, D, R]
  have hcoeff := congrArg (PowerSeries.coeff m.toNat) hRF
  dsimp only [R, P] at hcoeff
  rw [x2611_10200_Q] at hcoeff
  simp only [sub_mul, add_mul, one_mul, map_sub, map_add, Finset.sum_mul,
    map_sum, mul_assoc, PowerSeries.coeff_C_mul] at hcoeff
  simp only [hzero, hshift] at hcoeff
  rw [x2611_10200_gap_recurrence_aux1 B hB,
    x2611_10200_gap_recurrence_aux2 B hB m hm0 k (by omega),
    x2611_10200_gap_recurrence_aux2 B hB m hm0 (k + 1) (by push_cast; omega)] at hcoeff
  have hcast : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm0
  rw [hcast] at hcoeff
  push_cast at hcoeff ⊢
  nlinarith [hcoeff]
end

-- forge:entry x2611_16923_lemma2_4 kind=proved origin=paper
section
/- Lemma 2.4 -/
open scoped BigOperators Classical

theorem x2611_16923_lemma2_4_aux1 (r m : ℕ) (weak : Bool) (lower : ℕ)
    (upper : Option ℕ) (a : Fin m → ℕ) (b : Fin m → (Fin r →₀ ℕ))
    (e : Fin r →₀ ℕ) :
    x2611_16923_li r weak lower upper (List.ofFn fun i => (a i, b i)) e =
      ∑ n : Fin m → Fin (e.sum (fun _ a => a) + 1),
        if (∀ i, lower ≤ (n i).val) ∧
            (List.ofFn fun i => (n i).val).Pairwise
              (fun a b => if weak then a ≤ b else a < b) ∧
            (∀ M ∈ upper, ∀ i, (n i).val < M) ∧
            (∑ i, (n i).val • b i) = e then
          ∏ i, (((n i).val : ℚ) ^ a i)⁻¹ else 0 := by
  classical
  unfold x2611_16923_li
  let E := Equiv.arrowCongr (finCongr (List.length_ofFn (f := fun i => (a i, b i))))
    (Equiv.refl (Fin (e.sum (fun _ a => a) + 1)))
  apply Fintype.sum_equiv E
  intro n
  have h := List.length_ofFn (f := fun i => (a i, b i))
  have hs : (∑ i : Fin (List.ofFn fun i => (a i, b i)).length,
      (n i).val • ((List.ofFn fun i => (a i, b i)).get i).2) =
      ∑ i : Fin m, (E n i).val • b i := by
    apply Fintype.sum_equiv (finCongr h)
    intro i
    simp [E, Equiv.arrowCongr, Fin.cast]
  have hp : (∏ i : Fin (List.ofFn fun i => (a i, b i)).length,
      (((n i).val : ℚ) ^ ((List.ofFn fun i => (a i, b i)).get i).1)⁻¹) =
      ∏ i : Fin m, (((E n i).val : ℚ) ^ a i)⁻¹ := by
    apply Fintype.prod_equiv (finCongr h)
    intro i
    simp [E, Equiv.arrowCongr, Fin.cast]
  rw [hs, hp]
  congr 1
  apply propext
  simp only [List.pairwise_ofFn]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun i => h1 ((finCongr h).symm i),
      ?_,
      fun M hM i => h3 M hM ((finCongr h).symm i), h4⟩
    intro i j hij
    exact h2 (i := (finCongr h).symm i) (j := (finCongr h).symm j) (by simpa using hij)
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun i => ?_, ?_, fun M hM i => ?_, h4⟩
    · simpa [E, Equiv.arrowCongr] using h1 ((finCongr h) i)
    · intro i j hij
      simpa [E, Equiv.arrowCongr] using h2 (i := (finCongr h) i)
        (j := (finCongr h) j) (by simpa using hij)
    · simpa [E, Equiv.arrowCongr] using h3 M hM ((finCongr h) i)

theorem x2611_16923_lemma2_4_aux2 {r : ℕ} (e : Fin r →₀ ℕ) (i : Fin r) :
    e i < e.sum (fun _ a => a) + 1 := by
  rw [Finsupp.sum_fintype _ _ (by simp)]
  exact Nat.lt_succ_of_le (Finset.single_le_sum (fun j _ => Nat.zero_le (e j))
    (Finset.mem_univ i))

theorem x2611_16923_lemma2_4_aux3 {r : ℕ} (c : Composition r)
    (n : Fin c.length → ℕ) (i : Fin r) :
    (∑ h, n h • ∑ j, Finsupp.single (c.embedding h j) 1) i = n (c.index i) := by
  classical
  have H : (∑ h, n h • ∑ j, Finsupp.single (c.embedding h j) 1) =
      ∑ j : Fin r, Finsupp.single j (n (c.index j)) := by
    rw [← c.sum_sum_apply_embedding (fun j => Finsupp.single j (n (c.index j)))]
    simp [Finset.smul_sum, Finsupp.smul_single]
  rw [H]
  simp [Finsupp.single_apply, Finsupp.sum_apply]

theorem x2611_16923_lemma2_4_aux4 {r : ℕ} (c : Composition r)
    (k : Fin r → ℕ) (n : Fin c.length → ℕ) (e : Fin r →₀ ℕ)
    (hn : ∀ i, n (c.index i) = e i) :
    (∏ h, (((n h : ℚ) ^ (∑ j, k (c.embedding h j)))⁻¹)) =
      ∏ i, (((e i : ℚ) ^ k i)⁻¹) := by
  classical
  rw [← c.prod_prod_apply_embedding (fun i => (((e i : ℚ) ^ k i)⁻¹))]
  apply Finset.prod_congr rfl
  intro h _
  simp_rw [← hn (c.embedding h _), c.index_embedding]
  rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum]

theorem x2611_16923_lemma2_4_aux5 {r : ℕ} (c : Composition r) : Monotone c.index := by
  intro i j hij
  by_contra! h
  have h1 := c.lt_sizeUpTo_index_succ j
  have h2 := c.sizeUpTo_index_le i
  have h3 := c.monotone_sizeUpTo (Nat.succ_le_of_lt h)
  exact (not_lt_of_ge (le_trans (le_trans h3 h2) hij)) h1

theorem x2611_16923_lemma2_4_aux6 {r : ℕ} (c : Composition r) (i : Fin r) :
    i.castSucc ∈ c.boundaries ↔ c.sizeUpTo (c.index i) = i.val := by
  classical
  simp only [Composition.boundaries, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    have hjv : c.sizeUpTo j = i.val := congrArg Fin.val hj
    change c.sizeUpTo j.val = i.val at hjv
    have h1 := c.sizeUpTo_index_le i
    have h2 := c.lt_sizeUpTo_index_succ i
    change i.val < c.sizeUpTo ((c.index i).val + 1) at h2
    have heq : j.val = (c.index i).val := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have H := c.monotone_sizeUpTo (Nat.succ_le_of_lt hlt)
        have H' := c.sizeUpTo_strict_mono (by omega : j.val < c.length)
        simp only [Nat.succ_eq_add_one] at H H'
        omega
      · have H := c.monotone_sizeUpTo (Nat.succ_le_of_lt hgt)
        simp only [Nat.succ_eq_add_one] at H
        omega
    simpa [← heq] using hjv
  · intro h
    refine ⟨(c.index i).castSucc, ?_⟩
    apply Fin.ext
    exact h

theorem x2611_16923_lemma2_4_aux7 {r : ℕ} (c : Composition r)
    (j : ℕ) (hj : j + 1 < r) :
    (⟨j + 1, by omega⟩ : Fin (r + 1)) ∈ c.boundaries ↔
      c.index ⟨j, by omega⟩ ≠ c.index ⟨j + 1, hj⟩ := by
  change (⟨j + 1, hj⟩ : Fin r).castSucc ∈ c.boundaries ↔ _
  rw [x2611_16923_lemma2_4_aux6 c ⟨j + 1, hj⟩]
  change c.sizeUpTo (c.index ⟨j + 1, hj⟩).val = j + 1 ↔ _
  have h1 := c.sizeUpTo_index_le ⟨j + 1, hj⟩
  have h2 := c.lt_sizeUpTo_index_succ ⟨j + 1, hj⟩
  change c.sizeUpTo (c.index ⟨j + 1, hj⟩).val ≤ j + 1 at h1
  change j + 1 < c.sizeUpTo ((c.index ⟨j + 1, hj⟩).val + 1) at h2
  constructor
  · intro heq hi
    have := c.sizeUpTo_index_le ⟨j, by omega⟩
    rw [hi] at this
    change c.sizeUpTo (c.index ⟨j + 1, hj⟩).val ≤ j at this
    omega
  · intro hne
    by_contra heq
    have H : (⟨j, by omega⟩ : Fin r) ∈ Set.range (c.embedding (c.index ⟨j+1, hj⟩)) := by
      rw [c.mem_range_embedding_iff]
      constructor <;> dsimp at * <;> omega
    exact hne (c.mem_range_embedding_iff'.mp H).symm

theorem x2611_16923_lemma2_4_aux8 {r : ℕ} (k : Fin r → ℕ)
    (c : Composition r) (e : Fin r →₀ ℕ) :
    x2611_16923_li r false 1 none (x2611_16923_blocks k c) e =
      if (∃ n : Fin c.length → ℕ, (∀ h, 1 ≤ n h) ∧ StrictMono n ∧
          ∀ i, n (c.index i) = e i) then
        ∏ i, (((e i : ℚ) ^ k i)⁻¹) else 0 := by
  classical
  rw [x2611_16923_blocks, x2611_16923_lemma2_4_aux1]
  simp only [Bool.false_eq_true, ↓reduceIte, List.pairwise_ofFn, Option.mem_def,
    reduceCtorEq, false_implies, forall_const, true_and]
  by_cases H : ∃ n : Fin c.length → ℕ, (∀ h, 1 ≤ n h) ∧ StrictMono n ∧
      ∀ i, n (c.index i) = e i
  · rw [if_pos H]
    obtain ⟨n, hn, hs, he⟩ := H
    let nf : Fin c.length → Fin (e.sum (fun _ a => a) + 1) := fun h =>
      ⟨n h, by
        have hh := c.one_le_blocksFun h
        have H := he (c.embedding h ⟨0, hh⟩)
        rw [c.index_embedding] at H
        rw [H]
        exact x2611_16923_lemma2_4_aux2 e _⟩
    have hnfe : (∑ h, (nf h).val • ∑ j, Finsupp.single (c.embedding h j) 1) = e := by
      ext i
      rw [x2611_16923_lemma2_4_aux3]
      exact he i
    rw [Fintype.sum_eq_single nf]
    · rw [if_pos ⟨hn, hs, hnfe⟩]
      exact x2611_16923_lemma2_4_aux4 c k n e he
    · intro nf' hne
      apply if_neg
      rintro ⟨_, _, he'⟩
      apply hne
      funext h
      apply Fin.ext
      have hh := c.one_le_blocksFun h
      have H := congrArg (fun v : Fin r →₀ ℕ => v (c.embedding h ⟨0, hh⟩)) he'
      rw [x2611_16923_lemma2_4_aux3, c.index_embedding] at H
      change (nf' h).val = n h
      simpa only [c.index_embedding] using H.trans (he (c.embedding h ⟨0, hh⟩)).symm
  · rw [if_neg H]
    apply Finset.sum_eq_zero
    intro n _
    apply if_neg
    rintro ⟨hn, hs, he⟩
    apply H
    refine ⟨fun h => (n h).val, hn, hs, ?_⟩
    intro i
    have H := congrArg (fun v : Fin r →₀ ℕ => v i) he
    rwa [x2611_16923_lemma2_4_aux3] at H

theorem x2611_16923_lemma2_4_aux9 {r : ℕ} (k : Fin r → ℕ) (e : Fin r →₀ ℕ) :
    x2611_16923_li r true 1 none (x2611_16923_entries k) e =
      if (∀ i, 1 ≤ e i) ∧ Monotone e then
        ∏ i, (((e i : ℚ) ^ k i)⁻¹) else 0 := by
  classical
  rw [x2611_16923_entries, x2611_16923_lemma2_4_aux1]
  simp only [Bool.true_eq, ↓reduceIte, List.pairwise_ofFn, Option.mem_def,
    reduceCtorEq, false_implies, forall_const, true_and]
  let ne : Fin r → Fin (e.sum (fun _ a => a) + 1) :=
    fun i => ⟨e i, x2611_16923_lemma2_4_aux2 e i⟩
  have hsum (n : Fin r → Fin (e.sum (fun _ a => a) + 1)) :
      (∑ i, (n i).val • Finsupp.single i 1) = e ↔ ∀ i, (n i).val = e i := by
    constructor
    · intro h i
      have H := congrArg (fun v : Fin r →₀ ℕ => v i) h
      simpa [Finsupp.single_apply] using H
    · intro h
      ext i
      simpa [Finsupp.single_apply] using h i
  rw [Fintype.sum_eq_single ne]
  · have Hne : (∑ i, (ne i).val • Finsupp.single i 1) = e :=
      (hsum ne).mpr (fun _ => rfl)
    simp only [Hne, and_true]
    change (if (∀ i, 1 ≤ e i) ∧ (∀ ⦃i j : Fin r⦄, i < j → e i ≤ e j)
      then _ else _) = _
    congr 1
    apply propext
    exact and_congr_right fun _ => ⟨fun h i j hij =>
      (hij.eq_or_lt.elim (fun he => by simp [he]) (fun hij => h hij)),
      fun h i j hij => h hij.le⟩
  · intro n hne
    apply if_neg
    rintro ⟨_, _, he⟩
    apply hne
    funext i
    apply Fin.ext
    exact (hsum n).mp he i

theorem x2611_16923_lemma2_4_aux10 {r : ℕ} (f : Fin r → ℕ)
    (c d : Composition r) (n : Fin c.length → ℕ) (m : Fin d.length → ℕ)
    (hn : StrictMono n) (hm : StrictMono m)
    (hcn : ∀ i, n (c.index i) = f i) (hdm : ∀ i, m (d.index i) = f i) : c = d := by
  apply (compositionEquiv r).injective
  apply CompositionAsSet.ext
  change c.boundaries = d.boundaries
  ext i
  by_cases hi0 : i = 0
  · subst i
    simp [← Composition.toCompositionAsSet_boundaries]
  by_cases hir : i = Fin.last r
  · subst i
    simp [← Composition.toCompositionAsSet_boundaries]
  have hip : 0 < i.val := by
    have : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
    omega
  have hir' : i.val < r := by
    have : i.val ≠ r := fun h => hir (Fin.ext h)
    omega
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hip)
  have hjr : j + 1 < r := by omega
  have hji : (⟨j + 1, by omega⟩ : Fin (r + 1)) = i := by
    apply Fin.ext
    change j + 1 = i.val
    omega
  rw [← hji, x2611_16923_lemma2_4_aux7 c j hjr,
    x2611_16923_lemma2_4_aux7 d j hjr]
  have hc : c.index ⟨j, by omega⟩ = c.index ⟨j + 1, by omega⟩ ↔
      f ⟨j, by omega⟩ = f ⟨j + 1, by omega⟩ := by
    rw [← hcn, ← hcn]
    exact hn.injective.eq_iff.symm
  have hd : d.index ⟨j, by omega⟩ = d.index ⟨j + 1, by omega⟩ ↔
      f ⟨j, by omega⟩ = f ⟨j + 1, by omega⟩ := by
    rw [← hdm, ← hdm]
    exact hm.injective.eq_iff.symm
  exact not_congr (hc.trans hd.symm)

theorem x2611_16923_lemma2_4_aux11 {r : ℕ} (f : Fin r → ℕ) (hf : Monotone f) :
    ∃ c : Composition r, ∃ n : Fin c.length → ℕ,
      StrictMono n ∧ ∀ i, n (c.index i) = f i := by
  classical
  let s : CompositionAsSet r :=
    { boundaries := Finset.univ.filter fun i => i = 0 ∨ i = Fin.last r ∨
        ∃ (j : ℕ) (hj : j + 1 < r), i.val = j + 1 ∧
          f ⟨j, by omega⟩ ≠ f ⟨j + 1, hj⟩
      zero_mem := by simp
      getLast_mem := by simp }
  let c := s.toComposition
  have hchange (j : ℕ) (hj : j + 1 < r) :
      (⟨j + 1, by omega⟩ : Fin (r + 1)) ∈ c.boundaries ↔
        f ⟨j, by omega⟩ ≠ f ⟨j + 1, hj⟩ := by
    simp only [c, CompositionAsSet.toComposition_boundaries, s,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (h0 | hr | ⟨l, hl, he, hne⟩)
      · have := congrArg Fin.val h0
        simp only [Fin.val_mk, Fin.val_zero] at this
        omega
      · have := congrArg Fin.val hr
        simp only [Fin.val_mk, Fin.val_last] at this
        omega
      · have : l = j := by omega
        subst l
        exact hne
    · intro hne
      exact Or.inr (Or.inr ⟨j, hj, rfl, hne⟩)
  have hsame (j : ℕ) (hj : j + 1 < r)
      (h : c.index ⟨j, by omega⟩ = c.index ⟨j + 1, hj⟩) :
      f ⟨j, by omega⟩ = f ⟨j + 1, hj⟩ := by
    by_contra hne
    exact ((x2611_16923_lemma2_4_aux7 c j hj).mp ((hchange j hj).mpr hne)) h
  let n : Fin c.length → ℕ := fun h => f (c.embedding h ⟨0, c.one_le_blocksFun h⟩)
  have hconst (h : Fin c.length) (j : Fin (c.blocksFun h)) :
      f (c.embedding h j) = n h := by
    have H : ∀ (t : ℕ) (ht : t < c.blocksFun h), f (c.embedding h ⟨t, ht⟩) = n h := by
      intro t
      induction t with
      | zero => intro ht; rfl
      | succ t ih =>
        intro ht
        have htr : c.sizeUpTo h + t + 1 < r := (c.embedding h ⟨t+1, ht⟩).is_lt
        have H := hsame (c.sizeUpTo h + t) htr (by
          change c.index (c.embedding h ⟨t, by omega⟩) =
            c.index (c.embedding h ⟨t+1, ht⟩)
          simp)
        change f (c.embedding h ⟨t, by omega⟩) = f (c.embedding h ⟨t+1, ht⟩) at H
        exact H.symm.trans (ih (by omega))
    exact H j.val j.is_lt
  have he (i : Fin r) : n (c.index i) = f i := by
    simpa using (hconst (c.index i) (c.invEmbedding i)).symm
  have hnmono : Monotone n := by
    intro a b hab
    apply hf
    change c.sizeUpTo a + 0 ≤ c.sizeUpTo b + 0
    simpa using c.monotone_sizeUpTo hab
  have hstep (h : Fin c.length) (hh : h.val + 1 < c.length) :
      n h < n ⟨h.val + 1, hh⟩ := by
    let h' : Fin c.length := ⟨h.val+1, hh⟩
    let i := c.embedding h ⟨c.blocksFun h - 1, by
      have := c.one_le_blocksFun h
      omega⟩
    let j := c.embedding h' ⟨0, c.one_le_blocksFun h'⟩
    have hij : i.val + 1 = j.val := by
      change c.sizeUpTo h + (c.blocksFun h - 1) + 1 = c.sizeUpTo (h.val+1) + 0
      rw [c.sizeUpTo_succ' h]
      have := c.one_le_blocksFun h
      omega
    have hp : (⟨i.val, i.is_lt⟩ : Fin r) = i := rfl
    have hq : (⟨i.val+1, by omega⟩ : Fin r) = j := Fin.ext hij
    have hidx : c.index i ≠ c.index j := by
      simp only [i, j, c.index_embedding]
      intro H
      have := congrArg Fin.val H
      change h.val = h.val+1 at this
      omega
    have hne : f i ≠ f j := by
      have H := (hchange i.val (by omega)).mp
        ((x2611_16923_lemma2_4_aux7 c i.val (by omega)).mpr (by
          simpa only [hp, hq] using hidx))
      simpa only [hp, hq] using H
    have hlt : f i < f j := lt_of_le_of_ne (hf (by
      change i.val ≤ j.val
      omega)) hne
    change f (c.embedding h _) < n h' at hlt
    rw [hconst] at hlt
    exact hlt
  refine ⟨c, n, ?_, he⟩
  intro a b hab
  have hh : a.val+1 < c.length := lt_of_le_of_lt (Nat.succ_le_of_lt hab) b.is_lt
  exact lt_of_lt_of_le (hstep a hh) (hnmono (by
    change a.val+1 ≤ b.val
    omega))

theorem x2611_16923_lemma2_4 (r : ℕ) (hr : 0 < r) (k : Fin r → ℕ)
    (hk : ∀ i, 0 < k i) :
    x2611_16923_li r true 1 none (x2611_16923_entries k) =
      ∑ c : Composition r, x2611_16923_li r false 1 none (x2611_16923_blocks k c) := by
  classical
  apply MvPowerSeries.ext
  intro e
  simp only [map_sum]
  change x2611_16923_li r true 1 none (x2611_16923_entries k) e =
    ∑ c : Composition r, x2611_16923_li r false 1 none (x2611_16923_blocks k c) e
  rw [x2611_16923_lemma2_4_aux9]
  simp_rw [x2611_16923_lemma2_4_aux8]
  by_cases H : (∀ i, 1 ≤ e i) ∧ Monotone e
  · rw [if_pos H]
    obtain ⟨c, n, hs, he⟩ := x2611_16923_lemma2_4_aux11 e H.2
    have hn (h : Fin c.length) : 1 ≤ n h := by
      have hh := c.one_le_blocksFun h
      have H' := H.1 (c.embedding h ⟨0, hh⟩)
      rw [← he, c.index_embedding] at H'
      exact H'
    symm
    rw [Fintype.sum_eq_single c]
    · rw [if_pos ⟨n, hn, hs, he⟩]
    · intro d hdc
      apply if_neg
      rintro ⟨m, _, hm, hd⟩
      exact hdc (x2611_16923_lemma2_4_aux10 e d c m n hm hs hd he)
  · rw [if_neg H]
    symm
    apply Finset.sum_eq_zero
    intro c _
    apply if_neg
    rintro ⟨n, hn, hs, he⟩
    apply H
    constructor
    · intro i
      rw [← he]
      exact hn (c.index i)
    · intro i j hij
      rw [← he, ← he]
      exact hs.monotone (x2611_16923_lemma2_4_aux5 c hij)
end

-- forge:entry x2611_10200_lem3_1_s1h3 kind=proved origin=decomposition
section
/- x2611_10200_lem3_1 的证明骨架中第 3 个空洞 -/
lemma x2611_10200_lem3_1_s1h3_aux1 {R : Type*} [CommRing R]
    (D E T P : PowerSeries R) (L m : ℕ)
    (hD : PowerSeries.constantCoeff D = (1 : Rˣ))
    (hE : PowerSeries.constantCoeff E = (1 : Rˣ))
    (hDE : D - E = PowerSeries.X ^ L * T) (hm : m < L) :
    PowerSeries.coeff m (P * PowerSeries.invOfUnit E 1) =
      PowerSeries.coeff m (P * PowerSeries.invOfUnit D 1) := by
  let A := PowerSeries.invOfUnit D 1
  let B := PowerSeries.invOfUnit E 1
  have hAD : A * D = 1 := PowerSeries.invOfUnit_mul D 1 hD
  have hEB : E * B = 1 := PowerSeries.mul_invOfUnit E 1 hE
  have hdiff : P * B - P * A = PowerSeries.X ^ L * (P * T * A * B) := by
    calc
      P * B - P * A = P * ((A * D) * B - A * (E * B)) := by rw [hAD, hEB]; ring
      _ = P * (A * (D - E) * B) := by ring
      _ = PowerSeries.X ^ L * (P * T * A * B) := by rw [hDE]; ring
  have hh := congrArg (PowerSeries.coeff m) hdiff
  rw [map_sub, PowerSeries.coeff_X_pow_mul', if_neg (by omega : ¬ L ≤ m)] at hh
  exact sub_eq_zero.mp hh

lemma x2611_10200_lem3_1_s1h3_aux2 (g k N : ℕ) (m : ℤ)
    (hm : 0 ≤ m) (hml : m < ((g + k + 1 : ℕ) : ℤ)) :
    x2611_10200_f g k N m = x2611_10200_a g m -
      ((N : ℤ) - 1) * x2611_10200_a g (m - (k : ℤ)) +
      ((N : ℤ) - 2) * x2611_10200_a g (m - ((k + 1 : ℕ) : ℤ)) := by
  let D : PowerSeries ℤ := (1 - PowerSeries.X) ^ 2 * x2611_10200_Q g
  let E : PowerSeries ℤ := (1 - PowerSeries.X) ^ 2 *
    (x2611_10200_Q g - PowerSeries.C (N : ℤ) * PowerSeries.X ^ (g + k + 1))
  let P : PowerSeries ℤ := 1 - PowerSeries.C ((N : ℤ) - 1) * PowerSeries.X ^ k +
    PowerSeries.C ((N : ℤ) - 2) * PowerSeries.X ^ (k + 1)
  let A := PowerSeries.invOfUnit D 1
  have hQ : PowerSeries.constantCoeff (x2611_10200_Q g) = 1 := by
    dsimp [x2611_10200_Q]
    simp only [map_sub, map_one, map_sum, map_pow, PowerSeries.constantCoeff_X]
    have hz : (∑ j ∈ Finset.Icc 1 g, (0 : ℤ) ^ j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
      simp [hj0]
    rw [hz, sub_zero]
  have hD : PowerSeries.constantCoeff D = (1 : ℤˣ) := by simp [D, hQ]
  have hE : PowerSeries.constantCoeff E = (1 : ℤˣ) := by simp [E, hQ]
  have hDE : D - E = PowerSeries.X ^ (g + k + 1) *
      ((1 - PowerSeries.X) ^ 2 * PowerSeries.C (N : ℤ)) := by dsimp [D, E]; ring
  have hc := x2611_10200_lem3_1_s1h3_aux1 D E _ P (g + k + 1) m.toNat
    hD hE hDE (by omega)
  have hf : x2611_10200_f g k N m = PowerSeries.coeff m.toNat (P * A) := by
    simpa only [x2611_10200_f, if_neg (not_lt.mpr hm)] using hc
  have hshift (d : ℕ) : PowerSeries.coeff m.toNat (PowerSeries.X ^ d * A) =
      x2611_10200_a g (m - (d : ℤ)) := by
    rw [x2611_10200_coeff_recurrence_initial_aux3 A m hm d]
    rfl
  have hzero : PowerSeries.coeff m.toNat A = x2611_10200_a g m := by
    simp only [x2611_10200_a, if_neg (not_lt.mpr hm)]
    rfl
  rw [hf]
  dsimp only [P]
  simp only [add_mul, sub_mul, one_mul, mul_assoc, map_add, map_sub, PowerSeries.coeff_C_mul]
  rw [hzero, hshift k, hshift (k + 1)]

theorem x2611_10200_lem3_1_s1h3 : ∀ (g k N : ℕ), 1 ≤ g → 1 ≤ k → 1 ≤ N →
    (∀ m : ℤ, 0 ≤ m → m < (k : ℤ) → x2611_10200_f g k N m = x2611_10200_a g m) ∧
    ∀ r : ℕ, r ≤ g → x2611_10200_f g k N ((k + r : ℕ) : ℤ) =
      x2611_10200_a g ((k + r : ℕ) : ℤ) + 1 - (N : ℤ) * (2 : ℤ) ^ r := by
  intro g k N hg hk hN
  constructor
  · intro m hm hmk
    rw [x2611_10200_lem3_1_s1h3_aux2 g k N m hm (by omega)]
    have hneg1 : m - (k : ℤ) < 0 := by omega
    have hneg2 : m - ((k + 1 : ℕ) : ℤ) < 0 := by omega
    have hz1 : x2611_10200_a g (m - (k : ℤ)) = 0 := by
      simp only [x2611_10200_a, if_pos hneg1]
    have hz2 : x2611_10200_a g (m - ((k + 1 : ℕ) : ℤ)) = 0 := by
      simp only [x2611_10200_a, if_pos hneg2]
    rw [hz1, hz2]
    ring
  · intro r hr
    have hrec := x2611_10200_lem3_1_s1h3_aux2 g k N ((k + r : ℕ) : ℤ) (by omega) (by omega)
    have hi1 : ((k + r : ℕ) : ℤ) - (k : ℤ) = (r : ℤ) := by omega
    have hi2 : ((k + r : ℕ) : ℤ) - ((k + 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
    have ha := (x2611_10200_coeff_recurrence_initial g hg).2 r hr
    have hprev : x2611_10200_a g ((r : ℤ) - 1) = (2 : ℤ) ^ r - 1 := by
      cases r with
      | zero => simp [x2611_10200_a]
      | succ t =>
        have ht := (x2611_10200_coeff_recurrence_initial g hg).2 t (by omega)
        have heq : ((t + 1 : ℕ) : ℤ) - 1 = (t : ℤ) := by omega
        simpa only [heq] using ht
    rw [hi1, hi2, ha, hprev, pow_succ] at hrec
    rw [hrec]
    ring
end

-- forge:entry x2611_10200_lem3_1 kind=proved origin=paper
section
/- Lemma 3.1 -/
lemma x2611_10200_lem3_1_aux1
    (f : ℤ → ℤ) (g L : ℕ) (N c : ℤ)
    (hg : 2 ≤ g) (hL : 3 ≤ L) (hN : 0 < N) (hc : 0 < N + c)
    (hinit : ∀ m : ℤ, m < (L : ℤ) → 0 ≤ f m)
    (hzero : f 0 = 1)
    (hone : c < 0 → 3 ≤ f 1) (htwo : c < 0 → 1 ≤ f 2)
    (hrec : ∀ m : ℤ, (L : ℤ) ≤ m →
      f m = (Finset.Icc 1 g).sum (fun j => f (m - (j : ℤ))) +
        N * f (m - (L : ℤ)) + c) :
    (∀ m : ℤ, 0 ≤ f m) ∧ ∀ m : ℤ, (L : ℤ) ≤ m → 0 < f m := by
  have H : ∀ n : ℕ, 0 ≤ f (n : ℤ) ∧
      ((L : ℤ) ≤ (n : ℤ) → 0 < f (n : ℤ)) ∧
      ((L + 1 : ℕ) ≤ n → c < 0 → -c < f (n : ℤ)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hp : ∀ m : ℤ, m < (n : ℤ) → 0 ≤ f m := by
        intro m hm
        by_cases hm0 : m < 0
        · exact hinit m (by omega)
        · have hmn : m.toNat < n := by omega
          simpa only [Int.toNat_of_nonneg (by omega : 0 ≤ m)] using (ih m.toNat hmn).1
      by_cases hn : n < L
      · exact ⟨hinit n (by exact_mod_cast hn), by omega, by omega⟩
      have hLn : (L : ℤ) ≤ (n : ℤ) := by omega
      have hs (j : ℕ) (hj : j ∈ Finset.Icc 1 g) : 0 ≤ f ((n : ℤ) - j) := by
        have hj1 := (Finset.mem_Icc.mp hj).1
        apply hp
        omega
      have hs0 : 0 ≤ (Finset.Icc 1 g).sum (fun j => f ((n : ℤ) - j)) :=
        Finset.sum_nonneg hs
      have hs1 : f ((n : ℤ) - 1) ≤
          (Finset.Icc 1 g).sum (fun j => f ((n : ℤ) - j)) := by
        exact Finset.single_le_sum hs (by simp; omega)
      have hs2 : f ((n : ℤ) - 1) + f ((n : ℤ) - 2) ≤
          (Finset.Icc 1 g).sum (fun j => f ((n : ℤ) - j)) := by
        have hh : ({1, 2} : Finset ℕ) ⊆ Finset.Icc 1 g := by
          intro j hj
          simp only [Finset.mem_insert, Finset.mem_singleton] at hj
          rcases hj with rfl | rfl <;> simp <;> omega
        simpa using (Finset.sum_le_sum_of_subset_of_nonneg hh (by
          intro j hj _
          exact hs j hj) :
          ({1, 2} : Finset ℕ).sum (fun j => f ((n : ℤ) - j)) ≤ _)
      have hd : 0 ≤ N * f ((n : ℤ) - L) :=
        mul_nonneg (by omega) (hp _ (by omega))
      have hr := hrec (n : ℤ) hLn
      have ht : 0 < f (n : ℤ) ∧
          ((L + 1 : ℕ) ≤ n → c < 0 → -c < f (n : ℤ)) := by
        by_cases he : n = L
        · subst n
          have he0 : (L : ℤ) - L = 0 := sub_self _
          rw [he0, hzero, mul_one] at hr
          constructor
          · omega
          · omega
        have hprev : 0 < f ((n : ℤ) - 1) := by
          have hn1 : n - 1 < n := by omega
          have hh := (ih (n - 1) hn1).2.1 (by omega)
          have heq : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
          simpa only [heq] using hh
        by_cases hcn : 0 ≤ c
        · constructor
          · omega
          · omega
        have hcneg : c < 0 := by omega
        by_cases he1 : n = L + 1
        · have hd1 : (n : ℤ) - L = 1 := by omega
          rw [hd1] at hr
          have hmul : N * 3 ≤ N * f 1 :=
            mul_le_mul_of_nonneg_left (hone hcneg) (le_of_lt hN)
          constructor <;> intros <;> omega
        by_cases he2 : n = L + 2
        · have hd2 : (n : ℤ) - L = 2 := by omega
          rw [hd2] at hr
          have hmul : N ≤ N * f 2 := by
            simpa using mul_le_mul_of_nonneg_left (htwo hcneg) (by omega : 0 ≤ N)
          have hpp : -c < f ((n : ℤ) - 1) := by
            have hh := (ih (n - 1) (by omega)).2.2 (by omega) hcneg
            have heq : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
            simpa only [heq] using hh
          have hp2 := hp ((n : ℤ) - 2) (by omega)
          constructor <;> intros <;> omega
        have hpp1 : -c < f ((n : ℤ) - 1) := by
          have hh := (ih (n - 1) (by omega)).2.2 (by omega) hcneg
          have heq : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
          simpa only [heq] using hh
        have hpp2 : -c < f ((n : ℤ) - 2) := by
          have hh := (ih (n - 2) (by omega)).2.2 (by omega) hcneg
          have heq : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
          simpa only [heq] using hh
        constructor <;> intros <;> omega
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

lemma x2611_10200_lem3_1_aux2 (a : ℤ → ℤ) (g : ℕ) (hg : 1 ≤ g)
    (hneg : ∀ m : ℤ, m < 0 → a m = 0)
    (hrec : ∀ m : ℤ, 0 ≤ m → a m - 2 * a (m - 1) + a (m - (g : ℤ) - 1) = 1) :
    (∀ m : ℤ, 0 ≤ a m) ∧ ∀ m : ℤ, 0 ≤ m → 0 < a m := by
  have H : ∀ n : ℕ, 0 < a (n : ℤ) ∧ ∀ j : ℕ, j ≤ n → a (j : ℤ) ≤ a (n : ℤ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hr := hrec (n : ℤ) (by omega)
      by_cases hn : n = 0
      · subst n
        simp only [Nat.cast_zero] at *
        have ha : a ((0 : ℤ) - 1) = 0 := hneg _ (by omega)
        have hb : a ((0 : ℤ) - (g : ℤ) - 1) = 0 := hneg _ (by omega)
        rw [ha, hb] at hr
        refine ⟨by omega, ?_⟩
        intro j hj
        have : j = 0 := by omega
        subst j
        exact le_rfl
      have hn1 : n - 1 < n := by omega
      have heq : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
      have hp : 0 < a ((n : ℤ) - 1) := by
        simpa only [heq] using (ih (n - 1) hn1).1
      have hbound : a ((n : ℤ) - (g : ℤ) - 1) ≤ a ((n : ℤ) - 1) := by
        by_cases ht : (n : ℤ) - (g : ℤ) - 1 < 0
        · rw [hneg _ ht]
          omega
        · have hj : ((n : ℤ) - (g : ℤ) - 1).toNat ≤ n - 1 := by omega
          have hh := (ih (n - 1) hn1).2 _ hj
          simpa only [heq, Int.toNat_of_nonneg (by omega : 0 ≤ (n : ℤ) - (g : ℤ) - 1)] using hh
      have hstep : a ((n : ℤ) - 1) < a (n : ℤ) := by omega
      refine ⟨by omega, ?_⟩
      intro j hj
      by_cases he : j = n
      · subst j
        exact le_rfl
      · have hh := (ih (n - 1) hn1).2 j (by omega)
        rw [heq] at hh
        omega
  constructor
  · intro m
    by_cases hm : m < 0
    · rw [hneg m hm]
    · have hh := (H m.toNat).1
      rw [Int.toNat_of_nonneg (by omega)] at hh
      omega
  · intro m hm
    simpa only [Int.toNat_of_nonneg hm] using (H m.toNat).1

lemma x2611_10200_lem3_1_aux3 (a : ℤ → ℤ) (g k : ℕ) (N : ℤ)
    (hg : 1 ≤ g) (hk : 1 ≤ k) (hnon : ∀ m : ℤ, 0 ≤ a m)
    (hpos : 0 < a ((k : ℤ) - 1))
    (hrec : ∀ m : ℤ, 0 ≤ m → a m - 2 * a (m - 1) + a (m - (g : ℤ) - 1) = 1)
    (hbound : N * (2 : ℤ) ^ g ≤ a ((k + g : ℕ) : ℤ) + 1) :
    (∀ r : ℕ, r ≤ g → N * (2 : ℤ) ^ r ≤ a ((k + r : ℕ) : ℤ) + 1) ∧
      N < a (k : ℤ) + 1 := by
  have H : ∀ r : ℕ, r ≤ g →
      N * (2 : ℤ) ^ r ≤ a ((k + r : ℕ) : ℤ) + 1 ∧
      (r < g → N * (2 : ℤ) ^ r < a ((k + r : ℕ) : ℤ) + 1) := by
    intro r hr
    refine Nat.decreasingInduction (motive := fun r _ =>
      N * (2 : ℤ) ^ r ≤ a ((k + r : ℕ) : ℤ) + 1 ∧
      (r < g → N * (2 : ℤ) ^ r < a ((k + r : ℕ) : ℤ) + 1)) ?_ ?_ hr
    · intro s hs hnext
      have hm := hrec ((k + (s + 1) : ℕ) : ℤ) (by omega)
      have heq : ((k + (s + 1) : ℕ) : ℤ) - 1 = ((k + s : ℕ) : ℤ) := by omega
      rw [heq] at hm
      have hnn := hnon (((k + (s + 1) : ℕ) : ℤ) - (g : ℤ) - 1)
      rw [pow_succ] at hnext
      constructor
      · nlinarith only [hm, hnn, hnext.1]
      · intro _
        by_cases hs1 : s + 1 < g
        · have hh := hnext.2 hs1
          nlinarith only [hm, hnn, hh]
        · have hs2 : s + 1 = g := by omega
          have heq2 : ((k + (s + 1) : ℕ) : ℤ) - (g : ℤ) - 1 = (k : ℤ) - 1 := by omega
          rw [heq2] at hm
          nlinarith only [hm, hpos, hnext.1]
    · exact ⟨hbound, by omega⟩
  exact ⟨fun r hr => (H r hr).1, by simpa using (H 0 (by omega)).2 (by omega)⟩

theorem x2611_10200_lem3_1 (g k N : ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k) (hN : 1 ≤ N)
    (hM : (N : ℝ) ≤ x2611_10200_M g k) :
    (∀ m : ℤ, 0 ≤ x2611_10200_f g k N m) ∧
      ∀ m : ℤ, ((g + k + 1 : ℕ) : ℤ) ≤ m → 0 < x2611_10200_f g k N m := by
  have hR : ∀ (g k N : ℕ), 1 ≤ g → 1 ≤ k → 1 ≤ N → ∀ m : ℤ, (k : ℤ) ≤ m →
      x2611_10200_f g k N m =
        (Finset.Icc 1 g).sum (fun j => x2611_10200_f g k N (m - (j : ℤ))) +
        (N : ℤ) * x2611_10200_f g k N (m - ((g + k + 1 : ℕ) : ℤ)) +
        ((k : ℤ) + 2 - (N : ℤ)) := by
    exact x2611_10200_gap_recurrence
  have hA : ∀ (g : ℕ), 1 ≤ g →
      (∀ m : ℤ, 0 ≤ m → x2611_10200_a g m - 2 * x2611_10200_a g (m - 1) +
        x2611_10200_a g (m - (g : ℤ) - 1) = 1) ∧
      ∀ r : ℕ, r ≤ g → x2611_10200_a g (r : ℤ) = (2 : ℤ) ^ (r + 1) - 1 := by
    exact x2611_10200_coeff_recurrence_initial
  have hF : ∀ (g k N : ℕ), 1 ≤ g → 1 ≤ k → 1 ≤ N →
      (∀ m : ℤ, 0 ≤ m → m < (k : ℤ) → x2611_10200_f g k N m = x2611_10200_a g m) ∧
      ∀ r : ℕ, r ≤ g → x2611_10200_f g k N ((k + r : ℕ) : ℤ) =
        x2611_10200_a g ((k + r : ℕ) : ℤ) + 1 - (N : ℤ) * (2 : ℤ) ^ r := by
    exact x2611_10200_lem3_1_s1h3
  have hg1 : 1 ≤ g := by omega
  obtain ⟨har, hap⟩ := hA g hg1
  obtain ⟨hbelow, hmiddle⟩ := hF g k N hg1 hk hN
  obtain ⟨hanon, hapos⟩ := x2611_10200_lem3_1_aux2 (x2611_10200_a g) g hg1
    (by intro m hm; simp [x2611_10200_a, hm]) har
  have hMb : (N : ℤ) * (2 : ℤ) ^ g ≤ x2611_10200_a g ((k + g : ℕ) : ℤ) + 1 := by
    unfold x2611_10200_M at hM
    have hp : 0 < (2 : ℝ) ^ g := by positivity
    have hh := (le_div_iff₀ hp).mp hM
    have hh' : (N : ℤ) * (2 : ℤ) ^ g ≤ x2611_10200_a g ((g + k : ℕ) : ℤ) + 1 := by
      exact_mod_cast hh
    simpa only [Nat.add_comm g k] using hh'
  obtain ⟨hb, hstrict⟩ := x2611_10200_lem3_1_aux3 (x2611_10200_a g) g k (N : ℤ)
    hg1 hk hanon (hapos _ (by omega)) har hMb
  have ha0 : x2611_10200_a g 0 = 1 := by simpa using hap 0 (by omega)
  have ha1 : x2611_10200_a g 1 = 3 := by simpa using hap 1 (by omega)
  have ha2 : x2611_10200_a g 2 = 7 := by simpa using hap 2 (by omega)
  have hblock : ∀ m : ℤ, m < ((g + k + 1 : ℕ) : ℤ) → 0 ≤ x2611_10200_f g k N m := by
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
  have hzero : x2611_10200_f g k N 0 = 1 := by
    rw [hbelow 0 (by omega) (by omega), ha0]
  have hone : (k : ℤ) + 2 - (N : ℤ) < 0 → 3 ≤ x2611_10200_f g k N 1 := by
    intro hc
    have hk2 : 2 ≤ k := by
      by_contra hn
      have hk1 : k = 1 := by omega
      subst k
      simp only [Nat.cast_one, ha1] at hstrict
      omega
    rw [hbelow 1 (by omega) (by omega), ha1]
  have htwo : (k : ℤ) + 2 - (N : ℤ) < 0 → 1 ≤ x2611_10200_f g k N 2 := by
    intro hc
    have hk2 : 2 ≤ k := by
      by_contra hn
      have hk1 : k = 1 := by omega
      subst k
      simp only [Nat.cast_one, ha1] at hstrict
      omega
    by_cases hk3 : 3 ≤ k
    · rw [hbelow 2 (by omega) (by omega), ha2]
      norm_num
    · have hkexact : k = 2 := by omega
      subst k
      norm_num only [Nat.cast_ofNat, ha2] at hstrict
      have hh := hmiddle 0 (by omega)
      norm_num only [Nat.add_zero, Nat.cast_ofNat, pow_zero, mul_one] at hh
      rw [hh, ha2]
      omega
  apply x2611_10200_lem3_1_aux1 (x2611_10200_f g k N) g (g + k + 1)
    (N : ℤ) ((k : ℤ) + 2 - (N : ℤ)) hg (by omega) (by omega) (by omega)
    hblock hzero hone htwo
  intro m hm
  exact hR g k N hg1 hk hN m (by omega)
end

-- forge:entry x2611_16899_singleton_coefficient kind=proved origin=paper
section
/- Proof of Theorem 1 (singleton coefficient) -/
theorem x2611_16899_singleton_coefficient
    (K A : (Fin 1 → ℕ) → MvPolynomial (Fin 1) (RatFunc ℚ))
    (c : (Fin 1 → ℕ) → RatFunc ℚ)
    (hK : x2611_16899_key_family 1 K)
    (hA : x2611_16899_atom_family 1 RatFunc.X A)
    (hc : x2611_16899_expansion 1 1 (K (fun _ => 1)) A c) :
    c (fun _ => 1) = 1 := by
  have hK1 : K (fun _ => 1) = MvPolynomial.X (0 : Fin 1) := by
    simpa using hK.1 (fun _ => 1) (by intro i j hij; exact le_rfl)
  have hA1 : A (fun _ => 1) = MvPolynomial.X (0 : Fin 1) := by
    simpa using hA.1 (fun _ => 1) (by intro i j hij; exact le_rfl)
  unfold x2611_16899_expansion at hc
  rw [Finset.sum_eq_single (fun _ => (1 : Fin 2))] at hc
  · simp only [Fin.sum_univ_one, Fin.val_one, if_pos rfl] at hc
    rw [hK1, hA1] at hc
    have hcoeff := congrArg (MvPolynomial.coeff (Finsupp.single (0 : Fin 1) 1)) hc
    simpa using hcoeff.symm
  · intro γ hγ hne
    have hγne : (γ 0).val ≠ 1 := by
      intro heq
      apply hne
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      rw [hi]
      exact Fin.ext heq
    simp [Fin.sum_univ_one, hγne]
  · simp
end

end Mathlib2
