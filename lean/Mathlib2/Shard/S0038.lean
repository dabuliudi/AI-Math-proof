/- Mathlib2 分片 38（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0037
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry p6_prop33_ford kind=proved origin=paper
section
/- Proposition 3.3, first sentence: translation (x,y)→(x+j,y) and reflection (x,y)→(-x,y) preserve the family of Ford circles and map tangency points to tangency points [Formalised at the level of the labels: K[p,q]→K[p+jq,q], K[p,q]→K[-p,q]; determinant preserved up to sign and formula (1) transforms accordingly.] -/
theorem p6_prop33_ford (p q r s j : ℤ) (h : q ^ 2 + s ^ 2 ≠ 0) :
    (p + j * q) * s - q * (r + j * s) = p * s - q * r ∧
    (-p) * s - q * (-r) = -(p * s - q * r) ∧
    (((p + j * q) * q + (r + j * s) * s : ℤ) : ℝ) /
        ((q ^ 2 + s ^ 2 : ℤ) : ℝ) =
      ((p * q + r * s : ℤ) : ℝ) / ((q ^ 2 + s ^ 2 : ℤ) : ℝ) + (j : ℝ) ∧
    (((-p) * q + (-r) * s : ℤ) : ℝ) / ((q ^ 2 + s ^ 2 : ℤ) : ℝ) =
      -(((p * q + r * s : ℤ) : ℝ) / ((q ^ 2 + s ^ 2 : ℤ) : ℝ)) := by
  have hR : (q : ℝ) ^ 2 + (s : ℝ) ^ 2 ≠ 0 := by
    exact_mod_cast h
  refine ⟨by ring, by ring, ?_, ?_⟩
  · push_cast
    field_simp [hR] <;> ring
  · push_cast
    ring
end

-- forge:entry p6_cor32_lim_top kind=proved origin=paper
section
/- Corollary 3.2 (12), n→+∞: lim_{n→+∞} P_n = (σ_k^{-1}, 0) [Coordinatewise convergence.] -/
open Filter

theorem p6_cor32_lim_top_aux1 (k : ℤ) (hk : 1 ≤ k) (m : ℕ) :
    (m : ℤ) ≤ p6_kfib k (2 * (m : ℤ)) ∧
      (m : ℤ) + 1 ≤ p6_kfib k (2 * (m : ℤ) + 1) := by
  induction m with
  | zero =>
      have h0 := (p6_kfib_def k 0).1
      have h1 := (p6_kfib_def k 0).2.1
      simpa [h0, h1]
  | succ m ih =>
      have h1 : p6_kfib k (2 * (m : ℤ) + 2) =
          k * p6_kfib k (2 * (m : ℤ) + 1) + p6_kfib k (2 * (m : ℤ)) := by
        convert (p6_kfib_def k (2 * (m : ℤ) + 1)).2.2 using 1 <;> congr 1 <;> ring
      have h2 : p6_kfib k (2 * (m : ℤ) + 3) =
          k * p6_kfib k (2 * (m : ℤ) + 2) + p6_kfib k (2 * (m : ℤ) + 1) := by
        convert (p6_kfib_def k (2 * (m : ℤ) + 2)).2.2 using 1 <;> congr 1 <;> ring
      have hm : (0 : ℤ) ≤ m := Int.natCast_nonneg m
      have hb : (m : ℤ) + 1 ≤ p6_kfib k (2 * (m : ℤ) + 2) := by
        nlinarith [ih.1, ih.2]
      have hc : (m : ℤ) + 2 ≤ p6_kfib k (2 * (m : ℤ) + 3) := by
        nlinarith [ih.2]
      constructor
      · convert hb using 1 <;> push_cast <;> congr 1 <;> ring
      · convert hc using 1 <;> push_cast <;> congr 1 <;> ring

theorem p6_cor32_lim_top_aux2 (k n : ℤ) (hk : 1 ≤ k) (hn : 0 ≤ n) :
    0 ≤ p6_kfib k (2 * n) ∧ n ≤ p6_kfib k (2 * n + 1) := by
  have h := p6_cor32_lim_top_aux1 k hk n.toNat
  rw [Int.toNat_of_nonneg hn] at h
  constructor <;> omega

theorem p6_cor32_lim_top (k : ℤ) (hk : 1 ≤ k) :
    Filter.Tendsto (fun n : ℤ => ((p6_kfib k (2 * n) : ℤ) : ℝ) /
      ((p6_kfib k (2 * n + 1) : ℤ) : ℝ)) Filter.atTop
      (nhds ((((k : ℝ) + Real.sqrt ((k : ℝ) ^ 2 + 4)) / 2)⁻¹)) ∧
    Filter.Tendsto (fun n : ℤ => 1 / ((p6_kfib k (2 * n + 1) : ℤ) : ℝ))
      Filter.atTop (nhds 0) := by
  have hden : Tendsto (fun n : ℤ => (p6_kfib k (2 * n + 1) : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_intCast_atTop_atTop
    filter_upwards [eventually_ge_atTop (0 : ℤ)] with n hn
    exact_mod_cast (p6_cor32_lim_top_aux2 k n hk hn).2
  have hy : Tendsto (fun n : ℤ => 1 / (p6_kfib k (2 * n + 1) : ℝ))
      atTop (nhds 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hden
  refine ⟨?_, hy⟩
  have hlim : Tendsto
      (fun n : ℤ => (Real.sqrt ((k : ℝ)^2 + 4 -
        4 * (1 / (p6_kfib k (2 * n + 1) : ℝ))^2) - (k : ℝ)) / 2)
      atTop (nhds ((Real.sqrt ((k : ℝ)^2 + 4) - (k : ℝ)) / 2)) := by
    have hh : Tendsto (fun n : ℤ => (k : ℝ)^2 + 4 -
        4 * (1 / (p6_kfib k (2 * n + 1) : ℝ))^2)
        atTop (nhds ((k : ℝ)^2 + 4 - 4 * (0 : ℝ)^2)) :=
      tendsto_const_nhds.sub ((hy.pow 2).const_mul 4)
    have h := (hh.sqrt.sub_const (k : ℝ)).div_const 2
    simpa using h
  have hke : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsq := Real.sq_sqrt (show 0 ≤ (k : ℝ)^2 + 4 by positivity)
  have hnonneg := Real.sqrt_nonneg ((k : ℝ)^2 + 4)
  have hne : (k : ℝ) + Real.sqrt ((k : ℝ)^2 + 4) ≠ 0 := by linarith
  have hid : (Real.sqrt ((k : ℝ)^2 + 4) - (k : ℝ)) / 2 =
      (((k : ℝ) + Real.sqrt ((k : ℝ)^2 + 4)) / 2)⁻¹ := by
    field_simp [hne]
    nlinarith
  rw [hid] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (0 : ℤ)] with n hn
  have hp : (0 : ℝ) ≤ (p6_kfib k (2 * n) : ℝ) := by
    exact_mod_cast (p6_cor32_lim_top_aux2 k n hk hn).1
  have hq : (0 : ℝ) ≤ (p6_kfib k (2 * n + 1) : ℝ) := by
    exact_mod_cast (p6_odd_pos k n).le
  have hx : 0 ≤ (p6_kfib k (2 * n) : ℝ) / (p6_kfib k (2 * n + 1) : ℝ) :=
    div_nonneg hp hq
  have hc := p6_thm31_circle k n
  have hs : (2 * ((p6_kfib k (2 * n) : ℝ) /
      (p6_kfib k (2 * n + 1) : ℝ)) + (k : ℝ))^2 =
      (k : ℝ)^2 + 4 - 4 * (1 / (p6_kfib k (2 * n + 1) : ℝ))^2 := by
    nlinarith
  rw [← hs, Real.sqrt_sq (by linarith)]
  ring
end

-- forge:entry gr_set_card_disjoint_pairs kind=proved origin=conjecture
section
/- The number of ordered pairs of disjoint subsets of [n] is 3ⁿ — the bijection (A,B) ↦ (A,Bᶜ) maps disjoint pairs onto pairs with A ⊆ Bᶜ; Uses Mathlib2.comb_card_subset_pairs at the last step for the count of subset pairs. -/
theorem gr_set_card_disjoint_pairs (n : ℕ) :
    ((Finset.univ : Finset (Finset (Fin n) × Finset (Fin n))).filter
      (fun p => Disjoint p.1 p.2)).card = 3 ^ n := by
  classical
  calc
    _ = ((Finset.univ : Finset (Finset (Fin n) × Finset (Fin n))).filter
        (fun p => p.1 ⊆ p.2)).card := by
      refine Finset.card_bij'
        (fun p _ => (p.1, p.2ᶜ)) (fun p _ => (p.1, p.2ᶜ)) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact Finset.subset_compl_iff_disjoint_right.mpr hp
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact Finset.subset_compl_iff_disjoint_right.mp (by simpa using hp)
      · intro p hp
        simp
      · intro p hp
        simp
    _ = 3 ^ n := Mathlib2.comb_card_subset_pairs n
end

-- forge:entry p6_cor32_lim_bot kind=proved origin=paper
section
/- Corollary 3.2 (12), n→-∞: lim_{n→-∞} P_n = (-σ_k, 0) [Coordinatewise convergence.] -/
open Filter

theorem p6_cor32_lim_bot (k : ℤ) (hk : 1 ≤ k) : Filter.Tendsto (fun n : ℤ => ((p6_kfib k (2 * n) : ℤ) : ℝ) / ((p6_kfib k (2 * n + 1) : ℤ) : ℝ)) Filter.atBot (nhds (-(((k : ℝ) + Real.sqrt ((k : ℝ) ^ 2 + 4)) / 2))) ∧ Filter.Tendsto (fun n : ℤ => 1 / ((p6_kfib k (2 * n + 1) : ℤ) : ℝ)) Filter.atBot (nhds 0) := by
  let x : ℤ → ℝ := fun n => (p6_kfib k (2 * n) : ℝ) / (p6_kfib k (2 * n + 1) : ℝ)
  let y : ℤ → ℝ := fun n => 1 / (p6_kfib k (2 * n + 1) : ℝ)
  let C : ℝ := ((k : ℝ) ^ 2 + 4) / 4
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hypos (n : ℤ) : 0 < y n := by
    apply one_div_pos.mpr
    exact_mod_cast p6_odd_pos k n
  have hcircle (n : ℤ) : (x n + (k : ℝ) / 2) ^ 2 + (y n) ^ 2 = C :=
    p6_thm31_circle k n
  have hstep (n : ℤ) : x (n + 1) - x n = (k : ℝ) * y n * y (n + 1) := by
    calc
      x (n + 1) - x n = (k : ℝ) / ((p6_kfib k (2 * n + 1) : ℝ) * (p6_kfib k (2 * n + 3) : ℝ)) := p6_cor32_step k n
      _ = (k : ℝ) * y n * y (n + 1) := by
        dsimp [y]
        rw [show 2 * (n + 1) + 1 = 2 * n + 3 by ring]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  have hmono : Monotone x := by
    apply monotone_int_of_le_succ
    intro n
    have hp : 0 < (k : ℝ) * y n * y (n + 1) := mul_pos (mul_pos hkpos (hypos n)) (hypos (n + 1))
    linarith [hstep n]
  have hbound : BddBelow (Set.range x) := by
    refine ⟨-C - 1 - (k : ℝ) / 2, ?_⟩
    rintro _ ⟨n, rfl⟩
    nlinarith only [hcircle n, sq_nonneg (y n), sq_nonneg (x n + (k : ℝ) / 2 + 1), hC]
  let a : ℝ := ⨅ n, x n
  have hx : Tendsto x atBot (nhds a) := tendsto_atBot_ciInf hmono hbound
  have ha : a ≤ 0 := by
    have h := ciInf_le hbound (0 : ℤ)
    have hx0 : x 0 = 0 := by
      dsimp [x]
      simp [(p6_kfib_def k 0).1]
    simpa only [a, hx0] using h
  let b : ℝ := Real.sqrt (C - (a + (k : ℝ) / 2) ^ 2)
  have hy : Tendsto y atBot (nhds b) := by
    have ht : Tendsto (fun n => Real.sqrt (C - (x n + (k : ℝ) / 2) ^ 2)) atBot (nhds b) :=
      (tendsto_const_nhds.sub ((hx.add tendsto_const_nhds).pow 2)).sqrt
    have heq : (fun n => Real.sqrt (C - (x n + (k : ℝ) / 2) ^ 2)) = y := by
      funext n
      have he : C - (x n + (k : ℝ) / 2) ^ 2 = (y n) ^ 2 := by linarith [hcircle n]
      rw [he, Real.sqrt_sq (le_of_lt (hypos n))]
    rwa [heq] at ht
  have hshift : Tendsto (fun n : ℤ => n + 1) atBot atBot :=
    tendsto_atBot_add_const_right atBot 1 tendsto_id
  have hxshift : Tendsto (fun n : ℤ => x (n + 1)) atBot (nhds a) := hx.comp hshift
  have hyshift : Tendsto (fun n : ℤ => y (n + 1)) atBot (nhds b) := hy.comp hshift
  have hzero : (k : ℝ) * b * b = 0 := by
    have hl : Tendsto (fun n => x (n + 1) - x n) atBot (nhds 0) := by
      simpa using hxshift.sub hx
    have hr : Tendsto (fun n => (k : ℝ) * y n * y (n + 1)) atBot (nhds ((k : ℝ) * b * b)) :=
      (tendsto_const_nhds.mul hy).mul hyshift
    have heq : (fun n => (k : ℝ) * y n * y (n + 1)) = (fun n => x (n + 1) - x n) := by
      funext n
      exact (hstep n).symm
    rw [heq] at hr
    exact tendsto_nhds_unique hr hl
  have hb : b = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact False.elim ((ne_of_gt hkpos) h)
      · exact h
    · exact h
  have hlimcircle : (a + (k : ℝ) / 2) ^ 2 + (0 : ℝ) ^ 2 = ((k : ℝ) ^ 2 + 4) / 4 := by
    have ht : Tendsto (fun n => (x n + (k : ℝ) / 2) ^ 2 + (y n) ^ 2) atBot
        (nhds ((a + (k : ℝ) / 2) ^ 2 + b ^ 2)) :=
      ((hx.add tendsto_const_nhds).pow 2).add (hy.pow 2)
    have heq : (fun n => (x n + (k : ℝ) / 2) ^ 2 + (y n) ^ 2) = (fun _ : ℤ => C) := by
      funext n
      exact hcircle n
    rw [heq] at ht
    have he := tendsto_nhds_unique ht (tendsto_const_nhds : Tendsto (fun _ : ℤ => C) atBot (nhds C))
    simpa only [hb, C] using he
  have haeq : a = -(((k : ℝ) + Real.sqrt ((k : ℝ) ^ 2 + 4)) / 2) := by
    rcases (p6_thm31_feet k a).mp hlimcircle with h | h
    · have hs : 0 < (((k : ℝ) + Real.sqrt ((k : ℝ) ^ 2 + 4)) / 2) := by positivity
      have hp := inv_pos.mpr hs
      rw [← h] at hp
      linarith
    · exact h
  constructor
  · change Tendsto x atBot (nhds _)
    rwa [haeq] at hx
  · change Tendsto y atBot (nhds 0)
    rwa [hb] at hy
end

-- forge:entry p6_prop33_chain kind=proved origin=paper
section
/- Proposition 3.3, chain: translated point (f_{2n+2}/f_{2n+1},1/f_{2n+1}); reflected point with index n is the translated point with index -n-1; they lie on the circle with centre (k/2,0) and radius r_k -/
theorem p6_prop33_chain (k n : ℤ) :
    ((p6_kfib k (2 * n) : ℤ) : ℝ) / ((p6_kfib k (2 * n + 1) : ℤ) : ℝ) + (k : ℝ) =
      ((p6_kfib k (2 * n + 2) : ℤ) : ℝ) / ((p6_kfib k (2 * n + 1) : ℤ) : ℝ) ∧
    -(((p6_kfib k (2 * n) : ℤ) : ℝ) / ((p6_kfib k (2 * n + 1) : ℤ) : ℝ)) =
      ((p6_kfib k (2 * (-n - 1) + 2) : ℤ) : ℝ) /
        ((p6_kfib k (2 * (-n - 1) + 1) : ℤ) : ℝ) ∧
    ((p6_kfib k (2 * n + 1) : ℤ) : ℝ) =
      ((p6_kfib k (2 * (-n - 1) + 1) : ℤ) : ℝ) ∧
    (((p6_kfib k (2 * n + 2) : ℤ) : ℝ) / ((p6_kfib k (2 * n + 1) : ℤ) : ℝ) -
      (k : ℝ) / 2) ^ 2 + (1 / ((p6_kfib k (2 * n + 1) : ℤ) : ℝ)) ^ 2 =
        ((k : ℝ) ^ 2 + 4) / 4 := by
  have hzero := (p6_kfib_def k 0).1
  have hone := (p6_kfib_def k 0).2.1
  have hden : (p6_kfib k (2 * n + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (p6_odd_pos k n))
  have hrec : p6_kfib k (2 * n + 2) =
      k * p6_kfib k (2 * n + 1) + p6_kfib k (2 * n) := by
    simpa only [show 2 * n + 1 + 1 = 2 * n + 2 by ring,
      show 2 * n + 1 - 1 = 2 * n by ring] using
      (p6_kfib_def k (2 * n + 1)).2.2
  have hrecR : (p6_kfib k (2 * n + 2) : ℝ) =
      (k : ℝ) * (p6_kfib k (2 * n + 1) : ℝ) + (p6_kfib k (2 * n) : ℝ) := by
    exact_mod_cast hrec
  have htranslate : (p6_kfib k (2 * n) : ℝ) / (p6_kfib k (2 * n + 1) : ℝ) +
      (k : ℝ) = (p6_kfib k (2 * n + 2) : ℝ) /
        (p6_kfib k (2 * n + 1) : ℝ) := by
    field_simp [hden]
    nlinarith [hrecR]
  have heven : p6_kfib k (2 * (-n - 1) + 2) = -p6_kfib k (2 * n) := by
    have h := p6_lem23_eq10 k 0 (2 * n)
    simpa [hzero, hone, Int.negOnePow_two_mul,
      show 2 * (-n - 1) + 2 = -(2 * n) by ring] using h.symm
  have hodd : p6_kfib k (2 * (-n - 1) + 1) = p6_kfib k (2 * n + 1) := by
    have h := p6_lem23_eq10 k 0 (2 * n + 1)
    simp only [hzero, zero_mul, zero_add, hone, one_mul, zero_sub,
      Int.negOnePow_two_mul_add_one, Units.val_neg, Units.val_one,
      neg_one_mul] at h
    have hind : 2 * (-n - 1) + 1 = -(2 * n + 1) := by ring
    rw [hind]
    linarith
  refine ⟨htranslate, ?_, ?_, ?_⟩
  · rw [heven, hodd]
    simp only [Int.cast_neg, neg_div]
  · rw [hodd]
  · rw [← htranslate]
    convert p6_thm31_circle k n using 1 <;> ring
end

-- forge:entry gr_set_antichain_card_le_half kind=proved origin=conjecture
section
/- For n ≥ 1 an antichain of subsets of [n] has at most 2^(n−1) members — by Sperner (IsAntichain.sperner) |𝒜| ≤ C(n,⌊n/2⌋), and C(n,⌊n/2⌋) ≤ 2^(n−1) for n ≥ 1 since C(n,⌊n/2⌋) = C(n−1,⌊n/2⌋) + C(n−1,⌊n/2⌋−1) ≤ ∑_k C(n−1,k) (the two terms are distinct summands; for n = 1 it is 1 ≤ 1). -/
theorem gr_set_antichain_card_le_half (n : ℕ) (hn : 0 < n)
    (𝒜 : Finset (Finset (Fin n)))
    (h : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset (Fin n)))) :
    𝒜.card ≤ 2 ^ (n - 1) := by
  have hs : 𝒜.card ≤ n.choose (n / 2) := by
    simpa using h.sperner
  cases n with
  | zero => omega
  | succ n =>
    exact hs.trans (by simpa using Nat.choose_succ_le_two_pow n ((n + 1) / 2))
end

-- forge:entry gr_set_inter_closed_eq_univ kind=proved origin=conjecture
section
/- An intersection-closed family containing [n] and all co-singletons is the whole power set — prove S ∈ 𝒜 by induction on |Sᶜ| (Finset.induction on the complement): S = univ is h1, and removing one more point i is S ∩ (univ.erase i). -/
theorem gr_set_inter_closed_eq_univ (n : ℕ) (𝒜 : Finset (Finset (Fin n)))
    (h1 : (Finset.univ : Finset (Fin n)) ∈ 𝒜)
    (h2 : ∀ i : Fin n, (Finset.univ : Finset (Fin n)).erase i ∈ 𝒜)
    (h3 : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ∩ B ∈ 𝒜) : 𝒜 = Finset.univ := by
  classical
  have hc : ∀ T : Finset (Fin n), Tᶜ ∈ 𝒜 := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa using h1
    | @insert i T hi ih =>
        have heq : (insert i T)ᶜ = Tᶜ ∩ (Finset.univ.erase i) := by
          ext j
          simp [and_comm]
        rw [heq]
        exact h3 Tᶜ ih (Finset.univ.erase i) (h2 i)
  have hall : ∀ S : Finset (Fin n), S ∈ 𝒜 := by
    intro S
    simpa using hc Sᶜ
  ext S
  simp only [Finset.mem_univ, iff_true]
  exact hall S
end

-- forge:entry p6_rem34 kind=proved origin=paper
section
/- Remark 3.4: the symmetry (x,y)→(-k-x,y) swaps P_n and P_{-n-1} -/
theorem p6_rem34 (k n : ℤ) : -(k : ℝ) - ((p6_kfib k (2 * n) : ℤ) : ℝ) / ((p6_kfib k (2 * n + 1) : ℤ) : ℝ) = ((p6_kfib k (2 * (-n - 1)) : ℤ) : ℝ) / ((p6_kfib k (2 * (-n - 1) + 1) : ℤ) : ℝ) ∧ 1 / ((p6_kfib k (2 * n + 1) : ℤ) : ℝ) = 1 / ((p6_kfib k (2 * (-n - 1) + 1) : ℤ) : ℝ) := by
  have h := p6_prop33_chain k n
  have htranslate := (p6_prop33_chain k (-n - 1)).1
  constructor
  · linarith [h.2.1]
  · rw [h.2.2.1]
end

-- forge:entry p6_prop33_feet kind=proved origin=paper
section
/- Proposition 3.3, feet: which meets the axis at (σ_k,0) and (-σ_k^{-1},0) -/
theorem p6_prop33_feet (k : ℤ) (x : ℝ) :
    (x - (k : ℝ) / 2) ^ 2 + (0 : ℝ) ^ 2 = ((k : ℝ) ^ 2 + 4) / 4 ↔
      (x = (((k : ℝ) + Real.sqrt ((k : ℝ) ^ 2 + 4)) / 2) ∨
        x = -((((k : ℝ) + Real.sqrt ((k : ℝ) ^ 2 + 4)) / 2)⁻¹)) := by
  have hs : Real.sqrt ((k : ℝ) ^ 2 + 4) ^ 2 = (k : ℝ) ^ 2 + 4 :=
    Real.sq_sqrt (by positivity)
  have hi : ((k : ℝ) - Real.sqrt ((k : ℝ) ^ 2 + 4)) / 2 =
      -((((k : ℝ) + Real.sqrt ((k : ℝ) ^ 2 + 4)) / 2)⁻¹) := by
    have hp : (((k : ℝ) + Real.sqrt ((k : ℝ) ^ 2 + 4)) / 2) *
        (-(((k : ℝ) - Real.sqrt ((k : ℝ) ^ 2 + 4)) / 2)) = 1 := by
      nlinarith [hs]
    have hh := eq_inv_of_mul_eq_one_right hp
    linarith
  rw [← hi]
  constructor
  · intro h
    have hsq : (x - (k : ℝ) / 2) ^ 2 =
        (Real.sqrt ((k : ℝ) ^ 2 + 4) / 2) ^ 2 := by
      nlinarith [hs]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hp | hm
    · left
      linarith
    · right
      linarith
  · rintro (rfl | rfl) <;> nlinarith [hs]
end

-- forge:entry gr_set_sum_card_inter_pairs kind=proved origin=conjecture
section
/- ∑ over ordered pairs (A,B) of subsets of [n] of |A ∩ B| equals n·4^(n−1) — write |A ∩ B| = ∑_i 1[i ∈ A ∧ i ∈ B], swap sums; for fixed i the number of pairs with i in both is 2^(n−1)·2^(n−1). -/
lemma gr_set_sum_card_inter_pairs_aux1 {α : Type*} [Fintype α] [DecidableEq α]
    (a : α) :
    (Finset.univ.filter fun t : Finset α => a ∈ t).card =
      2 ^ (Fintype.card α - 1) := by
  simpa [Finset.Icc_eq_filter_powerset] using
    (Finset.card_Icc_finset (Finset.subset_univ ({a} : Finset α)))

lemma gr_set_sum_card_inter_pairs_aux2 {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) :
    ∑ t : Finset α, (s ∩ t).card = s.card * 2 ^ (Fintype.card α - 1) := by
  apply Finset.sum_card_inter
  intro a ha
  exact gr_set_sum_card_inter_pairs_aux1 a

theorem gr_set_sum_card_inter_pairs (n : ℕ) :
    ∑ p : Finset (Fin n) × Finset (Fin n), (p.1 ∩ p.2).card =
      n * 4 ^ (n - 1) := by
  classical
  rw [Fintype.sum_prod_type]
  simp_rw [gr_set_sum_card_inter_pairs_aux2, Fintype.card_fin]
  rw [← Finset.sum_mul]
  have hsum : (∑ s : Finset (Fin n), s.card) = n * 2 ^ (n - 1) := by
    simpa using
      (gr_set_sum_card_inter_pairs_aux2 (Finset.univ : Finset (Fin n)))
  rw [hsum, mul_assoc, ← mul_pow]
  norm_num
end

-- forge:entry gr_set_intersecting_union_free_quarter kind=proved origin=conjecture
section
/- Daykin–Lovász/Seymour: a family that is both intersecting and co-intersecting has at most 2^(n−2) members — let 𝒰 be the up-closure and 𝒟 the down-closure of 𝒜; 𝒰 is intersecting so |𝒰| ≤ 2^(n−1), 𝒟 is union-free so |𝒟| ≤ 2^(n−1) (cf. gr_set_union_ne_univ_card_le), and by Harris–Kleitman (IsUpperSet.card_inter_le_finset) 2ⁿ·|𝒜| ≤ 2ⁿ·|𝒰 ∩ 𝒟| ≤ |𝒰|·|𝒟| ≤ 4^(n−1)·... giving |𝒜| ≤ 2^(n−2). -/
theorem gr_set_intersecting_union_free_quarter (n : ℕ) (𝒜 : Finset (Finset (Fin n)))
    (h1 : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, (A ∩ B).Nonempty)
    (h2 : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ∪ B ≠ Finset.univ) :
    4 * 𝒜.card ≤ 2 ^ n := by
  classical
  let 𝒰 : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun B => ∃ A ∈ 𝒜, A ⊆ B)
  let 𝒟 : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun B => ∃ A ∈ 𝒜, B ⊆ A)
  have memU (B : Finset (Fin n)) : B ∈ 𝒰 ↔ ∃ A ∈ 𝒜, A ⊆ B := by
    simp [𝒰]
  have memD (B : Finset (Fin n)) : B ∈ 𝒟 ↔ ∃ A ∈ 𝒜, B ⊆ A := by
    simp [𝒟]
  have hU : IsUpperSet (𝒰 : Set (Finset (Fin n))) := by
    intro X Y hXY hX
    obtain ⟨A, hA, hAX⟩ := (memU X).1 hX
    exact (memU Y).2 ⟨A, hA, hAX.trans hXY⟩
  have hD : IsLowerSet (𝒟 : Set (Finset (Fin n))) := by
    intro Y X hXY hY
    obtain ⟨A, hA, hYA⟩ := (memD Y).1 hY
    exact (memD X).2 ⟨A, hA, hXY.trans hYA⟩
  have hUi : (𝒰 : Set (Finset (Fin n))).Intersecting := by
    intro X hX Y hY hd
    obtain ⟨A, hA, hAX⟩ := (memU X).1 hX
    obtain ⟨B, hB, hBY⟩ := (memU Y).1 hY
    obtain ⟨x, hx⟩ := h1 A hA B hB
    exact Finset.disjoint_left.mp hd (hAX (Finset.mem_inter.mp hx).1)
      (hBY (Finset.mem_inter.mp hx).2)
  have hUb : 2 * 𝒰.card ≤ 2 ^ n := by
    simpa using hUi.card_le
  have hDb : 2 * 𝒟.card ≤ 2 ^ n := by
    apply gr_set_union_ne_univ_card_le
    intro X hX Y hY hXY
    obtain ⟨A, hA, hXA⟩ := (memD X).1 hX
    obtain ⟨B, hB, hYB⟩ := (memD Y).1 hY
    apply h2 A hA B hB
    apply Finset.Subset.antisymm (Finset.subset_univ _)
    rw [← hXY]
    exact Finset.union_subset_union hXA hYB
  have hAcard : 𝒜.card ≤ (𝒰 ∩ 𝒟).card := by
    apply Finset.card_le_card
    intro A hA
    exact Finset.mem_inter.mpr
      ⟨(memU A).2 ⟨A, hA, Finset.Subset.refl A⟩,
        (memD A).2 ⟨A, hA, Finset.Subset.refl A⟩⟩
  have hHK : 2 ^ n * (𝒰 ∩ 𝒟).card ≤ 𝒰.card * 𝒟.card := by
    simpa using hU.card_inter_le_finset hD
  have hprod := Nat.mul_le_mul hUb hDb
  have hbase : 2 ^ n * 𝒜.card ≤ 𝒰.card * 𝒟.card :=
    (Nat.mul_le_mul_left (2 ^ n) hAcard).trans hHK
  apply Nat.le_of_mul_le_mul_left (c := 2 ^ n) _ (by positivity)
  nlinarith
end

-- forge:entry p6_arsinh_metallic kind=proved origin=paper
section
/- Proof of Corollary 3.6: arcsinh(k/2) = ln σ_k -/
theorem p6_arsinh_metallic (k : ℤ) :
    Real.arsinh ((k : ℝ) / 2) =
      Real.log (((k : ℝ) + Real.sqrt ((k : ℝ) ^ 2 + 4)) / 2) := by
  unfold Real.arsinh
  have hs : Real.sqrt (1 + ((k : ℝ) / 2) ^ 2) =
      Real.sqrt ((k : ℝ) ^ 2 + 4) / 2 := by
    rw [show 1 + ((k : ℝ) / 2) ^ 2 = ((k : ℝ) ^ 2 + 4) / 4 by ring,
      Real.sqrt_div' _ (by norm_num)]
    norm_num
  rw [hs]
  congr 1
  ring
end

-- forge:entry p6_lem35 kind=proved origin=paper
section
/- Lemma 3.5: p/q, r/s fractions with ps-qr=±1, a>=1 integer, (u,v)=a(r,s)+(p,q); T, T' tangency points of K[p,q],K[r,s] and K[r,s],K[u,v]: d_H(T,T') = 2 arcsinh(a/2) [Tangency points given by formula (1); d_H is Mathlib's hyperbolic distance on the upper half-plane. As printed there are no sign conditions on q, s, v (the formula (1) is used also for q=0 / negative denominators, per the paper's footnote).] -/
lemma p6_lem35_aux1 {K : Type*} [CommRing K] (p q r s a : K)
    (h : (p * s - q * r) ^ 2 = 1) :
    ((p * q + r * s) * (s ^ 2 + (a * s + q) ^ 2) -
      (r * s + (a * r + p) * (a * s + q)) * (q ^ 2 + s ^ 2)) ^ 2 +
      ((s ^ 2 + (a * s + q) ^ 2) - (q ^ 2 + s ^ 2)) ^ 2 =
      a ^ 2 * (q ^ 2 + s ^ 2) * (s ^ 2 + (a * s + q) ^ 2) := by
  calc
    _ = a ^ 2 * (p * s - q * r) ^ 2 * (q ^ 2 - s ^ 2 + a * q * s) ^ 2 +
        a ^ 2 * s ^ 2 * (2 * q + a * s) ^ 2 := by ring
    _ = _ := by rw [h]; ring

lemma p6_lem35_aux2 {K : Type*} [Field K] (p q r s a : K)
    (h : (p * s - q * r) ^ 2 = 1)
    (hD : q ^ 2 + s ^ 2 ≠ 0) (hE : s ^ 2 + (a * s + q) ^ 2 ≠ 0) :
    ((p * q + r * s) / (q ^ 2 + s ^ 2) -
      (r * s + (a * r + p) * (a * s + q)) / (s ^ 2 + (a * s + q) ^ 2)) ^ 2 +
      (1 / (q ^ 2 + s ^ 2) - 1 / (s ^ 2 + (a * s + q) ^ 2)) ^ 2 =
      a ^ 2 * (1 / (q ^ 2 + s ^ 2)) * (1 / (s ^ 2 + (a * s + q) ^ 2)) := by
  calc
    _ = (((p * q + r * s) * (s ^ 2 + (a * s + q) ^ 2) -
        (r * s + (a * r + p) * (a * s + q)) * (q ^ 2 + s ^ 2)) ^ 2 +
        ((s ^ 2 + (a * s + q) ^ 2) - (q ^ 2 + s ^ 2)) ^ 2) /
        ((q ^ 2 + s ^ 2) * (s ^ 2 + (a * s + q) ^ 2)) ^ 2 := by
      rw [div_sub_div _ _ hD hE, div_sub_div _ _ hD hE, div_pow, div_pow, ← add_div]
      ring
    _ = _ := by
      rw [p6_lem35_aux1 p q r s a h]
      field_simp [hD, hE]
      <;> ring

theorem p6_lem35 (p q r s a : ℤ) (ha : 1 ≤ a)
    (h : p * s - q * r = 1 ∨ p * s - q * r = -1) (T T' : UpperHalfPlane)
    (hT : (T : ℂ) = ⟨((p * q + r * s : ℤ) : ℝ) / ((q ^ 2 + s ^ 2 : ℤ) : ℝ),
      1 / ((q ^ 2 + s ^ 2 : ℤ) : ℝ)⟩)
    (hT' : (T' : ℂ) = ⟨((r * s + (a * r + p) * (a * s + q) : ℤ) : ℝ) /
      ((s ^ 2 + (a * s + q) ^ 2 : ℤ) : ℝ),
      1 / ((s ^ 2 + (a * s + q) ^ 2 : ℤ) : ℝ)⟩) :
    dist T T' = 2 * Real.arsinh ((a : ℝ) / 2) := by
  have hdet : ((p : ℝ) * s - q * r) ^ 2 = 1 := by
    have hi : (p * s - q * r) ^ 2 = 1 := by
      rcases h with h | h <;> rw [h] <;> norm_num
    exact_mod_cast hi
  push_cast at hT hT'
  have hTim : T.im = 1 / ((q : ℝ) ^ 2 + (s : ℝ) ^ 2) := by
    simpa only [UpperHalfPlane.coe_im] using congrArg Complex.im hT
  have hTim' : T'.im = 1 / ((s : ℝ) ^ 2 + ((a : ℝ) * s + q) ^ 2) := by
    simpa only [UpperHalfPlane.coe_im] using congrArg Complex.im hT'
  have hD : (q : ℝ) ^ 2 + (s : ℝ) ^ 2 ≠ 0 := by
    intro he
    have hp := T.im_pos
    rw [hTim, he] at hp
    norm_num at hp
  have hE : (s : ℝ) ^ 2 + ((a : ℝ) * s + q) ^ 2 ≠ 0 := by
    intro he
    have hp := T'.im_pos
    rw [hTim', he] at hp
    norm_num at hp
  have hd : dist (T : ℂ) (T' : ℂ) ^ 2 = (a : ℝ) ^ 2 * T.im * T'.im := by
    rw [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply, hTim, hTim', hT, hT']
    simpa only [Complex.sub_re, Complex.sub_im, ← sq] using
      p6_lem35_aux2 (p : ℝ) q r s a hdet hD hE
  have ha0 : 0 ≤ (a : ℝ) / 2 := by positivity
  apply (UpperHalfPlane.dist_eq_iff_eq_sq_sinh
    (mul_nonneg (by norm_num) (Real.arsinh_nonneg_iff.mpr ha0))).2
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.sinh_arsinh, hd]
  field_simp [T.im_ne_zero, T'.im_ne_zero]
  <;> ring
end

-- forge:entry p6_cor36 kind=proved origin=paper
section
/- Corollary 3.6 (Equidistance): d_H(P_m,P_n) = 2|m-n| ln σ_k, m,n in Z -/
lemma p6_cor36_aux1 (f : ℤ → ℝ) (t : ℝ) (h0 : f 0 = 1)
    (hs : ∀ n, f (n + 1) = f n * Real.exp t) (n : ℤ) :
    f n = Real.exp ((n : ℝ) * t) := by
  refine Int.inductionOn' n 0 ?_ ?_ ?_
  · simpa using h0
  · intro n hn ih
    rw [hs, ih, ← Real.exp_add]
    congr 1
    push_cast
    ring
  · intro n hn ih
    apply (mul_left_inj' (Real.exp_ne_zero t)).mp
    calc
      f (n - 1) * Real.exp t = f n := by simpa using (hs (n - 1)).symm
      _ = Real.exp ((n : ℝ) * t) := ih
      _ = Real.exp (((n - 1 : ℤ) : ℝ) * t) * Real.exp t := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring

lemma p6_cor36_aux2 (k : ℤ) (r t : ℝ) (hr : r ^ 2 + (k : ℝ) * r = 1)
    (ht : Real.exp t = (k : ℝ) ^ 2 + 1 + (k : ℝ) * r) (n : ℤ) :
    (p6_kfib k (2 * n + 1) : ℝ) + r * (p6_kfib k (2 * n) : ℝ) =
      Real.exp ((n : ℝ) * t) := by
  apply p6_cor36_aux1 (fun n => (p6_kfib k (2 * n + 1) : ℝ) +
    r * (p6_kfib k (2 * n) : ℝ)) t
  · simp [(p6_kfib_def k 0).1, (p6_kfib_def k 0).2.1]
  · intro j
    have ha : p6_kfib k (2 * (j + 1)) =
        k * p6_kfib k (2 * j + 1) + p6_kfib k (2 * j) := by
      convert (p6_kfib_def k (2 * j + 1)).2.2 using 1 <;> congr 1 <;> ring
    have hb : p6_kfib k (2 * (j + 1) + 1) =
        k * p6_kfib k (2 * (j + 1)) + p6_kfib k (2 * j + 1) := by
      convert (p6_kfib_def k (2 * j + 2)).2.2 using 1 <;> congr 1 <;> ring
    simp only [hb, ha, Int.cast_add, Int.cast_mul]
    rw [ht]
    linear_combination -(k : ℝ) * (p6_kfib k (2 * j) : ℝ) * hr

lemma p6_cor36_aux3 (a b c d k s : ℝ) (hb : b ≠ 0) (hd : d ≠ 0)
    (hm : b ^ 2 - k * a * b - a ^ 2 = 1)
    (hn : d ^ 2 - k * c * d - c ^ 2 = 1)
    (hs : s ^ 2 - k * s = 1) :
    ((a / b - c / d) ^ 2 + (1 / b) ^ 2 + (1 / d) ^ 2) /
      (2 * (1 / b) * (1 / d)) =
    ((b + (s - k) * a) * (d - s * c) +
      (b - s * a) * (d + (s - k) * c)) / 2 := by
  field_simp [hb, hd]
  nlinarith only [congrArg (fun x : ℝ => d ^ 2 * x) hm,
    congrArg (fun x : ℝ => b ^ 2 * x) hn,
    congrArg (fun x : ℝ => 2 * a * b * c * d * x) hs]

theorem p6_cor36 (k : ℤ) (hk : 1 ≤ k) (m n : ℤ) (P Q : UpperHalfPlane)
    (hP : (P : ℂ) = ⟨((p6_kfib k (2 * m) : ℤ) : ℝ) /
      ((p6_kfib k (2 * m + 1) : ℤ) : ℝ),
      1 / ((p6_kfib k (2 * m + 1) : ℤ) : ℝ)⟩)
    (hQ : (Q : ℂ) = ⟨((p6_kfib k (2 * n) : ℤ) : ℝ) /
      ((p6_kfib k (2 * n + 1) : ℤ) : ℝ),
      1 / ((p6_kfib k (2 * n + 1) : ℤ) : ℝ)⟩) :
    dist P Q = 2 * |((m - n : ℤ) : ℝ)| *
      Real.log (((k : ℝ) + Real.sqrt ((k : ℝ) ^ 2 + 4)) / 2) := by
  let s : ℝ := ((k : ℝ) + Real.sqrt ((k : ℝ) ^ 2 + 4)) / 2
  let t : ℝ := 2 * Real.log s
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsqrt := Real.sq_sqrt (show 0 ≤ (k : ℝ) ^ 2 + 4 by positivity)
  have hsqrt0 := Real.sqrt_nonneg ((k : ℝ) ^ 2 + 4)
  have hs0 : 0 < s := by dsimp [s]; linarith
  have hs1 : 1 ≤ s := by
    have : 1 ≤ Real.sqrt ((k : ℝ) ^ 2 + 4) := by nlinarith
    dsimp [s]
    linarith
  have hs : s ^ 2 - (k : ℝ) * s = 1 := by dsimp [s]; nlinarith
  have ht0 : 0 ≤ t := mul_nonneg (by norm_num) (Real.log_nonneg hs1)
  have ht : Real.exp t = s ^ 2 := by
    dsimp [t]
    rw [two_mul, Real.exp_add, Real.exp_log hs0]
    ring
  have htn : Real.exp (-t) = (k : ℝ) ^ 2 + 1 - (k : ℝ) * s := by
    rw [Real.exp_neg, ht]
    apply (mul_right_inj' (pow_ne_zero 2 (ne_of_gt hs0))).mp
    rw [mul_inv_cancel₀ (pow_ne_zero 2 (ne_of_gt hs0))]
    linear_combination ((k : ℝ) * s - 1) * hs
  have heplus (j : ℤ) :
      (p6_kfib k (2 * j + 1) : ℝ) + (s - (k : ℝ)) *
        (p6_kfib k (2 * j) : ℝ) = Real.exp ((j : ℝ) * t) := by
    apply p6_cor36_aux2 k (s - (k : ℝ)) t
    · nlinarith only [hs]
    · rw [ht]
      nlinarith only [hs]
  have heminus (j : ℤ) :
      (p6_kfib k (2 * j + 1) : ℝ) - s *
        (p6_kfib k (2 * j) : ℝ) = Real.exp ((j : ℝ) * (-t)) := by
    convert p6_cor36_aux2 k (-s) (-t) (by nlinarith only [hs])
      (by rw [htn]; ring) j using 1 <;> ring
  have hc (j : ℤ) : (p6_kfib k (2 * j + 1) : ℝ) ^ 2 -
      (k : ℝ) * (p6_kfib k (2 * j) : ℝ) *
        (p6_kfib k (2 * j + 1) : ℝ) - (p6_kfib k (2 * j) : ℝ) ^ 2 = 1 := by
    have hh : p6_kfib k (2 * j + 1) ^ 2 -
        k * p6_kfib k (2 * j) * p6_kfib k (2 * j + 1) -
        p6_kfib k (2 * j) ^ 2 = 1 := by
      simpa only [Int.negOnePow_two_mul, Units.val_one] using p6_lem23_eq9 k (2 * j)
    exact_mod_cast hh
  have hne (j : ℤ) : (p6_kfib k (2 * j + 1) : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (p6_odd_pos k j)
  have hcosh : Real.cosh (dist P Q) = Real.cosh (((m - n : ℤ) : ℝ) * t) := by
    rw [UpperHalfPlane.cosh_dist']
    have hPr := congrArg Complex.re hP
    have hPi := congrArg Complex.im hP
    have hQr := congrArg Complex.re hQ
    have hQi := congrArg Complex.im hQ
    change P.re = _ at hPr
    change P.im = _ at hPi
    change Q.re = _ at hQr
    change Q.im = _ at hQi
    rw [hPr, hPi, hQr, hQi]
    rw [p6_cor36_aux3 _ _ _ _ (k : ℝ) s (hne m) (hne n) (hc m) (hc n) hs]
    rw [heplus, heplus, heminus, heminus, Real.cosh_eq, ← Real.exp_add, ← Real.exp_add]
    congr 2 <;> congr 1 <;> push_cast <;> ring
  have habs : Real.cosh (dist P Q) = Real.cosh (|((m - n : ℤ) : ℝ)| * t) := by
    rw [← Real.cosh_abs (((m - n : ℤ) : ℝ) * t), abs_mul, abs_of_nonneg ht0] at hcosh
    exact hcosh
  have heq := Real.cosh_strictMonoOn.injOn (show dist P Q ∈ Set.Ici 0 from dist_nonneg)
    (show |((m - n : ℤ) : ℝ)| * t ∈ Set.Ici 0 from mul_nonneg (abs_nonneg _) ht0) habs
  change dist P Q = 2 * |((m - n : ℤ) : ℝ)| * Real.log s
  rw [heq]
  dsimp [t]
  ring
end

-- forge:entry p6_prop22_inf_point kind=proved origin=paper
section
/- Proposition 2.2 (Kocik), circle at infinity: First conjunct: formula (1) with (p,q,r,s)=(1,0,r,1) evaluates to (r,1). Second: (r,1) is the unique common point of the line y=1 and K[r,1]. -/
theorem p6_prop22_inf_point (r : ℤ) (x y : ℝ) : (((1 * 0 + r * 1 : ℤ) : ℝ) / ((0 ^ 2 + 1 ^ 2 : ℤ) : ℝ) = r ∧ 1 / ((0 ^ 2 + 1 ^ 2 : ℤ) : ℝ) = (1 : ℝ)) ∧ (y = 1 ∧ (x - r) ^ 2 + (y - 1 / 2) ^ 2 = (1 / 2) ^ 2 ↔ x = r ∧ y = 1) := by
  grind
end

-- forge:entry p6_prop21_inf_tangent kind=proved origin=paper
section
/- Proposition 2.1 (Ford), circle at infinity, tangency: K[r,s] has centre height 1/(2s^2) and radius 1/(2s^2); the line y=1 is tangent to it iff the gap 1 - 1/(2s^2) equals the radius. Determinant written literally for (p,q)=(1,0). -/
theorem p6_prop21_inf_tangent (r s : ℤ) (hs : 0 < s) :
    1 - 1 / (2 * (s : ℝ) ^ 2) = 1 / (2 * (s : ℝ) ^ 2) ↔
      (1 * s - 0 * r = 1 ∨ 1 * s - 0 * r = -1) := by
  have hs0 : (s : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hs)
  constructor
  · intro h
    have hsq : (s : ℝ) ^ 2 = 1 := by
      field_simp [hs0] at h
      nlinarith
    have hsq_int : s ^ 2 = 1 := by
      exact_mod_cast hsq
    simpa only [one_mul, zero_mul, sub_zero] using (sq_eq_one_iff.mp hsq_int)
  · intro h
    have hs1 : s = 1 ∨ s = -1 := by
      simpa only [one_mul, zero_mul, sub_zero] using h
    rcases hs1 with h | h <;> norm_num [h]
end

-- forge:entry p6_prop21_inf_disjoint kind=proved origin=paper
section
/- Proposition 2.1 (Ford), circle at infinity, disjointness: Disjoint from the line y=1 means the radius is smaller than the distance from the centre to the line. -/
theorem p6_prop21_inf_disjoint (r s : ℤ) (hs : 0 < s)
    (hdet : 1 * s - 0 * r ≠ 1) (hdet2 : 1 * s - 0 * r ≠ -1) :
    1 / (2 * (s : ℝ) ^ 2) < 1 - 1 / (2 * (s : ℝ) ^ 2) := by
  have hne : s ≠ 1 := by simpa using hdet
  have hs2 : (2 : ℤ) ≤ s := by omega
  have hsreal : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs2
  have hsq : (4 : ℝ) ≤ (s : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((s : ℝ) - 2)]
  have hden : 0 < 2 * (s : ℝ) ^ 2 := by nlinarith
  have hfrac : 1 / (2 * (s : ℝ) ^ 2) < (1 : ℝ) / 2 := by
    apply (div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)).2
    nlinarith
  linarith
end

-- forge:entry lw_55950 kind=proved origin=external
section
/- If $ x^2-3x+1=0 $ , what is the value of $ x^2 + (1/x)^2? $ -/
theorem lw_55950 (x : ℝ) (hx : x^2 - 3*x + 1 = 0) : x^2 + (1/x)^2 = 7 := by
  grind
end

-- forge:entry lw_8296 kind=proved origin=external
section
/- If $x^2 + 1/x^2 = 3$ , what is the value of $\dfrac{x^2}{(x^2+1)^2}$ ?\nSource: MATHCOUNTS 2012 Chapter #29 -/
theorem lw_8296 (x : ℝ) (h : x^2 + 1/x^2 = 3) : x^2/(x^2 + 1)^2 = 1/5 := by
  grind
end

-- forge:entry lw_12138 kind=disproved origin=external
section
/- Solve the system of equations: \n\n $\\begin{cases} \\frac{x-y}{\\sqrt[3]{x^2y}-\\sqrt[3]{xy^2}}=\\frac 72 \\\\\n \\\\\n\\sqrt[3]{x}-\\sqrt[3]{y}=3\\end{cases}$ -/
theorem lw_12138_disproof : ¬ (∀ (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x ≠ y),
    (x - y) / (x ^ (2 / 3) * y ^ (1 / 3) - x ^ (1 / 3) * y ^ (2 / 3)) = 7 / 2 ∧
      x ^ (1 / 3) - y ^ (1 / 3) = 3 ↔ x = 216 ∧ y = 27) := by
  intro h
  have hsystem := (h 216 27 (by norm_num) (by norm_num) (by norm_num)).mpr
    ⟨rfl, rfl⟩
  norm_num at hsystem
end

end Mathlib2
