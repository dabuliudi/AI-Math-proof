/- Mathlib2 分片 9（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0008
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry ana_sin_le_parabola kind=proved origin=conjecture
section
/- On [0,π] the sine lies below the parabola through (0,0), (π/2,1), (π,0) — by symmetry reduce to [0,π/2]; there h = parabola - sin has h(0)=h(π/2)=0, h'(π/2)=0 and h'' = sin x - 8/π^2 changes sign once, so h' is decreasing then increasing to 0, forcing h to rise then fall, hence h ≥ 0. -/
theorem ana_sin_le_parabola (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.pi) : Real.sin x ≤ 4 * x * (Real.pi - x) / Real.pi ^ 2 := by
  have hpi := Real.pi_gt_three
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 8 / Real.pi ^ 2 := ⟨_, rfl⟩
  have hapos : 0 < a := by rw [ha]; positivity
  have ha1 : a ≤ 1 := by rw [ha, div_le_one (by positivity)]; nlinarith
  have hapi : a * Real.pi ^ 2 = 8 := by rw [ha]; field_simp
  have hf : ∀ t : ℝ, HasDerivAt (fun t : ℝ => 1 - a / 2 * t ^ 2 - Real.cos t) (Real.sin t - a * t) t := by
    intro t
    have := ((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_pow 2 t).const_mul (a / 2))).sub
      (Real.hasDerivAt_cos t)
    convert! this using 1
    norm_num
    ring
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.sin t - a * t) (Real.cos t - a) t := by
    intro t
    have := (Real.hasDerivAt_sin t).sub ((hasDerivAt_id' t).const_mul a)
    convert! this using 1
    ring
  have hfd : Differentiable ℝ (fun t : ℝ => 1 - a / 2 * t ^ 2 - Real.cos t) :=
    fun t => (hf t).differentiableAt
  have hgd : Differentiable ℝ (fun t : ℝ => Real.sin t - a * t) := fun t => (hg t).differentiableAt
  have hderiv : deriv (fun t : ℝ => 1 - a / 2 * t ^ 2 - Real.cos t) = (fun t : ℝ => Real.sin t - a * t) :=
    funext fun t => (hf t).deriv
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Real.arccos a := ⟨_, rfl⟩
  have hcc : Real.cos c = a := by rw [hc]; exact Real.cos_arccos (by linarith) ha1
  have hc0 : 0 ≤ c := by rw [hc]; exact Real.arccos_nonneg a
  have hc2 : c ≤ Real.pi / 2 := by rw [hc]; exact Real.arccos_le_pi_div_two.mpr hapos.le
  have hgmono : MonotoneOn (fun t : ℝ => Real.sin t - a * t) (Set.Icc 0 c) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 c) hgd.continuous.continuousOn hgd.differentiableOn
    intro y hy
    rw [interior_Icc] at hy
    rw [(hg y).deriv]
    have := Real.cos_le_cos_of_nonneg_of_le_pi hy.1.le (by linarith) hy.2.le
    linarith
  have hfmono : MonotoneOn (fun t : ℝ => 1 - a / 2 * t ^ 2 - Real.cos t) (Set.Icc 0 c) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 c) hfd.continuous.continuousOn hfd.differentiableOn
    intro y hy
    rw [interior_Icc] at hy
    rw [(hf y).deriv]
    have h3 : Real.sin 0 - a * 0 ≤ Real.sin y - a * y :=
      hgmono (Set.left_mem_Icc.mpr hc0) ⟨hy.1.le, hy.2.le⟩ hy.1.le
    simpa using h3
  have hganti : AntitoneOn (fun t : ℝ => Real.sin t - a * t) (Set.Icc c (Real.pi / 2)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hgd.continuous.continuousOn hgd.differentiableOn
    intro y hy
    rw [interior_Icc] at hy
    rw [(hg y).deriv]
    have := Real.cos_le_cos_of_nonneg_of_le_pi hc0 (by linarith [hy.2]) hy.1.le
    linarith
  have hconc : ConcaveOn ℝ (Set.Icc c (Real.pi / 2)) (fun t : ℝ => 1 - a / 2 * t ^ 2 - Real.cos t) := by
    apply AntitoneOn.concaveOn_of_deriv (convex_Icc _ _) hfd.continuous.continuousOn hfd.differentiableOn
    rw [hderiv]
    exact hganti.mono interior_subset
  have key : ∀ t : ℝ, 0 ≤ t → t ≤ Real.pi / 2 → Real.cos t ≤ 1 - a / 2 * t ^ 2 := by
    intro t ht0 ht2
    have hfc : 1 - a / 2 * (0:ℝ) ^ 2 - Real.cos 0 ≤ 1 - a / 2 * c ^ 2 - Real.cos c :=
      hfmono (Set.left_mem_Icc.mpr hc0) (Set.right_mem_Icc.mpr hc0) hc0
    simp at hfc
    rcases le_total t c with h | h
    · have h3 : 1 - a / 2 * (0:ℝ) ^ 2 - Real.cos 0 ≤ 1 - a / 2 * t ^ 2 - Real.cos t :=
        hfmono (Set.left_mem_Icc.mpr hc0) ⟨ht0, h⟩ ht0
      simp at h3
      linarith
    · have h3 : min (1 - a / 2 * c ^ 2 - Real.cos c) (1 - a / 2 * (Real.pi / 2) ^ 2 - Real.cos (Real.pi / 2))
          ≤ 1 - a / 2 * t ^ 2 - Real.cos t := hconc.min_le_of_mem_Icc (Set.left_mem_Icc.mpr hc2) (Set.right_mem_Icc.mpr hc2) ⟨h, ht2⟩
      have hend : 1 - a / 2 * (Real.pi / 2) ^ 2 - Real.cos (Real.pi / 2) = 0 := by
        rw [Real.cos_pi_div_two]; nlinarith
      rw [hend] at h3
      have h4 : (0:ℝ) ≤ min (1 - a / 2 * c ^ 2 - Real.cos c) 0 := le_min (by linarith) le_rfl
      linarith
  have hk := key |x - Real.pi / 2| (abs_nonneg _) (abs_le.mpr ⟨by linarith, by linarith⟩)
  rw [Real.cos_abs, Real.cos_sub_pi_div_two, sq_abs] at hk
  have e : 1 - a / 2 * (x - Real.pi / 2) ^ 2 = 4 * x * (Real.pi - x) / Real.pi ^ 2 := by
    rw [ha]; field_simp; ring
  linarith
end

-- forge:entry comb_card_surjective_fin_three kind=proved origin=conjecture
section
/- The number of surjections from an m-set (m = n+1 ≥ 1) onto a 3-set is 3^m - 3·2^m + 3 — inclusion–exclusion over the set of missed values: functions missing value i number 2^m, missing two fixed values number 1. -/
theorem comb_card_surjective_fin_three (n : ℕ) : Fintype.card {f : Fin (n + 1) → Fin 3 // Function.Surjective f} + 3 * 2 ^ (n + 1) = 3 ^ (n + 1) + 3 := by
  classical
  have hB : ∀ S T : Finset (Fin 3), Fintype.piFinset (fun _ : Fin (n + 1) => S) ∩ Fintype.piFinset (fun _ => T) = Fintype.piFinset (fun _ => S ∩ T) := by
    intro S T
    ext f
    simp only [Finset.mem_inter, Fintype.mem_piFinset]
    exact forall_and.symm
  have hc : ∀ S : Finset (Fin 3), (Fintype.piFinset (fun _ : Fin (n + 1) => S)).card = S.card ^ (n + 1) := by
    intro S
    rw [Fintype.card_piFinset]
    simp
  have hU : ∀ X Y Z : Finset (Fin (n + 1) → Fin 3), (X ∪ Y ∪ Z).card + (X ∩ Y).card + ((X ∩ Z) ∪ (Y ∩ Z)).card = X.card + Y.card + Z.card := by
    intro X Y Z
    have h1 := Finset.card_union_add_card_inter X Y
    have h2 := Finset.card_union_add_card_inter (X ∪ Y) Z
    rw [Finset.union_inter_distrib_right] at h2
    omega
  have h3 := hU (Fintype.piFinset (fun _ => Finset.univ.erase 0)) (Fintype.piFinset (fun _ => Finset.univ.erase 1)) (Fintype.piFinset (fun _ => Finset.univ.erase 2))
  have h4 := Finset.card_union_add_card_inter
    (Fintype.piFinset (fun _ : Fin (n + 1) => (Finset.univ.erase 0 ∩ Finset.univ.erase 2 : Finset (Fin 3))))
    (Fintype.piFinset (fun _ : Fin (n + 1) => (Finset.univ.erase 1 ∩ Finset.univ.erase 2 : Finset (Fin 3))))
  have d0 : (Finset.univ.erase 0 : Finset (Fin 3)).card = 2 := by decide
  have d1 : (Finset.univ.erase 1 : Finset (Fin 3)).card = 2 := by decide
  have d2 : (Finset.univ.erase 2 : Finset (Fin 3)).card = 2 := by decide
  have d01 : (Finset.univ.erase 0 ∩ Finset.univ.erase 1 : Finset (Fin 3)).card = 1 := by decide
  have d02 : (Finset.univ.erase 0 ∩ Finset.univ.erase 2 : Finset (Fin 3)).card = 1 := by decide
  have d12 : (Finset.univ.erase 1 ∩ Finset.univ.erase 2 : Finset (Fin 3)).card = 1 := by decide
  have d012 : ((Finset.univ.erase 0 ∩ Finset.univ.erase 2) ∩ (Finset.univ.erase 1 ∩ Finset.univ.erase 2) : Finset (Fin 3)).card = 0 := by decide
  simp only [hB, hc, d0, d1, d2, d01, d02, d12, d012, one_pow, zero_pow (Nat.succ_ne_zero n)] at h3 h4
  have h5 := Finset.card_compl_add_card (Fintype.piFinset (fun _ : Fin (n + 1) => (Finset.univ.erase 0 : Finset (Fin 3))) ∪ Fintype.piFinset (fun _ => Finset.univ.erase 1) ∪ Fintype.piFinset (fun _ => Finset.univ.erase 2))
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h5
  rw [Fintype.card_of_subtype (Fintype.piFinset (fun _ : Fin (n + 1) => (Finset.univ.erase 0 : Finset (Fin 3))) ∪ Fintype.piFinset (fun _ => Finset.univ.erase 1) ∪ Fintype.piFinset (fun _ => Finset.univ.erase 2))ᶜ]
  · generalize 2 ^ (n + 1) = a at *
    generalize 3 ^ (n + 1) = b at *
    omega
  · intro f
    simp only [Finset.mem_compl, Finset.mem_union, Fintype.mem_piFinset, Finset.mem_erase, Finset.mem_univ, and_true, not_or, not_forall, not_not]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2⟩ i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
    · intro hs
      exact ⟨⟨hs 0, hs 1⟩, hs 2⟩
end

-- forge:entry r3_sylvester_nonrepresentable_count_v2_s1h3 kind=proved origin=decomposition
section
/- r3_sylvester_nonrepresentable_count_v2 的证明骨架中第 3 个空洞 -/
theorem r3_sylvester_nonrepresentable_count_v2_s1h3 : ∀ (a b : ℕ), 0 < a → 0 < b → a.Coprime b → ∀ (M : ℕ) (P : ℕ → Prop) [inst : DecidablePred fun (n : ℕ) => ¬P n], (∀ n < M, P n ↔ ¬P (M - 1 - n)) → 2 * {n ∈ Finset.range M | ¬P n}.card = M := by
  intro a b _ _ _ M P inst h
  classical
  have h1 := (Finset.range M).card_filter_add_card_filter_not P
  have h2 : ((Finset.range M).filter (fun n => ¬ P n)).card = ((Finset.range M).filter P).card := by
    refine Finset.card_nbij' (fun n => M - 1 - n) (fun n => M - 1 - n) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hn ⊢
      refine ⟨by omega, ?_⟩
      by_contra hc; exact hn.2 ((h n hn.1).mpr hc)
    · intro n hn
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hn ⊢
      exact ⟨by omega, (h n hn.1).mp hn.2⟩
    · intro n hn
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hn
      show M - 1 - (M - 1 - n) = n
      omega
    · intro n hn
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hn
      show M - 1 - (M - 1 - n) = n
      omega
  rw [Finset.card_range] at h1
  omega
end

-- forge:entry lin_two_by_two_order_three kind=proved origin=conjecture
section
/- A real 2×2 matrix with determinant 1 and trace −1 satisfies A³ = I — by 2×2 Cayley–Hamilton A² + A + I = 0, then A³ − I = (A − I)(A² + A + I) = 0. -/
theorem lin_two_by_two_order_three (A : Matrix (Fin 2) (Fin 2) ℝ) (hd : Matrix.det A = 1) (ht : Matrix.trace A = -1) : A ^ 3 = 1 := by
  have h := Mathlib2.lin_cayley_hamilton_two ℝ A
  rw [hd, ht, one_smul, neg_one_smul, sub_neg_eq_add] at h
  have h2 : A * A = -A - 1 := by
    rw [← sub_eq_zero]; rw [← h]; abel
  have h3 : A ^ 3 = A * (A * A) := by noncomm_ring
  have h4 : A * (-A - 1) = -(A * A) - A := by noncomm_ring
  rw [h3, h2, h4, h2]; abel
end

-- forge:entry r3_wolstenholme_harmonic_s1h3 kind=proved origin=decomposition
section
/- r3_wolstenholme_harmonic 的证明骨架中第 3 个空洞 -/
theorem r3_wolstenholme_harmonic_s1h3_aux1 (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : k ∈ Finset.Icc 1 (p - 1)) :
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

theorem r3_wolstenholme_harmonic_s1h3 : ∀ (p : ℕ), Nat.Prime p → 5 ≤ p → ∀ k ∈ Finset.Icc 1 (p - 1), (↑((p - 1).factorial / (k * (p - k))) : ZMod p) = (↑k : ZMod p)⁻¹ ^ 2 := by
  intro p hp h5 k hk
  haveI := Fact.mk hp
  obtain ⟨m, c, hm, hk0, hm0, hc⟩ := r3_wolstenholme_harmonic_s1h3_aux1 p hp k hk
  have hpk : p - k = m := by omega
  have e3 : k * m * c / (k * m) = c := Nat.mul_div_cancel_left _ (Nat.mul_pos hk0 hm0)
  have hw : ((k * m * c : ℕ) : ZMod p) = -1 := by rw [← hc]; exact ZMod.wilsons_lemma p
  have hs : ((k + m : ℕ) : ZMod p) = 0 := by rw [← hm]; exact ZMod.natCast_self p
  push_cast at hw hs
  have hk0' : (k : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    have := Nat.le_of_dvd hk0 h
    omega
  rw [hpk, hc, e3, inv_pow]
  apply eq_inv_of_mul_eq_one_left
  linear_combination (-1 : ZMod p) * hw + (k : ZMod p) * c * hs
end

-- forge:entry lin_commutator_sq_scalar kind=proved origin=conjecture
section
/- The square of a commutator of 2×2 matrices is the scalar matrix −det(AB−BA)·I — the commutator C has trace 0, so 2×2 Cayley–Hamilton gives C² = −(det C) I. -/
theorem lin_commutator_sq_scalar (R : Type) [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R) : (A * B - B * A) * (A * B - B * A) = (-Matrix.det (A * B - B * A)) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  have h := Mathlib2.lin_cayley_hamilton_two R (A * B - B * A)
  have ht : Matrix.trace (A * B - B * A) = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_mul_comm A B, sub_self]
  rw [ht, zero_smul, sub_zero] at h
  rw [neg_smul]
  exact eq_neg_of_add_eq_zero_left h
end

-- forge:entry r3_sylvester_nonrepresentable_count_v2_s1h1 kind=proved origin=decomposition
section
/- r3_sylvester_nonrepresentable_count_v2 的证明骨架中第 1 个空洞 -/
theorem r3_sylvester_nonrepresentable_count_v2_s1h1 : ∀ (a b : ℕ), 0 < a → 0 < b → a.Coprime b → ∀ n < (a - 1) * (b - 1), (∃ (x : ℕ) (y : ℕ), a * x + b * y = n) → ¬∃ (x : ℕ) (y : ℕ), a * x + b * y = (a - 1) * (b - 1) - 1 - n := by
  intro a b ha hb hab
  have hM : (a - 1) * (b - 1) + a + b = a * b + 1 := by
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  generalize (a - 1) * (b - 1) = M at hM ⊢
  rintro n hn ⟨x, y, h1⟩ ⟨x', y', h2⟩
  have key : a * (x + x' + 1) + b * (y + y' + 1) = a * b := by
    have e : a * x + b * y + (a * x' + b * y') + 1 = M := by omega
    linarith
  have h : b ∣ a * (x + x' + 1) + b * (y + y' + 1) := by rw [key]; exact dvd_mul_left b a
  have hd : b ∣ a * (x + x' + 1) := by
    have h' : b ∣ b * (y + y' + 1) := Nat.dvd_mul_right b _
    first | exact (Nat.dvd_add_left h').mp h | exact (Nat.dvd_add_iff_left h').mpr h | exact (Nat.dvd_add_right h').mp (by rwa [add_comm] at h)
  have hd2 : b ∣ x + x' + 1 := (Nat.Coprime.symm hab).dvd_of_dvd_mul_left hd
  have hle : b ≤ x + x' + 1 := Nat.le_of_dvd (by omega) hd2
  have h3 : a * b ≤ a * (x + x' + 1) := Nat.mul_le_mul_left a hle
  have h4 : 0 < b * (y + y' + 1) := Nat.mul_pos hb (by omega)
  omega
end

-- forge:entry r3_sylvester_nonrepresentable_count_v2_s1h2 kind=proved origin=decomposition
section
/- r3_sylvester_nonrepresentable_count_v2 的证明骨架中第 2 个空洞 -/
theorem r3_sylvester_nonrepresentable_count_v2_s1h2 : ∀ (a b : ℕ), 0 < a → 0 < b → a.Coprime b → ∀ n < (a - 1) * (b - 1), (¬∃ (x : ℕ) (y : ℕ), a * x + b * y = n) → ∃ (x : ℕ) (y : ℕ), a * x + b * y = (a - 1) * (b - 1) - 1 - n := by
  intro a b ha hb hab
  by_cases hb1 : b = 1
  · subst hb1; intro n hn; simp at hn
  have hb2 : 1 < b := by omega
  have hM : (a - 1) * (b - 1) + a + b = a * b + 1 := by
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  generalize (a - 1) * (b - 1) = M at hM ⊢
  intro n hn hrep
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hab hb2
  have hx : m * n % b < b := Nat.mod_lt _ hb
  have h4 : a * (m * n % b) ≡ n [MOD b] := by
    have h1 : a * (m * n % b) ≡ a * (m * n) [MOD b] := Nat.ModEq.mul_left a (Nat.mod_modEq _ _)
    have h3 : a * m * n ≡ 1 * n [MOD b] :=
      Nat.ModEq.mul_right n (by unfold Nat.ModEq; rw [hm, Nat.mod_eq_of_lt hb2])
    rw [← mul_assoc a m n] at h1
    simpa using h1.trans h3
  generalize m * n % b = x at hx h4
  by_cases hle : a * x ≤ n
  · exfalso
    obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hle).mp h4
    exact hrep ⟨x, t, by omega⟩
  · have hlt : n < a * x := by omega
    obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hlt.le).mp h4.symm
    have htpos : t ≠ 0 := by rintro rfl; rw [mul_zero] at ht; omega
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    obtain ⟨d, hd⟩ : ∃ d, b = d + 1 + x := ⟨b - 1 - x, by omega⟩
    have hab' : a * b = a * d + a + a * x := by rw [hd]; ring
    have ht' : a * x = n + b * (t' + 1) := by omega
    have hfin : a * d + b * t' + n + 1 = M := by first | linarith | nlinarith
    exact ⟨d, t', by omega⟩
end

-- forge:entry r3_wolstenholme_harmonic kind=proved origin=conjecture
section
/- Wolstenholme's theorem: for a prime p ≥ 5 the numerator of H_{p-1} is divisible by p^2, stated as p^2 | (p-1)! * (1 + 1/2 + ... + 1/(p-1)) with exact natural-number divisions. Proof idea: pair k with p-k: 1/k + 1/(p-k) = p/(k(p-k)), so 2·S = p·Σ (p-1)!/(k(p-k)); modulo p the inner sum is -(p-1)!·Σ k^{-2} ≡ -(p-1)!·Σ_{j=1}^{p-1} j^2 = -(p-1)!·(p-1)p(2p-1)/6 ≡ 0 for p ≥ 5 (inversion permutes the units of ZMod p); finally p odd lets one cancel the 2. -/
theorem r3_wolstenholme_harmonic (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) : p ^ 2 ∣ ∑ k ∈ Finset.Icc 1 (p - 1), (p - 1).factorial / k := by
  have H : (∀ k ∈ Finset.Icc 1 (p - 1), (p - 1).factorial / k + (p - 1).factorial / (p - k) = p * ((p - 1).factorial / (k * (p - k))))
      ∧ (∑ k ∈ Finset.Icc 1 (p - 1), (p - 1).factorial / (p - k) = ∑ k ∈ Finset.Icc 1 (p - 1), (p - 1).factorial / k)
      ∧ (∀ k ∈ Finset.Icc 1 (p - 1), (((p - 1).factorial / (k * (p - k)) : ℕ) : ZMod p) = ((k : ZMod p)⁻¹) ^ 2)
      ∧ (∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 2 = 0) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · (first | exact @Mathlib2.r3_wolstenholme_harmonic_s1h1 p hp h5 | exact Mathlib2.r3_wolstenholme_harmonic_s1h1 | apply Mathlib2.r3_wolstenholme_harmonic_s1h1 <;> assumption | simpa using Mathlib2.r3_wolstenholme_harmonic_s1h1)
    · (first | exact @Mathlib2.r3_wolstenholme_harmonic_s1h2 p hp h5 | exact Mathlib2.r3_wolstenholme_harmonic_s1h2 | apply Mathlib2.r3_wolstenholme_harmonic_s1h2 <;> assumption | simpa using Mathlib2.r3_wolstenholme_harmonic_s1h2)
    · (first | exact @Mathlib2.r3_wolstenholme_harmonic_s1h3 p hp h5 | exact Mathlib2.r3_wolstenholme_harmonic_s1h3 | apply Mathlib2.r3_wolstenholme_harmonic_s1h3 <;> assumption | simpa using Mathlib2.r3_wolstenholme_harmonic_s1h3)
    · (first | exact @Mathlib2.r3_wolstenholme_harmonic_s1h4 p hp h5 | exact Mathlib2.r3_wolstenholme_harmonic_s1h4 | apply Mathlib2.r3_wolstenholme_harmonic_s1h4 <;> assumption | simpa using Mathlib2.r3_wolstenholme_harmonic_s1h4)
  obtain ⟨h1, h2, h3, h4⟩ := H
  have hT : p ∣ ∑ k ∈ Finset.Icc 1 (p - 1), (p - 1).factorial / (k * (p - k)) := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sum, Finset.sum_congr rfl h3, h4]
  have h2S : 2 * ∑ k ∈ Finset.Icc 1 (p - 1), (p - 1).factorial / k = p * ∑ k ∈ Finset.Icc 1 (p - 1), (p - 1).factorial / (k * (p - k)) := by
    rw [two_mul]; nth_rewrite 2 [← h2]; rw [← Finset.sum_add_distrib, Finset.sum_congr rfl h1, Finset.mul_sum]
  obtain ⟨c, hc⟩ := hT
  have hd : p ^ 2 ∣ 2 * ∑ k ∈ Finset.Icc 1 (p - 1), (p - 1).factorial / k := by
    rw [h2S, hc]; exact ⟨c, by ring⟩
  have hodd : Nat.Coprime (p ^ 2) 2 := by
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_primes hp Nat.prime_two]; omega
  exact hodd.dvd_of_dvd_mul_left hd
end

-- forge:entry r3_sylvester_nonrepresentable_count_v2 kind=proved origin=conjecture
section
/- Sylvester's theorem (1884): for coprime positive a, b the set of natural numbers not of the form ax+by (x,y ≥ 0) is finite with exactly (a-1)(b-1)/2 elements. Mathlib has only the Frobenius number (frobeniusNumber_pair), not the count. Proof idea: every n has a unique representation n = ax+by with 0 ≤ x < b, y ∈ ℤ, and n is representable iff y ≥ 0; hence everything ≥ (a-1)(b-1) is representable, and for 0 ≤ n ≤ ab-a-b the reflection n ↦ ab-a-b-n (sending (x,y) to (b-1-x, -1-y)) swaps representable and non-representable numbers, so exactly half of range((a-1)(b-1)) is non-representable. -/
theorem r3_sylvester_nonrepresentable_count_v2 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) : ∃ S : Finset ℕ, (∀ n : ℕ, n ∈ S ↔ ¬ ∃ x y : ℕ, a * x + b * y = n) ∧ 2 * S.card = (a - 1) * (b - 1) := by
  classical
  have h1 : ∀ n : ℕ, (a - 1) * (b - 1) ≤ n → ∃ x y : ℕ, a * x + b * y = n := by
    intro n hn
    obtain ⟨x, y, h⟩ := Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le a b n
      (by rw [Nat.Coprime.gcd_eq_one hab]; exact one_dvd _) (by first | exact hn | simpa using hn)
    exact ⟨x, y, by linarith⟩
  have H : (∀ n : ℕ, n < (a-1)*(b-1) → (∃ x y : ℕ, a * x + b * y = n) → ¬ ∃ x y : ℕ, a * x + b * y = (a-1)*(b-1) - 1 - n)
     ∧ (∀ n : ℕ, n < (a-1)*(b-1) → (¬ ∃ x y : ℕ, a * x + b * y = n) → ∃ x y : ℕ, a * x + b * y = (a-1)*(b-1) - 1 - n)
     ∧ (∀ (M : ℕ) (P : ℕ → Prop) [DecidablePred fun n => ¬ P n], (∀ n < M, P n ↔ ¬ P (M - 1 - n)) → 2 * ((Finset.range M).filter (fun n => ¬ P n)).card = M) := by
    clear h1
    refine ⟨?_, ?_, ?_⟩
    · (first | exact @Mathlib2.r3_sylvester_nonrepresentable_count_v2_s1h1 a b ha hb hab | exact Mathlib2.r3_sylvester_nonrepresentable_count_v2_s1h1 | apply Mathlib2.r3_sylvester_nonrepresentable_count_v2_s1h1 <;> assumption | simpa using Mathlib2.r3_sylvester_nonrepresentable_count_v2_s1h1)
    · (first | exact @Mathlib2.r3_sylvester_nonrepresentable_count_v2_s1h2 a b ha hb hab | exact Mathlib2.r3_sylvester_nonrepresentable_count_v2_s1h2 | apply Mathlib2.r3_sylvester_nonrepresentable_count_v2_s1h2 <;> assumption | simpa using Mathlib2.r3_sylvester_nonrepresentable_count_v2_s1h2)
    · (first | exact @Mathlib2.r3_sylvester_nonrepresentable_count_v2_s1h3 a b ha hb hab | exact Mathlib2.r3_sylvester_nonrepresentable_count_v2_s1h3 | apply Mathlib2.r3_sylvester_nonrepresentable_count_v2_s1h3 <;> assumption | simpa using Mathlib2.r3_sylvester_nonrepresentable_count_v2_s1h3)
  obtain ⟨h2, h3, h4⟩ := H
  refine ⟨(Finset.range ((a-1)*(b-1))).filter (fun n => ¬ ∃ x y : ℕ, a * x + b * y = n), ?_, ?_⟩
  · intro n
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      by_contra hlt
      exact h (h1 n (by omega))
  · apply h4
    intro n hn
    constructor
    · exact h2 n hn
    · intro h; by_contra h'; exact h (h3 n hn h')
end

-- forge:entry comb_sum_mul_choose_sq kind=proved origin=conjecture
section
/- ∑_k k·C(n,k)² = n·C(2n-1,n-1) — use k·C(n,k) = n·C(n-1,k-1) and C(n,k) = C(n,n-k), then Vandermonde (Nat.add_choose_eq) for ∑ C(n-1,k-1)·C(n,n-k) = C(2n-1,n-1). -/
theorem comb_sum_mul_choose_sq (n : ℕ) : ∑ k ∈ Finset.range (n + 1), k * (n.choose k) ^ 2 = n * (2 * n - 1).choose (n - 1) := by
  rcases n with _ | m
  · simp
  · have e1 : 2 * (m + 1) - 1 = m + (m + 1) := by omega
    have e2 : m + 1 - 1 = m := by omega
    have hV : (m + (m + 1)).choose m = ∑ k ∈ Finset.range (m + 1), m.choose k * (m + 1).choose (m - k) := by
      rw [Nat.add_choose_eq]
      exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => m.choose i * (m + 1).choose j) m
    rw [Finset.sum_range_succ', e1, e2, hV, Finset.mul_sum]
    simp only [Nat.zero_mul, Nat.add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have h1 : (m + 1) * m.choose k = (m + 1).choose (k + 1) * (k + 1) := Nat.add_one_mul_choose_eq m k
    have h2 : (m + 1).choose (m - k) = (m + 1).choose (k + 1) := by
      rw [← Nat.choose_symm (by omega : k + 1 ≤ m + 1)]
      congr 1
      omega
    rw [h2, sq, ← mul_assoc (m + 1), h1]
    ring
end

-- forge:entry lin_symm_nilpotent_eq_zero kind=proved origin=conjecture
section
/- A nilpotent real symmetric matrix is zero — for symmetric B, B² = BᵀB = 0 forces B = 0 (sum of squares of entries); apply repeatedly to A^(2^m) with 2^m ≥ k, noting powers of a symmetric matrix are symmetric. -/
theorem lin_symm_nilpotent_eq_zero (n k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hs : A.IsSymm) (h : A ^ k = 0) : A = 0 := by
  induction k with
  | zero =>
    rw [pow_zero] at h
    rw [← mul_one A, h, mul_zero]
  | succ k ih =>
    cases k with
    | zero => simpa using h
    | succ k =>
      apply ih
      have h2 : (A ^ (k + 1)).conjTranspose * A ^ (k + 1) = 0 := by
        rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_pow, hs.eq, ← pow_add]
        have : k + 1 + (k + 1) = (k + 1 + 1) + k := by ring
        rw [this, pow_add, h, zero_mul]
      exact Matrix.conjTranspose_mul_self_eq_zero.mp h2
end

-- forge:entry alg_isunit_one_sub_mul_comm kind=proved origin=conjecture
section
/- In any ring, if 1 - ab is a unit then so is 1 - ba — if c is the inverse of 1 - ab then 1 + b*c*a is a two-sided inverse of 1 - ba. -/
theorem alg_isunit_one_sub_mul_comm (R : Type*) [Ring R] (a b : R) (h : IsUnit (1 - a * b)) : IsUnit (1 - b * a) := by
  obtain ⟨u, hu⟩ := h
  have h1 : (1 - a * b) * (↑u⁻¹ : R) = 1 := by rw [← hu]; exact u.mul_inv
  have h2 : (↑u⁻¹ : R) * (1 - a * b) = 1 := by rw [← hu]; exact u.inv_mul
  have e1 : (1 - b * a) * (1 + b * (↑u⁻¹ : R) * a) = 1 + b * ((1 - a * b) * (↑u⁻¹ : R) - 1) * a := by
    noncomm_ring
  have e2 : (1 + b * (↑u⁻¹ : R) * a) * (1 - b * a) = 1 + b * ((↑u⁻¹ : R) * (1 - a * b) - 1) * a := by
    noncomm_ring
  rw [h1] at e1
  rw [h2] at e2
  simp only [sub_self, mul_zero, zero_mul, add_zero] at e1 e2
  exact ⟨⟨_, _, e1, e2⟩, rfl⟩
end

-- forge:entry lin_idempotent_join kind=proved origin=conjecture
section
/- For commuting idempotent matrices A, B the join A + B − AB is idempotent — it equals I − (I − A)(I − B), a product of commuting idempotents; or expand and rewrite with the three hypotheses. -/
theorem lin_idempotent_join (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A * A = A) (hB : B * B = B) (hAB : A * B = B * A) : (A + B - A * B) * (A + B - A * B) = A + B - A * B := by
  have e : A + B - A * B = 1 - (1 - A) * (1 - B) := by noncomm_ring
  have hA' : IsIdempotentElem A := hA
  have hB' : IsIdempotentElem B := hB
  have hc : Commute (1 - A) (1 - B) :=
    (Commute.one_left _).sub_left ((Commute.one_right A).sub_right hAB)
  have := (IsIdempotentElem.mul_of_commute hc hA'.one_sub hB'.one_sub).one_sub
  rw [e]
  exact this.eq
end

-- forge:entry alg_perm_fin_center_eq_bot kind=proved origin=conjecture
section
/- The center of the symmetric group S_n is trivial for n ≥ 3 — if σ i = j ≠ i pick k ∉ {i, j}; then σ does not commute with the transposition swap j k. -/
theorem alg_perm_fin_center_eq_bot (n : ℕ) (hn : 3 ≤ n) : Subgroup.center (Equiv.Perm (Fin n)) = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra hall
    push_neg at hall
    exact hne (Equiv.ext hall)
  have hv : (σ i).val ≠ i.val := fun h => hi (Fin.ext h)
  have : ∃ m : ℕ, m < n ∧ m ≠ i.val ∧ m ≠ (σ i).val := by
    by_cases h0 : 0 ≠ i.val ∧ 0 ≠ (σ i).val
    · exact ⟨0, by omega, h0.1, h0.2⟩
    by_cases h1 : 1 ≠ i.val ∧ 1 ≠ (σ i).val
    · exact ⟨1, by omega, h1.1, h1.2⟩
    exact ⟨2, by omega, by omega, by omega⟩
  obtain ⟨m, hm, hmi, hms⟩ := this
  have hki : (⟨m, hm⟩ : Fin n) ≠ i := fun h => hmi (congrArg Fin.val h)
  have hks : (⟨m, hm⟩ : Fin n) ≠ σ i := fun h => hms (congrArg Fin.val h)
  have hc := Subgroup.mem_center_iff.mp hσ (Equiv.swap (σ i) ⟨m, hm⟩)
  have := congrArg (fun f : Equiv.Perm (Fin n) => f i) hc
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at this
  rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hi) (Ne.symm hki)] at this
  exact hks this
end

-- forge:entry alg_x_pow_four_add_one_not_irreducible_zmod kind=proved origin=conjecture
section
/- X^4 + 1 is reducible modulo every prime — for p = 2 it is (X+1)^4; for odd p one of -1, 2, -2 is a square mod p (Legendre symbol multiplicativity), giving (X²+a)(X²-a), (X²+bX+1)(X²-bX+1) or (X²+cX-1)(X²-cX-1). -/
open Polynomial

lemma alg_x_pow_four_add_one_not_irreducible_zmod_aux1 (F : Type) [Field F] (a b c d : F) :
    ¬ Irreducible ((X ^ 2 + C a * X + C b) * (X ^ 2 + C c * X + C d) : F[X]) := by
  intro h
  have d1 : (X ^ 2 + C a * X + C b : F[X]).natDegree = 2 := by compute_degree!
  have d2 : (X ^ 2 + C c * X + C d : F[X]).natDegree = 2 := by compute_degree!
  rcases h.isUnit_or_isUnit rfl with u | u
  · have := Polynomial.natDegree_eq_zero_of_isUnit u; omega
  · have := Polynomial.natDegree_eq_zero_of_isUnit u; omega

theorem alg_x_pow_four_add_one_not_irreducible_zmod (p : ℕ) [Fact p.Prime] : ¬ Irreducible (Polynomial.X ^ 4 + 1 : Polynomial (ZMod p)) := by
  have c2 : (C (2 : ZMod p) : (ZMod p)[X]) = 2 := map_ofNat C 2
  by_cases h1 : IsSquare (-1 : ZMod p)
  · obtain ⟨r, hr⟩ := h1
    have e : (X ^ 4 + 1 : (ZMod p)[X]) = (X ^ 2 + C 0 * X + C r) * (X ^ 2 + C 0 * X + C (-r)) := by
      have : (X ^ 4 + 1 : (ZMod p)[X]) = X ^ 4 - C (r * r) := by rw [← hr]; simp
      rw [this]; simp only [C_mul, C_neg, C_0]; ring
    rw [e]; exact alg_x_pow_four_add_one_not_irreducible_zmod_aux1 _ _ _ _ _
  by_cases h2 : IsSquare (2 : ZMod p)
  · obtain ⟨r, hr⟩ := h2
    have e : (X ^ 4 + 1 : (ZMod p)[X]) = (X ^ 2 + C r * X + C 1) * (X ^ 2 + C (-r) * X + C 1) := by
      have : (X ^ 4 + 1 : (ZMod p)[X]) = X ^ 4 + (2 - C (r * r)) * X ^ 2 + 1 := by rw [← hr]; simp [c2]
      rw [this]; simp only [C_mul, C_neg, C_1]; ring
    rw [e]; exact alg_x_pow_four_add_one_not_irreducible_zmod_aux1 _ _ _ _ _
  have q1 := quadraticChar_neg_one_iff_not_isSquare.mpr h1
  have q2 := quadraticChar_neg_one_iff_not_isSquare.mpr h2
  have q3 : quadraticChar (ZMod p) (-2) = 1 := by
    have : (-2 : ZMod p) = (-1) * 2 := by ring
    rw [this, map_mul, q1, q2]; norm_num
  have hne : (-2 : ZMod p) ≠ 0 := by
    intro h0; rw [h0] at q3; simp at q3
  obtain ⟨r, hr⟩ := (quadraticChar_one_iff_isSquare hne).mp q3
  have e : (X ^ 4 + 1 : (ZMod p)[X]) = (X ^ 2 + C r * X + C (-1)) * (X ^ 2 + C (-r) * X + C (-1)) := by
    have : (X ^ 4 + 1 : (ZMod p)[X]) = X ^ 4 + (-2 - C (r * r)) * X ^ 2 + 1 := by rw [← hr]; simp [c2]
    rw [this]; simp only [C_mul, C_neg, C_1]; ring
  rw [e]; exact alg_x_pow_four_add_one_not_irreducible_zmod_aux1 _ _ _ _ _
end

-- forge:entry comb_card_involutions_rec kind=proved origin=conjecture
section
/- The number a(n) of involutions (σ² = 1) in S_n satisfies a(n+2) = a(n+1) + (n+1)·a(n) — split on whether σ fixes the last point (restrict to Fin (n+1)) or swaps it with one of the n+1 others (remove both points, leaving an involution of an n-set). -/
open Equiv Equiv.Perm

theorem comb_card_involutions_rec_aux1 (n : ℕ) (e : Perm (Fin n)) :
    (decomposeFin.symm ((0 : Fin (n + 1)), e)) * (decomposeFin.symm (0, e)) = 1 ↔ e * e = 1 := by
  constructor
  · intro h
    refine Equiv.ext fun x => ?_
    have h2 := Equiv.Perm.congr_fun h x.succ
    simp only [Perm.mul_apply, Perm.one_apply, decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply] at h2
    exact Fin.succ_injective _ h2
  · intro hee
    refine Equiv.ext fun y => ?_
    refine Fin.cases ?_ (fun x => ?_) y
    · simp only [Perm.mul_apply, Perm.one_apply, decomposeFin_symm_apply_zero]
    · have hee' : e (e x) = x := Equiv.Perm.congr_fun hee x
      simp only [Perm.mul_apply, Perm.one_apply, decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply, hee']

theorem comb_card_involutions_rec_aux2 (n : ℕ) (r : Fin n) (e : Perm (Fin n)) :
    (decomposeFin.symm (r.succ, e)) * (decomposeFin.symm (r.succ, e)) = 1 ↔ e r = r ∧ e * e = 1 := by
  constructor
  · intro h
    have h1 := Equiv.Perm.congr_fun h 0
    simp only [Perm.mul_apply, Perm.one_apply, decomposeFin_symm_apply_zero, decomposeFin_symm_apply_succ] at h1
    have her : e r = r := by
      have h1' := congrArg (Equiv.swap 0 r.succ) h1
      rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at h1'
      exact Fin.succ_injective _ h1'
    refine ⟨her, Equiv.ext fun x => ?_⟩
    by_cases hx : x = r
    · subst hx
      simp [her]
    · have hex : e x ≠ r := fun hc => hx (e.injective (hc.trans her.symm))
      have h2 := Equiv.Perm.congr_fun h x.succ
      rw [Perm.mul_apply, decomposeFin_symm_apply_succ,
        Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun hc => hex (Fin.succ_injective _ hc)),
        decomposeFin_symm_apply_succ] at h2
      have h3 := congrArg (Equiv.swap 0 r.succ) h2
      rw [Equiv.swap_apply_self, Perm.one_apply,
        Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun hc => hx (Fin.succ_injective _ hc))] at h3
      exact Fin.succ_injective _ h3
  · rintro ⟨her, hee⟩
    refine Equiv.ext fun y => ?_
    rw [Perm.mul_apply, Perm.one_apply]
    refine Fin.cases ?_ (fun x => ?_) y
    · rw [decomposeFin_symm_apply_zero, decomposeFin_symm_apply_succ, her, Equiv.swap_apply_right]
    · by_cases hx : x = r
      · subst hx
        rw [decomposeFin_symm_apply_succ, her, Equiv.swap_apply_right, decomposeFin_symm_apply_zero]
      · have hex : e x ≠ r := fun hc => hx (e.injective (hc.trans her.symm))
        have hee' : e (e x) = x := Equiv.Perm.congr_fun hee x
        rw [decomposeFin_symm_apply_succ,
          Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun hc => hex (Fin.succ_injective _ hc)),
          decomposeFin_symm_apply_succ, hee',
          Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun hc => hx (Fin.succ_injective _ hc))]

theorem comb_card_involutions_rec_aux3 (n : ℕ) (q : Fin (n + 1)) :
    (Finset.univ.filter (fun e : Perm (Fin (n + 1)) => e q = q ∧ e * e = 1)).card
      = (Finset.univ.filter (fun e : Perm (Fin n) => e * e = 1)).card := by
  have hs : Equiv.swap 0 q * Equiv.swap 0 q = 1 := Equiv.swap_mul_self 0 q
  have ha : (Finset.univ.filter (fun e : Perm (Fin (n + 1)) => e q = q ∧ e * e = 1)).card
      = (Finset.univ.filter (fun e : Perm (Fin (n + 1)) => e 0 = 0 ∧ e * e = 1)).card := by
    refine Finset.card_nbij' (fun e => Equiv.swap 0 q * e * Equiv.swap 0 q) (fun e => Equiv.swap 0 q * e * Equiv.swap 0 q) ?_ ?_ ?_ ?_
    · intro e he
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at he ⊢
      refine ⟨by simp [he.1], ?_⟩
      rw [show Equiv.swap 0 q * e * Equiv.swap 0 q * (Equiv.swap 0 q * e * Equiv.swap 0 q)
        = Equiv.swap 0 q * (e * (Equiv.swap 0 q * Equiv.swap 0 q) * e) * Equiv.swap 0 q by group,
        hs, mul_one, he.2, mul_one, hs]
    · intro e he
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at he ⊢
      refine ⟨by simp [he.1], ?_⟩
      rw [show Equiv.swap 0 q * e * Equiv.swap 0 q * (Equiv.swap 0 q * e * Equiv.swap 0 q)
        = Equiv.swap 0 q * (e * (Equiv.swap 0 q * Equiv.swap 0 q) * e) * Equiv.swap 0 q by group,
        hs, mul_one, he.2, mul_one, hs]
    · intro e _
      show Equiv.swap 0 q * (Equiv.swap 0 q * e * Equiv.swap 0 q) * Equiv.swap 0 q = e
      rw [show Equiv.swap 0 q * (Equiv.swap 0 q * e * Equiv.swap 0 q) * Equiv.swap 0 q
        = (Equiv.swap 0 q * Equiv.swap 0 q) * e * (Equiv.swap 0 q * Equiv.swap 0 q) by group, hs, one_mul, mul_one]
    · intro e _
      show Equiv.swap 0 q * (Equiv.swap 0 q * e * Equiv.swap 0 q) * Equiv.swap 0 q = e
      rw [show Equiv.swap 0 q * (Equiv.swap 0 q * e * Equiv.swap 0 q) * Equiv.swap 0 q
        = (Equiv.swap 0 q * Equiv.swap 0 q) * e * (Equiv.swap 0 q * Equiv.swap 0 q) by group, hs, one_mul, mul_one]
  rw [ha]
  symm
  refine Finset.card_bij (fun e _ => decomposeFin.symm (0, e)) ?_ ?_ ?_
  · intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨Finset.mem_univ _, decomposeFin_symm_apply_zero _ _, (comb_card_involutions_rec_aux1 n e).2 he.2⟩
  · intro a _ b _ hab
    simpa using decomposeFin.symm.injective hab
  · intro σ hσ
    rw [Finset.mem_filter] at hσ
    obtain ⟨⟨p, e⟩, rfl⟩ := decomposeFin.symm.surjective σ
    have h0 := hσ.2.1
    rw [decomposeFin_symm_apply_zero] at h0
    subst h0
    exact ⟨e, Finset.mem_filter.2 ⟨Finset.mem_univ _, (comb_card_involutions_rec_aux1 n e).1 hσ.2.2⟩, rfl⟩

theorem comb_card_involutions_rec (n : ℕ) : Fintype.card {σ : Equiv.Perm (Fin (n + 2)) // σ * σ = 1} = Fintype.card {σ : Equiv.Perm (Fin (n + 1)) // σ * σ = 1} + (n + 1) * Fintype.card {σ : Equiv.Perm (Fin n) // σ * σ = 1} := by
  rw [Fintype.card_of_subtype (Finset.univ.filter (fun e : Perm (Fin (n + 1)) => e * e = 1)) (by simp),
    Fintype.card_of_subtype (Finset.univ.filter (fun e : Perm (Fin n) => e * e = 1)) (by simp),
    Fintype.card_congr ((decomposeFin (n := n + 1)).subtypeEquiv
      (q := fun pe => decomposeFin.symm pe * decomposeFin.symm pe = 1) (by intro a; simp)),
    Fintype.card_of_subtype (Finset.univ.filter (fun pe : Fin (n + 2) × Perm (Fin (n + 1)) =>
      decomposeFin.symm pe * decomposeFin.symm pe = 1)) (by simp),
    Finset.card_filter, Fintype.sum_prod_type, Fin.sum_univ_succ]
  have h0 : (∑ e : Perm (Fin (n + 1)), if decomposeFin.symm ((0 : Fin (n + 2)), e) * decomposeFin.symm (0, e) = 1 then 1 else 0)
      = (Finset.univ.filter (fun e : Perm (Fin (n + 1)) => e * e = 1)).card := by
    rw [← Finset.card_filter]
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact comb_card_involutions_rec_aux1 (n + 1) e
  have h1 : ∀ r : Fin (n + 1), (∑ e : Perm (Fin (n + 1)), if decomposeFin.symm (r.succ, e) * decomposeFin.symm (r.succ, e) = 1 then 1 else 0)
      = (Finset.univ.filter (fun e : Perm (Fin n) => e * e = 1)).card := by
    intro r
    rw [← Finset.card_filter, ← comb_card_involutions_rec_aux3 n r]
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact comb_card_involutions_rec_aux2 (n + 1) r e
  rw [h0, Finset.sum_congr rfl (fun r _ => h1 r)]
  simp
end

-- forge:entry lin_gram_det_eq_zero_iff kind=proved origin=conjecture
section
/- The Gram determinant of two vectors vanishes exactly when they are linearly dependent — the determinant is ‖x‖²‖y‖² − ⟨x,y⟩²; use the equality case of Cauchy–Schwarz (inner_mul_inner_self_le with equality iff one vector is a multiple of the other) and LinearIndependent.pair_iff. -/
theorem lin_gram_det_eq_zero_iff (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (x y : V) : Matrix.det !![inner ℝ x x, inner ℝ x y; inner ℝ y x, inner ℝ y y] = 0 ↔ ¬ LinearIndependent ℝ ![x, y] := by
  rw [Matrix.det_fin_two_of]
  by_cases hx : x = 0
  · subst hx
    simp only [inner_zero_left, inner_zero_right, zero_mul, sub_zero, true_iff]
    intro h
    exact h.ne_zero 0 rfl
  · rw [LinearIndependent.pair_iff' hx]
    push_neg
    have hxx : inner ℝ x x ≠ 0 := fun h => hx (inner_self_eq_zero.mp h)
    constructor
    · intro h
      refine ⟨inner ℝ x y / inner ℝ x x, ?_⟩
      have hz : inner ℝ (y - (inner ℝ x y / inner ℝ x x) • x) (y - (inner ℝ x y / inner ℝ x x) • x) = (0:ℝ) := by
        simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, real_inner_comm x y] at h ⊢
        simp only [conj_trivial]
        field_simp
        linarith
      have := inner_self_eq_zero.mp hz
      exact (sub_eq_zero.mp this).symm
    · rintro ⟨a, rfl⟩
      simp only [inner_smul_left, inner_smul_right, conj_trivial]
      ring
end

-- forge:entry comb_exists_block_sum_dvd kind=proved origin=conjecture
section
/- Among any n integers a_0..a_{n-1} some nonempty consecutive block has sum divisible by n — the n+1 prefix sums S_0..S_n take two equal values mod n by pigeonhole; their difference is a block sum (Finset.sum_Ico_eq_sub). -/
theorem comb_exists_block_sum_dvd (n : ℕ) (hn : 0 < n) (a : ℕ → ℤ) : ∃ i j : ℕ, i < j ∧ j ≤ n ∧ (n : ℤ) ∣ ∑ k ∈ Finset.Ico i j, a k := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have key : ∀ i j : ℕ, i < j → j ∈ Finset.range (n + 1) →
      ((∑ k ∈ Finset.range i, a k : ℤ) : ZMod n) = ((∑ k ∈ Finset.range j, a k : ℤ) : ZMod n) →
      ∃ i j : ℕ, i < j ∧ j ≤ n ∧ (n : ℤ) ∣ ∑ k ∈ Finset.Ico i j, a k := by
    intro i j hij hj h
    refine ⟨i, j, hij, Nat.lt_succ_iff.1 (Finset.mem_range.1 hj), ?_⟩
    rw [Finset.sum_Ico_eq_sub _ hij.le]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ n).1 h
  obtain ⟨x, hx, y, hy, hxy, hf⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (n + 1)) (t := (Finset.univ : Finset (ZMod n)))
    (f := fun i => ((∑ k ∈ Finset.range i, a k : ℤ) : ZMod n))
    (by simp [ZMod.card]) (fun _ _ => Finset.mem_univ _)
  rcases lt_or_gt_of_ne hxy with h | h
  · exact key x y h hy hf
  · exact key y x h hx hf.symm
end

-- forge:entry alg_card_range_sq_zmod_prime kind=proved origin=conjecture
section
/- For an odd prime p there are exactly (p+1)/2 squares in ZMod p — the squaring map is 2-to-1 on nonzero elements (x² = y² iff x = ±y and x ≠ -x), plus 0. -/
theorem alg_card_range_sq_zmod_prime (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : Nat.card (Set.range (fun x : ZMod p => x ^ 2)) = (p + 1) / 2 := by
  classical
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  set S := Finset.univ.image (fun x : ZMod p => x ^ 2) with hS
  have hcard : Nat.card (Set.range (fun x : ZMod p => x ^ 2)) = S.card := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', Set.toFinset_range]
  have h0 : (0 : ZMod p) ∈ S := Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by simp⟩
  have hfib : ∀ b ∈ S, (Finset.univ.filter (fun a : ZMod p => a ^ 2 = b)).card
      + (if b = 0 then 1 else 0) = 2 := by
    intro b hb
    by_cases hb0 : b = 0
    · subst hb0
      simp [Finset.filter_eq']
    · obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hb
      have hsq : IsSquare b := ⟨y, by rw [← hy]; ring⟩
      have hq := (quadraticChar_one_iff_isSquare hb0).mpr hsq
      have hc := quadraticChar_card_sqrts hchar b
      rw [hq] at hc
      simp only [Set.toFinset_setOf] at hc
      rw [if_neg hb0]
      norm_num at hc ⊢
      exact_mod_cast hc
  have hsum : (Finset.univ : Finset (ZMod p)).card
      = ∑ b ∈ S, (Finset.univ.filter (fun a : ZMod p => a ^ 2 = b)).card :=
    Finset.card_eq_sum_card_fiberwise (f := fun x : ZMod p => x ^ 2)
      (fun x _ => Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ x)))
  have h2 := Finset.sum_congr rfl hfib
  rw [Finset.sum_add_distrib, ← hsum, Finset.sum_ite_eq', if_pos h0, Finset.card_univ, ZMod.card,
    Finset.sum_const, smul_eq_mul] at h2
  rw [hcard]; omega
end

end Mathlib2
