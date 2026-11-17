/- Mathlib2 分片 56（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0053
import Mathlib2.Shard.S0054
import Mathlib2.Shard.S0055
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry x2611_14754_nonattacking kind=definition origin=definition
section
def x2611_14754_nonattacking {n d : ℕ} (S : Finset (Fin d → ZMod n)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
    ¬ ∃ v : Fin d → ℤ, x2611_14754_direction d v ∧
      ∃ c : ZMod n, x - y = fun i => c * (v i : ZMod n)
end

-- forge:entry x2611_15512_graph_d kind=definition origin=definition
section
noncomputable def x2611_15512_graph_d {α L R : Type*} [Fintype L] [Fintype R]
    (E : Finset α) (l : α → L) (r : α → R) : MvPolynomial α ℝ := by
  classical
  exact x2611_15512_graph_star E l * x2611_15512_graph_star E r +
    ((∏ a ∈ E, (1 + MvPolynomial.X a)) - 1) *
      ((∑ A ∈ (E.powersetCard 2).filter
          (fun A => (A.image l).card = 2 ∧ (A.image r).card = 2),
        ∏ a ∈ A, MvPolynomial.X a) - ∑ a ∈ E, MvPolynomial.X a)
end

-- forge:entry x2611_16458_blockPolynomialProduct kind=definition origin=definition
section
noncomputable def x2611_16458_blockPolynomialProduct {V : Type*} [Finite V]
    (P N : SimpleGraph V) : Polynomial ℤ := by
  classical
  letI := Fintype.ofFinite V
  exact Finset.prod (Finset.univ.filter (fun S : Set V => x2611_16458_isBlock (P ⊔ N) S))
    (fun S => x2611_16458_zeroFree (P.induce S) (N.induce S))
end

-- forge:entry x2611_15505_R kind=definition origin=definition
section
noncomputable def x2611_15505_R (u r : ℝ) : Polynomial ℝ :=
  (Polynomial.X + Polynomial.C u) * Polynomial.X *
    (Polynomial.X - Polynomial.C 1) *
    (Polynomial.X - Polynomial.C (1 + u + 2 * r))
end

-- forge:entry x2611_15008_parallelClass kind=definition origin=definition
section
def x2611_15008_parallelClass {V E : Type*} (G : Graph V E) (e : E) : Set E :=
  {f | ∃ u v, u ≠ v ∧ G.IsLink e u v ∧ G.IsLink f u v}
end

-- forge:entry x2611_15723_fundamental kind=definition origin=definition
section
def x2611_15723_fundamental (m n : ℕ) (J : Finset ℕ)
    (x : Fin m → ℚ) : ℚ :=
  ∑ w : Fin n → Fin m,
    if Monotone w ∧
        (∀ i j : Fin n, j.val = i.val + 1 → i.val + 1 ∈ J → w i < w j)
    then ∏ i : Fin n, x (w i) else 0
end

-- forge:entry lw_55799 kind=disproved origin=external
section
/- For $ a,b,c,d $ positive, prove: \n\n $$ \frac{2a}{a^2+bc} +\frac{2b}{b^2+cd} +\frac{2c}{c^2+da} +\frac{2d}{d^2+ab}\le \frac{1}{a} +\frac{1}{b} +\frac{1}{c} +\frac{1}{d} $$ \n\n -/
theorem lw_55799_disproof :
    ¬ (∀ (a b c d : ℝ),
      (2 * a / (a ^ 2 + b * c) + 2 * b / (b ^ 2 + c * d) +
        2 * c / (c ^ 2 + d * a) + 2 * d / (d ^ 2 + a * b)) ≤
        1 / a + 1 / b + 1 / c + 1 / d) := by
  intro h
  have hcounter := h 1 0 0 0
  norm_num at hcounter
end

-- forge:entry lw_54556 kind=disproved origin=external
section
/- for a,b,c>0 such that a+b+c=3.prove that $\frac{a}{{{b^2} + {c^2}}} + \frac{b}{{{a^2} + {c^2}}} + \frac{c}{{{b^2} + {a^2}}} \ge \frac{3}{4}(\frac{{{a^2}b + {b^2}c + {c^2}a}}{{{a^2}{b^2} + {b^2}{c^2} + {c^2}{a^2}}} + 1)$ -/
theorem lw_54556_disproof : ¬ (∀ (a b c : ℝ),
    0 < a → 0 < b → 0 < c → a + b + c = 3 →
    (a / (b ^ 2 + c ^ 2) + b / (a ^ 2 + c ^ 2) + c / (b ^ 2 + a ^ 2)) ≥
      (3 / 4) * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) /
        (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) + 1) := by
  intro h
  have hbad := h 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hbad
end

-- forge:entry lw_52672 kind=proved origin=external
section
/- Let $a$ and $b$ be positive real. Prove that $a^2b^2(a^2+b^2-2)\ge(a+b)(ab-1)$ . -/
lemma lw_52672_aux1 (s p : ℝ) (hs : 0 ≤ s) (hp : 0 ≤ p)
    (h : 4 * p ≤ s ^ 2) :
    s * (p - 1) ≤ p ^ 2 * (s ^ 2 - 2 * p - 2) := by
  by_cases hsp : p + 1 ≤ s
  · have hc : 0 ≤ p ^ 2 * (s + p + 1) - p + 1 := by
      have hm := mul_nonneg (sq_nonneg p) (show 0 ≤ s + p by positivity)
      nlinarith [sq_nonneg (p - 1)]
    have hb := sq_nonneg (p ^ 2 - 1)
    have ht := mul_nonneg (sub_nonneg.mpr hsp) hc
    nlinarith only [hb, ht]
  · have hu : 0 ≤ (p - 1) * (2 * p ^ 2 - s) := by
      by_cases hp1 : p ≤ 1
      · have hp2 : p ^ 2 ≤ p := by nlinarith
        have hs2 : (2 * p) ^ 2 ≤ s ^ 2 := by nlinarith
        have ht := (sq_le_sq₀ (show 0 ≤ 2 * p by positivity) hs).mp hs2
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      · have hp2 : p ≤ p ^ 2 := by nlinarith
        exact mul_nonneg (by linarith) (by linarith)
    have ht := mul_nonneg (sq_nonneg p) (sub_nonneg.mpr h)
    nlinarith only [ht, hu]

theorem lw_52672 : ∀ a b : ℝ, a > 0 ∧ b > 0 →
    a ^ 2 * b ^ 2 * (a ^ 2 + b ^ 2 - 2) ≥ (a + b) * (a * b - 1) := by
  intro a b hab
  have h := lw_52672_aux1 (a + b) (a * b)
    (by linarith [hab.1, hab.2])
    (le_of_lt (mul_pos hab.1 hab.2))
    (by nlinarith [sq_nonneg (a - b)])
  nlinarith only [h]
end

-- forge:entry x2611_14754_fourier kind=definition origin=definition
section
noncomputable def x2611_14754_fourier (n d : ℕ) [NeZero n]
    (f : (Fin d → ZMod n) → ℂ) (ξ : Fin d → ZMod n) : ℂ :=
  ∑ x : Fin d → ZMod n, f x * ZMod.stdAddChar (dotProduct ξ x)
end

-- forge:entry x2611_15512_graph_q kind=definition origin=definition
section
noncomputable def x2611_15512_graph_q {α L R : Type*}
    (E : Finset α) (l : α → L) (r : α → R) : MvPolynomial α ℝ := by
  classical
  exact MvPolynomial.C (1 / 4 : ℝ) *
    ∑ A ∈ E.powersetCard 5, ∑ z ∈ A,
      if ((A.erase z).image l).card = 2 ∧ ((A.erase z).image r).card = 2 ∧
          Xor (l z ∈ (A.erase z).image l) (r z ∈ (A.erase z).image r) then
        MvPolynomial.X z *
          ∑ B ∈ ((A.erase z).powersetCard 2).filter
              (fun B => (B.image l).card = 2 ∧ (B.image r).card = 2),
            ((∏ a ∈ B, MvPolynomial.X a) -
              ∏ a ∈ A.erase z \ B, MvPolynomial.X a) ^ 2
      else 0
end

-- forge:entry x2611_15505_F kind=definition origin=definition
section
noncomputable def x2611_15505_F (u r : ℝ) : Polynomial ℝ :=
  Polynomial.C (1 / 30 : ℝ) * Polynomial.X ^ 6 -
  Polynomial.C ((1 + r) / 10) * Polynomial.X ^ 5 -
  Polynomial.C ((u ^ 2 + u + 2 * u * r - 2 * r - 1) / 12) * Polynomial.X ^ 4 +
  Polynomial.C (u * (1 + u + 2 * r) / 6) * Polynomial.X ^ 3
end

-- forge:entry x2611_15008_seriesClass kind=definition origin=definition
section
noncomputable def x2611_15008_seriesClass {V E : Type*} (G : Graph V E) (e : E) : Set E :=
  {f | e ∈ G.edgeSet ∧ f ∈ G.edgeSet ∧ ¬ x2611_15008_bridge G e ∧
    ¬ x2611_15008_bridge G f ∧
    (e = f ∨ x2611_15008_components G < x2611_15008_components (G.deleteEdges {e, f}))}
end

-- forge:entry x2611_12360_noMono kind=definition origin=definition
section
def x2611_12360_noMono (n M : ℕ) (a : ℝ)
    (color : EuclideanSpace ℝ (Fin n) → Prop) : Prop :=
  ∀ x v : EuclideanSpace ℝ (Fin n), ‖v‖ = a →
    ¬ (∀ k : ℕ, k < M → color (x + (k : ℝ) • v))
end

-- forge:entry x2611_15723_psi kind=definition origin=definition
section
def x2611_15723_psi (q : ℚ) (n : ℕ) (J : Finset ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun m =>
    x2611_15723_fundamental m n J (fun i => q ^ i.val))
end

-- forge:entry x2611_14754_auxiliary kind=definition origin=definition
section
def x2611_14754_auxiliary (n d r : ℕ) [NeZero n]
    (y : Fin r → Fin d → ℤ) (x : Fin d → ZMod n) : ℤ :=
  if r ≤ n + 1 then
    ∑ α ∈ Finset.Nat.antidiagonalTuple r (n + 1 - r),
      if x = (fun i => ∑ j : Fin r, (α j : ZMod n) * (y j i : ZMod n))
      then 1 else 0
  else 0
end

-- forge:entry x2611_15008_multipleBridge kind=definition origin=definition
section
noncomputable def x2611_15008_multipleBridge {V E : Type*} (G : Graph V E) (e : E) : Prop :=
  x2611_15008_bridge (G.deleteEdges (x2611_15008_parallelClass G e \ {e})) e
end

-- forge:entry lw_5832 kind=proved origin=external
section
/- Prove that: $ \ln (1+x) \le x-\frac{x^2}{2}+\frac{x^3}{3}, \forall x \ge 0$ -/
theorem lw_5832 (x : ℝ) (hx : 0 ≤ x) : Real.log (1 + x) ≤ x - x^2 / 2 + x^3 / 3 := by
  have hk : ∀ y : ℝ, 0 ≤ y → HasDerivAt
      (fun y : ℝ => y - y ^ 2 / 2 + y ^ 3 / 3 - Real.log (1 + y))
      (y ^ 3 / (1 + y)) y := by
    intro y hy
    have hne : (1 + y) ≠ 0 := by positivity
    have := (((hasDerivAt_id' y).sub ((hasDerivAt_pow 2 y).div_const 2)).add
      ((hasDerivAt_pow 3 y).div_const 3)).sub
      (((hasDerivAt_id' y).const_add 1).log hne)
    convert! this using 1
    field_simp
    ring
  have hmono : MonotoneOn
      (fun y : ℝ => y - y ^ 2 / 2 + y ^ 3 / 3 - Real.log (1 + y))
      (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun y hy => (hk y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact (hk y (le_of_lt hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici, Set.mem_Ioi] at hy
      rw [(hk y hy.le).deriv]
      positivity
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  simp at this
  linarith
end

-- forge:entry lw_55838 kind=proved origin=external
section
/- If the condition is changed to $a, b, c > 0$ and $abc = 1$, prove that $(a + b)(b + c)(c + a) \geq (a + 1)(b + 1)(c + 1)$. -/
lemma lw_55838_aux1 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a * b * c = 1) : 3 ≤ a + b + c := by
  have h := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := (1 / 3 : ℝ)) (w₂ := (1 / 3 : ℝ)) (w₃ := (1 / 3 : ℝ))
    (p₁ := a) (p₂ := b) (p₃ := c)
    (by norm_num) (by norm_num) (by norm_num) ha hb hc (by norm_num)
  have hp : a ^ (1 / 3 : ℝ) * b ^ (1 / 3 : ℝ) * c ^ (1 / 3 : ℝ) = 1 := by
    rw [← Real.mul_rpow ha hb, ← Real.mul_rpow (mul_nonneg ha hb) hc, habc,
      Real.one_rpow]
  rw [hp] at h
  linarith

theorem lw_55838 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a + b) * (b + c) * (c + a) ≥ (a + 1) * (b + 1) * (c + 1) := by
  have hx := lw_55838_aux1 a b c ha.le hb.le hc.le habc
  have hp : (a * b) * (b * c) * (c * a) = 1 := by
    calc
      (a * b) * (b * c) * (c * a) = (a * b * c) ^ 2 := by ring
      _ = 1 := by rw [habc]; norm_num
  have hy := lw_55838_aux1 (a * b) (b * c) (c * a)
    (mul_nonneg ha.le hb.le) (mul_nonneg hb.le hc.le) (mul_nonneg hc.le ha.le) hp
  have hxy := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)
  nlinarith
end

-- forge:entry x2611_12360_notArrow kind=definition origin=definition
section
def x2611_12360_notArrow (n r M : ℕ) (a : ℝ) : Prop :=
  ∃ red : EuclideanSpace ℝ (Fin n) → Prop,
    x2611_12360_noMono n r 1 red ∧
    x2611_12360_noMono n M a (fun x => ¬ red x)
end

end Mathlib2
