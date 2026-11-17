/- Mathlib2 分片 48（forge 自动维护，追加式）。 -/
import Mathlib
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry lw_50221 kind=proved origin=external
section
/- Let $a,b,c$ be the sides of a triangle. Prove that $\frac{a^{3}}{b^{2}}+\frac{b^{3}}{c^{2}}+\frac{c^{3}}{a^{2}}\geq \frac{a}{c}(a+b-c)+\frac{c}{b}(c+a-b)+\frac{b}{a}(b+c-a)$ . -/
lemma lw_50221_aux1 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ (x+z)^5 * (x+y+2*z)^2 + (x+y+z)^5 * (x+z)^2 + (x+y+2*z)^5 * (x+y+z)^2
      - (x+z)^3 * (x+y+z)^2 * (x+y+2*z) * ((x+z) + (x+y+z) - (x+y+2*z))
      - (x+y+2*z)^3 * (x+z)^2 * (x+y+z) * ((x+y+2*z) + (x+z) - (x+y+z))
      - (x+y+z)^3 * (x+y+2*z)^2 * (x+z) * ((x+y+z) + (x+y+2*z) - (x+z)) := by
  ring_nf
  positivity

lemma lw_50221_aux2 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ (x+z)^5 * (x+y+z)^2 + (x+y+2*z)^5 * (x+z)^2 + (x+y+z)^5 * (x+y+2*z)^2
      - (x+z)^3 * (x+y+2*z)^2 * (x+y+z) * ((x+z) + (x+y+2*z) - (x+y+z))
      - (x+y+z)^3 * (x+z)^2 * (x+y+2*z) * ((x+y+z) + (x+z) - (x+y+2*z))
      - (x+y+2*z)^3 * (x+y+z)^2 * (x+z) * ((x+y+2*z) + (x+y+z) - (x+z)) := by
  calc
    0 ≤ 3*y*z^2*(y^2-z^2)^2 + (3 * x^5 * y^2
          + 3 * x^5 * y * z
          + 3 * x^5 * z^2
          + 10 * x^4 * y^3
          + 21 * x^4 * y^2 * z
          + 21 * x^4 * y * z^2
          + 20 * x^4 * z^3
          + 14 * x^3 * y^4
          + 44 * x^3 * y^3 * z
          + 50 * x^3 * y^2 * z^2
          + 60 * x^3 * y * z^3
          + 54 * x^3 * z^4
          + 11 * x^2 * y^5
          + 46 * x^2 * y^4 * z
          + 60 * x^2 * y^3 * z^2
          + 50 * x^2 * y^2 * z^3
          + 87 * x^2 * y * z^4
          + 73 * x^2 * z^5
          + 5 * x * y^6
          + 27 * x * y^5 * z
          + 46 * x * y^4 * z^2
          + 23 * x * y^3 * z^3
          + 18 * x * y^2 * z^4
          + 63 * x * y * z^5
          + 49 * x * z^6
          + y^7
          + 7 * y^6 * z
          + 14 * y^5 * z^2
          + 14 * y^4 * z^3
          + 3 * y^3 * z^4
          + 15 * y * z^6
          + 13 * z^7) := by positivity
    _ = _ := by ring

lemma lw_50221_aux3 (a b c : ℝ)
    (hab : 0 ≤ a + b - c) (hbc : 0 ≤ b + c - a) (hca : 0 ≤ a + c - b) :
    0 ≤ (a)^5 * (c)^2 + (b)^5 * (a)^2 + (c)^5 * (b)^2
      - (a)^3 * (b)^2 * (c) * ((a) + (b) - (c))
      - (c)^3 * (a)^2 * (b) * ((c) + (a) - (b))
      - (b)^3 * (c)^2 * (a) * ((b) + (c) - (a)) := by
  wlog hmin : a ≤ b ∧ a ≤ c generalizing a b c
  · rcases le_total b c with h | h
    · have hb : b ≤ a := by grind
      convert this b c a hbc (by linarith) (by linarith) ⟨h, hb⟩ using 1 <;> ring
    · have hc : c ≤ a := by grind
      convert this c a b (by linarith) hab (by linarith) ⟨hc, h⟩ using 1 <;> ring
  rcases le_total b c with h | h
  · convert lw_50221_aux1 (a+b-c) (b-a) (c-b) hab
      (sub_nonneg.mpr hmin.1) (sub_nonneg.mpr h) using 1 <;> ring
  · convert lw_50221_aux2 (a+c-b) (c-a) (b-c) hca
      (sub_nonneg.mpr hmin.2) (sub_nonneg.mpr h) using 1 <;> ring

theorem lw_50221 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0)
    (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) :
    a^3 / b^2 + b^3 / c^2 + c^3 / a^2 ≥
      a / c * (a + b - c) + c / b * (c + a - b) + b / a * (b + c - a) := by
  have ha : a ≠ 0 := ne_of_gt hx.1
  have hb : b ≠ 0 := ne_of_gt hx.2.1
  have hc : c ≠ 0 := ne_of_gt hx.2.2
  have hd : 0 < a^2 * b^2 * c^2 := by positivity
  have hp := lw_50221_aux3 a b c (by linarith) (by linarith) (by linarith)
  have heq : (a^3 / b^2 + b^3 / c^2 + c^3 / a^2 -
      (a / c * (a + b - c) + c / b * (c + a - b) + b / a * (b + c - a))) *
      (a^2 * b^2 * c^2) = (a)^5 * (c)^2 + (b)^5 * (a)^2 + (c)^5 * (b)^2
      - (a)^3 * (b)^2 * (c) * ((a) + (b) - (c))
      - (c)^3 * (a)^2 * (b) * ((c) + (a) - (b))
      - (b)^3 * (c)^2 * (a) * ((b) + (c) - (a)) := by
    field_simp
    <;> ring
  apply sub_nonneg.mp
  apply (mul_nonneg_iff_of_pos_right hd).mp
  rw [heq]
  exact hp
end

-- forge:entry lw_53529 kind=proved origin=external
section
/- Let $ a,b \in [0,1] .$ Prove that\n$$\frac{2}{\sqrt{3}}-\frac{1}{3} \leq \frac{2a}{b+1}+\frac{b}{3a+1}+(1-a)(1-b) \leq 2$$\n$$\sqrt{3}-\frac{3}{4}\leq\frac{3a}{b+1}+\frac{b}{2a+1}+(1-a)(1-b) \leq 3$$ -/
lemma lw_53529_aux1 (a c d : ℝ) (ha : a ∈ Set.Icc 0 1)
    (hc : 2 ≤ c) (hd : 1 ≤ d) :
    AntitoneOn (fun b : ℝ => c * a / (b + 1) + b / (d * a + 1) +
      (1 - a) * (1 - b)) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  have hda : 0 < d * a + 1 := by nlinarith [mul_nonneg (by linarith : 0 ≤ d) ha.1]
  have hxp : 0 < x + 1 := by linarith [hx.1]
  have hyp : 0 < y + 1 := by linarith [hy.1]
  have hp : 0 < (x + 1) * (y + 1) := mul_pos hxp hyp
  have hp4 : (x + 1) * (y + 1) ≤ 4 := by
    nlinarith [hy.2, mul_nonneg (sub_nonneg.mpr hx.2) (le_of_lt hyp)]
  have hda2 : d * a + 1 ≤ 2 * d := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ d) (sub_nonneg.mpr ha.2)]
  have h1 : (1 : ℝ) / 2 ≤ c / ((x + 1) * (y + 1)) := by
    apply (le_div_iff₀ hp).2
    nlinarith
  have h2 : (1 : ℝ) / 2 ≤ d / (d * a + 1) := by
    apply (le_div_iff₀ hda).2
    linarith
  have hn : 0 ≤ a * (y - x) *
      (c / ((x + 1) * (y + 1)) + d / (d * a + 1) - 1) :=
    mul_nonneg (mul_nonneg ha.1 (sub_nonneg.mpr hxy)) (by linarith)
  have he :
      (c * a / (x + 1) + x / (d * a + 1) + (1 - a) * (1 - x)) -
      (c * a / (y + 1) + y / (d * a + 1) + (1 - a) * (1 - y)) =
      a * (y - x) * (c / ((x + 1) * (y + 1)) + d / (d * a + 1) - 1) := by
    field_simp [ne_of_gt hxp, ne_of_gt hyp, ne_of_gt hda]
    ring_nf
    field_simp [show 1 + a * d ≠ 0 by nlinarith [hda]]
    <;> ring
  linarith

lemma lw_53529_aux2 (a : ℝ) (ha : 0 ≤ a) :
    2 / Real.sqrt 3 - 1 / 3 ≤ a + 1 / (3 * a + 1) := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hd : 0 < 3 * a + 1 := by linarith
  have he : 2 / Real.sqrt 3 = 2 * Real.sqrt 3 / 3 := by
    apply (div_eq_iff (ne_of_gt hs)).2
    nlinarith
  rw [he]
  have h : (2 * Real.sqrt 3 / 3 - 1 / 3) * (3 * a + 1) ≤
      a * (3 * a + 1) + 1 := by
    nlinarith [sq_nonneg (3 * a + 1 - Real.sqrt 3)]
  have he2 : a + 1 / (3 * a + 1) = (a * (3 * a + 1) + 1) / (3 * a + 1) := by
    field_simp
  rw [he2]
  exact (le_div_iff₀ hd).2 h

lemma lw_53529_aux3 (a : ℝ) (ha : 0 ≤ a) :
    Real.sqrt 3 - 3 / 4 ≤ 3 * a / 2 + 1 / (2 * a + 1) := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hd : 0 < 2 * a + 1 := by linarith
  have h : (Real.sqrt 3 - 3 / 4) * (2 * a + 1) ≤
      (3 * a / 2) * (2 * a + 1) + 1 := by
    nlinarith [sq_nonneg (3 * a + 3 / 2 - Real.sqrt 3)]
  have he : 3 * a / 2 + 1 / (2 * a + 1) =
      ((3 * a / 2) * (2 * a + 1) + 1) / (2 * a + 1) := by
    field_simp
  rw [he]
  exact (le_div_iff₀ hd).2 h

theorem lw_53529 : ∀ a b : ℝ, a ∈ Set.Icc 0 1 ∧ b ∈ Set.Icc 0 1 →
    (2 / Real.sqrt 3 - 1 / 3) ≤
      (2 * a / (b + 1) + b / (3 * a + 1) + (1 - a) * (1 - b)) ∧
    (2 * a / (b + 1) + b / (3 * a + 1) + (1 - a) * (1 - b)) ≤ 2 ∧
    (Real.sqrt 3 - 3 / 4) ≤
      (3 * a / (b + 1) + b / (2 * a + 1) + (1 - a) * (1 - b)) ∧
    (3 * a / (b + 1) + b / (2 * a + 1) + (1 - a) * (1 - b)) ≤ 3 := by
  intro a b ⟨ha, hb⟩
  have hf := lw_53529_aux1 a 2 3 ha (by norm_num) (by norm_num)
  have hg := lw_53529_aux1 a 3 2 ha (by norm_num) (by norm_num)
  have h01 : (0 : ℝ) ∈ Set.Icc 0 1 := by constructor <;> norm_num
  have h11 : (1 : ℝ) ∈ Set.Icc 0 1 := by constructor <;> norm_num
  have hflo := hf hb h11 hb.2
  have hfhi := hf h01 hb hb.1
  have hglo := hg hb h11 hb.2
  have hghi := hg h01 hb hb.1
  norm_num at hflo hfhi hglo hghi
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (lw_53529_aux2 a ha.1).trans (by simpa only [one_div] using hflo)
  · nlinarith [hfhi, ha.2]
  · exact (lw_53529_aux3 a ha.1).trans (by simpa only [one_div] using hglo)
  · nlinarith [hghi, ha.2]
end

-- forge:entry lw_965 kind=proved origin=external
section
/- Given $a,b,c\in R^+$, prove that $\prod_{cyc}\left(a+\frac {1}{a+1}\right)\geqslant\frac {27}{8}$ given that $abc=1$. -/
lemma lw_965_aux1 (x : ℝ) (hx : 0 < x) :
    9 * x ≤ 4 * (x + 1 / (x + 1)) ^ 2 := by
  have hden : x + 1 ≠ 0 := ne_of_gt (by positivity)
  have hid : 4 * (x + 1 / (x + 1)) ^ 2 - 9 * x =
      (x - 1) ^ 2 * (4 * x ^ 2 + 7 * x + 4) / (x + 1) ^ 2 := by
    field_simp
    <;> ring
  have hnonneg : 0 ≤ (x - 1) ^ 2 * (4 * x ^ 2 + 7 * x + 4) /
      (x + 1) ^ 2 := by positivity
  linarith

theorem lw_965 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (habc : a * b * c = 1) :
    (a + 1 / (a + 1)) * (b + 1 / (b + 1)) * (c + 1 / (c + 1)) ≥ 27 / 8 := by
  have hprod : (729 : ℝ) ≤ 64 *
      ((a + 1 / (a + 1)) * (b + 1 / (b + 1)) * (c + 1 / (c + 1))) ^ 2 := by
    calc
      (729 : ℝ) = 729 * (a * b * c) := by rw [habc]; norm_num
      _ = (9 * a) * (9 * b) * (9 * c) := by ring
      _ ≤ (4 * (a + 1 / (a + 1)) ^ 2) *
          (4 * (b + 1 / (b + 1)) ^ 2) *
          (4 * (c + 1 / (c + 1)) ^ 2) :=
        mul_le_mul
          (mul_le_mul (lw_965_aux1 a ha) (lw_965_aux1 b hb)
            (by positivity) (by positivity))
          (lw_965_aux1 c hc) (by positivity) (by positivity)
      _ = _ := by ring
  have hsquare : (27 / 8 : ℝ) ^ 2 ≤
      ((a + 1 / (a + 1)) * (b + 1 / (b + 1)) * (c + 1 / (c + 1))) ^ 2 := by
    linarith only [hprod]
  apply (mul_self_le_mul_self_iff (by norm_num : (0 : ℝ) ≤ 27 / 8)
    (by positivity : 0 ≤ (a + 1 / (a + 1)) * (b + 1 / (b + 1)) *
      (c + 1 / (c + 1)))).2
  nlinarith only [hsquare]
end

-- forge:entry lw_6289 kind=proved origin=external
section
/- If k=1 ,we get an old problem of canhang2007 \n $ \frac {ab}{(a + b)^2} + \frac {bc}{(b + c)^2} + \frac {ca}{(c + a)^2} \le \frac {1}{4} + \frac {4abc}{(a + b)(b + c)(c + a)}$ (Vo Quoc Ba Can) -/
lemma lw_6289_aux1 (a b : ℝ) : a * b / (a + b) ^ 2 ≤ 1 / 4 := by
  by_cases h : a + b = 0
  · simp [h]
  · apply (div_le_iff₀ (sq_pos_of_ne_zero h)).2
    nlinarith [sq_nonneg (a - b)]

lemma lw_6289_aux2 (a b c : ℝ) (hab : a + b = 0) :
    a * b / (a + b) ^ 2 + b * c / (b + c) ^ 2 + c * a / (c + a) ^ 2 ≤ 1 / 4 := by
  by_cases hbc : b + c = 0
  · simpa [hab, hbc] using lw_6289_aux1 c a
  by_cases hca : c + a = 0
  · simpa [hab, hca] using lw_6289_aux1 b c
  have hb : b = -a := by linarith
  subst b
  have hid : (-a) * c / (-a + c) ^ 2 + c * a / (c + a) ^ 2 =
      -(4 * a ^ 2 * c ^ 2 / ((-a + c) ^ 2 * (c + a) ^ 2)) := by
    field_simp
    <;> ring
  simp only [add_neg_cancel, zero_pow (by norm_num : 2 ≠ 0), div_zero, zero_add]
  rw [hid]
  have hnonneg : 0 ≤ 4 * a ^ 2 * c ^ 2 / ((-a + c) ^ 2 * (c + a) ^ 2) := by
    positivity
  linarith

theorem lw_6289 (a b c : ℝ) :
    (a * b / (a + b) ^ 2 + b * c / (b + c) ^ 2 + c * a / (c + a) ^ 2) ≤
      1 / 4 + (4 * a * b * c) / (a + b) / (b + c) / (c + a) := by
  by_cases hab : a + b = 0
  · simpa [hab] using lw_6289_aux2 a b c hab
  by_cases hbc : b + c = 0
  · have h := lw_6289_aux2 b c a hbc
    simp [hbc] at h ⊢
    linarith
  by_cases hca : c + a = 0
  · have h := lw_6289_aux2 c a b hca
    simp [hca] at h ⊢
    linarith
  have hid :
      1 / 4 + (4 * a * b * c) / (a + b) / (b + c) / (c + a) -
        (a * b / (a + b) ^ 2 + b * c / (b + c) ^ 2 + c * a / (c + a) ^ 2) =
      ((a - b) * (b - c) * (c - a)) ^ 2 /
        (4 * (a + b) ^ 2 * (b + c) ^ 2 * (c + a) ^ 2) := by
    field_simp
    <;> ring
  have hnonneg : 0 ≤ ((a - b) * (b - c) * (c - a)) ^ 2 /
      (4 * (a + b) ^ 2 * (b + c) ^ 2 * (c + a) ^ 2) := by
    positivity
  linarith
end

-- forge:entry lw_9702 kind=disproved origin=external
section
/- $(a+b+c)(a^2b+b^2c+c^2a-abc)\ge \sum_{cyc}ab(c^2+ab)$ -/
theorem lw_9702_disproof : ¬ (∀ (a b c : ℝ),
    (a + b + c) * (a^2 * b + b^2 * c + c^2 * a - a * b * c) ≥
      a * b * (c^2 + a * b) + b * c * (a^2 + b * c) +
        c * a * (b^2 + c * a)) := by
  intro h
  have hbad := h 1 (-1) 0
  norm_num at hbad
end

-- forge:entry lw_10479 kind=proved origin=external
section
/- By Trivial Inequality, $(a-b)^2\ge 0\Longleftrightarrow a^2 + b^2 \ge 2ab \Longleftrightarrow 1\ge \frac{2ab}{a^2 + b^2}\Longleftrightarrow 3\ge \sum_{cyc}{\frac{2ab}{a^2 + b^2}}$ -/
lemma lw_10479_aux1 (a b : ℝ) : 2 * a * b / (a ^ 2 + b ^ 2) ≤ 1 := by
  apply div_le_one_of_le₀
  · nlinarith [sq_nonneg (a - b)]
  · exact add_nonneg (sq_nonneg a) (sq_nonneg b)

theorem lw_10479 : ∀ a b c : ℝ, 3 ≥ 2 * a * b / (a ^ 2 + b ^ 2) + 2 * b * c / (b ^ 2 + c ^ 2) + 2 * c * a / (c ^ 2 + a ^ 2) := by
  intro a b c
  have hab := lw_10479_aux1 a b
  have hbc := lw_10479_aux1 b c
  have hca := lw_10479_aux1 c a
  linarith
end

-- forge:entry lw_1076 kind=proved origin=external
section
/- Note that for any reals $a, b, c, d$ we have $(a^2+b^2+c^2+d^2)^2+16abcd\geq 2(a+c)^2(b+d)^2$ -/
theorem lw_1076 (a b c d : ℝ) :
    (a^2+b^2+c^2+d^2)^2+16*a*b*c*d ≥ 2*(a+c)^2*(b+d)^2 := by
  nlinarith [sq_nonneg (a^2 + c^2 - b^2 - d^2),
    mul_nonneg (sq_nonneg (a-c)) (sq_nonneg (b-d))]
end

-- forge:entry lw_12165 kind=proved origin=external
section
/- Let $a, b, c > 0$ and $a + b + c = 1$. Prove that:\n$$\frac{a}{\sqrt{(c+a)(a+b)}}+\frac{b}{\sqrt{(a+b)(b+c)}}+\frac{c}{\sqrt{(b+c)(c+a)}}\le \frac {3}{2}.$$ -/
lemma lw_12165_aux1 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    2 / Real.sqrt (x * y) ≤ 1 / x + 1 / y := by
  have hspos : 0 < Real.sqrt (x * y) := Real.sqrt_pos.2 (mul_pos hx hy)
  have hs : Real.sqrt (x * y) ^ 2 = x * y := Real.sq_sqrt (le_of_lt (mul_pos hx hy))
  have hsum : 2 * Real.sqrt (x * y) ≤ x + y := by
    rw [Real.sqrt_mul (le_of_lt hx)]
    nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y),
      Real.sq_sqrt (le_of_lt hx), Real.sq_sqrt (le_of_lt hy)]
  apply (div_le_iff₀ hspos).2
  apply (mul_le_mul_iff_left₀ (mul_pos hx hy)).mp
  have hid : ((1 / x + 1 / y) * Real.sqrt (x * y)) * (x * y) =
      (x + y) * Real.sqrt (x * y) := by
    field_simp [ne_of_gt hx, ne_of_gt hy]
    <;> ring
  rw [hid]
  nlinarith [mul_le_mul_of_nonneg_right hsum (le_of_lt hspos)]

lemma lw_12165_aux2 (a x y : ℝ) (ha : 0 ≤ a) (hx : 0 < x) (hy : 0 < y) :
    2 * (a / Real.sqrt (x * y)) ≤ a / x + a / y := by
  calc
    2 * (a / Real.sqrt (x * y)) = a * (2 / Real.sqrt (x * y)) := by ring
    _ ≤ a * (1 / x + 1 / y) := mul_le_mul_of_nonneg_left (lw_12165_aux1 x y hx hy) ha
    _ = a / x + a / y := by ring

theorem lw_12165 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a + b + c = 1) :
    a / (Real.sqrt ((a + c) * (a + b))) +
      b / (Real.sqrt ((a + b) * (b + c))) +
      c / (Real.sqrt ((b + c) * (a + c))) ≤ 3 / 2 := by
  have habpos : 0 < a + b := add_pos ha hb
  have hacpos : 0 < a + c := add_pos ha hc
  have hbcpos : 0 < b + c := add_pos hb hc
  have h1 := lw_12165_aux2 a (a + c) (a + b) ha.le hacpos habpos
  have h2 := lw_12165_aux2 b (a + b) (b + c) hb.le habpos hbcpos
  have h3 := lw_12165_aux2 c (b + c) (a + c) hc.le hbcpos hacpos
  have h4 : a / (a + c) + a / (a + b) +
      (b / (a + b) + b / (b + c)) +
      (c / (b + c) + c / (a + c)) = 3 := by
    field_simp
    <;> ring
  linarith
end

-- forge:entry lw_56592 kind=proved origin=external
section
/- Let $x,y,z \in \mathbb{R}^+$ such that $xyz=1$ . Prove that $$(xy^3+yz^3+zx^3)^5 \geq 3(x^2+y^2+z^2)^4$$ -/
lemma lw_56592_aux1 (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    3 * ((w + u + v) * (w + v) * w) ^ 4 *
      ((w + u + v)^2 + (w + v)^2 + w^2)^4 ≤
      ((w + u + v) * (w + v)^3 + (w + v) * w^3 + w * (w + u + v)^3)^5 := by
  apply sub_nonneg.mp
  ring_nf (config := {mode := .raw})
  simp only [Mathlib.Tactic.RingNF.nat_rawCast_0, Mathlib.Tactic.RingNF.nat_rawCast_1,
    Mathlib.Tactic.RingNF.nat_rawCast_2]
  repeat' apply add_nonneg
  all_goals positivity

lemma lw_56592_aux2 (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    3 * ((w + v) * (w + u + v) * w) ^ 4 *
      ((w + v)^2 + (w + u + v)^2 + w^2)^4 ≤
      ((w + v) * (w + u + v)^3 + (w + u + v) * w^3 + w * (w + v)^3)^5 := by
  apply sub_nonneg.mp
  ring_nf (config := {mode := .raw})
  simp only [Mathlib.Tactic.RingNF.nat_rawCast_0, Mathlib.Tactic.RingNF.nat_rawCast_1,
    Mathlib.Tactic.RingNF.nat_rawCast_2]
  repeat' apply add_nonneg
  all_goals positivity

theorem lw_56592 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x*y*z = 1) : (x*y^3 + y*z^3 + z*x^3)^5 ≥ 3*(x^2 + y^2 + z^2)^4 := by
  have H : 3 * (x*y*z)^4 * (x^2+y^2+z^2)^4 ≤ (x*y^3+y*z^3+z*x^3)^5 := by
    rcases le_total x y with hxy | hyx
    · rcases le_total y z with hyz | hzy
      · have H := lw_56592_aux2 (z-y) (y-x) x (sub_nonneg.mpr hyz) (sub_nonneg.mpr hxy) hx.le
        simpa only [show x + (z-y) + (y-x) = z by ring,
          show x + (y-x) = y by ring, add_comm, add_left_comm, add_assoc,
          mul_comm, mul_left_comm, mul_assoc] using H
      · rcases le_total x z with hxz | hzx
        · have H := lw_56592_aux1 (y-z) (z-x) x (sub_nonneg.mpr hzy) (sub_nonneg.mpr hxz) hx.le
          simpa only [show x + (y-z) + (z-x) = y by ring,
            show x + (z-x) = z by ring, add_comm, add_left_comm, add_assoc,
            mul_comm, mul_left_comm, mul_assoc] using H
        · have H := lw_56592_aux2 (y-x) (x-z) z (sub_nonneg.mpr hxy) (sub_nonneg.mpr hzx) hz.le
          simpa only [show z + (y-x) + (x-z) = y by ring,
            show z + (x-z) = x by ring, add_comm, add_left_comm, add_assoc,
            mul_comm, mul_left_comm, mul_assoc] using H
    · rcases le_total x z with hxz | hzx
      · have H := lw_56592_aux1 (z-x) (x-y) y (sub_nonneg.mpr hxz) (sub_nonneg.mpr hyx) hy.le
        simpa only [show y + (z-x) + (x-y) = z by ring,
          show y + (x-y) = x by ring, add_comm, add_left_comm, add_assoc,
          mul_comm, mul_left_comm, mul_assoc] using H
      · rcases le_total y z with hyz | hzy
        · have H := lw_56592_aux2 (x-z) (z-y) y (sub_nonneg.mpr hzx) (sub_nonneg.mpr hyz) hy.le
          simpa only [show y + (x-z) + (z-y) = x by ring,
            show y + (z-y) = z by ring, add_comm, add_left_comm, add_assoc,
            mul_comm, mul_left_comm, mul_assoc] using H
        · have H := lw_56592_aux1 (x-y) (y-z) z (sub_nonneg.mpr hyx) (sub_nonneg.mpr hzy) hz.le
          simpa only [show z + (x-y) + (y-z) = x by ring,
            show z + (y-z) = y by ring, add_comm, add_left_comm, add_assoc,
            mul_comm, mul_left_comm, mul_assoc] using H
  simpa [h] using H
end

-- forge:entry lw_122 kind=proved origin=external
section
/- Let $a,b,c>0$ , such that $a+b+c=3$ , Prove that : $\frac{a^2}{a+b}+\frac{b^2}{b+c}+\frac{c^2}{c+a}+\frac{6abc}{(a+b)(a+c)(b+c)} \ge \frac{9}{4}$ -/
lemma lw_122_aux1 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 * (a + b + c) / 4 ≤
      a ^ 2 / (a + b) + b ^ 2 / (b + c) + c ^ 2 / (c + a) +
        2 * (a + b + c) * a * b * c / (a + b) / (a + c) / (b + c) := by
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  have hbc : b + c ≠ 0 := ne_of_gt (add_pos hb hc)
  have hca : c + a ≠ 0 := ne_of_gt (add_pos hc ha)
  have hac : a + c ≠ 0 := ne_of_gt (add_pos ha hc)
  have hid :
      a ^ 2 / (a + b) + b ^ 2 / (b + c) + c ^ 2 / (c + a) +
        2 * (a + b + c) * a * b * c / (a + b) / (a + c) / (b + c) -
        3 * (a + b + c) / 4 =
      (a * b * (a - b) ^ 2 + b * c * (b - c) ^ 2 + c * a * (c - a) ^ 2) /
        (4 * (a + b) * (a + c) * (b + c)) := by
    field_simp
    <;> ring
  have hn : 0 ≤
      (a * b * (a - b) ^ 2 + b * c * (b - c) ^ 2 + c * a * (c - a) ^ 2) /
        (4 * (a + b) * (a + c) * (b + c)) := by
    positivity
  linarith

theorem lw_122 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (hab : a + b + c = 3) :
    (a^2 / (a + b) + b^2 / (b + c) + c^2 / (c + a) +
      6 * a * b * c / (a + b) / (a + c) / (b + c)) ≥ 9 / 4 := by
  have h := lw_122_aux1 a b c ha hb hc
  norm_num [hab] at h
  exact h
end

-- forge:entry lw_16076 kind=proved origin=external
section
/- Prove that for all real numbers x and y, \(\frac{2}{x+y+2} \le \frac{1}{(1+\sqrt{x})^2}+\frac{1}{(1+\sqrt{y})^2}\) where x, y >= 0. -/
lemma lw_16076_aux1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    2 / (a + b) ≤ 1 / (2 * a) + 1 / (2 * b) := by
  have h2a : 0 < 2 * a := by positivity
  have h2b : 0 < 2 * b := by positivity
  rw [div_add_div _ _ (ne_of_gt h2a) (ne_of_gt h2b)]
  apply (div_le_div_iff₀ (add_pos ha hb) (mul_pos h2a h2b)).2
  nlinarith [sq_nonneg (a - b)]

lemma lw_16076_aux2 (x : ℝ) (hx : 0 ≤ x) :
    1 / (2 * (x + 1)) ≤ 1 / (1 + Real.sqrt x) ^ 2 := by
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [Real.sq_sqrt hx, sq_nonneg (Real.sqrt x - 1)]

theorem lw_16076 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (2 / (x + y + 2) ≤ (1 / (1 + Real.sqrt x) ^ 2) +
      (1 / (1 + Real.sqrt y) ^ 2)) := by
  calc
    2 / (x + y + 2) = 2 / ((x + 1) + (y + 1)) := by ring
    _ ≤ 1 / (2 * (x + 1)) + 1 / (2 * (y + 1)) :=
      lw_16076_aux1 (x + 1) (y + 1) (by linarith) (by linarith)
    _ ≤ 1 / (1 + Real.sqrt x) ^ 2 + 1 / (1 + Real.sqrt y) ^ 2 :=
      add_le_add (lw_16076_aux2 x hx) (lw_16076_aux2 y hy)
end

-- forge:entry lw_17303 kind=proved origin=external
section
/- Let $a,b,c \in \left[ {1;2} \right]$ . Prove that: ${a^3} + {b^3} + {c^3} \le 5abc$ -/
theorem lw_17303 (a b c : ℝ) (ha : 1 ≤ a ∧ a ≤ 2)
    (hb : 1 ≤ b ∧ b ≤ 2) (hc : 1 ≤ c ∧ c ≤ 2) :
    a^3 + b^3 + c^3 ≤ 5 * a * b * c := by
  have ha1 : 0 ≤ a - 1 := sub_nonneg.mpr ha.1
  have ha2 : 0 ≤ 2 - a := sub_nonneg.mpr ha.2
  have hb1 : 0 ≤ b - 1 := sub_nonneg.mpr hb.1
  have hb2 : 0 ≤ 2 - b := sub_nonneg.mpr hb.2
  have hc1 : 0 ≤ c - 1 := sub_nonneg.mpr hc.1
  have hc2 : 0 ≤ 2 - c := sub_nonneg.mpr hc.2
  have ha3 : 0 ≤ a + 3 := by linarith [ha.1]
  have hb3 : 0 ≤ b + 3 := by linarith [hb.1]
  have hc3 : 0 ≤ c + 3 := by linarith [hc.1]
  have h : 0 ≤
      (a - 1) * (2 - a) * (a + 3) +
      (b - 1) * (2 - b) * (b + 3) +
      (c - 1) * (2 - c) * (c + 3) +
      2 * (2 - a) * (2 - b) * (2 - c) +
      3 * (a - 1) * (b - 1) * (2 - c) +
      3 * (a - 1) * (2 - b) * (c - 1) +
      3 * (2 - a) * (b - 1) * (c - 1) +
      16 * (a - 1) * (b - 1) * (c - 1) := by
    positivity
  nlinarith only [h]
end

-- forge:entry lw_18429 kind=proved origin=external
section
/- For all positive real numbers $a, b, c$ , prove that $ \frac{a^4+5b^4}{a(a+2b)} + \frac{b^4+5c^4}{b(b+2c)} + \frac{c^4+5a^4}{c(c+2a)} \geq 2(a^2+b^2+c^2). $ -/
lemma lw_18429_aux1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (8 * b ^ 2 - 2 * a ^ 2) / 3 ≤ (a ^ 4 + 5 * b ^ 4) / (a * (a + 2 * b)) := by
  have hden : 0 < a * (a + 2 * b) := by positivity
  apply (le_div_iff₀ hden).2
  have hfactor : 0 ≤ 5 * a ^ 2 + 14 * a * b + 15 * b ^ 2 := by positivity
  have hsq := mul_nonneg (sq_nonneg (a - b)) hfactor
  nlinarith

theorem lw_18429 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    (a^4 + 5 * b^4) / (a * (a + 2 * b)) +
      (b^4 + 5 * c^4) / (b * (b + 2 * c)) +
      (c^4 + 5 * a^4) / (c * (c + 2 * a)) ≥ 2 * (a^2 + b^2 + c^2) := by
  have hab := lw_18429_aux1 a b ha hb
  have hbc := lw_18429_aux1 b c hb hc
  have hca := lw_18429_aux1 c a hc ha
  linarith
end

-- forge:entry lw_21945 kind=disproved origin=external
section
/- Prove that for each positive integer $n$ :\n\n$$\frac{(\sqrt[n]{a_1a_2\cdots a_n})^2}{\frac{a_1+a_2+\cdots +a_n}{n}}+\frac{\left(\frac{n}{\frac{1}{a_1}+\frac{1}{a_2}+\cdots+\frac{1}{a_n}}\right)^2}{\sqrt[n]{a_1a_2\cdots a_n}}+\frac{a_1+a_2+\cdots +a_n}{n}\geq \frac{2n}{\frac{1}{a_1}+\frac{1}{a_2}+\cdots+\frac{1}{a_n}}+\sqrt[n]{a_1a_2\cdots a_n} .$$\n\nProposed by Kunihiko Chikaya -/
theorem lw_21945_disproof :
    ¬ (∀ (n : ℕ) (a : Fin n → ℝ),
      (n / ∑ i, 1 / a i) ^ 2 * ∏ i, a i + (∑ i, a i) ^ 2 / n ≥
        2 * n / (∑ i, 1 / a i) + ∏ i, a i ^ (1 / n)) := by
  intro h
  have h1 := h 1 (fun _ => 1)
  norm_num at h1
end

-- forge:entry lw_22013 kind=disproved origin=external
section
/- Corrected inequality: \nProve that for positive real numbers x, y, and z, the following inequality holds: \n$\sum(yz\frac{y+z}{x})\geq \frac{1}{2}\sum{(y+z)^2}+\frac{3}{4}x(\frac{1}{y}+\frac{1}{z})(y-z)^2$ -/
theorem lw_22013_disproof : ¬ (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z),
    (y * z * (y + z) / x + z * x * (z + x) / y + x * y * (x + y) / z) ≥
      (1 / 2) * (x ^ 2 + y ^ 2 + z ^ 2 + (x + y) ^ 2 + (x + z) ^ 2 +
        (y + z) ^ 2) +
      (3 / 4) * x * ((1 / y) + (1 / z)) * (y - z) ^ 2) := by
  intro h
  have hcontra := h 1 1 1 (by norm_num) (by norm_num) (by norm_num)
  norm_num at hcontra
end

-- forge:entry lw_23573 kind=disproved origin=external
section
/- Prove that $ (a+b+c)(\frac{1}{a}+\frac{1}{b}+\frac{1}{c})=t \ge 9$ implies $ (t-1)(t-9)\ge 0$ -/
theorem lw_23573_disproof :
    ¬ (∀ (a b c t : ℝ), a * b * c = 1 →
      (a + b + c) * (1 / a + 1 / b + 1 / c) = t →
      (t - 1) * (t - 9) ≥ 0) := by
  intro h
  have hbad := h 1 (-2) (-(1 / 2)) (9 / 4) (by norm_num) (by norm_num)
  norm_num at hbad
end

-- forge:entry lw_24988 kind=disproved origin=external
section
/- Let $x,y,z$ be positive reals such that $(x+y)(y+z)(z+x)=8$ , prove that:\n\n $1.$ $ x^3+y^3+z^3 \geq xy+yz+zx$ \n\n $2.$ $ x^3+y^3+z^3 \geq 2+ xyz $ \n\n $3.$ $ xy+yz+zx \geq 1+ 2xyz $ \n\n -/
theorem lw_24988_disproof :
    ¬ (∀ (x y z : ℝ) (hx : x > 0 ∧ y > 0 ∧ z > 0)
      (h : (x+y)*(y+z)*(z+x) = 8),
      x^3 + y^3 + z^3 ≥ x*y + y*z + z*x ∧
      x^3 + y^3 + z^3 ≥ 2 + x*y*z ∧
      x*y + y*z + z*x ≥ 1 + 2*x*y*z) := by
  intro hall
  have hc := (hall (127 / 16) (1 / 16) (1 / 16) (by norm_num) (by norm_num)).2.2
  norm_num at hc
end

-- forge:entry lw_25706 kind=proved origin=external
section
/- Prove $\sum_{cyc}\frac{x^2+2xy}{x^2+xy+y^2}\leq4$ -/
lemma lw_25706_aux1 (x y : ℝ) :
    (x ^ 2 + 2 * x * y) / (x ^ 2 + x * y + y ^ 2) ≤ (4 : ℝ) / 3 := by
  have hnonneg : 0 ≤ x ^ 2 + x * y + y ^ 2 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x + y)]
  by_cases hzero : x ^ 2 + x * y + y ^ 2 = 0
  · norm_num [hzero]
  · have hpos : 0 < x ^ 2 + x * y + y ^ 2 :=
      lt_of_le_of_ne hnonneg (Ne.symm hzero)
    apply (div_le_iff₀ hpos).2
    nlinarith [sq_nonneg (x - y), sq_nonneg y]

theorem lw_25706 (x y z : ℝ) :
    (x^2 + 2 * x * y) / (x^2 + x * y + y^2) +
      (y^2 + 2 * y * z) / (y^2 + y * z + z^2) +
      (z^2 + 2 * z * x) / (z^2 + z * x + x^2) ≤ 4 := by
  have hxy := lw_25706_aux1 x y
  have hyz := lw_25706_aux1 y z
  have hzx := lw_25706_aux1 z x
  linarith
end

-- forge:entry lw_20431 kind=proved origin=external
section
/- Solve the functional equation\n\n- $ f : N$ ----> $ N$ \n- $ f(2) = 2$ \n- $ f(mn) = f(m).f(n)$ for all m and n relatively prime \nf is increasing\n\nClaim: $ \forall n: f(n)=n$ -/
lemma lw_20431_aux1 {f : ℕ → ℕ} (hf : Monotone f)
    (hd : ∀ m, Odd m → f (2 * m) = 2 * f m) :
    ∃ C : ℕ, ∀ n, f n ≤ C * (n + 1) := by
  let C := f 12 + 1
  have hb : ∀ n, 4 ≤ n → f n ≤ C * (n - 3) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hs : n ≤ 12
      · have hf' := hf hs
        have ht : 1 ≤ n - 3 := by omega
        dsimp [C]
        nlinarith
      · let m := 2 * ((n + 1) / 4) + 1
        have hm : 4 ≤ m := by dsimp [m]; omega
        have hmn : m < n := by dsimp [m]; omega
        have hnm : n ≤ 2 * m := by dsimp [m]; omega
        have hclose : 2 * m ≤ n + 3 := by dsimp [m]; omega
        have hodd : Odd m := by
          refine ⟨(n + 1) / 4, ?_⟩
          dsimp [m]
        have hi := ih m hmn hm
        have he := hd m hodd
        have hmono := hf hnm
        have hm' : m - 3 + 3 = m := by omega
        have hn' : n - 3 + 3 = n := by omega
        nlinarith
  refine ⟨C, ?_⟩
  intro n
  by_cases hn : 4 ≤ n
  · have h := hb n hn
    exact h.trans (Nat.mul_le_mul_left C (by omega))
  · have h := hf (show n ≤ 12 by omega)
    dsimp [C]
    nlinarith

lemma lw_20431_aux2 {f : ℕ → ℕ}
    (hf1 : ∀ m n, Nat.Coprime m n → f (m * n) = f m * f n)
    (hf3 : StrictMono f) {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    ∃ m : ℕ, n ∣ m ∧ m + 2 ≤ 2 * n ^ k ∧ (f n) ^ k ≤ f m + 1 := by
  induction k with
  | zero =>
    refine ⟨0, dvd_zero n, ?_, ?_⟩ <;> simp
  | succ k ih =>
    obtain ⟨m, hdiv, hbound, hfun⟩ := ih
    have hcop : Nat.Coprime n (m + 1) := by
      obtain ⟨t, rfl⟩ := hdiv
      simpa using (Nat.coprime_mul_left_add_right n 1 t).2 (Nat.coprime_one_right n)
    have he := hf1 n (m + 1) hcop
    have hs : f m < f (m + 1) := hf3 (by omega)
    have hnp : 0 < n ^ k := pow_pos (by omega) _
    refine ⟨n * (m + 1), dvd_mul_right n (m + 1), ?_, ?_⟩
    · rw [pow_succ]
      nlinarith
    · rw [pow_succ]
      have ht := Nat.mul_le_mul_left (f n) hfun
      have hu := Nat.mul_le_mul_left (f n) (show f m + 1 ≤ f (m + 1) by omega)
      nlinarith

lemma lw_20431_aux3 (n k : ℕ) :
    n ^ (k + 1) + (k + 1) * n ^ k ≤ (n + 1) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := Nat.mul_le_mul_right (n + 1) ih
    have hz : 0 ≤ (k + 1) * n ^ k := Nat.zero_le _
    simp only [pow_succ] at *
    nlinarith only [h, hz]

theorem lw_20431 {f : ℕ → ℕ}
    (hf1 : ∀ m n, Nat.Coprime m n → f (m * n) = f m * f n)
    (hf2 : f 2 = 2) (hf3 : StrictMono f) : ∀ n, f n = n := by
  have hd : ∀ m, Odd m → f (2 * m) = 2 * f m := by
    intro m hm
    rw [hf1 2 m hm.coprime_two_left, hf2]
  obtain ⟨C, hC⟩ := lw_20431_aux1 hf3.monotone hd
  intro n
  have hlo : n ≤ f n := hf3.id_le n
  apply Nat.le_antisymm _ hlo
  by_contra h
  have hfn : n + 1 ≤ f n := by omega
  have hn : 2 ≤ n := by
    by_contra hn
    have hn2 : n < 2 := by omega
    have h01 := hf3 (show 0 < 1 by decide)
    have h12 := hf3 (show 1 < 2 by decide)
    rw [hf2] at h12
    interval_cases n <;> omega
  let k := 2 * C * n
  obtain ⟨m, hmdiv, hmb, hmf⟩ := lw_20431_aux2 hf1 hf3 hn (k + 1)
  have hp : 0 < n ^ k := pow_pos (by omega) _
  have hp' : 0 < n ^ (k + 1) := pow_pos (by omega) _
  have hpow : (n + 1) ^ (k + 1) ≤ (f n) ^ (k + 1) := Nat.pow_le_pow_left hfn _
  have hbin := lw_20431_aux3 n k
  have hCm := hC m
  have hmul := Nat.mul_le_mul_left C hmb
  have hu : f m + 1 ≤ (2 * C + 1) * n ^ (k + 1) := by nlinarith
  have hall : n ^ (k + 1) + (k + 1) * n ^ k ≤ (2 * C + 1) * n ^ (k + 1) :=
    hbin.trans (hpow.trans (hmf.trans hu))
  rw [pow_succ] at hall
  have hcancel : n + (k + 1) ≤ (2 * C + 1) * n := by
    have heq : (n + (k + 1)) * n ^ k ≤ ((2 * C + 1) * n) * n ^ k := by
      nlinarith only [hall]
    exact Nat.le_of_mul_le_mul_right heq hp
  dsimp [k] at hcancel
  nlinarith only [hcancel]
end

-- forge:entry lw_28812 kind=proved origin=external
section
/- Prove or disprove that \(\frac{(a + b + c)^2}{a^2 + b^2 + c^2} + 3 \geq \frac{(a + b)^2}{a^2 + b^2} + \frac{(b + c)^2}{b^2 + c^2} + \frac{(c + a)^2}{c^2 + a^2}\) for \(a, b, c\) real numbers. -/
lemma lw_28812_aux1 (a b c : ℝ) :
    (a + b) ^ 2 / (a ^ 2 + b ^ 2) ≤
      ((a + b) ^ 2 + 2 * c ^ 2) / (a ^ 2 + b ^ 2 + c ^ 2) := by
  by_cases h : a ^ 2 + b ^ 2 = 0
  · simp only [h, div_zero]
    positivity
  · have hp : 0 < a ^ 2 + b ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
    have hs : 0 < a ^ 2 + b ^ 2 + c ^ 2 := by positivity
    apply (div_le_div_iff₀ hp hs).2
    nlinarith [mul_nonneg (sq_nonneg (a - b)) (sq_nonneg c)]

theorem lw_28812 (a b c : ℝ) :
    (a + b + c) ^ 2 / (a ^ 2 + b ^ 2 + c ^ 2) + 3 ≥
      (a + b) ^ 2 / (a ^ 2 + b ^ 2) +
      (b + c) ^ 2 / (b ^ 2 + c ^ 2) +
      (c + a) ^ 2 / (c ^ 2 + a ^ 2) := by
  have h1 := lw_28812_aux1 a b c
  have h2 : (b + c) ^ 2 / (b ^ 2 + c ^ 2) ≤
      ((b + c) ^ 2 + 2 * a ^ 2) / (a ^ 2 + b ^ 2 + c ^ 2) := by
    convert lw_28812_aux1 b c a using 1 <;> ring
  have h3 : (c + a) ^ 2 / (c ^ 2 + a ^ 2) ≤
      ((c + a) ^ 2 + 2 * b ^ 2) / (a ^ 2 + b ^ 2 + c ^ 2) := by
    convert lw_28812_aux1 c a b using 1 <;> ring
  have hsum : (a + b) ^ 2 / (a ^ 2 + b ^ 2) +
      (b + c) ^ 2 / (b ^ 2 + c ^ 2) +
      (c + a) ^ 2 / (c ^ 2 + a ^ 2) ≤
      ((a + b + c) ^ 2 + 3 * (a ^ 2 + b ^ 2 + c ^ 2)) /
        (a ^ 2 + b ^ 2 + c ^ 2) := by
    calc
      _ ≤ _ := add_le_add (add_le_add h1 h2) h3
      _ = _ := by
        rw [← add_div, ← add_div]
        congr 1
        ring
  by_cases h : a ^ 2 + b ^ 2 + c ^ 2 = 0
  · simp only [h, div_zero] at hsum ⊢
    linarith
  · simpa [add_div, h] using hsum
end

end Mathlib2
