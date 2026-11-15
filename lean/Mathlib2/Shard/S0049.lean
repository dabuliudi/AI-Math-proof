/- Mathlib2 分片 49（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0048
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry lw_26448 kind=proved origin=external
section
/- Prove that for a, b, c > 0 and a + b + c = 1, the following inequality holds:\n$ \frac{1+a}{1-a}+\frac{1+b}{1-b}+\frac{1+c}{1-c}\leq 2(\frac{a}{b}+\frac{b}{c}+\frac{c}{a})$ -/
lemma lw_26448_aux1 (a b c : ℝ) (hc : 0 ≤ c) (hca : c ≤ a) (hcb : c ≤ b) :
    0 ≤ 2 * (a * a * c + b * b * a + c * c * b) * (a + b) * (b + c) * (c + a) -
      a * b * c * (3 * (a + b) * (b + c) * (c + a) +
        2 * (a * (c + a) * (a + b) + b * (a + b) * (b + c) +
          c * (b + c) * (c + a))) := by
  have hx : 0 ≤ a - c := sub_nonneg.mpr hca
  have hy : 0 ≤ b - c := sub_nonneg.mpr hcb
  have hid :
      2 * (a * a * c + b * b * a + c * c * b) * (a + b) * (b + c) * (c + a) -
        a * b * c * (3 * (a + b) * (b + c) * (c + a) +
          2 * (a * (c + a) * (a + b) + b * (a + b) * (b + c) +
            c * (b + c) * (c + a))) =
      6 * c ^ 4 * ((a - b) ^ 2 + (a - c) ^ 2 + (b - c) ^ 2) +
      c ^ 3 * (10 * (a - c) ^ 3 + (a - c) ^ 2 * (b - c) +
        17 * (a - c) * (b - c) ^ 2 + 10 * (b - c) ^ 3) +
      c ^ 2 * (2 * (a - c) ^ 4 + 3 * (a - c) ^ 3 * (b - c) +
        18 * (a - c) ^ 2 * (b - c) ^ 2 + 19 * (a - c) * (b - c) ^ 3 +
        2 * (b - c) ^ 4) +
      c * (5 * (a - c) ^ 3 * (b - c) ^ 2 +
        13 * (a - c) ^ 2 * (b - c) ^ 3 + 4 * (a - c) * (b - c) ^ 4) +
      2 * (a - c) ^ 3 * (b - c) ^ 3 + 2 * (a - c) ^ 2 * (b - c) ^ 4 := by ring
  rw [hid]
  positivity

lemma lw_26448_aux2 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ 2 * (a * a * c + b * b * a + c * c * b) * (a + b) * (b + c) * (c + a) -
      a * b * c * (3 * (a + b) * (b + c) * (c + a) +
        2 * (a * (c + a) * (a + b) + b * (a + b) * (b + c) +
          c * (b + c) * (c + a))) := by
  rcases le_total c a with hca | hac
  · rcases le_total c b with hcb | hbc
    · exact lw_26448_aux1 a b c hc hca hcb
    · convert lw_26448_aux1 c a b hb hbc (hbc.trans hca) using 1 <;> ring
  · rcases le_total a b with hab | hba
    · convert lw_26448_aux1 b c a ha hab hac using 1 <;> ring
    · convert lw_26448_aux1 c a b hb (hba.trans hac) hba using 1 <;> ring

lemma lw_26448_aux3 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 + 2 * (a / (b + c) + b / (c + a) + c / (a + b)) ≤
      2 * (a / b + b / c + c / a) := by
  have hp := lw_26448_aux2 a b c ha.le hb.le hc.le
  have hd : 0 < a * b * c * (a + b) * (b + c) * (c + a) := by positivity
  have hid :
      2 * (a / b + b / c + c / a) -
        (3 + 2 * (a / (b + c) + b / (c + a) + c / (a + b))) =
      (2 * (a * a * c + b * b * a + c * c * b) * (a + b) * (b + c) * (c + a) -
        a * b * c * (3 * (a + b) * (b + c) * (c + a) +
          2 * (a * (c + a) * (a + b) + b * (a + b) * (b + c) +
            c * (b + c) * (c + a)))) /
        (a * b * c * (a + b) * (b + c) * (c + a)) := by
    field_simp [ha.ne', hb.ne', hc.ne', (add_pos ha hb).ne',
      (add_pos hb hc).ne', (add_pos hc ha).ne']
    <;> ring
  have hgap : 0 ≤ 2 * (a / b + b / c + c / a) -
      (3 + 2 * (a / (b + c) + b / (c + a) + c / (a + b))) := by
    rw [hid]
    exact div_nonneg hp hd.le
  linarith only [hgap]

theorem lw_26448 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a + b + c = 1) :
    (1 + a) / (1 - a) + (1 + b) / (1 - b) + (1 + c) / (1 - c) ≤
      2 * (a / b + b / c + c / a) := by
  have hda : 1 - a = b + c := by linarith
  have hdb : 1 - b = c + a := by linarith
  have hdc : 1 - c = a + b := by linarith
  have hna : 1 + a = (b + c) + 2 * a := by linarith
  have hnb : 1 + b = (c + a) + 2 * b := by linarith
  have hnc : 1 + c = (a + b) + 2 * c := by linarith
  calc
    (1 + a) / (1 - a) + (1 + b) / (1 - b) + (1 + c) / (1 - c) =
        3 + 2 * (a / (b + c) + b / (c + a) + c / (a + b)) := by
      rw [hda, hdb, hdc, hna, hnb, hnc]
      field_simp [(add_pos ha hb).ne', (add_pos hb hc).ne', (add_pos hc ha).ne']
      <;> ring
    _ ≤ 2 * (a / b + b / c + c / a) := lw_26448_aux3 a b c ha hb hc
end

-- forge:entry lw_30393 kind=proved origin=external
section
/- For all positive reals $a,b,c$ prove that $a^2+b^2+c^2+2abc+3\geq (1+a)(1+b)(1+c).$ -/
lemma lw_30393_aux1 (x y z : ℝ) (hz : -1 ≤ z) (hxy : 0 ≤ x * y) :
    0 ≤ x ^ 2 + y ^ 2 + z ^ 2 + x * y * z := by
  have h : 0 ≤ x * y * (z + 1) := mul_nonneg hxy (by linarith)
  nlinarith [sq_nonneg (x - y), sq_nonneg z]

lemma lw_30393_aux2 (x y z : ℝ) (hx : -1 ≤ x) (hy : -1 ≤ y)
    (hz : -1 ≤ z) : 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 + x * y * z := by
  rcases le_total 0 x with hx0 | hx0
  · rcases le_total 0 y with hy0 | hy0
    · exact lw_30393_aux1 x y z hz (mul_nonneg hx0 hy0)
    · rcases le_total 0 z with hz0 | hz0
      · nlinarith [lw_30393_aux1 x z y hy (mul_nonneg hx0 hz0)]
      · nlinarith [lw_30393_aux1 y z x hx
          (mul_nonneg_of_nonpos_of_nonpos hy0 hz0)]
  · rcases le_total 0 y with hy0 | hy0
    · rcases le_total 0 z with hz0 | hz0
      · nlinarith [lw_30393_aux1 y z x hx (mul_nonneg hy0 hz0)]
      · nlinarith [lw_30393_aux1 x z y hy
          (mul_nonneg_of_nonpos_of_nonpos hx0 hz0)]
    · exact lw_30393_aux1 x y z hz (mul_nonneg_of_nonpos_of_nonpos hx0 hy0)

theorem lw_30393 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^2 + b^2 + c^2 + 2 * a * b * c + 3 ≥ (1 + a) * (1 + b) * (1 + c) := by
  have h := lw_30393_aux2 (a - 1) (b - 1) (c - 1)
    (by linarith) (by linarith) (by linarith)
  nlinarith
end

-- forge:entry lw_33948 kind=disproved origin=external
section
/- Prove that $2(x^{3}+y^{3}+z^{3})+3xyz \ge 3(xy^{2}+yz^{2}+zx^{2}).$ -/
theorem lw_33948_disproof :
    ¬ (∀ (x y z : ℝ),
      2 * (x ^ 3 + y ^ 3 + z ^ 3) + 3 * x * y * z ≥
        3 * (x * y ^ 2 + y * z ^ 2 + z * x ^ 2)) := by
  intro h
  have hbad := h (-1) 0 0
  norm_num at hbad
end

-- forge:entry lw_37466 kind=disproved origin=external
section
/- Prove (without induction) that: $n(2^n-1)<1.2^1+2.2^2+...+n.2^n<2n(2^n-1)$ -/
theorem lw_37466_disproof :
    ¬ (∀ (n : ℕ),
      n * (2 ^ n - 1) < (∑ k ∈ Finset.range n, (k * 2 ^ k)) ∧
      (∑ k ∈ Finset.range n, (k * 2 ^ k)) < 2 * n * (2 ^ n - 1)) := by
  intro h
  have h1 := (h 1).1
  norm_num at h1
end

-- forge:entry lw_38012 kind=disproved origin=external
section
/- If $k\ge 0$ and $a_1,a_2,...,a_n\ge 0$ , then \n\n $(a_1^2+n-1+k)(a_2^2+n-1+k)...(a_n^2+n-1+k)\ge (n+k)^{n-2}(a_1+a_2+...+a_n+k)^2$. -/
theorem lw_38012_disproof : ¬ (∀ (n k : ℕ) (a : ℕ → ℕ) (ha : 0 < n) (h : 0 < k) (hab : 0 < a), (∏ i ∈ Finset.range n, ((a i ^ 2 + n - 1 + k))) ≥ (n + k) ^ (n - 2) * (∑ i ∈ Finset.range n, (a i + k)) ^ 2) := by
  intro hall
  have hpos : (0 : ℕ → ℕ) < (fun _ => 1) := by
    apply lt_of_le_of_ne
    · intro i
      norm_num
    · intro he
      have := congrFun he 0
      norm_num at this
  have hbad := hall 1 1 (fun _ => 1) (by norm_num) (by norm_num) hpos
  norm_num at hbad
end

-- forge:entry lw_34437 kind=proved origin=external
section
/- If $a, b, c>0, a+b+c=3$ prove that \n $\frac{1}{\sqrt{1+3a^4}}+\frac{1}{\sqrt{1+3b^4}}+\frac{1}{\sqrt{1+3c^4}}\ge\frac{3}{2}\cdot\frac{ab+bc+ca}{a^2+b^2+c^2}$ -/
lemma lw_34437_aux1 (x : ℝ) (hx : 0 ≤ x) (hp : 0 ≤ 4 - x - x ^ 2) :
    (4 - x - x ^ 2) ^ 2 * (1 + 3 * x ^ 4) ≤ 16 := by
  have hid : 16 - (4 - x - x ^ 2) ^ 2 * (1 + 3 * x ^ 4) =
      x * (x - 1) ^ 2 *
        ((4 - x - x ^ 2) * (3 * x ^ 3 + 9 * x ^ 2 + 3 * x) +
          3 * x ^ 2 + 11 * x + 8) := by ring
  have hn : 0 ≤ x * (x - 1) ^ 2 *
        ((4 - x - x ^ 2) * (3 * x ^ 3 + 9 * x ^ 2 + 3 * x) +
          3 * x ^ 2 + 11 * x + 8) := by positivity
  linarith only [hid, hn]

lemma lw_34437_aux2 (x : ℝ) (hx : 0 ≤ x) :
    (4 - x - x ^ 2) / 4 ≤ 1 / Real.sqrt (1 + 3 * x ^ 4) := by
  have hs : 0 < Real.sqrt (1 + 3 * x ^ 4) := by positivity
  by_cases hp : 0 ≤ 4 - x - x ^ 2
  · have hpoly := lw_34437_aux1 x hx hp
    have hs2 : (Real.sqrt (1 + 3 * x ^ 4)) ^ 2 = 1 + 3 * x ^ 4 :=
      Real.sq_sqrt (by positivity)
    have hsq : ((4 - x - x ^ 2) * Real.sqrt (1 + 3 * x ^ 4)) ^ 2 ≤ (4 : ℝ) ^ 2 := by
      rw [mul_pow, hs2]
      norm_num only [show (4 : ℝ) ^ 2 = 16 by norm_num]
      exact hpoly
    have hm : (4 - x - x ^ 2) * Real.sqrt (1 + 3 * x ^ 4) ≤ 4 :=
      (sq_le_sq₀ (mul_nonneg hp hs.le) (by norm_num)).mp hsq
    apply (le_div_iff₀ hs).mpr
    nlinarith only [hm]
  · have hr : 0 ≤ 1 / Real.sqrt (1 + 3 * x ^ 4) := by positivity
    have hl : (4 - x - x ^ 2) / 4 ≤ 0 := by linarith
    exact hl.trans hr

theorem lw_34437 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a + b + c = 3) :
    (1 / Real.sqrt (1 + 3 * a ^ 4) + 1 / Real.sqrt (1 + 3 * b ^ 4) +
      1 / Real.sqrt (1 + 3 * c ^ 4)) ≥
      (3 / 2) * (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) := by
  have hA := lw_34437_aux2 a ha.le
  have hB := lw_34437_aux2 b hb.le
  have hC := lw_34437_aux2 c hc.le
  have hsum2 : (a + b + c) ^ 2 = 9 := by rw [habc]; norm_num
  have hid : a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) = 9 := by
    nlinarith only [hsum2]
  have hq : 3 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hqpos : 0 < a ^ 2 + b ^ 2 + c ^ 2 := by linarith
  have hp : 0 ≤ a * b + b * c + c * a := by positivity
  have hbound : (3 / 2 : ℝ) * (a * b + b * c + c * a) /
      (a ^ 2 + b ^ 2 + c ^ 2) ≤ (a * b + b * c + c * a) / 2 := by
    apply (div_le_iff₀ hqpos).mpr
    nlinarith only [mul_nonneg hp (sub_nonneg.mpr hq)]
  have hlow : (a * b + b * c + c * a) / 2 ≤
      1 / Real.sqrt (1 + 3 * a ^ 4) + 1 / Real.sqrt (1 + 3 * b ^ 4) +
        1 / Real.sqrt (1 + 3 * c ^ 4) := by
    nlinarith only [hA, hB, hC, hid, habc]
  exact hbound.trans hlow
end

-- forge:entry lw_38747 kind=disproved origin=external
section
/- Prove that $8x^2y^2 +x^2+y^2 \geq 1$ if $x +y <1$ -/
theorem lw_38747_disproof :
    ¬ (∀ (x y : ℝ) (h : x + y < 1), 8*x^2*y^2 + x^2 + y^2 ≥ 1) := by
  intro h
  have h0 := h 0 0 (by norm_num)
  norm_num at h0
end

-- forge:entry lw_38140 kind=proved origin=external
section
/- Let $a,b,c>0$ .Prove that:\n\n $\sqrt{abc}(\sqrt{a}+\sqrt{b}+\sqrt{c})+(a+b+c)^2\geq4\sqrt{3abc(a+b+c)}$ -/
lemma lw_38140_aux1 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    9 * (x * y * z) ≤ (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2) := by
  have h : 0 ≤ (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) :=
    mul_nonneg (by positivity) (by positivity)
  nlinarith [mul_nonneg hx (sq_nonneg (y - z)),
    mul_nonneg hy (sq_nonneg (z - x)), mul_nonneg hz (sq_nonneg (x - y))]

lemma lw_38140_aux2 (s p t r : ℝ) (hs : 0 ≤ s) (hp : 0 ≤ p)
    (ht : 0 < t) (hr : t ≤ r) (hr2 : r ^ 2 = 3 * s)
    (hprod : 9 * p ≤ t * s) : 4 * p * r ≤ s ^ 2 + p * t := by
  have hq : t * (4 * r - t) ≤ 9 * s := by
    have hn := mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ 3 * r - t by linarith)
    nlinarith
  have hm1 := mul_le_mul_of_nonneg_right hprod hs
  have hm2 := mul_le_mul_of_nonneg_left hq hp
  have hh : t * (4 * p * r) ≤ t * (s ^ 2 + p * t) := by
    nlinarith [hm1, hm2]
  exact (mul_le_mul_left ht).mp hh

theorem lw_38140 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Real.sqrt (a * b * c) * (Real.sqrt a + Real.sqrt b + Real.sqrt c) +
      (a + b + c) ^ 2 ≥ 4 * Real.sqrt (3 * a * b * c * (a + b + c)) := by
  let s := a + b + c
  let p := Real.sqrt (a * b * c)
  let t := Real.sqrt a + Real.sqrt b + Real.sqrt c
  let r := Real.sqrt (3 * s)
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hp : 0 ≤ p := Real.sqrt_nonneg _
  have ht : 0 < t := by dsimp [t]; positivity
  have ha2 := Real.sq_sqrt ha.le
  have hb2 := Real.sq_sqrt hb.le
  have hc2 := Real.sq_sqrt hc.le
  have hr2 : r ^ 2 = 3 * s := Real.sq_sqrt (by positivity)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have ht2 : t ^ 2 ≤ 3 * s := by
    dsimp [t, s]
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b),
      sq_nonneg (Real.sqrt b - Real.sqrt c), sq_nonneg (Real.sqrt c - Real.sqrt a)]
  have hr : t ≤ r := by nlinarith
  have hpeq : p = Real.sqrt a * Real.sqrt b * Real.sqrt c := by
    dsimp [p]
    rw [Real.sqrt_mul (mul_nonneg ha.le hb.le), Real.sqrt_mul ha.le]
  have hprod : 9 * p ≤ t * s := by
    have h := lw_38140_aux1 (Real.sqrt a) (Real.sqrt b) (Real.sqrt c)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [ha2, hb2, hc2] at h
    simpa [t, s, hpeq] using h
  have h := lw_38140_aux2 s p t r hs hp ht hr hr2 hprod
  have hroot : Real.sqrt (3 * a * b * c * (a + b + c)) = p * r := by
    calc
      Real.sqrt (3 * a * b * c * (a + b + c)) =
          Real.sqrt ((a * b * c) * (3 * s)) := by congr 1 <;> dsimp [s] <;> ring
      _ = p * r := Real.sqrt_mul (by positivity) _
  rw [hroot]
  dsimp [s, p, t, r] at h ⊢
  nlinarith [h]
end

-- forge:entry lw_39 kind=proved origin=external
section
/- (\sin x+\sin5x)+\sin3x =(2 \sin3x \cos x)+\sin3x = \sin3x(2 \cos x+1) = 0\nThis means $\sin3x = 0$ or $2\cos x+1=0$ -/
theorem lw_39 (x : ℝ)
    (h₀ : Real.sin x + Real.sin (5 * x) + Real.sin (3 * x) = 0) :
    Real.sin (3 * x) = 0 ∨ 2 * Real.cos x + 1 = 0 := by
  have hsum := Real.sin_add_sin (5 * x) x
  rw [show (5 * x + x) / 2 = 3 * x by ring,
    show (5 * x - x) / 2 = 2 * x by ring] at hsum
  have htriple := Real.sin_add_sin (3 * x) (-x)
  rw [show (3 * x + -x) / 2 = x by ring,
    show (3 * x - -x) / 2 = 2 * x by ring,
    Real.sin_neg] at htriple
  have hprod : Real.sin (3 * x) * (2 * Real.cos (2 * x) + 1) = 0 := by
    nlinarith [hsum, h₀]
  left
  rcases mul_eq_zero.mp hprod with h | h
  · exact h
  · calc
      Real.sin (3 * x) = Real.sin x * (2 * Real.cos (2 * x) + 1) := by
        nlinarith [htriple]
      _ = 0 := by rw [h, mul_zero]
end

-- forge:entry lw_39587 kind=proved origin=external
section
/- Let $a,b$ are positive real number such that $a+3b=2.$ Prove that $$\frac{1}{3+a^{2}}+\frac{3}{3 +b^{2}}\leq \frac{16}{13} $$ -/
theorem lw_39587 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a + 3 * b = 2) :
    (1 / (3 + a ^ 2) + 3 / (3 + b ^ 2)) ≤ 16 / 13 := by
  have hda : 0 < 3 + a ^ 2 := by positivity
  have hdb : 0 < 3 + b ^ 2 := by positivity
  have haeq : a = 2 - 3 * b := by linarith
  have hnonneg : 0 ≤ (2 * b - 1) ^ 2 * ((6 * b - 1) ^ 2 + 23) := by
    positivity
  calc
    1 / (3 + a ^ 2) + 3 / (3 + b ^ 2) =
        ((3 + b ^ 2) + 3 * (3 + a ^ 2)) /
          ((3 + a ^ 2) * (3 + b ^ 2)) := by
      field_simp
      <;> ring
    _ ≤ 16 / 13 := by
      apply (div_le_div_iff₀ (mul_pos hda hdb) (by norm_num : (0 : ℝ) < 13)).2
      rw [haeq]
      nlinarith only [hnonneg]
end

-- forge:entry lw_3832 kind=proved origin=external
section
/- Let $a$ , $b$ and $c$ be positive numbers. Prove that: \n $$\sqrt{\frac{a}{a+3b+3c}}+\sqrt{\frac{b}{b+3c+3a}}+\sqrt{\frac{c}{c+3a+3b}}\leq\frac{3}{\sqrt7}$$ $(1,1,8)$ -/
lemma lw_3832_aux1 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hm : x + y ≤ 2 * z) :
    0 ≤ 63 * (x ^ 2 + y ^ 2 + z ^ 2) * (x + y + z) ^ 4 +
      648 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2) * (x + y + z) ^ 2 +
      2916 * x ^ 2 * y ^ 2 * z ^ 2 - 49 * (x + y + z) ^ 6 := by
  let m := (x + y) / 2
  let d := (x - y) / 2
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  have hzm : 0 ≤ z - m := by dsimp [m]; linarith
  have hpos : 0 ≤
      2 * (z - m) ^ 2 * (z - 4 * m) ^ 2 * (7 * z ^ 2 + 28 * m * z + 46 * m ^ 2) +
      d ^ 2 * (1422 * (z - m) ^ 4 + 11880 * m * (z - m) ^ 3 +
        28188 * m ^ 2 * (z - m) ^ 2 + 25272 * m ^ 3 * (z - m) + 4374 * m ^ 4) +
      d ^ 4 * (3564 * z ^ 2 + 2592 * m * z + 2592 * m ^ 2) := by positivity
  convert hpos using 1 <;> dsimp [m, d] <;> ring

lemma lw_3832_aux2 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ 63 * (x ^ 2 + y ^ 2 + z ^ 2) * (x + y + z) ^ 4 +
      648 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2) * (x + y + z) ^ 2 +
      2916 * x ^ 2 * y ^ 2 * z ^ 2 - 49 * (x + y + z) ^ 6 := by
  rcases le_total x z with hxz | hzx
  · rcases le_total y z with hyz | hzy
    · exact lw_3832_aux1 x y z hx hy hz (by linarith)
    · have h := lw_3832_aux1 x z y hx hz hy (by linarith)
      convert h using 1 <;> ring
  · rcases le_total y x with hyx | hxy
    · have h := lw_3832_aux1 y z x hy hz hx (by linarith)
      convert h using 1 <;> ring
    · have h := lw_3832_aux1 x z y hx hz hy (by linarith)
      convert h using 1 <;> ring

lemma lw_3832_aux3 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : x ^ 2 + y ^ 2 + z ^ 2 +
      8 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2) +
      28 * x ^ 2 * y ^ 2 * z ^ 2 = 1) :
    7 * (x + y + z) ^ 2 ≤ 9 := by
  have hp := lw_3832_aux2 x y z hx hy hz
  let t := (x + y + z) ^ 2
  let q := x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2
  let r := x ^ 2 * y ^ 2 * z ^ 2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have he :
      (9 - 7 * t) * (49 * t ^ 2 + 504 * t * q + 252 * (9 + 7 * t) * r) =
      7 * (63 * (x ^ 2 + y ^ 2 + z ^ 2) * (x + y + z) ^ 4 +
      648 * q * (x + y + z) ^ 2 + 2916 * r - 49 * (x + y + z) ^ 6) := by
    dsimp [t, q, r] at *
    linear_combination -441 * (x + y + z) ^ 4 * h
  by_contra hn
  have hgt : 9 < 7 * t := by dsimp [t]; linarith
  have hfac : 0 < 49 * t ^ 2 + 504 * t * q + 252 * (9 + 7 * t) * r := by
    have ht0 : 0 < t := by linarith
    positivity
  have hneg := mul_neg_of_neg_of_pos (by linarith : 9 - 7 * t < 0) hfac
  rw [he] at hneg
  dsimp [q, r] at hneg
  linarith

theorem lw_3832 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    √(a / (a + 3 * b + 3 * c)) + √(b / (b + 3 * c + 3 * a)) +
      √(c / (c + 3 * a + 3 * b)) ≤ 3 / √7 := by
  have haD : 0 < a + 3 * b + 3 * c := by positivity
  have hbD : 0 < b + 3 * c + 3 * a := by positivity
  have hcD : 0 < c + 3 * a + 3 * b := by positivity
  let x := √(a / (a + 3 * b + 3 * c))
  let y := √(b / (b + 3 * c + 3 * a))
  let z := √(c / (c + 3 * a + 3 * b))
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = a / (a + 3 * b + 3 * c) := Real.sq_sqrt (by positivity)
  have hy2 : y ^ 2 = b / (b + 3 * c + 3 * a) := Real.sq_sqrt (by positivity)
  have hz2 : z ^ 2 = c / (c + 3 * a + 3 * b) := Real.sq_sqrt (by positivity)
  have he : x ^ 2 + y ^ 2 + z ^ 2 +
      8 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2) +
      28 * x ^ 2 * y ^ 2 * z ^ 2 = 1 := by
    rw [hx2, hy2, hz2]
    field_simp
    <;> ring
  have hs := lw_3832_aux3 x y z hx hy hz he
  have h7 : (√(7 : ℝ)) ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have h7p : 0 < √(7 : ℝ) := by positivity
  change x + y + z ≤ 3 / √7
  apply (le_div_iff₀ h7p).2
  have hnon : 0 ≤ (x + y + z) * √7 := by positivity
  nlinarith [sq_nonneg ((x + y + z) * √7 - 3)]
end

-- forge:entry lw_4050 kind=proved origin=external
section
/- Let $a,b,c$ be positive reals such that $a+2b=1.$ Prove that \n $$\frac{1}{a}+\frac{1}{ \sqrt{ab}}\geq \frac {9}{2}$$ -/
theorem lw_4050 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a + 2 * b = 1) : 1 / a + 1 / Real.sqrt (a * b) ≥ 9 / 2 := by
  let s := Real.sqrt (a * b)
  have hs : 0 < s := Real.sqrt_pos.2 (mul_pos ha hb)
  have hs_sq : s ^ 2 = a * b := Real.sq_sqrt (le_of_lt (mul_pos ha hb))
  have hnorm : a ^ 2 + 2 * s ^ 2 = a := by
    nlinarith [congrArg (fun x : ℝ => a * x) hab]
  have hpoly : 0 ≤ a * (2 * a + 2 * s - 9 * a * s) := by
    have hpos : 0 ≤ 2 * a + s := by positivity
    have hsq := mul_nonneg (sq_nonneg (a - 2 * s)) hpos
    nlinarith [congrArg (fun x : ℝ => a * x) hnorm,
      congrArg (fun x : ℝ => s * x) hnorm]
  have hbound : 0 ≤ 2 * a + 2 * s - 9 * a * s :=
    nonneg_of_mul_nonneg_right hpoly ha
  change 9 / 2 ≤ 1 / a + 1 / s
  rw [div_add_div _ _ (ne_of_gt ha) (ne_of_gt hs)]
  apply (le_div_iff₀ (mul_pos ha hs)).2
  nlinarith
end

-- forge:entry lw_41213 kind=proved origin=external
section
/- Let $ a,b,c\geq 0$ be nonnegative real numbers. Prove that \n $ a^3 + b^3 + c^3 + 3abc\cdot \frac {a^2b + b^2c + c^2a}{ab^2 + bc^2 + ca^2} \ge ab(a + b) + bc(b + c) + ca(c + a).$ \nWhen does equality occur? -/
lemma lw_41213_aux1 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ ((z+x+y) ^ 3 + (z+y) ^ 3 + (z) ^ 3 - ((z+x+y) ^ 2 * (z+y) + (z+y) ^ 2 * (z) + (z) ^ 2 * (z+x+y)) - ((z+x+y) * (z+y) ^ 2 + (z+y) * (z) ^ 2 + (z) * (z+x+y) ^ 2)) * ((z+x+y) * (z+y) ^ 2 + (z+y) * (z) ^ 2 + (z) * (z+x+y) ^ 2) + 3 * (z+x+y) * (z+y) * (z) * ((z+x+y) ^ 2 * (z+y) + (z+y) ^ 2 * (z) + (z) ^ 2 * (z+x+y)) := by
  have hid : ((z+x+y) ^ 3 + (z+y) ^ 3 + (z) ^ 3 - ((z+x+y) ^ 2 * (z+y) + (z+y) ^ 2 * (z) + (z) ^ 2 * (z+x+y)) - ((z+x+y) * (z+y) ^ 2 + (z+y) * (z) ^ 2 + (z) * (z+x+y) ^ 2)) * ((z+x+y) * (z+y) ^ 2 + (z+y) * (z) ^ 2 + (z) * (z+x+y) ^ 2) + 3 * (z+x+y) * (z+y) * (z) * ((z+x+y) ^ 2 * (z+y) + (z+y) ^ 2 * (z) + (z) ^ 2 * (z+x+y)) =
      x ^ 5 * z + x ^ 4 * y ^ 2 + 6 * x ^ 4 * y * z + 4 * x ^ 4 * z ^ 2 + 3 * x ^ 3 * y ^ 3 + 16 * x ^ 3 * y ^ 2 * z + 20 * x ^ 3 * y * z ^ 2 + 6 * x ^ 3 * z ^ 3 + 2 * x ^ 2 * y ^ 4 + 16 * x ^ 2 * y ^ 3 * z + 30 * x ^ 2 * y ^ 2 * z ^ 2 + 18 * x ^ 2 * y * z ^ 3 + 3 * x ^ 2 * z ^ 4 + 5 * x * y ^ 4 * z + 14 * x * y ^ 3 * z ^ 2 + 12 * x * y ^ 2 * z ^ 3 + 3 * x * y * z ^ 4 + y ^ 5 * z + 4 * y ^ 4 * z ^ 2 + 6 * y ^ 3 * z ^ 3 + 3 * y ^ 2 * z ^ 4 := by ring
  rw [hid]
  positivity

lemma lw_41213_aux2 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ ((z+y) ^ 3 + (z+x+y) ^ 3 + (z) ^ 3 - ((z+y) ^ 2 * (z+x+y) + (z+x+y) ^ 2 * (z) + (z) ^ 2 * (z+y)) - ((z+y) * (z+x+y) ^ 2 + (z+x+y) * (z) ^ 2 + (z) * (z+y) ^ 2)) * ((z+y) * (z+x+y) ^ 2 + (z+x+y) * (z) ^ 2 + (z) * (z+y) ^ 2) + 3 * (z+y) * (z+x+y) * (z) * ((z+y) ^ 2 * (z+x+y) + (z+x+y) ^ 2 * (z) + (z) ^ 2 * (z+y)) := by
  have hid : ((z+y) ^ 3 + (z+x+y) ^ 3 + (z) ^ 3 - ((z+y) ^ 2 * (z+x+y) + (z+x+y) ^ 2 * (z) + (z) ^ 2 * (z+y)) - ((z+y) * (z+x+y) ^ 2 + (z+x+y) * (z) ^ 2 + (z) * (z+y) ^ 2)) * ((z+y) * (z+x+y) ^ 2 + (z+x+y) * (z) ^ 2 + (z) * (z+y) ^ 2) + 3 * (z+y) * (z+x+y) * (z) * ((z+y) ^ 2 * (z+x+y) + (z+x+y) ^ 2 * (z) + (z) ^ 2 * (z+y)) =
      x ^ 5 * y + x ^ 5 * z + 4 * x ^ 4 * y ^ 2 + 7 * x ^ 4 * y * z + 4 * x ^ 4 * z ^ 2 + 5 * x ^ 3 * y ^ 3 + 12 * x ^ 3 * y ^ 2 * z + 14 * x ^ 3 * y * z ^ 2 + 6 * x ^ 3 * z ^ 3 + 2 * x ^ 2 * y ^ 4 + 6 * x ^ 2 * y ^ 3 * z + 12 * x ^ 2 * y ^ 2 * z ^ 2 + 12 * x ^ 2 * y * z ^ 3 + 3 * x ^ 2 * z ^ 4 + 2 * x * y ^ 3 * z ^ 2 + 6 * x * y ^ 2 * z ^ 3 + 3 * x * y * z ^ 4 + y ^ 5 * z + 4 * y ^ 4 * z ^ 2 + 6 * y ^ 3 * z ^ 3 + 3 * y ^ 2 * z ^ 4 := by ring
  rw [hid]
  positivity

lemma lw_41213_aux3 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ ((a) ^ 3 + (b) ^ 3 + (c) ^ 3 - ((a) ^ 2 * (b) + (b) ^ 2 * (c) + (c) ^ 2 * (a)) - ((a) * (b) ^ 2 + (b) * (c) ^ 2 + (c) * (a) ^ 2)) * ((a) * (b) ^ 2 + (b) * (c) ^ 2 + (c) * (a) ^ 2) + 3 * (a) * (b) * (c) * ((a) ^ 2 * (b) + (b) ^ 2 * (c) + (c) ^ 2 * (a)) := by
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · convert lw_41213_aux2 (c - b) (b - a) a
        (sub_nonneg.mpr hbc) (sub_nonneg.mpr hab) ha using 1 <;> ring
    · rcases le_total a c with hac | hca
      · convert lw_41213_aux1 (b - c) (c - a) a
          (sub_nonneg.mpr hcb) (sub_nonneg.mpr hac) ha using 1 <;> ring
      · convert lw_41213_aux2 (b - a) (a - c) c
          (sub_nonneg.mpr hab) (sub_nonneg.mpr hca) hc using 1 <;> ring
  · rcases le_total a c with hac | hca
    · convert lw_41213_aux1 (c - a) (a - b) b
        (sub_nonneg.mpr hac) (sub_nonneg.mpr hba) hb using 1 <;> ring
    · rcases le_total b c with hbc | hcb
      · convert lw_41213_aux2 (a - c) (c - b) b
          (sub_nonneg.mpr hca) (sub_nonneg.mpr hbc) hb using 1 <;> ring
      · convert lw_41213_aux1 (a - b) (b - c) c
          (sub_nonneg.mpr hba) (sub_nonneg.mpr hcb) hc using 1 <;> ring

theorem lw_41213 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a^3 + b^3 + c^3 + 3 * a * b * c * (a^2 * b + b^2 * c + c^2 * a) /
      (a * b^2 + b * c^2 + c * a^2) ≥
      a * b * (a + b) + b * c * (b + c) + c * a * (c + a) := by
  have h1 : 0 ≤ a * b ^ 2 := mul_nonneg ha (sq_nonneg b)
  have h2 : 0 ≤ b * c ^ 2 := mul_nonneg hb (sq_nonneg c)
  have h3 : 0 ≤ c * a ^ 2 := mul_nonneg hc (sq_nonneg a)
  by_cases hq : a * b ^ 2 + b * c ^ 2 + c * a ^ 2 = 0
  · have hab2 : a * b ^ 2 = 0 := by linarith
    have hbc2 : b * c ^ 2 = 0 := by linarith
    have hca2 : c * a ^ 2 = 0 := by linarith
    have hab : a * b = 0 := by
      rcases mul_eq_zero.mp hab2 with h | h
      · simp [h]
      · simp [sq_eq_zero_iff.mp h]
    have hbc : b * c = 0 := by
      rcases mul_eq_zero.mp hbc2 with h | h
      · simp [h]
      · simp [sq_eq_zero_iff.mp h]
    have hca : c * a = 0 := by
      rcases mul_eq_zero.mp hca2 with h | h
      · simp [h]
      · simp [sq_eq_zero_iff.mp h]
    simp only [hq, div_zero, add_zero, hab, hbc, hca, zero_mul]
    positivity
  · have hqpos : 0 < a * b ^ 2 + b * c ^ 2 + c * a ^ 2 :=
      lt_of_le_of_ne (by positivity) (Ne.symm hq)
    rw [add_div_eq_mul_add_div _ _ hq]
    apply (le_div_iff₀ hqpos).2
    nlinarith only [lw_41213_aux3 a b c ha hb hc]
end

-- forge:entry lw_43103 kind=disproved origin=external
section
/- Prove that: \n $\frac{a}{{\sqrt {a + 3b} }} + \frac{b}{{\sqrt {b + 3c} }} + \frac{c}{{\sqrt {c + 3d} }} + \frac{d}{{\sqrt {d + 3a} }} \ge \sqrt {a + b + c + d} $\n -/
theorem lw_43103_disproof : ¬ (∀ (a b c d : ℝ),
    (a / Real.sqrt (a + 3 * b) + b / Real.sqrt (b + 3 * c) +
      c / Real.sqrt (c + 3 * d) + d / Real.sqrt (d + 3 * a)) ≥
      Real.sqrt (a + b + c + d)) := by
  intro h
  have hbad := h (-2) 1 0 0
  norm_num [Real.sqrt_eq_zero_of_nonpos] at hbad
end

-- forge:entry lw_41875 kind=proved origin=external
section
/- Let $ a,b> 0 $ and $a+b+ab\leq 3 .$ Prove that \n $$ \frac{a}{b}+\frac{b}{a} +\frac{72 }{a+b+1}\geq 26$$ \n $$ \frac{a}{b^2}+\frac{b}{a^2} +\frac{171 }{a+b+1} \geq 59$$ \n $$\frac{a^2}{b^2}+\frac{b^2}{a^2} +\frac{288}{a+b+1} \geq 98$$ -/
lemma lw_41875_aux1 (s p : ℝ) (hs : 2 ≤ s) (hp : 0 ≤ p)
    (hsp : s + p ≤ 3) :
    0 ≤ s ^ 2 * (s + 1) + (44 - 28 * s) * p ∧
    0 ≤ s ^ 3 * (s + 1) - 3 * p * s * (s + 1) + (112 - 59 * s) * p ^ 2 ∧
    0 ≤ s ^ 4 * (s + 1) - 4 * s ^ 2 * (s + 1) * p + (192 - 96 * s) * p ^ 2 := by
  have hs0 : 0 ≤ s := by linarith
  have hc₁ : 0 ≤ 28 * s - 44 := by linarith
  have hs3 : s ≤ 3 := by linarith
  have hq : 0 ≤ 3 - s := by linarith
  have hr : 0 ≤ 3 - s - p := by linarith
  have h₁ : 0 ≤ (s - 2) ^ 2 * (s + 33) + (3 - s - p) * (28 * s - 44) := by positivity
  have hc₂ : 0 ≤ s ^ 2 - 51 * s + 252 := by nlinarith [sq_nonneg s]
  have hc₃ : 0 ≤ s ^ 3 + 9 * s ^ 2 - 72 * s + 432 := by
    nlinarith [sq_nonneg s, pow_nonneg hs0 3]
  constructor
  · nlinarith only [h₁]
  constructor
  · have h₂ : 0 ≤ (s - 2) ^ 2 * (s ^ 2 - 51 * s + 252) +
        (3 - s - p) * (3 * s * (s + 1) + (59 * s - 112) * (p + (3 - s))) := by
      apply add_nonneg (mul_nonneg (sq_nonneg _) hc₂)
      apply mul_nonneg hr
      have : 0 ≤ 59 * s - 112 := by linarith
      positivity
    nlinarith only [h₂]
  · have h₃ : 0 ≤ (s - 2) ^ 2 * (s ^ 3 + 9 * s ^ 2 - 72 * s + 432) +
        (3 - s - p) * (4 * s ^ 2 * (s + 1) + (96 * s - 192) * (p + (3 - s))) := by
      apply add_nonneg (mul_nonneg (sq_nonneg _) hc₃)
      apply mul_nonneg hr
      have : 0 ≤ 96 * s - 192 := by linarith
      positivity
    nlinarith only [h₃]

lemma lw_41875_aux2 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : a + b ≤ 2) :
    0 ≤ (a + b) ^ 2 * (a + b + 1) + (44 - 28 * (a + b)) * (a * b) ∧
    0 ≤ (a + b) ^ 3 * (a + b + 1) - 3 * (a * b) * (a + b) * (a + b + 1) +
      (112 - 59 * (a + b)) * (a * b) ^ 2 ∧
    0 ≤ (a + b) ^ 4 * (a + b + 1) - 4 * (a + b) ^ 2 * (a + b + 1) * (a * b) +
      (192 - 96 * (a + b)) * (a * b) ^ 2 := by
  have ht : 0 ≤ 2 - (a + b) := by linarith
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hd : 0 ≤ (a - b) ^ 2 := sq_nonneg _
  have hs0 : 0 ≤ a + b := add_nonneg ha hb
  have hsum : 0 ≤ (a + b) * (2 - (a + b)) := mul_nonneg hs0 (by linarith)
  have hpa : 0 ≤ a + b - 2 * (a * b) := by nlinarith
  have hcub : 0 ≤ a ^ 3 + b ^ 3 - 2 * (a * b) ^ 2 := by
    have h : 0 ≤ (a + b) * (a - b) ^ 2 + a * b * (a + b - 2 * (a * b)) := by positivity
    nlinarith only [h]
  constructor
  · have h : 0 ≤ (a - b) ^ 2 * (a + b + 1) + 24 * (a * b) * (2 - (a + b)) := by positivity
    nlinarith only [h]
  constructor
  · have h : 0 ≤ (a ^ 3 + b ^ 3 - 2 * (a * b) ^ 2) * (a + b + 1) +
        57 * (a * b) ^ 2 * (2 - (a + b)) := by positivity
    nlinarith only [h]
  · have h : 0 ≤ (a ^ 2 - b ^ 2) ^ 2 * (a + b + 1) +
        96 * (a * b) ^ 2 * (2 - (a + b)) := by positivity
    nlinarith only [h]

theorem lw_41875 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b + a * b ≤ 3) :
    a / b + b / a + 72 / (a + b + 1) ≥ 26 ∧
    a / b^2 + b / a^2 + 171 / (a + b + 1) ≥ 59 ∧
    a^2 / b^2 + b^2 / a^2 + 288 / (a + b + 1) ≥ 98 := by
  have hpoly :
      0 ≤ (a + b) ^ 2 * (a + b + 1) + (44 - 28 * (a + b)) * (a * b) ∧
      0 ≤ (a + b) ^ 3 * (a + b + 1) - 3 * (a * b) * (a + b) * (a + b + 1) +
        (112 - 59 * (a + b)) * (a * b) ^ 2 ∧
      0 ≤ (a + b) ^ 4 * (a + b + 1) - 4 * (a + b) ^ 2 * (a + b + 1) * (a * b) +
        (192 - 96 * (a + b)) * (a * b) ^ 2 := by
    by_cases hs : a + b ≤ 2
    · exact lw_41875_aux2 a b ha.le hb.le hs
    · exact lw_41875_aux1 (a + b) (a * b) (by linarith) (by positivity) hab
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hs0 : a + b + 1 ≠ 0 := by positivity
  constructor
  · apply sub_nonneg.mp
    convert div_nonneg hpoly.1 (show 0 ≤ a * b * (a + b + 1) by positivity) using 1 <;>
      field_simp <;> ring
  constructor
  · apply sub_nonneg.mp
    convert div_nonneg hpoly.2.1 (show 0 ≤ (a * b) ^ 2 * (a + b + 1) by positivity) using 1 <;>
      field_simp <;> ring
  · apply sub_nonneg.mp
    convert div_nonneg hpoly.2.2 (show 0 ≤ (a * b) ^ 2 * (a + b + 1) by positivity) using 1 <;>
      field_simp <;> ring
end

-- forge:entry lw_45132 kind=disproved origin=external
section
/- prove that $\frac{a^2+2b}{b+2c}+\frac{b^2+2c}{c+2a}+\frac{c^2+2a}{a+2b} \ge \frac{7}{3}$ -/
theorem lw_45132_disproof :
    ¬ (∀ (a b c : ℝ),
      (a^2 + 2 * b) / (b + 2 * c) +
      (b^2 + 2 * c) / (c + 2 * a) +
      (c^2 + 2 * a) / (a + 2 * b) ≥ 7 / 3) := by
  intro h
  have hneg := h (-1) (-1) (-1)
  norm_num at hneg
end

-- forge:entry lw_44792 kind=disproved origin=external
section
/- Homogenised obtain: \n $ \sqrt{\frac{(x+y+z)\sqrt[3]{xyz}}{3}}\le\sqrt[3]{\frac{(x+y)(y+z)(z+x)}{8}} $ -/
theorem lw_44792_disproof :
    ¬ (∀ (x y z : ℝ),
      Real.sqrt ((x + y + z) * (x * y * z)^(1 / 3) / 3) ≤
        (x + y) * (y + z) * (z + x) / 8) := by
  intro h
  have hnonneg : (0 : ℝ) ≤
      ((-1 : ℝ) + -1) * ((-1 : ℝ) + -1) * ((-1 : ℝ) + -1) / 8 :=
    (Real.sqrt_nonneg _).trans (h (-1) (-1) (-1))
  norm_num at hnonneg
end

-- forge:entry lw_46571 kind=disproved origin=external
section
/- Prove that \n $$8(a^2+b^2) \ge (a^2-b^2)^2+4\sqrt{2}(a+b)(a^2+b^2)\sqrt{a^2+b^2} $$ -/
theorem lw_46571_disproof : ¬ (∀ a b : ℝ, 8 * (a ^ 2 + b ^ 2) ≥ (a ^ 2 - b ^ 2) ^ 2 + 4 * Real.sqrt 2 * (a + b) * (a ^ 2 + b ^ 2) * Real.sqrt (a ^ 2 + b ^ 2)) := by
  intro h
  have h30 := h 3 0
  norm_num at h30
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]
end

-- forge:entry lw_43396 kind=proved origin=external
section
/- Suppose that $a, b, c, d, e, f >0$ . Prove that $\sqrt{ab} + \sqrt{cd} + \sqrt{ ef} \leq \sqrt{(a+c+e)(b+d+f)}$ , with equality if and only if $\frac{a}{b} = \frac{c}{d} = \frac{e}{f}$ . -/
lemma lw_43396_aux1 (a b c d e f : ℝ) :
    (a * b + c * d + e * f) ^ 2 =
        (a ^ 2 + c ^ 2 + e ^ 2) * (b ^ 2 + d ^ 2 + f ^ 2) ↔
      a * d = c * b ∧ c * f = e * d ∧ a * f = e * b := by
  have hid :
      (a ^ 2 + c ^ 2 + e ^ 2) * (b ^ 2 + d ^ 2 + f ^ 2) -
        (a * b + c * d + e * f) ^ 2 =
      (a * d - c * b) ^ 2 + (c * f - e * d) ^ 2 + (a * f - e * b) ^ 2 := by
    ring
  constructor
  · intro h
    have hz : (a * d - c * b) ^ 2 + (c * f - e * d) ^ 2 +
        (a * f - e * b) ^ 2 = 0 := by
      rw [← hid, h]
      ring
    have h1 : (a * d - c * b) ^ 2 = 0 := by
      nlinarith only [hz, sq_nonneg (a * d - c * b),
        sq_nonneg (c * f - e * d), sq_nonneg (a * f - e * b)]
    have h2 : (c * f - e * d) ^ 2 = 0 := by
      nlinarith only [hz, sq_nonneg (a * d - c * b),
        sq_nonneg (c * f - e * d), sq_nonneg (a * f - e * b)]
    have h3 : (a * f - e * b) ^ 2 = 0 := by
      nlinarith only [hz, sq_nonneg (a * d - c * b),
        sq_nonneg (c * f - e * d), sq_nonneg (a * f - e * b)]
    exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp h1),
      sub_eq_zero.mp (sq_eq_zero_iff.mp h2), sub_eq_zero.mp (sq_eq_zero_iff.mp h3)⟩
  · rintro ⟨h1, h2, h3⟩
    rw [h1, h2, h3] at hid
    nlinarith only [hid]

theorem lw_43396 (a b c d e f : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f) :
    (Real.sqrt (a * b) + Real.sqrt (c * d) + Real.sqrt (e * f)) ≤
        Real.sqrt ((a + c + e) * (b + d + f)) ∧
      (Real.sqrt (a * b) + Real.sqrt (c * d) + Real.sqrt (e * f)) =
        Real.sqrt ((a + c + e) * (b + d + f)) ↔
      a / b = c / d ∧ c / d = e / f := by
  have hprod : 0 ≤ (a + c + e) * (b + d + f) := by positivity
  rw [Real.sqrt_mul ha.le, Real.sqrt_mul hc.le, Real.sqrt_mul he.le]
  constructor
  · rintro ⟨_, h⟩
    have hs := congrArg (fun x : ℝ => x ^ 2) h
    dsimp only at hs
    rw [Real.sq_sqrt hprod] at hs
    have hsq :
        (Real.sqrt a * Real.sqrt b + Real.sqrt c * Real.sqrt d +
          Real.sqrt e * Real.sqrt f) ^ 2 =
        ((Real.sqrt a) ^ 2 + (Real.sqrt c) ^ 2 + (Real.sqrt e) ^ 2) *
          ((Real.sqrt b) ^ 2 + (Real.sqrt d) ^ 2 + (Real.sqrt f) ^ 2) := by
      simpa only [Real.sq_sqrt ha.le, Real.sq_sqrt hb.le, Real.sq_sqrt hc.le,
        Real.sq_sqrt hd.le, Real.sq_sqrt he.le, Real.sq_sqrt hf.le] using hs
    obtain ⟨h1, h2, _⟩ :=
      (lw_43396_aux1 (Real.sqrt a) (Real.sqrt b) (Real.sqrt c)
        (Real.sqrt d) (Real.sqrt e) (Real.sqrt f)).mp hsq
    constructor
    · apply (div_eq_div_iff hb.ne' hd.ne').mpr
      have hh := congrArg (fun x : ℝ => x ^ 2) h1
      simpa only [mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hb.le,
        Real.sq_sqrt hc.le, Real.sq_sqrt hd.le] using hh
    · apply (div_eq_div_iff hd.ne' hf.ne').mpr
      have hh := congrArg (fun x : ℝ => x ^ 2) h2
      simpa only [mul_pow, Real.sq_sqrt hc.le, Real.sq_sqrt hd.le,
        Real.sq_sqrt he.le, Real.sq_sqrt hf.le] using hh
  · rintro ⟨h1, h2⟩
    have h3 := h1.trans h2
    have hc1 := (div_eq_div_iff hb.ne' hd.ne').mp h1
    have hc2 := (div_eq_div_iff hd.ne' hf.ne').mp h2
    have hc3 := (div_eq_div_iff hb.ne' hf.ne').mp h3
    have hr1 : Real.sqrt a * Real.sqrt d = Real.sqrt c * Real.sqrt b := by
      simpa only [Real.sqrt_mul ha.le, Real.sqrt_mul hc.le] using
        congrArg Real.sqrt hc1
    have hr2 : Real.sqrt c * Real.sqrt f = Real.sqrt e * Real.sqrt d := by
      simpa only [Real.sqrt_mul hc.le, Real.sqrt_mul he.le] using
        congrArg Real.sqrt hc2
    have hr3 : Real.sqrt a * Real.sqrt f = Real.sqrt e * Real.sqrt b := by
      simpa only [Real.sqrt_mul ha.le, Real.sqrt_mul he.le] using
        congrArg Real.sqrt hc3
    have hs := (lw_43396_aux1 (Real.sqrt a) (Real.sqrt b) (Real.sqrt c)
      (Real.sqrt d) (Real.sqrt e) (Real.sqrt f)).mpr ⟨hr1, hr2, hr3⟩
    simp only [Real.sq_sqrt ha.le, Real.sq_sqrt hb.le, Real.sq_sqrt hc.le,
      Real.sq_sqrt hd.le, Real.sq_sqrt he.le, Real.sq_sqrt hf.le] at hs
    have hsum : 0 ≤ Real.sqrt a * Real.sqrt b + Real.sqrt c * Real.sqrt d +
        Real.sqrt e * Real.sqrt f := by positivity
    have heq : Real.sqrt a * Real.sqrt b + Real.sqrt c * Real.sqrt d +
        Real.sqrt e * Real.sqrt f = Real.sqrt ((a + c + e) * (b + d + f)) := by
      nlinarith only [hs, hsum, Real.sqrt_nonneg ((a + c + e) * (b + d + f)),
        Real.sq_sqrt hprod]
    exact ⟨le_of_eq heq, heq⟩
end

-- forge:entry lw_48624 kind=disproved origin=external
section
/- Determine if the inequality $\left(x^2+\dfrac{1}{2}x\right)^2 < x^4+x^3+x^2+x+1 < \left(x^2+\dfrac{1}{2}x+\dfrac{1}{2}\right)^2$ holds for all integers $x \geq 4$, and find the solutions for $x = 0, 1, 2, 3$. -/
theorem lw_48624_disproof :
    ¬ (∀ (x : ℤ) (hx : x ≥ 4),
      (x^2 + 1/2*x)^2 < x^4 + x^3 + x^2 + x + 1 ∧
        x^4 + x^3 + x^2 + x + 1 < (x^2 + 1/2*x + 1/2)^2) := by
  intro h
  have hfour := h 4 (by norm_num)
  norm_num at hfour
end

end Mathlib2
