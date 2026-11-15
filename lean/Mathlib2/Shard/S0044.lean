/- Mathlib2 分片 44（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0043
namespace Mathlib2

-- forge:entry lw_11611 kind=proved origin=external
section
/- Let $a,b,c>0$ satisfy $b+c\leq a.$ Prove: $\frac{1}{a}(b+c)+a(\frac{1}{b}+\frac{1}{c})\geq 5$ -/
theorem lw_11611 (a b c : ℝ) (h1 : 0 < a ∧ 0 < b ∧ 0 < c)
    (h2 : b + c ≤ a) :
    1 / a * (b + c) + a * (1 / b + 1 / c) ≥ 5 := by
  rcases h1 with ⟨ha, hb, hc⟩
  have hgap : 0 ≤ a - (b + c) := sub_nonneg.mpr h2
  have hbc : 0 ≤ a * (b + c) - b * c := by
    have hprod : 0 ≤ (a - (b + c)) * (b + c) :=
      mul_nonneg hgap (by positivity)
    nlinarith [sq_nonneg b, sq_nonneg c, mul_pos hb hc]
  have hp : 0 ≤ a * (b - c) ^ 2 +
      (a - (b + c)) * (a * (b + c) - b * c) :=
    add_nonneg (mul_nonneg ha.le (sq_nonneg (b - c))) (mul_nonneg hgap hbc)
  have heq : 1 / a * (b + c) + a * (1 / b + 1 / c) =
      ((b + c) * b * c + a ^ 2 * (b + c)) / (a * b * c) := by
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc]
    <;> ring
  rw [heq]
  apply (le_div_iff₀ (by positivity : 0 < a * b * c)).2
  nlinarith only [hp]
end

-- forge:entry lw_10713 kind=proved origin=external
section
/- Let $x,y,z>0$ and $x^2+y^2+z^2=3$ \n $\left(x+2y+z\right) \left(\frac{x}{y}+\frac{2y}{z}+\frac{z}{x}\right) \geq 12$ -/
theorem lw_10713_aux1 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    48 * (x ^ 2 + y ^ 2 + z ^ 2) * (x * y * z) ^ 2 ≤
      ((x + 2 * y + z) * (x ^ 2 * z + 2 * x * y ^ 2 + y * z ^ 2)) ^ 2 := by
  have hs : 0 ≤
      1 * (y ^ 2 * z ^ 6) +
      (59 / 15 : ℝ) * (y * z ^ 3) * (1 * (x ^ 2) - (y * z)) ^ 2 +
      (4 / 3 : ℝ) * (z ^ 4) * ((1 / 4 : ℝ) * (x ^ 2) - (y ^ 2)) ^ 2 +
      (479 / 340 : ℝ) * (x * y ^ 2 * z ^ 3) * (1 * (x) - (z)) ^ 2 +
      4 * (x * y * z ^ 4) * ((1 / 2 : ℝ) * (x) - (y)) ^ 2 +
      16 * (x * y ^ 4 * z) * ((1 / 4 : ℝ) * (x) - (z)) ^ 2 +
      16 * (x * y ^ 3 * z ^ 2) * ((1 / 4 : ℝ) * (x) - (y)) ^ 2 +
      (313 / 510 : ℝ) * (x ^ 2 * y * z ^ 3) * (1 * (y) - (z)) ^ 2 +
      (265 / 408 : ℝ) * (x ^ 2 * y * z ^ 3) * (2 * (y) - (z)) ^ 2 +
      1 * (x * y ^ 3) * (4 * (x * y) - (z ^ 2)) ^ 2 +
      1 * (x ^ 2 * y ^ 3 * z) * (4 * (y) - (z)) ^ 2 +
      (501 / 680 : ℝ) * (x ^ 2 * y * z ^ 3) * (4 * (y) - (z)) ^ 2 +
      16 * (x ^ 2 * y ^ 6) +
      3 * (x * y * z ^ 4) * (1 * (x) - (y)) ^ 2 +
      (13 / 68 : ℝ) * (x ^ 3 * y ^ 2 * z) * (4 * (x) - (z)) ^ 2 +
      (320 / 17 : ℝ) * (x ^ 3 * y * z ^ 2) * ((1 / 4 : ℝ) * (x) - (y)) ^ 2 +
      (1952 / 85 : ℝ) * (x ^ 3 * z) * ((1 / 4 : ℝ) * (x * z) - (y ^ 2)) ^ 2 +
      4 * (x ^ 2 * y ^ 4 * z ^ 2) +
      (8 / 3 : ℝ) * (z ^ 4) * ((1 / 2 : ℝ) * (x ^ 2) - (y ^ 2)) ^ 2 +
      (16 / 17 : ℝ) * (x ^ 3 * y ^ 2 * z) * (1 * (x) - (z)) ^ 2 +
      1 * (x ^ 4 * y * z) * (4 * (y) - (z)) ^ 2 +
      (201 / 340 : ℝ) * (x * y ^ 2 * z ^ 3) * (4 * (x) - (z)) ^ 2 +
      (1 / 4 : ℝ) * (x ^ 4) * (4 * (y ^ 2) - (z ^ 2)) ^ 2 +
      (3 / 85 : ℝ) * (x ^ 3 * z) * (4 * (x * z) - (y ^ 2)) ^ 2 +
      (3 / 17 : ℝ) * (x ^ 3 * y * z ^ 2) * (4 * (x) - (y)) ^ 2 +
      (1 / 15 : ℝ) * (y * z ^ 3) * (4 * (x ^ 2) - (y * z)) ^ 2 +
      1 * (x ^ 6 * z ^ 2) := by positivity
  have he :
      1 * (y ^ 2 * z ^ 6) +
      (59 / 15 : ℝ) * (y * z ^ 3) * (1 * (x ^ 2) - (y * z)) ^ 2 +
      (4 / 3 : ℝ) * (z ^ 4) * ((1 / 4 : ℝ) * (x ^ 2) - (y ^ 2)) ^ 2 +
      (479 / 340 : ℝ) * (x * y ^ 2 * z ^ 3) * (1 * (x) - (z)) ^ 2 +
      4 * (x * y * z ^ 4) * ((1 / 2 : ℝ) * (x) - (y)) ^ 2 +
      16 * (x * y ^ 4 * z) * ((1 / 4 : ℝ) * (x) - (z)) ^ 2 +
      16 * (x * y ^ 3 * z ^ 2) * ((1 / 4 : ℝ) * (x) - (y)) ^ 2 +
      (313 / 510 : ℝ) * (x ^ 2 * y * z ^ 3) * (1 * (y) - (z)) ^ 2 +
      (265 / 408 : ℝ) * (x ^ 2 * y * z ^ 3) * (2 * (y) - (z)) ^ 2 +
      1 * (x * y ^ 3) * (4 * (x * y) - (z ^ 2)) ^ 2 +
      1 * (x ^ 2 * y ^ 3 * z) * (4 * (y) - (z)) ^ 2 +
      (501 / 680 : ℝ) * (x ^ 2 * y * z ^ 3) * (4 * (y) - (z)) ^ 2 +
      16 * (x ^ 2 * y ^ 6) +
      3 * (x * y * z ^ 4) * (1 * (x) - (y)) ^ 2 +
      (13 / 68 : ℝ) * (x ^ 3 * y ^ 2 * z) * (4 * (x) - (z)) ^ 2 +
      (320 / 17 : ℝ) * (x ^ 3 * y * z ^ 2) * ((1 / 4 : ℝ) * (x) - (y)) ^ 2 +
      (1952 / 85 : ℝ) * (x ^ 3 * z) * ((1 / 4 : ℝ) * (x * z) - (y ^ 2)) ^ 2 +
      4 * (x ^ 2 * y ^ 4 * z ^ 2) +
      (8 / 3 : ℝ) * (z ^ 4) * ((1 / 2 : ℝ) * (x ^ 2) - (y ^ 2)) ^ 2 +
      (16 / 17 : ℝ) * (x ^ 3 * y ^ 2 * z) * (1 * (x) - (z)) ^ 2 +
      1 * (x ^ 4 * y * z) * (4 * (y) - (z)) ^ 2 +
      (201 / 340 : ℝ) * (x * y ^ 2 * z ^ 3) * (4 * (x) - (z)) ^ 2 +
      (1 / 4 : ℝ) * (x ^ 4) * (4 * (y ^ 2) - (z ^ 2)) ^ 2 +
      (3 / 85 : ℝ) * (x ^ 3 * z) * (4 * (x * z) - (y ^ 2)) ^ 2 +
      (3 / 17 : ℝ) * (x ^ 3 * y * z ^ 2) * (4 * (x) - (y)) ^ 2 +
      (1 / 15 : ℝ) * (y * z ^ 3) * (4 * (x ^ 2) - (y * z)) ^ 2 +
      1 * (x ^ 6 * z ^ 2) =
      ((x + 2 * y + z) * (x ^ 2 * z + 2 * x * y ^ 2 + y * z ^ 2)) ^ 2 -
        48 * (x ^ 2 + y ^ 2 + z ^ 2) * (x * y * z) ^ 2 := by ring
  rw [he] at hs
  linarith

theorem lw_10713 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 3) :
    (x + 2 * y + z) * (x / y + 2 * y / z + z / x) ≥ 12 := by
  have hs := lw_10713_aux1 x y z hx.le hy.le hz.le
  let p := (x + 2 * y + z) * (x / y + 2 * y / z + z / x)
  have hp : 0 < p := by dsimp [p]; positivity
  have ht : 0 < (x * y * z) ^ 2 := by positivity
  have he : (x + 2 * y + z) * (x ^ 2 * z + 2 * x * y ^ 2 + y * z ^ 2) =
      p * (x * y * z) := by
    dsimp [p]
    field_simp [ne_of_gt hx, ne_of_gt hy, ne_of_gt hz]
    <;> ring
  rw [he, h, mul_pow] at hs
  have hh : (144 : ℝ) ≤ p ^ 2 := by
    apply (mul_le_mul_iff_left₀ ht).mp
    nlinarith [hs]
  change 12 ≤ p
  nlinarith
end

-- forge:entry lw_13889 kind=disproved origin=external
section
/- If $a,b,c$ are positive numbers and $ab+bc+ca=abc$ , prove that $5(a+b+c) \geq 18 +3(ab+bc+ca)$ . -/
theorem lw_13889_disproof :
    ¬ (∀ (a b c : ℝ)
      (h : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = a * b + b * c + c * a),
      5 * (a + b + c) ≥ 18 + 3 * (a * b + b * c + c * a)) := by
  intro h
  have hfalse := h 3 3 3 (by norm_num)
  norm_num at hfalse
end

-- forge:entry lw_15162 kind=disproved origin=external
section
/- prove that : \n $ \frac {ab}{c(c + a)} + \frac {bc}{a(a + b)} + \frac {ca}{b(b + c)}\geq \frac {a}{c + a} + \frac {b}{a + b} + \frac {c}{b + c}$\n given $ a,b,c \geq 0$ -/
theorem lw_15162_disproof : ¬ (∀ (a b c : ℝ),
    (a * b) / (c * (c + a)) + (b * c) / (a * (a + b)) +
      (c * a) / (b * (b + c)) ≥
    a / (c + a) + b / (a + b) + c / (b + c)) := by
  intro h
  have hbad := h 1 1 0
  norm_num at hbad
end

-- forge:entry lw_14406 kind=disproved origin=external
section
/- Let $a,b,c$ be positive real numbers. \n $$\frac{a^2}{(a+b)^2} + \frac{b^2}{(b+c)^2}+\frac{c^2}{(c+a)^2} \ge \frac12(\frac{b}{a+b}+\frac{c}{b+c}+\frac{a}{c+a} )$$ -/
theorem lw_14406_disproof :
    ¬ (∀ (a b c : ℝ),
      (a^2/(a+b)^2 + b^2/(b+c)^2 + c^2/(c+a)^2) ≥
        1/2 * (b/(a+b) + c/(b+c) + a/(c+a))) := by
  intro h
  have hbad := h 3 1 (-1)
  norm_num at hbad
end

-- forge:entry lw_15324 kind=proved origin=external
section
/- Let $a,b>0$ and $a+b=1.$ Prove that $\frac{16}{a^3}+\frac{1}{b^3}\geq 81.$ -/
theorem lw_15324 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    16 / a ^ 3 + 1 / b ^ 3 ≥ 81 := by
  have ha_bound : 216 - 243 * a ≤ 16 / a ^ 3 := by
    apply (le_div_iff₀ (pow_pos ha 3)).2
    have h := mul_nonneg (sq_nonneg (3 * a - 2))
      (show 0 ≤ 27 * a ^ 2 + 12 * a + 4 by positivity)
    nlinarith
  have hb_bound : 108 - 243 * b ≤ 1 / b ^ 3 := by
    apply (le_div_iff₀ (pow_pos hb 3)).2
    have h := mul_nonneg (sq_nonneg (3 * b - 1))
      (show 0 ≤ 27 * b ^ 2 + 6 * b + 1 by positivity)
    nlinarith
  linarith
end

-- forge:entry lw_16415 kind=proved origin=external
section
/- Let $ a,b,c>0$ such that $ ab+bc+ca=a+b+c$ \nprove that: \n $ \frac{3}{ab+bc+ca+1}+\frac{1}{(1+a)^2}+\frac{1}{(1+b)^2}+\frac{1}{(1+c)^2} \ge \frac{2(a+b+c+3)}{(a+1)(b+1)(c+1)}$ -/
theorem lw_16415 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a * b + b * c + c * a = a + b + c) :
    3 / (a * b + b * c + c * a + 1) + 1 / (1 + a) ^ 2 +
      1 / (1 + b) ^ 2 + 1 / (1 + c) ^ 2 ≥
        2 * (a + b + c + 3) / (a + 1) / (b + 1) / (c + 1) := by
  have ha1 : 0 < 1 + a := by positivity
  have hb1 : 0 < 1 + b := by positivity
  have hc1 : 0 < 1 + c := by positivity
  have hd : 0 < a * b + b * c + c * a + 1 := by positivity
  let x : ℝ := 1 / (1 + a)
  let y : ℝ := 1 / (1 + b)
  let z : ℝ := 1 / (1 + c)
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have hz : 0 < z := by dsimp [z]; positivity
  have hp : 0 < x + y + z := by positivity
  have hs := an_schur_deg_one x y z hx.le hy.le hz.le
  have hid : (x + y + z) * (3 / (a * b + b * c + c * a + 1)) =
      9 * x * y * z := by
    dsimp [x, y, z]
    rw [hab]
    field_simp [ne_of_gt ha1, ne_of_gt hb1, ne_of_gt hc1]
    nlinarith [hab]
  have hrhs : 2 * (a + b + c + 3) / (a + 1) / (b + 1) / (c + 1) =
      2 * (x * y + y * z + z * x) := by
    dsimp [x, y, z]
    field_simp [ne_of_gt ha1, ne_of_gt hb1, ne_of_gt hc1]
    ring
  have hmain : 2 * (x * y + y * z + z * x) ≤
      3 / (a * b + b * c + c * a + 1) + x ^ 2 + y ^ 2 + z ^ 2 := by
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith only [hs, hid]
  rw [hrhs]
  dsimp [x, y, z] at hmain
  simpa only [div_pow, one_pow] using hmain
end

-- forge:entry lw_16903 kind=proved origin=external
section
/- Prove that for $a, b, c > 0$ and $abc = 1$, the following inequality holds: $T = \frac{b^2}{a} + \frac{c^2}{b} + \frac{a^2}{c} + \frac{13}{3(ab + bc + ca)} \ge \frac{14}{9} + \frac{26}{9}$. -/
theorem lw_16903 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (habc : a * b * c = 1) :
    (b ^ 2 / a + c ^ 2 / b + a ^ 2 / c +
      13 / (3 * (a * b + b * c + c * a))) ≥ 14 / 9 + 26 / 9 := by
  set p : ℝ := a + b + c with hpdef
  set q : ℝ := a * b + b * c + c * a with hqdef
  have hp : 0 < p := by dsimp [p]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hcube : 27 ≤ p ^ 3 := by
    have h := an_amgm_three_cube a b c ha.le hb.le hc.le
    rw [habc] at h
    dsimp [p]
    nlinarith only [h]
  have hp3 : 3 ≤ p := by
    by_contra h
    have hlt : p < 3 := lt_of_not_ge h
    have ht : 0 < (3 - p) * (p ^ 2 + 3 * p + 9) :=
      mul_pos (by linarith) (by positivity)
    nlinarith only [hcube, ht]
  have hpq : 3 * q ≤ p ^ 2 := by
    dsimp [p, q]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hs1 : 2 * b - a ≤ b ^ 2 / a := by
    apply (le_div_iff₀ ha).2
    nlinarith [sq_nonneg (a - b)]
  have hs2 : 2 * c - b ≤ c ^ 2 / b := by
    apply (le_div_iff₀ hb).2
    nlinarith [sq_nonneg (b - c)]
  have hs3 : 2 * a - c ≤ a ^ 2 / c := by
    apply (le_div_iff₀ hc).2
    nlinarith [sq_nonneg (c - a)]
  have hs : p ≤ b ^ 2 / a + c ^ 2 / b + a ^ 2 / c := by
    dsimp [p]
    linarith
  have hrec : 13 / p ^ 2 ≤ 13 / (3 * q) := by
    apply (div_le_div_iff₀ (pow_pos hp 2) (by positivity : 0 < 3 * q)).2
    nlinarith only [hpq]
  have hquad : 0 ≤ 9 * p ^ 2 - 13 * p - 39 := by
    nlinarith [sq_nonneg (p - 3)]
  have hfactor := mul_nonneg (sub_nonneg.mpr hp3) hquad
  have huni : (40 : ℝ) / 9 ≤ p + 13 / p ^ 2 := by
    have hid : p + 13 / p ^ 2 = (p ^ 3 + 13) / p ^ 2 := by
      field_simp
      <;> ring
    rw [hid]
    apply (le_div_iff₀ (pow_pos hp 2)).2
    nlinarith only [hfactor]
  change 14 / 9 + 26 / 9 ≤ b ^ 2 / a + c ^ 2 / b + a ^ 2 / c + 13 / (3 * q)
  linarith
end

-- forge:entry lw_19885 kind=proved origin=external
section
/- Given $ x+y+z=1$ and $ x$ , $ y$ , $ z>0$ \n\nProve that: $ x^3+y^3 + z^3 + 6xyz \ge \dfrac{1}{4}$ -/
theorem lw_19885 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h : x + y + z = 1) :
    x ^ 3 + y ^ 3 + z ^ 3 + 6 * x * y * z ≥ 1 / 4 := by
  have hs := an_schur_deg_one x y z hx.le hy.le hz.le
  have hc : (x + y + z) ^ 3 = 1 := by rw [h]; norm_num
  have hp : 0 ≤ x * y * z := by positivity
  nlinarith only [hs, hc, hp]
end

-- forge:entry lw_2456 kind=proved origin=external
section
/- The sum of non-negative numbers $ x $ , $ y $ and $ z $ is $3$ . Prove the inequality\n\n $ {1 \over x ^ 2 + y + z} + {1 \over x + y ^ 2 + z} + {1 \over x + y + z ^ 2} \leq 1. $ -/
lemma lw_2456_aux1 (t : ℝ) (ht : t ≤ 3) :
    1 / (t ^ 2 - t + 3) ≤ (4 - t) / 9 := by
  have hd : 0 < t ^ 2 - t + 3 := by
    nlinarith [sq_nonneg (t - 1 / 2)]
  apply (div_le_iff₀ hd).2
  have hp : 0 ≤ (3 - t) * (t - 1) ^ 2 :=
    mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg (t - 1))
  nlinarith

theorem lw_2456 (x y z : ℝ) (hx : x + y + z = 3)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z) :
    1 / (x ^ 2 + y + z) + 1 / (x + y ^ 2 + z) +
      1 / (x + y + z ^ 2) ≤ 1 := by
  have hx3 : x ≤ 3 := by linarith
  have hy3 : y ≤ 3 := by linarith
  have hz3 : z ≤ 3 := by linarith
  have hdx : x ^ 2 + y + z = x ^ 2 - x + 3 := by linarith
  have hdy : x + y ^ 2 + z = y ^ 2 - y + 3 := by linarith
  have hdz : x + y + z ^ 2 = z ^ 2 - z + 3 := by linarith
  rw [hdx, hdy, hdz]
  have h1 := lw_2456_aux1 x hx3
  have h2 := lw_2456_aux1 y hy3
  have h3 := lw_2456_aux1 z hz3
  linarith
end

-- forge:entry lw_17592 kind=proved origin=external
section
/- prove $\sqrt{n}^{\sqrt{n+1}} >\sqrt{n+1}^\sqrt{n}$ for natural $n \geq 7 $ -/
lemma lw_17592_aux1 (x y : ℝ) (hx : 0 < x) (hxy : x < y)
    (hlog : 1 ≤ Real.log x) : x * Real.log y < y * Real.log x := by
  have hy : 0 < y := hx.trans hxy
  have hratio : 1 < y / x := (lt_div_iff₀ hx).2 (by simpa using hxy)
  have h : Real.log y / y < Real.log x / x := by
    rw [div_lt_iff₀ hy, ← sub_lt_sub_iff_right (Real.log x)]
    calc
      Real.log y - Real.log x = Real.log (y / x) :=
        (Real.log_div hy.ne' hx.ne').symm
      _ < y / x - 1 := Real.log_lt_sub_one_of_pos (div_pos hy hx) (ne_of_gt hratio)
      _ ≤ Real.log x * (y / x - 1) :=
        le_mul_of_one_le_left (by linarith) hlog
      _ = Real.log x / x * y - Real.log x := by ring
  have := (div_lt_div_iff₀ hy hx).1 h
  nlinarith only [this]

theorem lw_17592 (n : ℕ) (hn : 7 ≤ n) :
    (Real.sqrt n : ℝ)^(Real.sqrt (n+1)) >
      (Real.sqrt (n+1) : ℝ)^(Real.sqrt n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hs0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hs1 : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 hn1
  apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos hs1 _)
    (Real.rpow_pos_of_pos hs0 _)).1
  rw [Real.log_rpow hs1, Real.log_rpow hs0]
  by_cases heq : n = 7
  · subst n
    norm_num at *
    have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      convert Real.log_pow (2 : ℝ) 3 using 1 <;> norm_num
    have hlog7 : (1.9458 : ℝ) < Real.log 7 := by
      have h := Real.one_sub_inv_le_log_of_pos
        (show (0 : ℝ) < (7 : ℝ)^5 / (2 : ℝ)^14 by norm_num)
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_pow] at h
      norm_num at h
      linarith [Real.log_two_gt_d9]
    have hlog8b : Real.log (8 : ℝ) < 2.07945 := by
      rw [hlog8]
      linarith [Real.log_two_lt_d9]
    have hs7 : Real.sqrt (7 : ℝ) < 2.6458 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_nonneg (7 : ℝ)]
    have hs8 : (2.8284 : ℝ) < Real.sqrt 8 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num), Real.sqrt_nonneg (8 : ℝ)]
    rw [Real.log_sqrt (by norm_num), Real.log_sqrt (by norm_num)]
    have hleft : Real.sqrt (7 : ℝ) * Real.log 8 < 2.6458 * 2.07945 :=
      mul_lt_mul hs7 hlog8b.le (by positivity) (by norm_num)
    have hright : (2.8284 : ℝ) * 1.9458 < Real.sqrt 8 * Real.log 7 :=
      mul_lt_mul hs8 hlog7.le (by norm_num) (by positivity)
    nlinarith
  · have hn8 : 8 ≤ n := by omega
    have h8 : Real.log (8 : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn8)
    have hlog : 1 ≤ Real.log (Real.sqrt (n : ℝ)) := by
      rw [Real.log_sqrt hn0.le]
      have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
        convert Real.log_pow (2 : ℝ) 3 using 1 <;> norm_num
      linarith [Real.log_two_gt_d9]
    exact lw_17592_aux1 _ _ hs0 (Real.sqrt_lt_sqrt hn0.le (by linarith)) hlog
end

-- forge:entry lw_24699 kind=disproved origin=external
section
/- If a,b,c are positive numbers and $a+b+c=1$ then $\sum_{cyc} \frac{a+b^2}{c}\geq 4$ -/
theorem lw_24699_disproof :
    ¬ (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
      (habc : a + b + c = 1),
      a + b ^ 2 / c + c + a ^ 2 / b + b + c ^ 2 / a ≥ 4) := by
  intro h
  have hbad := h (1 / 3) (1 / 3) (1 / 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hbad
end

-- forge:entry lw_24585 kind=disproved origin=external
section
/- And Cauchy-Schwarz inequality: $ ab+bc+ca \ge 2abc\left(\frac{1}{a+b}+\frac{1}{b+c}+\frac{1}{c+a}\right) $ . -/
theorem lw_24585_disproof :
    ¬ (∀ (a b c : ℝ),
      a * b + b * c + c * a ≥
        2 * a * b * c * (1 / (a + b) + 1 / (b + c) + 1 / (c + a))) := by
  intro h
  have hcounterexample := h 1 1 (-2)
  norm_num at hcounterexample
end

-- forge:entry lw_27325 kind=proved origin=external
section
/- Let $a,b,c>0$ and $\big( \frac{1}{a}-1\big) \big( \frac{1}{b}-1\big)\big( \frac{1}{c}-1\big)=8.$ Prove that $$a+b+c\geq 1$$ -/
theorem lw_27325 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (habc : a * b * c = 1)
    (h : (1 - 1 / a) * (1 - 1 / b) * (1 - 1 / c) = 8) : a + b + c ≥ 1 := by
  by_contra hsum
  have hsum_lt : a + b + c < 1 := lt_of_not_ge hsum
  have ha_lt : a < 1 := by linarith
  have hb_lt : b < 1 := by linarith
  have hc_lt : c < 1 := by linarith
  have hab_lt : a * b < 1 := by
    calc
      a * b < 1 * b := mul_lt_mul_of_pos_right ha_lt hb
      _ = b := one_mul b
      _ < 1 := hb_lt
  have habc_lt : a * b * c < 1 := by
    calc
      a * b * c < 1 * c := mul_lt_mul_of_pos_right hab_lt hc
      _ = c := one_mul c
      _ < 1 := hc_lt
  linarith
end

-- forge:entry lw_25828 kind=disproved origin=external
section
/- Prove that $bc(b+c)(a-b)^2+ca(c+a)(b-c)^2+ab(a+b)(c-a)^2 \geqslant 0$. -/
theorem lw_25828_disproof :
    ¬ (∀ (a b c : ℝ),
      b * c * (b + c) * (a - b) ^ 2 +
        c * a * (c + a) * (b - c) ^ 2 +
        a * b * (a + b) * (c - a) ^ 2 ≥ 0) := by
  intro h
  have hbad := h (-1) (-1) 0
  norm_num at hbad
end

-- forge:entry lw_21888 kind=proved origin=external
section
/- Let $a,b,c$ be positive real numbers. Prove that \n\n $\frac{1}{(1+a)^{3}}+\frac{1}{(1+b)^{3}}+\frac{1}{(1+c)^{3}}\ge\frac{3}{4(1+abc)}.$ -/
lemma lw_21888_aux1 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hx1 : x ≤ 1) (hy1 : y ≤ 1) (hz1 : z ≤ 1) :
    x * y * z ≤ (x + y + z) * (1 - (x + y + z) + (x * y + y * z + z * x)) := by
  have hs : 0 ≤ x + y + z := by positivity
  have hr : 0 ≤ x * y * z := by positivity
  by_cases h : x + y + z ≤ 1
  · have hsq : x * y * z ≤ (x + y + z) * (x * y + y * z + z * x) := by
      calc
        x * y * z = x * (y * z) := by ring
        _ ≤ (x + y + z) * (x * y + y * z + z * x) := by
          apply mul_le_mul
          · linarith
          · nlinarith [mul_nonneg hx hy, mul_nonneg hz hx]
          · positivity
          · exact hs
    have hpos := mul_nonneg hs (sub_nonneg.mpr h)
    nlinarith only [hsq, hpos]
  · have hcomp : 0 ≤ (1 - x) * (1 - y) * (1 - z) :=
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1))
        (sub_nonneg.mpr hz1)
    have hpos := mul_nonneg (by linarith : 0 ≤ x + y + z - 1) hr
    have hpos2 := mul_nonneg hs hcomp
    nlinarith only [hpos, hpos2]

lemma lw_21888_aux2 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hx1 : x ≤ 1) (hy1 : y ≤ 1) (hz1 : z ≤ 1) :
    3 * (x * y * z) ≤
      4 * (1 - (x + y + z) + (x * y + y * z + z * x)) * (x ^ 3 + y ^ 3 + z ^ 3) := by
  have hmain := lw_21888_aux1 x y z hx hy hz hx1 hy1 hz1
  have hvar : 0 ≤ (x + y + z) ^ 2 - 3 * (x * y + y * z + z * x) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have hr : 0 ≤ x * y * z := by positivity
  have hprod := mul_nonneg hvar (sub_nonneg.mpr hmain)
  have hsquare := mul_nonneg hr (sq_nonneg (3 - 2 * (x + y + z)))
  nlinarith only [hprod, hsquare]

theorem lw_21888 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    (1 / (1 + a) ^ 3 + 1 / (1 + b) ^ 3 + 1 / (1 + c) ^ 3) ≥
      3 / (4 * (1 + a * b * c)) := by
  have ha1 : 0 < 1 + a := by linarith
  have hb1 : 0 < 1 + b := by linarith
  have hc1 : 0 < 1 + c := by linarith
  let x := 1 / (1 + a)
  let y := 1 / (1 + b)
  let z := 1 / (1 + c)
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have hz : 0 < z := by dsimp [z]; positivity
  have hx1 : x ≤ 1 := by dsimp [x]; apply (div_le_iff₀ ha1).2; linarith
  have hy1 : y ≤ 1 := by dsimp [y]; apply (div_le_iff₀ hb1).2; linarith
  have hz1 : z ≤ 1 := by dsimp [z]; apply (div_le_iff₀ hc1).2; linarith
  have hpoly := lw_21888_aux2 x y z hx.le hy.le hz.le hx1 hy1 hz1
  have hid : 1 - (x + y + z) + (x * y + y * z + z * x) =
      (1 + a * b * c) * (x * y * z) := by
    dsimp [x, y, z]
    field_simp [ne_of_gt ha1, ne_of_gt hb1, ne_of_gt hc1]
    <;> ring
  have hr : 0 < x * y * z := by positivity
  have hbound : 3 ≤ 4 * (1 + a * b * c) * (x ^ 3 + y ^ 3 + z ^ 3) := by
    apply (mul_le_mul_iff_left₀ hr).mp
    calc
      3 * (x * y * z) ≤
          4 * (1 - (x + y + z) + (x * y + y * z + z * x)) *
            (x ^ 3 + y ^ 3 + z ^ 3) := hpoly
      _ = (4 * (1 + a * b * c) * (x ^ 3 + y ^ 3 + z ^ 3)) * (x * y * z) := by
        rw [hid]
        ring
  dsimp [x, y, z] at hbound
  simp only [div_pow, one_pow] at hbound
  apply (div_le_iff₀ (by positivity : 0 < 4 * (1 + a * b * c))).2
  nlinarith only [hbound]
end

-- forge:entry lw_36000 kind=disproved origin=external
section
/- Let $a,b,c $ be reals such that $abc=4 $ and $a+2\sqrt {|b|}+c=2 $ . Prove that $$|a|-|b|+|c| \leq -2$$ -/
theorem lw_36000_disproof : ¬ (∀ (a b c : ℝ), (a * b * c = 4) →
    (a + 2 * Real.sqrt (|b|) + c = 2) → |a| - |b| + |c| ≤ -2) := by
  intro h
  have hc := h 2 (-1) (-2) (by norm_num) (by norm_num)
  norm_num at hc
end

-- forge:entry lw_31420 kind=proved origin=external
section
/- Let $a,b,c>0.$ Prove that \n $$\frac{a}{b+c+ka}+\frac{b}{c+a+kb}+\frac{c}{a+b+kc}\leq\frac{3}{k+2}$$ $k \geqslant 1.$ -/
lemma lw_31420_aux1 (x s t : ℝ) (hx : 0 ≤ x) (hs : 0 < s) (ht : 0 ≤ t) :
    x / (s + t * x) ≤ (t * s + 9 * x) / (s * (t + 3) ^ 2) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [mul_nonneg ht (sq_nonneg (s - 3 * x))]

theorem lw_31420 (a b c k : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : k ≥ 1) :
    (a / (b + c + k * a) + b / (c + a + k * b) + c / (a + b + k * c)) ≤
      3 / (k + 2) := by
  have hs : 0 < a + b + c := by positivity
  have ht : 0 ≤ k - 1 := by linarith
  have hk : k + 2 ≠ 0 := by linarith
  have h₁ := lw_31420_aux1 a (a + b + c) (k - 1) ha.le hs ht
  have h₂ := lw_31420_aux1 b (a + b + c) (k - 1) hb.le hs ht
  have h₃ := lw_31420_aux1 c (a + b + c) (k - 1) hc.le hs ht
  have he₁ : a + b + c + (k - 1) * a = b + c + k * a := by ring
  have he₂ : a + b + c + (k - 1) * b = c + a + k * b := by ring
  have he₃ : a + b + c + (k - 1) * c = a + b + k * c := by ring
  rw [he₁] at h₁
  rw [he₂] at h₂
  rw [he₃] at h₃
  calc
    _ ≤ ((k - 1) * (a + b + c) + 9 * a) / ((a + b + c) * (k - 1 + 3) ^ 2) +
        ((k - 1) * (a + b + c) + 9 * b) / ((a + b + c) * (k - 1 + 3) ^ 2) +
        ((k - 1) * (a + b + c) + 9 * c) / ((a + b + c) * (k - 1 + 3) ^ 2) :=
      add_le_add (add_le_add h₁ h₂) h₃
    _ = 3 / (k + 2) := by
      have he : k - 1 + 3 = k + 2 := by ring
      rw [he]
      field_simp [ne_of_gt hs, hk]
      <;> ring
end

-- forge:entry lw_3621 kind=disproved origin=external
section
/- $\sqrt n+\sqrt{n+2}>\sqrt{4n+3}$ -/
theorem lw_3621_disproof :
    ¬ (∀ n : ℕ, Real.sqrt n + Real.sqrt (n + 2) > Real.sqrt (4 * n + 3)) := by
  intro h
  have hzero : Real.sqrt (3 : ℝ) < Real.sqrt (2 : ℝ) := by
    simpa using h 0
  exact (not_lt_of_ge (Real.sqrt_le_sqrt (by norm_num : (2 : ℝ) ≤ 3))) hzero
end

-- forge:entry lw_37171 kind=disproved origin=external
section
/- Solve the equation:\n$x^{4}-6x^{3}+x+6=0$ -/
theorem lw_37171_disproof :
    ¬ (∀ (x : ℂ), x^4 - 6 * x^3 + x + 6 = 0 ↔
      x = 3 ∨ x = -2 ∨ x = 1 ∨ x = -1) := by
  intro h
  have h1 := (h 1).mpr (by simp)
  norm_num at h1
end

end Mathlib2
