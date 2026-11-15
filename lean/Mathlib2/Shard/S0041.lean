/- Mathlib2 分片 41（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0040
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry lw_15028 kind=proved origin=external
section
/- Let $a,b,c>0$ with $abc=1$ .Prove that: $2(\frac{a}{b}+\frac{b}{c}+\frac{c}{a})\geq a+b+c+\frac{1}{a}+\frac{1}{b}+\frac{1}{c}$ -/
lemma lw_15028_aux1 (x y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : x ^ 3 = y * y * z) : 3 * x ≤ 2 * y + z := by
  have hcube : x ^ 3 ≤ ((y + y + z) / 3) ^ 3 := by
    rw [h]
    exact an_amgm_three_cube y y z hy hy hz
  have hle : x ≤ (y + y + z) / 3 :=
    le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by positivity) hcube
  linarith

theorem lw_15028 (a b c : ℝ)
    (h : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1) :
    2 * (a / b + b / c + c / a) ≥
      a + b + c + 1 / a + 1 / b + 1 / c := by
  rcases h with ⟨ha, hb, hc, habc⟩
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hc_eq : c = 1 / (a * b) := by
    apply (eq_div_iff (mul_ne_zero ha0 hb0)).2
    nlinarith [habc]
  let x := a / b
  let y := b / c
  let z := c / a
  have hx : 0 ≤ x := le_of_lt (div_pos ha hb)
  have hy : 0 ≤ y := le_of_lt (div_pos hb hc)
  have hz : 0 ≤ z := le_of_lt (div_pos hc ha)
  have h1 : 3 * a ≤ 2 * x + y := by
    apply lw_15028_aux1 a x y hx hy
    dsimp [x, y]
    rw [hc_eq]
    field_simp
    <;> ring
  have h2 : 3 * b ≤ 2 * y + z := by
    apply lw_15028_aux1 b y z hy hz
    dsimp [y, z]
    rw [hc_eq]
    field_simp
    <;> ring
  have h3 : 3 * c ≤ 2 * z + x := by
    apply lw_15028_aux1 c z x hz hx
    dsimp [z, x]
    rw [hc_eq]
    field_simp
    <;> ring
  have h4 : 3 * (1 / a) ≤ 2 * z + y := by
    apply lw_15028_aux1 (1 / a) z y hz hy
    dsimp [z, y]
    rw [hc_eq]
    field_simp
    <;> ring
  have h5 : 3 * (1 / b) ≤ 2 * x + z := by
    apply lw_15028_aux1 (1 / b) x z hx hz
    dsimp [x, z]
    rw [hc_eq]
    field_simp
    <;> ring
  have h6 : 3 * (1 / c) ≤ 2 * y + x := by
    apply lw_15028_aux1 (1 / c) y x hy hx
    dsimp [y, x]
    rw [hc_eq]
    field_simp
    <;> ring
  change a + b + c + 1 / a + 1 / b + 1 / c ≤ 2 * (x + y + z)
  linarith
end

-- forge:entry lw_55543 kind=proved origin=external
section
/- Let $a,b,c >0$ such that $abc=1$ . Prove $3 \leq \frac{a(3a+1)}{(a+1)^2}+\frac{b(3b+1)}{(b+1)^2}+\frac{c(3c+1)}{(c+1)^2}$ -/
theorem lw_55543_aux1 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (habc : a * b * c = 1) : 3 ≤ a + b + c := by
  have h := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := (1 / 3 : ℝ)) (w₂ := (1 / 3 : ℝ)) (w₃ := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) ha hb hc (by norm_num)
  have hp : a ^ (1 / 3 : ℝ) * b ^ (1 / 3 : ℝ) * c ^ (1 / 3 : ℝ) = 1 := by
    rw [← Real.mul_rpow ha hb, ← Real.mul_rpow (mul_nonneg ha hb) hc,
      habc, Real.one_rpow]
  rw [hp] at h
  linarith

theorem lw_55543_aux2 (s q : ℝ) (hs : 3 ≤ s) (hq : 3 ≤ q)
    (hsq : 3 * s ≤ q ^ 2) : 0 ≤ 3 * q ^ 2 + s * q - q - 7 * s - 12 := by
  by_cases hq7 : q ≤ 7
  · have h₁ : 0 ≤ (q - 3) * (q ^ 2 + 5 * q + 12) :=
      mul_nonneg (by linarith) (by positivity)
    have h₂ : 0 ≤ (7 - q) * (q ^ 2 - 3 * s) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith only [h₁, h₂]
  · have h₁ : 0 ≤ (q - 3) * (3 * q + 11) :=
      mul_nonneg (by linarith) (by positivity)
    have h₂ : 0 ≤ (s - 3) * (q - 7) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith only [h₁, h₂]

theorem lw_55543 (a b c : ℝ)
    (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1) :
    3 ≤ a * (3 * a + 1) / (a + 1) ^ 2 +
      b * (3 * b + 1) / (b + 1) ^ 2 + c * (3 * c + 1) / (c + 1) ^ 2 := by
  rcases ha with ⟨ha, hb, hc, habc⟩
  have hs := lw_55543_aux1 a b c ha.le hb.le hc.le habc
  have hprod : (a * b) * (b * c) * (c * a) = 1 := by
    calc
      (a * b) * (b * c) * (c * a) = (a * b * c) ^ 2 := by ring
      _ = 1 := by rw [habc]; norm_num
  have hq := lw_55543_aux1 (a * b) (b * c) (c * a)
    (by positivity) (by positivity) (by positivity) hprod
  have hsq : 3 * (a + b + c) ≤ (a * b + b * c + c * a) ^ 2 := by
    have h₁ := congrArg (fun x : ℝ => x * a) habc
    have h₂ := congrArg (fun x : ℝ => x * b) habc
    have h₃ := congrArg (fun x : ℝ => x * c) habc
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a),
      sq_nonneg (c * a - a * b)]
  have hn := lw_55543_aux2 (a + b + c) (a * b + b * c + c * a) hs hq hsq
  have ha1 : a + 1 ≠ 0 := by positivity
  have hb1 : b + 1 ≠ 0 := by positivity
  have hc1 : c + 1 ≠ 0 := by positivity
  have hid :
      (a * (3 * a + 1) / (a + 1) ^ 2 +
        b * (3 * b + 1) / (b + 1) ^ 2 + c * (3 * c + 1) / (c + 1) ^ 2 - 3) *
        ((a + 1) ^ 2 * (b + 1) ^ 2 * (c + 1) ^ 2) =
      6 * (a * b * c) ^ 2 + 7 * (a * b + b * c + c * a) * (a * b * c) +
        3 * (a * b + b * c + c * a) ^ 2 - 2 * (a + b + c) * (a * b * c) +
        (a + b + c) * (a * b + b * c + c * a) - 15 * (a * b * c) -
        8 * (a * b + b * c + c * a) - 5 * (a + b + c) - 3 := by
    field_simp
    <;> ring
  rw [habc] at hid
  have hd : 0 < (a + 1) ^ 2 * (b + 1) ^ 2 * (c + 1) ^ 2 := by positivity
  have hn' : 0 ≤
      (a * (3 * a + 1) / (a + 1) ^ 2 +
        b * (3 * b + 1) / (b + 1) ^ 2 + c * (3 * c + 1) / (c + 1) ^ 2 - 3) *
        ((a + 1) ^ 2 * (b + 1) ^ 2 * (c + 1) ^ 2) := by
    rw [hid]
    nlinarith only [hn]
  exact le_of_sub_nonneg ((mul_nonneg_iff_of_pos_right hd).mp hn')
end

-- forge:entry lw_20617 kind=disproved origin=external
section
/- Prove that for any positive real numbers $a, b, c$ with $a + b + c = 3$, the following inequality holds: $\frac{a}{b^2 + 2} + \frac{b}{c^2 + 2} + \frac{c}{a^2 + 2} \geq \frac{3}{2}$. -/
theorem lw_20617_disproof :
    ¬ (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
      (habc : a + b + c = 3),
      (a / (b ^ 2 + 2) + b / (c ^ 2 + 2) + c / (a ^ 2 + 2)) ≥ 3 / 2) := by
  intro h
  have hcounter := h 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hcounter
end

-- forge:entry lw_51373 kind=proved origin=external
section
/- Prove that for all $a, b, c \in \mathbb{R}$ such that $abc = 1$ and $a, b, c > 0$, the following inequality holds:\n$\frac{1}{a^3(b+c)(c+a)} + \frac{1}{b^3(c+a)(a+b)} + \frac{1}{c^3(a+b)(b+c)} \ge \frac{3}{4}$ -/
lemma lw_51373_aux1 (u v w t : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hw : 0 ≤ w) (hprod : t ^ 3 ≤ u * v * w) :
    3 * t ≤ u + v + w := by
  have hm := Mathlib2.an_amgm_three_cube u v w hu hv hw
  have ht : t ≤ (u + v + w) / 3 :=
    le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (by positivity)
      (hprod.trans hm)
  linarith

lemma lw_51373_aux2 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z = 1) :
    3 * ((x + y) * (y + z) * (z + x)) ≤
      4 * (x ^ 4 * z + y ^ 4 * x + z ^ 4 * y + x ^ 2 + y ^ 2 + z ^ 2) := by
  have hp1 : (x ^ 2 * y) ^ 3 ≤ (x ^ 4 * z) * (y ^ 4 * x) * x ^ 2 := by
    have he : (x ^ 4 * z) * (y ^ 4 * x) * x ^ 2 =
        (x * y * z) * (x ^ 2 * y) ^ 3 := by ring
    rw [he, h, one_mul]
  have hp2 : (y ^ 2 * z) ^ 3 ≤ (y ^ 4 * x) * (z ^ 4 * y) * y ^ 2 := by
    have he : (y ^ 4 * x) * (z ^ 4 * y) * y ^ 2 =
        (x * y * z) * (y ^ 2 * z) ^ 3 := by ring
    rw [he, h, one_mul]
  have hp3 : (z ^ 2 * x) ^ 3 ≤ (z ^ 4 * y) * (x ^ 4 * z) * z ^ 2 := by
    have he : (z ^ 4 * y) * (x ^ 4 * z) * z ^ 2 =
        (x * y * z) * (z ^ 2 * x) ^ 3 := by ring
    rw [he, h, one_mul]
  have hp4 : (x ^ 2 * z) ^ 3 ≤ (x ^ 4 * z) * x ^ 2 * z ^ 2 := by ring_nf; exact le_rfl
  have hp5 : (y ^ 2 * x) ^ 3 ≤ (y ^ 4 * x) * y ^ 2 * x ^ 2 := by ring_nf; exact le_rfl
  have hp6 : (z ^ 2 * y) ^ 3 ≤ (z ^ 4 * y) * z ^ 2 * y ^ 2 := by ring_nf; exact le_rfl
  have h1 := lw_51373_aux1 (x ^ 4 * z) (y ^ 4 * x) (x ^ 2) (x ^ 2 * y)
    (by positivity) (by positivity) (by positivity) hp1
  have h2 := lw_51373_aux1 (y ^ 4 * x) (z ^ 4 * y) (y ^ 2) (y ^ 2 * z)
    (by positivity) (by positivity) (by positivity) hp2
  have h3 := lw_51373_aux1 (z ^ 4 * y) (x ^ 4 * z) (z ^ 2) (z ^ 2 * x)
    (by positivity) (by positivity) (by positivity) hp3
  have h4 := lw_51373_aux1 (x ^ 4 * z) (x ^ 2) (z ^ 2) (x ^ 2 * z)
    (by positivity) (by positivity) (by positivity) hp4
  have h5 := lw_51373_aux1 (y ^ 4 * x) (y ^ 2) (x ^ 2) (y ^ 2 * x)
    (by positivity) (by positivity) (by positivity) hp5
  have h6 := lw_51373_aux1 (z ^ 4 * y) (z ^ 2) (y ^ 2) (z ^ 2 * y)
    (by positivity) (by positivity) (by positivity) hp6
  have hpA : (1 : ℝ) ^ 3 ≤ (x ^ 4 * z) * (y ^ 4 * x) * (z ^ 4 * y) := by
    have he : (x ^ 4 * z) * (y ^ 4 * x) * (z ^ 4 * y) = (x * y * z) ^ 5 := by ring
    rw [he, h]
    norm_num
  have hpB : (1 : ℝ) ^ 3 ≤ x ^ 2 * y ^ 2 * z ^ 2 := by
    have he : x ^ 2 * y ^ 2 * z ^ 2 = (x * y * z) ^ 2 := by ring
    rw [he, h]
    norm_num
  have hA := lw_51373_aux1 (x ^ 4 * z) (y ^ 4 * x) (z ^ 4 * y) 1
    (by positivity) (by positivity) (by positivity) hpA
  have hB := lw_51373_aux1 (x ^ 2) (y ^ 2) (z ^ 2) 1
    (by positivity) (by positivity) (by positivity) hpB
  nlinarith only [h1, h2, h3, h4, h5, h6, hA, hB, h]

lemma lw_51373_aux3 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z = 1) :
    3 / 4 ≤ x ^ 3 * z / ((y + z) * (z + x)) +
      y ^ 3 * x / ((z + x) * (x + y)) + z ^ 3 * y / ((x + y) * (y + z)) := by
  have hxy : x + y ≠ 0 := ne_of_gt (add_pos hx hy)
  have hyz : y + z ≠ 0 := ne_of_gt (add_pos hy hz)
  have hzx : z + x ≠ 0 := ne_of_gt (add_pos hz hx)
  have he : x ^ 3 * z / ((y + z) * (z + x)) +
      y ^ 3 * x / ((z + x) * (x + y)) + z ^ 3 * y / ((x + y) * (y + z)) =
      (x ^ 4 * z + y ^ 4 * x + z ^ 4 * y +
        (x * y * z) * (x ^ 2 + y ^ 2 + z ^ 2)) / ((x + y) * (y + z) * (z + x)) := by
    field_simp
    <;> ring
  rw [he, h, one_mul]
  apply (le_div_iff₀ (by positivity : 0 < (x + y) * (y + z) * (z + x))).2
  have hp := lw_51373_aux2 x y z hx hy hz h
  nlinarith only [hp]

theorem lw_51373 (a b c : ℝ) (h : a * b * c = 1) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) : (1 / (a ^ 3 * (b + c) * (c + a))) +
      (1 / (b ^ 3 * (c + a) * (a + b))) +
      (1 / (c ^ 3 * (a + b) * (b + c))) ≥ 3 / 4 := by
  have hi : (1 / a) * (1 / b) * (1 / c) = 1 := by
    rw [one_div_mul_one_div, one_div_mul_one_div, h]
    norm_num
  have hp := lw_51373_aux3 (1 / a) (1 / b) (1 / c)
    (by positivity) (by positivity) (by positivity) hi
  have he : (1 / a) ^ 3 * (1 / c) / ((1 / b + 1 / c) * (1 / c + 1 / a)) +
      (1 / b) ^ 3 * (1 / a) / ((1 / c + 1 / a) * (1 / a + 1 / b)) +
      (1 / c) ^ 3 * (1 / b) / ((1 / a + 1 / b) * (1 / b + 1 / c)) =
      (a * b * c) * (1 / (a ^ 3 * (b + c) * (c + a)) +
        1 / (b ^ 3 * (c + a) * (a + b)) + 1 / (c ^ 3 * (a + b) * (b + c))) := by
    field_simp
    <;> ring
  rw [he, h, one_mul] at hp
  exact hp
end

-- forge:entry lw_18650 kind=proved origin=external
section
/- If $ x,y,z\in [1,2] $ show $ \frac{x^2+y^2+z^2}{xy+yz+zx}\le\frac{6}{5} $ -/
theorem lw_18650 (x y z : ℝ) (hx : 1 ≤ x ∧ x ≤ 2)
    (hy : 1 ≤ y ∧ y ≤ 2) (hz : 1 ≤ z ∧ z ≤ 2) :
    (x^2 + y^2 + z^2) / (x*y + y*z + z*x) ≤ 6/5 := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hy0 : 0 < y := by linarith [hy.1]
  have hz0 : 0 < z := by linarith [hz.1]
  have hden : 0 < x*y + y*z + z*x := by positivity
  have hxL : 0 ≤ x - 1 := sub_nonneg.mpr hx.1
  have hyL : 0 ≤ y - 1 := sub_nonneg.mpr hy.1
  have hzL : 0 ≤ z - 1 := sub_nonneg.mpr hz.1
  have hxU : 0 ≤ 2 - x := sub_nonneg.mpr hx.2
  have hyU : 0 ≤ 2 - y := sub_nonneg.mpr hy.2
  have hzU : 0 ≤ 2 - z := sub_nonneg.mpr hz.2
  apply (div_le_iff₀ hden).2
  nlinarith only [mul_nonneg hxL hxU, mul_nonneg hyL hyU,
    mul_nonneg hzL hzU, mul_nonneg (mul_nonneg hxU hyU) hzU,
    mul_nonneg hxL hyL, mul_nonneg hyL hzL, mul_nonneg hzL hxL,
    mul_nonneg (mul_nonneg hxL hyL) hzL]
end

-- forge:entry lw_22941 kind=proved origin=external
section
/- a,b,c positive integer and ab+ac+bc=3,then prove that\n$\frac{1}{4+(a+b)^2}+\frac{1}{4+(b+c)^2}+\frac{1}{4+(a+c)^2} \le \frac{3}{8} $ -/
theorem lw_22941 (a b c : ℤ) (hab : a * b + a * c + b * c = 3) :
    (1 / (4 + (a + b) ^ 2) + 1 / (4 + (b + c) ^ 2) +
      1 / (4 + (c + a) ^ 2)) ≤ (3 / 8) := by
  have h : ∀ x : ℤ, 1 / (4 + x ^ 2) = 0 := by
    intro x
    apply Int.ediv_eq_zero_of_lt (by norm_num)
    nlinarith [sq_nonneg x]
  rw [h (a + b), h (b + c), h (c + a)]
  norm_num
end

-- forge:entry lw_56101 kind=proved origin=external
section
/- Let $ a,\ b,\ c$ be positive real numbers such that $ abc = 1$ . Find the possible greatest value of $ M$ satisfying the following inequality: \n\n $ (a^2 + b^2 + c^2)(a^2 + b^2 + c^2 + 3)^2\left\\{\\frac {b}{(a^2 + 1)^2} + \\frac {c}{(b^2 + 1)^2} + \\frac {a}{(c^2 + 1)^2}\\right\\}\\geq M.$ \n\nBY AM-GM inequality,we have: \n\n $ LHS \ge\ 81\sqrt[3]{((a^2+1)(b^2+1)(c^2+1))^2} \sqrt[3]{\\frac{abc}{((a^2+1)(b^2+1)(c^2+1))^2}} =81$ \n\nthen M=81 -/
lemma lw_56101_aux1 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    27 * (x * y * z) ≤ (x + y + z) ^ 3 := by
  have h := an_amgm_three_cube x y z hx hy hz
  nlinarith only [h]

lemma lw_56101_aux2 (x y z u v w : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (huvw : u * v * w = 1) :
    27 ≤ (x + y + z) ^ 2 * (u / x ^ 2 + v / y ^ 2 + w / z ^ 2) := by
  let P := x * y * z
  let D := x + y + z
  let T := u / x ^ 2 + v / y ^ 2 + w / z ^ 2
  have hD : 27 * P ≤ D ^ 3 := lw_56101_aux1 x y z hx.le hy.le hz.le
  have hT := lw_56101_aux1 (u / x ^ 2) (v / y ^ 2) (w / z ^ 2)
    (by positivity) (by positivity) (by positivity)
  have hprod : (u / x ^ 2 * (v / y ^ 2) * (w / z ^ 2)) * P ^ 2 = 1 := by
    dsimp [P]
    field_simp
    nlinarith only [huvw]
  have hTC : 27 ≤ T ^ 3 * P ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hT (sq_nonneg P)
    change 27 * (u / x ^ 2 * (v / y ^ 2) * (w / z ^ 2)) * P ^ 2 ≤ T ^ 3 * P ^ 2 at h
    nlinarith only [h, hprod]
  have hDsq : (27 * P) ^ 2 ≤ (D ^ 3) ^ 2 := by
    exact pow_le_pow_left₀ (by dsimp [P]; positivity) hD 2
  have hcube : (27 : ℝ) ^ 3 ≤ (D ^ 2 * T) ^ 3 := by
    calc
      (27 : ℝ) ^ 3 ≤ T ^ 3 * (27 * P) ^ 2 := by nlinarith only [hTC]
      _ ≤ T ^ 3 * (D ^ 3) ^ 2 := mul_le_mul_of_nonneg_left hDsq (by dsimp [T]; positivity)
      _ = (D ^ 2 * T) ^ 3 := by ring
  exact (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 27)
    (by positivity) (by decide : (3 : ℕ) ≠ 0)).mp hcube

theorem lw_56101 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (habc : a * b * c = 1) :
    (a^2 + b^2 + c^2) * (a^2 + b^2 + c^2 + 3)^2 *
      (b / (a^2 + 1)^2 + c / (b^2 + 1)^2 + a / (c^2 + 1)^2) ≥ 81 := by
  have hprod : a ^ 2 * b ^ 2 * c ^ 2 = 1 := by
    calc
      a ^ 2 * b ^ 2 * c ^ 2 = (a * b * c) ^ 2 := by ring
      _ = 1 := by rw [habc]; norm_num
  have hS := lw_56101_aux1 (a ^ 2) (b ^ 2) (c ^ 2)
    (sq_nonneg a) (sq_nonneg b) (sq_nonneg c)
  have hS3 : (3 : ℝ) ^ 3 ≤ (a ^ 2 + b ^ 2 + c ^ 2) ^ 3 := by
    nlinarith only [hS, hprod]
  have hSbound : 3 ≤ a ^ 2 + b ^ 2 + c ^ 2 :=
    (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 3)
      (by positivity) (by decide : (3 : ℕ) ≠ 0)).mp hS3
  have hT := lw_56101_aux2 (a ^ 2 + 1) (b ^ 2 + 1) (c ^ 2 + 1) b c a
    (by positivity) (by positivity) (by positivity) hb.le hc.le ha.le
    (by nlinarith only [habc])
  have hT' : 27 ≤ (a ^ 2 + b ^ 2 + c ^ 2 + 3) ^ 2 *
      (b / (a ^ 2 + 1) ^ 2 + c / (b ^ 2 + 1) ^ 2 + a / (c ^ 2 + 1) ^ 2) := by
    convert hT using 1 <;> ring
  have h := mul_le_mul hSbound hT' (by norm_num : (0 : ℝ) ≤ 27) (by positivity)
  nlinarith only [h]
end

-- forge:entry lw_7616 kind=proved origin=external
section
/- Show that every integer $k$ divisible by $3$ can be written as the sum of four cubes. -/
theorem lw_7616 (k : ℤ) (h : 3 ∣ k) : ∃ a b c d : ℤ, k = a^3 + b^3 + c^3 + d^3 := by
  obtain ⟨n, rfl⟩ := h
  have hn : n = 2 * (n / 2) ∨ n = 2 * (n / 2) + 1 := by omega
  rcases hn with hn | hn
  · refine ⟨n / 2 + 1, n / 2 - 1, -(n / 2), -(n / 2), ?_⟩
    calc
      3 * n = 6 * (n / 2) := by omega
      _ = (n / 2 + 1)^3 + (n / 2 - 1)^3 + (-(n / 2))^3 + (-(n / 2))^3 := by ring
  · refine ⟨2 * (n / 2) + 7, -2 * (n / 2) - 6, n / 2 + 1, -(n / 2) - 5, ?_⟩
    calc
      3 * n = 6 * (n / 2) + 3 := by omega
      _ = (2 * (n / 2) + 7)^3 + (-2 * (n / 2) - 6)^3 + (n / 2 + 1)^3 + (-(n / 2) - 5)^3 := by ring
end

-- forge:entry lw_26927 kind=disproved origin=external
section
/- $(x+y-z)(x-y)^2+(-x+y+z)(y-z)^2+(x-y+z)(z-x)^2\geq 0$ -/
theorem lw_26927_disproof : ¬ (∀ (x y z : ℝ),
    (x + y - z) * (x - y) ^ 2 + (-x + y + z) * (y - z) ^ 2 +
      (x - y + z) * (z - x) ^ 2 ≥ 0) := by
  intro h
  have hbad := h (-1) 0 0
  norm_num at hbad
end

-- forge:entry lw_909 kind=proved origin=external
section
/- For non-negative reals a,b,c s.t $a+b+c=1$ prove that $(a^3-3a+3)(b^3-3b+3)(c^3-3c+3)\le 9$ -/
theorem lw_909_aux1 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a ^ 3 - 3 * a * (a + b + c) ^ 2 + 3 * (a + b + c) ^ 3) *
      (b ^ 3 - 3 * b * (a + b + c) ^ 2 + 3 * (a + b + c) ^ 3) *
      (c ^ 3 - 3 * c * (a + b + c) ^ 2 + 3 * (a + b + c) ^ 3) ≤
      9 * (a + b + c) ^ 9 := by
  apply sub_nonneg.mp
  ring_nf
  positivity

theorem lw_909 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c = 1) :
    (a ^ 3 - 3 * a + 3) * (b ^ 3 - 3 * b + 3) * (c ^ 3 - 3 * c + 3) ≤ 9 := by
  simpa [habc] using lw_909_aux1 a b c ha hb hc
end

-- forge:entry lw_940 kind=proved origin=external
section
/- Prove that for any real number $a,b,c>0$ , $\frac{1}{ab+1}+\frac{1}{bc+1}+\frac{1}{ac+1}\leq\frac{1}{2}(\frac{1}{a}+\frac{1}{b}+\frac{1}{c}).$ -/
lemma lw_940_aux1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    4 / (a * b + 1) ≤ 1 / a + 1 / b := by
  have hab : 0 < a * b + 1 := by positivity
  have hid : 1 / a + 1 / b = (a + b) / (a * b) := by
    field_simp
    <;> ring
  rw [hid]
  apply (div_le_div_iff₀ hab (mul_pos ha hb)).2
  nlinarith [mul_nonneg (le_of_lt ha) (sq_nonneg (b - 1)),
    mul_nonneg (le_of_lt hb) (sq_nonneg (a - 1))]

theorem lw_940 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a * b + 1) + 1 / (b * c + 1) + 1 / (a * c + 1) ≤
      1 / 2 * (1 / a + 1 / b + 1 / c) := by
  have hab := lw_940_aux1 a b ha hb
  have hbc := lw_940_aux1 b c hb hc
  have hac := lw_940_aux1 a c ha hc
  simp only [div_eq_mul_inv] at hab hbc hac ⊢
  linarith
end

-- forge:entry lw_20733 kind=proved origin=external
section
/- For $a,b,c>0$ prove that \n$$a^{3}+b^{3}+c^{3}+3abc \geq ab\sqrt{2(a^{2}+b^{2})}+bc\sqrt{2(b^{2}+c^{2})}+ca\sqrt{2(a^{2}+c^{2})}$$ -/
lemma lw_20733_aux1 (s t : ℝ) (hs : 0 < s) (ht : 0 ≤ t) :
    Real.sqrt (s ^ 2 + t) ≤ s + t / (2 * s) := by
  have hd : 2 * s ≠ 0 := by positivity
  have he : t / (2 * s) * (2 * s) = t := div_mul_cancel₀ t hd
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [sq_nonneg (t / (2 * s))]

lemma lw_20733_aux2 (a b c : ℝ) (hc : 0 ≤ c) (hab : b ≤ a) (hbc : c ≤ b) :
    0 ≤ 2 * (a^3 + b^3 + c^3 + 3*a*b*c - a*b*(a+b) - b*c*(b+c) - c*a*(c+a)) *
      (a+b)*(b+c)*(c+a) -
      (a*b*(a-b)^2*(b+c)*(c+a) + b*c*(b-c)^2*(c+a)*(a+b) +
        c*a*(c-a)^2*(a+b)*(b+c)) := by
  let x := a - b
  let y := b - c
  let z := c
  have hx : 0 ≤ x := sub_nonneg.mpr hab
  have hy : 0 ≤ y := sub_nonneg.mpr hbc
  have hz : 0 ≤ z := hc
  calc
    0 ≤ x^5*(2*y+4*z) + x^4*(9*y^2+26*y*z+16*z^2) +
      x^3*(14*y^3+54*y^2*z+62*y*z^2+20*z^3) +
      x^2*(7*y^4+36*y^3*z+66*y^2*z^2+46*y*z^3+8*z^4) +
      x*(8*y^3*z^2+18*y^2*z^3+8*y*z^4) +
      4*y^4*z^2+12*y^3*z^3+8*y^2*z^4 := by positivity
    _ = _ := by dsimp [x, y, z]; ring

lemma lw_20733_aux3 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ 2 * (a^3 + b^3 + c^3 + 3*a*b*c - a*b*(a+b) - b*c*(b+c) - c*a*(c+a)) *
      (a+b)*(b+c)*(c+a) -
      (a*b*(a-b)^2*(b+c)*(c+a) + b*c*(b-c)^2*(c+a)*(a+b) +
        c*a*(c-a)^2*(a+b)*(b+c)) := by
  rcases le_total a b with hab | hba
  · rcases le_total c a with hca | hac
    · convert lw_20733_aux2 b a c hc hab hca using 1 <;> ring
    · rcases le_total c b with hcb | hbc
      · convert lw_20733_aux2 b c a ha hcb hac using 1 <;> ring
      · convert lw_20733_aux2 c b a ha hbc hab using 1 <;> ring
  · rcases le_total c b with hcb | hbc
    · exact lw_20733_aux2 a b c hc hba hcb
    · rcases le_total c a with hca | hac
      · convert lw_20733_aux2 a c b hb hca hbc using 1 <;> ring
      · convert lw_20733_aux2 c a b hb hac hba using 1 <;> ring

lemma lw_20733_aux4 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a*b*(a+b+(a-b)^2/(2*(a+b))) + b*c*(b+c+(b-c)^2/(2*(b+c))) +
      c*a*(c+a+(c-a)^2/(2*(c+a))) ≤ a^3+b^3+c^3+3*a*b*c := by
  have hab : a+b ≠ 0 := ne_of_gt (add_pos ha hb)
  have hbc : b+c ≠ 0 := ne_of_gt (add_pos hb hc)
  have hca : c+a ≠ 0 := ne_of_gt (add_pos hc ha)
  have hp := lw_20733_aux3 a b c ha.le hb.le hc.le
  have he :
    ((a^3+b^3+c^3+3*a*b*c) -
      (a*b*(a+b+(a-b)^2/(2*(a+b))) + b*c*(b+c+(b-c)^2/(2*(b+c))) +
        c*a*(c+a+(c-a)^2/(2*(c+a))))) * (2*(a+b)*(b+c)*(c+a)) =
      2 * (a^3 + b^3 + c^3 + 3*a*b*c - a*b*(a+b) - b*c*(b+c) - c*a*(c+a)) *
        (a+b)*(b+c)*(c+a) -
        (a*b*(a-b)^2*(b+c)*(c+a) + b*c*(b-c)^2*(c+a)*(a+b) +
          c*a*(c-a)^2*(a+b)*(b+c)) := by
    field_simp
    <;> ring
  have hm : 0 ≤ ((a^3+b^3+c^3+3*a*b*c) -
      (a*b*(a+b+(a-b)^2/(2*(a+b))) + b*c*(b+c+(b-c)^2/(2*(b+c))) +
        c*a*(c+a+(c-a)^2/(2*(c+a))))) * (2*(a+b)*(b+c)*(c+a)) := by
    rw [he]
    exact hp
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_left hm (by positivity))

theorem lw_20733 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^3 + b^3 + c^3 + 3*a*b*c ≥
      a*b*Real.sqrt (2 * (a^2 + b^2)) + b*c*Real.sqrt (2 * (b^2 + c^2)) +
        c*a*Real.sqrt (2 * (a^2 + c^2)) := by
  have hpair : ∀ x y : ℝ, 0 < x → 0 < y →
      x*y*Real.sqrt (2*(x^2+y^2)) ≤ x*y*(x+y+(x-y)^2/(2*(x+y))) := by
    intro x y hx hy
    have h := lw_20733_aux1 (x+y) ((x-y)^2) (add_pos hx hy) (sq_nonneg _)
    have he : (x+y)^2+(x-y)^2 = 2*(x^2+y^2) := by ring
    rw [he] at h
    exact mul_le_mul_of_nonneg_left h (mul_nonneg hx.le hy.le)
  have hab := hpair a b ha hb
  have hbc := hpair b c hb hc
  have hca := hpair c a hc ha
  have hr := lw_20733_aux4 a b c ha hb hc
  have he : a^2+c^2 = c^2+a^2 := by ring
  rw [he]
  exact (add_le_add (add_le_add hab hbc) hca).trans hr
end

-- forge:entry lw_3063 kind=disproved origin=external
section
/- Prove $a^kb + b^kc + c^ka\le 3$ given $a+b+c=3$ and $k \in (0,1]$ -/
theorem lw_3063_disproof : ¬ (∀ (a b c : ℝ) (k : ℝ),
    a + b + c = 3 ∧ 0 < k ∧ k ≤ 1 →
    a ^ k * b + b ^ k * c + c ^ k * a ≤ 3) := by
  intro h
  have hp : (-1 : ℝ) ^ (1 / 6 : ℝ) = Real.sqrt 3 / 2 := by
    rw [Real.rpow_def_of_neg (by norm_num : (-1 : ℝ) < 0),
      Real.log_neg_eq_log, Real.log_one, zero_mul, Real.exp_zero, one_mul]
    rw [show (1 / 6 : ℝ) * Real.pi = Real.pi / 6 by ring,
      Real.cos_pi_div_six]
  have hh := h 0 (-1) 4 (1 / 6) (by norm_num)
  rw [Real.zero_rpow (by norm_num : (1 / 6 : ℝ) ≠ 0), hp] at hh
  norm_num at hh
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  nlinarith
end

-- forge:entry lw_11055 kind=proved origin=external
section
/- $\bullet$ We have : $$\sqrt{ab}+\sqrt{bc}+\sqrt{ca}+\sqrt{a^2+b^2+c^2-ab-bc-ca} \ge a+b+c$$ \n $$\iff a^2+b^2+c^2-ab-bc-ca \ge (a+b+c-\sqrt{ab}-\sqrt{bc}-\sqrt{ca})^2 \iff \sum \sqrt{ab}(\sqrt{a}-\sqrt{b})^2 \ge 0$$ -/
lemma lw_11055_aux1 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x) ^ 2 ≤
      (x ^ 2) ^ 2 + (y ^ 2) ^ 2 + (z ^ 2) ^ 2 -
        x ^ 2 * y ^ 2 - y ^ 2 * z ^ 2 - z ^ 2 * x ^ 2 := by
  nlinarith only [mul_nonneg (mul_nonneg hx hy) (sq_nonneg (x - y)),
    mul_nonneg (mul_nonneg hy hz) (sq_nonneg (y - z)),
    mul_nonneg (mul_nonneg hz hx) (sq_nonneg (z - x))]

theorem lw_11055 (a b c : NNReal) :
    Real.sqrt (a * b) + Real.sqrt (b * c) + Real.sqrt (c * a) +
      Real.sqrt (a^2 + b^2 + c^2 - a * b - b * c - c * a) ≥ a + b + c := by
  have ha : 0 ≤ (a : ℝ) := a.coe_nonneg
  have hb : 0 ≤ (b : ℝ) := b.coe_nonneg
  have hc : 0 ≤ (c : ℝ) := c.coe_nonneg
  have ha2 := Real.sq_sqrt ha
  have hb2 := Real.sq_sqrt hb
  have hc2 := Real.sq_sqrt hc
  have hd : 0 ≤ (a : ℝ) ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a := by
    nlinarith [sq_nonneg ((a : ℝ) - b), sq_nonneg ((b : ℝ) - c),
      sq_nonneg ((c : ℝ) - a)]
  have h := lw_11055_aux1 (Real.sqrt a) (Real.sqrt b) (Real.sqrt c)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [ha2, hb2, hc2] at h
  have hs : 0 ≤ (a : ℝ) + b + c - Real.sqrt a * Real.sqrt b -
      Real.sqrt b * Real.sqrt c - Real.sqrt c * Real.sqrt a := by
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b),
      sq_nonneg (Real.sqrt b - Real.sqrt c),
      sq_nonneg (Real.sqrt c - Real.sqrt a)]
  have hr := (sq_le_sq₀ hs (Real.sqrt_nonneg
    ((a : ℝ) ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a))).mp
      (by rw [Real.sq_sqrt hd]; exact h)
  rw [Real.sqrt_mul ha, Real.sqrt_mul hb, Real.sqrt_mul hc]
  linarith
end

-- forge:entry lw_32968 kind=disproved origin=external
section
/- Let $a=c+u+v,b=c+u$ ( $u,v\geq 0$ ) we can get $\sum a=3c+2u+v,\sum a^2=3c^2+2c(2u+v)+2u^2+2uv+v^2,$ $\sum a^2b=3c^3+3c^2(2u+v)+c(4u^2+4uv+v^2)+u^3+2u^2v+uv^2.$ -/
theorem lw_32968_disproof : ¬ (∀ (a b c u v : ℝ) (h₁ : a = c + u + v) (h₂ : b = c + u), a + b + c = 3 * c + 2 * u + v ∧ a^2 + b^2 + c^2 = 3 * c^2 + 2 * c * (2 * u + v) + 2 * u^2 + 2 * u * v + v^2 ∧ a^2 * b = 3 * c^3 + 3 * c^2 * (2 * u + v) + c * (4 * u^2 + 4 * u * v + v^2) + u^3 + 2 * u^2 * v + u * v^2) := by
  intro h
  have hbad := h 1 1 1 0 0 (by norm_num) (by norm_num)
  norm_num at hbad
end

-- forge:entry lw_13491 kind=proved origin=external
section
/- Given a number $z\in\mathbb{C}$ satisfying $\left\vert z+\frac{1}{z}\right\vert=2$ . Prove that $\vert z\vert\leq 1+\sqrt{2}$ . -/
theorem lw_13491 (z : ℂ) (hz : ‖z + 1/z‖ = 2) : ‖z‖ ≤ 1 + Real.sqrt 2 := by
  by_cases hz0 : z = 0
  · subst z
    norm_num at hz
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hbound : ‖z‖ ≤ 2 + 1 / ‖z‖ := by
    simpa only [add_sub_cancel_right, hz, norm_div, norm_one] using
      (norm_sub_le (z + 1/z) (1/z))
  have hquad : ‖z‖ * ‖z‖ ≤ 2 * ‖z‖ + 1 := by
    have hm := mul_le_mul_of_nonneg_right hbound (norm_nonneg z)
    simpa only [add_mul, div_mul_cancel₀ 1 (ne_of_gt hr)] using hm
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  by_contra h
  have hlt : 1 + Real.sqrt 2 < ‖z‖ := lt_of_not_ge h
  have hp : 0 < (‖z‖ - (1 + Real.sqrt 2)) * (‖z‖ - 1 + Real.sqrt 2) :=
    mul_pos (by linarith) (by linarith)
  nlinarith
end

-- forge:entry lw_54762 kind=proved origin=external
section
/- Prove the inequality $x^y+y^z+z^x{\leq}x^x+y^y+z^z$ for all positive numbers $x, y, z$. -/
open MeasureTheory Set intervalIntegral

lemma lw_54762_aux1 (t b : ℝ) (ht : 0 < t) (hb : b ≤ t) :
    b * t ^ (b - 1) ≤ t ^ t := by
  have h := one_add_mul_self_le_rpow_one_add
    (s := t - 1) (p := t + 1 - b) (by linarith) (by linarith)
  have hpow : b ≤ t ^ (t + 1 - b) := by
    have hn : 0 ≤ t * (t - b) := mul_nonneg ht.le (sub_nonneg.mpr hb)
    simp only [add_sub_cancel] at h
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg ht.le (b - 1))
  rw [← Real.rpow_add ht] at hm
  convert hm using 1 <;> congr 1 <;> ring

lemma lw_54762_aux2 (t b : ℝ) (ht : 0 < t) (htb : t ≤ b)
    (hside : b ≤ 1 ∨ 1 ≤ t) : t ^ t ≤ b * t ^ (b - 1) := by
  have hpow : t ^ (t + 1 - b) ≤ b := by
    rcases hside with hb | ht1
    · have h := rpow_one_add_le_one_add_mul_self
        (s := t - 1) (p := t + 1 - b) (by linarith) (by linarith) (by linarith)
      have hn : t * (t - b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le (sub_nonpos.mpr htb)
      simp only [add_sub_cancel] at h
      nlinarith
    · exact (Real.rpow_le_self_of_one_le ht1 (by linarith)).trans htb
  have hm := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg ht.le (b - 1))
  rw [← Real.rpow_add ht] at hm
  convert hm using 1 <;> congr 1 <;> ring

lemma lw_54762_aux3 (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hside : b ≤ 1 ∨ 1 ≤ a) :
    (∫ t in a..b, Real.exp (t * Real.log t)) ≤ b ^ b - a ^ b := by
  apply integral_le_sub_of_hasDeriv_right_of_le hab
    (g := fun t : ℝ => t ^ b) (g' := fun t => b * t ^ (b - 1))
  · intro t ht
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (ha.trans_le ht.1)))).continuousAt.continuousWithinAt
  · intro t ht
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (ha.trans ht.1)))).hasDerivWithinAt
  · exact (Real.continuous_exp.comp Real.continuous_mul_log).continuousOn.integrableOn_Icc
  · intro t ht
    have ht0 := ha.trans ht.1
    rw [show t * Real.log t = Real.log t * t by ring, ← Real.rpow_def_of_pos ht0]
    apply lw_54762_aux2 t b ht0 ht.2.le
    exact hside.imp id (fun h => h.trans ht.1.le)

lemma lw_54762_aux4 (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) :
    a ^ b - b ^ b ≤ ∫ t in b..a, Real.exp (t * Real.log t) := by
  apply sub_le_integral_of_hasDeriv_right_of_le hba
    (g' := fun t => b * t ^ (b - 1))
  · intro t ht
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (hb.trans_le ht.1)))).continuousAt.continuousWithinAt
  · intro t ht
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (hb.trans ht.1)))).hasDerivWithinAt
  · exact (Real.continuous_exp.comp Real.continuous_mul_log).continuousOn.integrableOn_Icc
  · intro t ht
    have ht0 := hb.trans ht.1
    rw [show t * Real.log t = Real.log t * t by ring, ← Real.rpow_def_of_pos ht0]
    exact lw_54762_aux1 t b ht0 ht.1.le

lemma lw_54762_aux5 (b : ℝ) (hb : 1 ≤ b) :
    (∫ t in 1..b, Real.exp (t * Real.log t)) ≤ b ^ b - 1 := by
  have h : (∫ t in 1..b, Real.exp (t * Real.log t)) ≤
      Real.exp (b * Real.log b) - Real.exp (1 * Real.log 1) := by
    apply integral_le_sub_of_hasDeriv_right_of_le hb
      (g' := fun t => Real.exp (t * Real.log t) * (Real.log t + 1))
    · exact (Real.continuous_exp.comp Real.continuous_mul_log).continuousOn
    · intro t ht
      exact (Real.hasDerivAt_mul_log (ne_of_gt (lt_trans zero_lt_one ht.1))).exp.hasDerivWithinAt
    · exact (Real.continuous_exp.comp Real.continuous_mul_log).continuousOn.integrableOn_Icc
    · intro t ht
      have hlog : 0 ≤ Real.log t := Real.log_nonneg ht.1.le
      nlinarith [Real.exp_pos (t * Real.log t)]
  simpa [Real.rpow_def_of_pos (by linarith : 0 < b), mul_comm] using h

lemma lw_54762_aux6 (a b : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hb : 1 ≤ b) :
    a ^ b ≤ b ^ b + ∫ t in b..a, Real.exp (t * Real.log t) := by
  have hleft : (∫ t in a..1, Real.exp (t * Real.log t)) ≤ 1 - a := by
    apply integral_le_sub_of_hasDeriv_right_of_le ha1 (g := fun t : ℝ => t)
      (g' := fun _ => (1 : ℝ))
    · exact continuous_id.continuousOn
    · intro t ht
      exact (hasDerivAt_id t).hasDerivWithinAt
    · exact (Real.continuous_exp.comp Real.continuous_mul_log).continuousOn.integrableOn_Icc
    · intro t ht
      exact Real.exp_le_one_iff.mpr (Real.mul_log_nonpos (ha.trans ht.1).le ht.2.le)
  have hright := lw_54762_aux5 b hb
  have hadd := integral_add_adjacent_intervals
    ((Real.continuous_exp.comp Real.continuous_mul_log).intervalIntegrable (μ := volume) a 1)
    ((Real.continuous_exp.comp Real.continuous_mul_log).intervalIntegrable (μ := volume) 1 b)
  simp only [Function.comp_apply] at hadd
  have hpow := Real.rpow_le_self_of_le_one ha.le ha1 hb
  rw [integral_symm a b]
  linarith

lemma lw_54762_aux7 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a ^ b ≤ b ^ b + ∫ t in b..a, Real.exp (t * Real.log t) := by
  by_cases hab : b ≤ a
  · have h := lw_54762_aux4 a b hb hab
    linarith
  · have hab' := le_of_not_ge hab
    by_cases hb1 : b ≤ 1
    · have h := lw_54762_aux3 a b ha hab' (Or.inl hb1)
      rw [integral_symm a b]
      linarith
    · by_cases ha1 : 1 ≤ a
      · have h := lw_54762_aux3 a b ha hab' (Or.inr ha1)
        rw [integral_symm a b]
        linarith
      · exact lw_54762_aux6 a b ha (le_of_not_ge ha1) (le_of_not_ge hb1)

theorem lw_54762 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x^y + y^z + z^x ≤ x^x + y^y + z^z := by
  have hxy := lw_54762_aux7 x y hx hy
  have hyz := lw_54762_aux7 y z hy hz
  have hzx := lw_54762_aux7 z x hz hx
  have hsum := integral_add_adjacent_intervals_cancel
    ((Real.continuous_exp.comp Real.continuous_mul_log).intervalIntegrable (μ := volume) z y)
    ((Real.continuous_exp.comp Real.continuous_mul_log).intervalIntegrable (μ := volume) y x)
  simp only [Function.comp_apply] at hsum
  linarith
end

-- forge:entry lw_3525 kind=proved origin=external
section
/- Let $x, y, z > 0$ and $x^2 + y^2 + z^2 + xyz = 4$. Prove that $(x + 1)(y - 1)(z + 1) \leq \frac{27}{16}$ -/
theorem lw_3525 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h : x^2 + y^2 + z^2 + x * y * z = 4) :
    (x + 1) * (y - 1) * (z + 1) ≤ (27 / 16 : ℝ) := by
  by_cases hy1 : y ≤ 1
  · have hp : 0 ≤ (x + 1) * (z + 1) :=
      mul_nonneg (by linarith) (by linarith)
    have hn := mul_nonpos_of_nonneg_of_nonpos hp (by linarith : y - 1 ≤ 0)
    nlinarith only [hn]
  · have hy1' : 0 ≤ y - 1 := by linarith
    have hxyz : 0 ≤ x * y * z := le_of_lt (mul_pos (mul_pos hx hy) hz)
    have hy2 : y ≤ 2 := by
      nlinarith [sq_nonneg x, sq_nonneg z]
    let s : ℝ := (x + z) / 2
    have hsym : (y + 2) * (s ^ 2 + y - 2) ≤ 0 := by
      have hnn := mul_nonneg (by linarith : 0 ≤ 2 - y) (sq_nonneg (x - z))
      dsimp [s]
      nlinarith only [h, hnn]
    have hsy : s ^ 2 + y ≤ 2 := by
      by_contra! hb
      have hp := mul_pos (by linarith : 0 < y + 2)
        (by linarith : 0 < s ^ 2 + y - 2)
      linarith
    have hpair : (x + 1) * (z + 1) ≤ (s + 1) ^ 2 := by
      dsimp [s]
      nlinarith only [sq_nonneg (x - z)]
    have hfirst := mul_le_mul_of_nonneg_right hpair hy1'
    have hsecond := mul_le_mul_of_nonneg_left
      (by linarith [hsy] : y - 1 ≤ 1 - s ^ 2) (sq_nonneg (s + 1))
    have hmax : (s + 1) ^ 2 * (1 - s ^ 2) ≤ (27 / 16 : ℝ) := by
      nlinarith only [sq_nonneg ((s - 1 / 2) * (s + 3 / 2)),
        sq_nonneg (s - 1 / 2)]
    calc
      (x + 1) * (y - 1) * (z + 1) = ((x + 1) * (z + 1)) * (y - 1) := by ring
      _ ≤ (s + 1) ^ 2 * (y - 1) := hfirst
      _ ≤ (s + 1) ^ 2 * (1 - s ^ 2) := hsecond
      _ ≤ (27 / 16 : ℝ) := hmax
end

-- forge:entry lw_11675 kind=proved origin=external
section
/- If $ a,b,c>0$ and $ a+b+c=3$ , then \n\n $ \frac{a^2+b}{b(a^2+ab+b^2)}+\frac{b^2+c}{c(b^2+bc+c^2)}+\frac{c^2+a}{a(c^2+ca+a^2)}\geq2$ -/
lemma lw_11675_aux1 (a b c : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hac : a ≤ c) :
    0 ≤ (3 * (a+b+c) * a^2 + (a+b+c)^2 * b) * a*c *
        (b^2+b*c+c^2) * (c^2+c*a+a^2) +
      (3 * (a+b+c) * b^2 + (a+b+c)^2 * c) * a*b *
        (c^2+c*a+a^2) * (a^2+a*b+b^2) +
      (3 * (a+b+c) * c^2 + (a+b+c)^2 * a) * b*c *
        (a^2+a*b+b^2) * (b^2+b*c+c^2) -
      18 * (a*b*c * (a^2+a*b+b^2) * (b^2+b*c+c^2) * (c^2+c*a+a^2)) := by
  obtain ⟨x, hx, rfl⟩ := exists_nonneg_add_of_le hab
  obtain ⟨y, hy, rfl⟩ := exists_nonneg_add_of_le hac
  have h : 0 ≤
      189*a^7*((x-y)^2+x*y) +
      a^6*(387*(x^3+y^3)+81*x*y*(x+y)) +
      a^5*(327*(x^4+y^4)+507*x*y*(x^2+y^2)+306*x^2*y^2) +
      a^4*(135*(x^5+y^5)+480*x*y*(x^3+y^3)+540*x^2*y^2*(x+y)) +
      a^3*(25*(x^6+y^6)+195*x*y*(x^4+y^4)+378*x^2*y^2*(x^2+y^2)+434*x^3*y^3) +
      a^2*(x^7+y^7+34*x*y*(x^5+y^5)+117*x^2*y^2*(x^3+y^3)+197*x^3*y^3*(x+y)) +
      a*(x^7*y+x*y^7+15*x^2*y^2*(x^4+y^4)+39*x^3*y^3*(x^2+y^2)+59*x^4*y^4) +
      3*x^3*y^3*(x^3+y^3)+6*x^4*y^4*(x+y) := by positivity
  convert h using 1 <;> ring

lemma lw_11675_aux2 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ (3 * (a+b+c) * a^2 + (a+b+c)^2 * b) * a*c *
        (b^2+b*c+c^2) * (c^2+c*a+a^2) +
      (3 * (a+b+c) * b^2 + (a+b+c)^2 * c) * a*b *
        (c^2+c*a+a^2) * (a^2+a*b+b^2) +
      (3 * (a+b+c) * c^2 + (a+b+c)^2 * a) * b*c *
        (a^2+a*b+b^2) * (b^2+b*c+c^2) -
      18 * (a*b*c * (a^2+a*b+b^2) * (b^2+b*c+c^2) * (c^2+c*a+a^2)) := by
  by_cases hab : a ≤ b
  · by_cases hac : a ≤ c
    · exact lw_11675_aux1 a b c ha hab hac
    · have h := lw_11675_aux1 c a b hc (le_of_not_ge hac) (le_trans (le_of_not_ge hac) hab)
      convert h using 1 <;> ring
  · by_cases hbc : b ≤ c
    · have h := lw_11675_aux1 b c a hb hbc (le_of_not_ge hab)
      convert h using 1 <;> ring
    · have h := lw_11675_aux1 c a b hc (le_trans (le_of_not_ge hbc) (le_of_not_ge hab)) (le_of_not_ge hbc)
      convert h using 1 <;> ring

theorem lw_11675 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a + b + c = 3) :
    (a^2 + b) / (b * (a^2 + a*b + b^2)) +
    (b^2 + c) / (c * (b^2 + b*c + c^2)) +
    (c^2 + a) / (a * (c^2 + c*a + a^2)) ≥ 2 := by
  have hq1 : 0 < a^2+a*b+b^2 := by positivity
  have hq2 : 0 < b^2+b*c+c^2 := by positivity
  have hq3 : 0 < c^2+c*a+a^2 := by positivity
  have hD : 0 < a*b*c * (a^2+a*b+b^2) * (b^2+b*c+c^2) * (c^2+c*a+a^2) := by positivity
  have hp := lw_11675_aux2 a b c ha.le hb.le hc.le
  rw [habc] at hp
  have hclear :
      ((a^2+b)/(b*(a^2+a*b+b^2)) + (b^2+c)/(c*(b^2+b*c+c^2)) +
        (c^2+a)/(a*(c^2+c*a+a^2))) *
        (a*b*c * (a^2+a*b+b^2) * (b^2+b*c+c^2) * (c^2+c*a+a^2)) =
      (a^2+b)*a*c*(b^2+b*c+c^2)*(c^2+c*a+a^2) +
      (b^2+c)*a*b*(c^2+c*a+a^2)*(a^2+a*b+b^2) +
      (c^2+a)*b*c*(a^2+a*b+b^2)*(b^2+b*c+c^2) := by
    field_simp
    <;> ring
  apply (mul_le_mul_iff_left₀ hD).mp
  nlinarith only [hp, hclear]
end

-- forge:entry lw_22697 kind=proved origin=external
section
/- Let $ a,b,c$ positive real numbers. Prove or disprove that \n\n $ \sum\frac{a}{\sqrt{a+b}} \geq \frac{4(\sqrt{2a} + \sqrt{2b} + \sqrt{2c}) - 5\sqrt{a+b+c}}{4}$ \n\n -/
lemma lw_22697_aux1 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) :
    Real.sqrt (2 * x) ≤ x / y + y / 2 := by
  have hs : Real.sqrt (2 * x) ^ 2 = 2 * x :=
    Real.sq_sqrt (by positivity)
  have hd : x / y * y = x := div_mul_cancel₀ x (ne_of_gt hy)
  have h : Real.sqrt (2 * x) * y ≤ (x / y + y / 2) * y := by
    nlinarith [sq_nonneg (Real.sqrt (2 * x) - y)]
  exact (mul_le_mul_iff_left₀ hy).mp (by nlinarith [h])

lemma lw_22697_aux2 (x y z t : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hs : x ^ 2 + y ^ 2 + z ^ 2 ≤ 2 * t ^ 2) :
    x + y + z ≤ 5 / 2 * t := by
  have hcs : (x + y + z) ^ 2 ≤ 6 * t ^ 2 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  nlinarith [sq_nonneg (x + y + z - 5 / 2 * t)]

theorem lw_22697 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a)) ≥
      (4 * (Real.sqrt (2 * a) + Real.sqrt (2 * b) + Real.sqrt (2 * c)) -
        5 * Real.sqrt (a + b + c)) / 4 := by
  have h1 := lw_22697_aux1 a (Real.sqrt (a + b)) (le_of_lt ha)
    (Real.sqrt_pos.2 (by linarith))
  have h2 := lw_22697_aux1 b (Real.sqrt (b + c)) (le_of_lt hb)
    (Real.sqrt_pos.2 (by linarith))
  have h3 := lw_22697_aux1 c (Real.sqrt (c + a)) (le_of_lt hc)
    (Real.sqrt_pos.2 (by linarith))
  have hab : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt (by linarith)
  have hbc : Real.sqrt (b + c) ^ 2 = b + c := Real.sq_sqrt (by linarith)
  have hca : Real.sqrt (c + a) ^ 2 = c + a := Real.sq_sqrt (by linarith)
  have hs : Real.sqrt (a + b + c) ^ 2 = a + b + c := Real.sq_sqrt (by linarith)
  have hd := lw_22697_aux2 (Real.sqrt (a + b)) (Real.sqrt (b + c))
    (Real.sqrt (c + a)) (Real.sqrt (a + b + c))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (by nlinarith)
  linarith
end

end Mathlib2
