/- Mathlib2 分片 40（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0002
namespace Mathlib2

-- forge:entry lw_32539 kind=proved origin=external
section
/- Let $a, b, c$ and $d$ are non-negative numbers such that $a+b+c+d=4$ . Prove that: \n $\frac{a}{a^3+1}+\frac{b}{b^3+1}+\frac{c}{c^3+1}+\frac{d}{d^3+1}\leq2$ -/
lemma lw_32539_aux1 (x : ℝ) (hx : 0 ≤ x) :
    x / (x ^ 3 + 1) ≤ 3 / 5 := by
  have hden : 0 < x ^ 3 + 1 := by positivity
  apply (div_le_iff₀ hden).2
  have hp := mul_nonneg (sq_nonneg (x - 3 / 4))
    (show 0 ≤ 3 * x + 9 / 2 by linarith)
  nlinarith

lemma lw_32539_aux2 (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 9 / 4) :
    x / (x ^ 3 + 1) ≤ (3 - x) / 4 := by
  have hden : 0 < x ^ 3 + 1 := by positivity
  apply (div_le_iff₀ hden).2
  have hp : 0 ≤ x * (9 / 4 - x) :=
    mul_nonneg hx (sub_nonneg.mpr hx')
  have hq : 0 ≤ 3 + x - x ^ 2 := by nlinarith
  have hr := mul_nonneg (sq_nonneg (x - 1)) hq
  nlinarith

lemma lw_32539_aux3 (x : ℝ) (hx : 9 / 4 ≤ x) :
    x / (x ^ 3 + 1) ≤ 1 / 5 := by
  have hx0 : 0 ≤ x := by linarith
  have hden : 0 < x ^ 3 + 1 := by positivity
  apply (div_le_iff₀ hden).2
  have hsq : 0 ≤ x ^ 2 - 5 := by nlinarith [sq_nonneg (x - 2)]
  have hp := mul_nonneg hx0 hsq
  nlinarith

theorem lw_32539 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hab : a + b + c + d = 4) :
    a / (a ^ 3 + 1) + b / (b ^ 3 + 1) + c / (c ^ 3 + 1) +
      d / (d ^ 3 + 1) ≤ 2 := by
  have ha0 := lw_32539_aux1 a ha
  have hb0 := lw_32539_aux1 b hb
  have hc0 := lw_32539_aux1 c hc
  have hd0 := lw_32539_aux1 d hd
  by_cases ha' : a ≤ 9 / 4
  · by_cases hb' : b ≤ 9 / 4
    · by_cases hc' : c ≤ 9 / 4
      · by_cases hd' : d ≤ 9 / 4
        · have ha1 := lw_32539_aux2 a ha ha'
          have hb1 := lw_32539_aux2 b hb hb'
          have hc1 := lw_32539_aux2 c hc hc'
          have hd1 := lw_32539_aux2 d hd hd'
          linarith
        · have hd1 := lw_32539_aux3 d (le_of_lt (lt_of_not_ge hd'))
          linarith
      · have hc1 := lw_32539_aux3 c (le_of_lt (lt_of_not_ge hc'))
        linarith
    · have hb1 := lw_32539_aux3 b (le_of_lt (lt_of_not_ge hb'))
      linarith
  · have ha1 := lw_32539_aux3 a (le_of_lt (lt_of_not_ge ha'))
    linarith
end

-- forge:entry lw_44805 kind=disproved origin=external
section
/- prove that: $x^2+y^2+z^2+x+y+z\geq x^2+y^2+z^2+3\geq2(xy+xz+yz)$ -/
theorem lw_44805_disproof : ¬ (∀ x y z : ℝ, x ^ 2 + y ^ 2 + z ^ 2 + x + y + z ≥ x ^ 2 + y ^ 2 + z ^ 2 + 3 ∧ x ^ 2 + y ^ 2 + z ^ 2 + 3 ≥ 2 * (x * y + x * z + y * z)) := by
  intro h
  have hzero := (h 0 0 0).1
  norm_num at hzero
end

-- forge:entry lw_42735 kind=proved origin=external
section
/- Given $x,y>0$ ; $x+y<27$ , prove that $$\frac{\sqrt{x}+\sqrt{y}}{\sqrt{xy}}+\frac{1}{\sqrt{27-x-y}}\geq1$$ -/
theorem lw_42735_aux1 {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (a r : K) (ha : 0 < a) (hr : 0 < r) :
    (3 * r ^ 2 - a ^ 2) / (2 * r ^ 3) ≤ 1 / a := by
  apply (div_le_div_iff₀ (show 0 < 2 * r ^ 3 by positivity) ha).2
  nlinarith [mul_nonneg (sq_nonneg (a - r))
    (show 0 ≤ a + 2 * r by positivity)]

theorem lw_42735 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y < 27) :
    (Real.sqrt x + Real.sqrt y) / Real.sqrt (x * y) +
      1 / Real.sqrt (27 - x - y) ≥ 1 := by
  have hz : 0 < 27 - x - y := by linarith
  have bound : ∀ t : ℝ, 0 < t → (27 - t) / 54 ≤ 1 / Real.sqrt t := by
    intro t ht
    have h := lw_42735_aux1 (Real.sqrt t) 3
      (Real.sqrt_pos.2 ht) (by norm_num)
    norm_num [Real.sq_sqrt ht.le] at h
    simpa only [one_div] using h
  have hx' := bound x hx
  have hy' := bound y hy
  have hz' := bound (27 - x - y) hz
  have hsx : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  have hsy : Real.sqrt y ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hy)
  rw [Real.sqrt_mul hx.le]
  have heq : (Real.sqrt x + Real.sqrt y) / (Real.sqrt x * Real.sqrt y) =
      1 / Real.sqrt x + 1 / Real.sqrt y := by
    field_simp
    <;> ring
  rw [heq]
  linarith
end

-- forge:entry lw_45020 kind=disproved origin=external
section
/- Let $a,b,c \ge 0 $ and $a+b+c=1$ . prove that:\n $ \frac{1}{\sqrt{a+\frac{(b-c)^{2}}{4}}}+\frac{1}{\sqrt{b+\frac{(c-a)^{2}}{4}}}+\frac{1}{\sqrt{c+\frac{(a-b)^{2}}{4}}}\geq 5$ -/
theorem lw_45020_disproof : ¬ (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0)
    (hc : c ≥ 0) (hab : a + b + c = 1),
    (1 / Real.sqrt (a + (b - c) ^ 2 / 4) +
      1 / Real.sqrt (b + (c - a) ^ 2 / 4) +
      1 / Real.sqrt (c + (a - b) ^ 2 / 4)) ≥ 5) := by
  intro h
  have hs : Real.sqrt (9 / 16 : ℝ) = 3 / 4 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  have hx := h 0 (1 / 2) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [hs] at hx
end

-- forge:entry lw_37015 kind=proved origin=external
section
/- For positive real numbers $ x,y,z,$ prove that\n\n $ \sqrt {\left(x^2y + y^2z + z^2x\right)\left(xy^2 + yz^2 + zx^2\right)}\n\n $ \n\n $ \geq xyz + \sqrt [3]{\left(x^3 + xyz\right)\left(y^3 + xyz\right)\left(z^3 + xyz\right)}.$ -/
lemma lw_37015_aux1 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    3 * a * b * c ≤ a ^ 3 + b ^ 3 + c ^ 3 := by
  have h := mul_nonneg (show 0 ≤ a + b + c by positivity)
    (show 0 ≤ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 by positivity)
  nlinarith

lemma lw_37015_aux2 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    9 * (x * y * z) ^ 2 ≤
      (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) *
        (x * y ^ 2 + y * z ^ 2 + z * x ^ 2) := by
  have h1 := lw_37015_aux1 x y z hx hy hz
  have h2 := lw_37015_aux1 (x * y) (y * z) (z * x)
    (mul_nonneg hx hy) (mul_nonneg hy hz) (mul_nonneg hz hx)
  have h3 := mul_nonneg (show 0 ≤ x * y * z by positivity) (sub_nonneg.mpr h1)
  nlinarith

lemma lw_37015_aux3 (p s t : ℝ) (hp : 0 ≤ p) (hs : 3 * p ≤ s)
    (ht : t ^ 3 = p * (s ^ 2 - p ^ 2)) : p + t ≤ s := by
  have hsp : 0 ≤ s - p := by linarith
  have hs0 : 0 ≤ s := by linarith
  have hf := mul_nonneg (mul_nonneg hs0 hsp) (sub_nonneg.mpr hs)
  have hc : t ^ 3 ≤ (s - p) ^ 3 := by nlinarith [hf]
  have hle : t ≤ s - p := le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) hsp hc
  linarith

theorem lw_37015 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    Real.sqrt ((x^2 * y + y^2 * z + z^2 * x) * (x * y^2 + y * z^2 + z * x^2)) ≥ x * y * z + (x^3 + x * y * z)^((1:ℝ) / 3) * (y^3 + x * y * z)^((1:ℝ) / 3) * (z^3 + x * y * z)^((1:ℝ) / 3) := by
  let p := x * y * z
  let D := (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) *
    (x * y ^ 2 + y * z ^ 2 + z * x ^ 2)
  let s := Real.sqrt D
  let t := (x ^ 3 + p) ^ ((1 : ℝ) / 3) *
    (y ^ 3 + p) ^ ((1 : ℝ) / 3) * (z ^ 3 + p) ^ ((1 : ℝ) / 3)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hs0 : 0 ≤ s := Real.sqrt_nonneg D
  have hs2 : s ^ 2 = D := Real.sq_sqrt hD
  have hbound : 9 * p ^ 2 ≤ D := lw_37015_aux2 x y z hx.le hy.le hz.le
  have hs : 3 * p ≤ s := by nlinarith
  have hxc : ((x ^ 3 + p) ^ ((1 : ℝ) / 3)) ^ 3 = x ^ 3 + p := by
    simpa only [one_div, Nat.cast_ofNat] using
      (Real.rpow_inv_natCast_pow (show 0 ≤ x ^ 3 + p by positivity) (by decide : (3 : ℕ) ≠ 0))
  have hyc : ((y ^ 3 + p) ^ ((1 : ℝ) / 3)) ^ 3 = y ^ 3 + p := by
    simpa only [one_div, Nat.cast_ofNat] using
      (Real.rpow_inv_natCast_pow (show 0 ≤ y ^ 3 + p by positivity) (by decide : (3 : ℕ) ≠ 0))
  have hzc : ((z ^ 3 + p) ^ ((1 : ℝ) / 3)) ^ 3 = z ^ 3 + p := by
    simpa only [one_div, Nat.cast_ofNat] using
      (Real.rpow_inv_natCast_pow (show 0 ≤ z ^ 3 + p by positivity) (by decide : (3 : ℕ) ≠ 0))
  have ht : t ^ 3 = p * (s ^ 2 - p ^ 2) := by
    dsimp [t]
    rw [mul_pow, mul_pow, hxc, hyc, hzc, hs2]
    dsimp [p, D]
    ring
  exact lw_37015_aux3 p s t hp hs ht

end

-- forge:entry lw_4668 kind=proved origin=external
section
/- for $a,b,c$ are three sides of triangle $ABC$ , and $x,y,z$ > $0$ , prove $a/x+b/y+c/z > a/(y+z)+b/(x+z)+c/(x+y)$ . -/
lemma lw_4668_aux1 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    0 < 1 / x + 1 / y - 1 / (y + z) - 1 / (x + z) := by
  have h₁ : 1 / (x + z) < 1 / x :=
    one_div_lt_one_div_of_lt hx (by linarith)
  have h₂ : 1 / (y + z) < 1 / y :=
    one_div_lt_one_div_of_lt hy (by linarith)
  linarith

theorem lw_4668 (a b c x y z : ℝ) (hx : 0 < x ∧ 0 < y ∧ 0 < z)
    (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) :
    a/x+b/y+c/z > a/(y+z)+b/(x+z)+c/(x+y) := by
  obtain ⟨hx, hy, hz⟩ := hx
  have hxy := lw_4668_aux1 x y z hx hy hz
  have hyz := lw_4668_aux1 y z x hy hz hx
  have hxz := lw_4668_aux1 x z y hx hz hy
  simp only [add_comm z x, add_comm y x, add_comm z y] at hyz hxz
  have h₁ := mul_pos (sub_pos.mpr hab) hxy
  have h₂ := mul_pos (sub_pos.mpr hbc) hyz
  have h₃ := mul_pos (sub_pos.mpr hca) hxz
  simp only [div_eq_mul_inv, one_mul] at h₁ h₂ h₃ ⊢
  nlinarith only [h₁, h₂, h₃]
end

-- forge:entry lw_43838 kind=proved origin=external
section
/- Let $ a,b,c \in (0;+\infty)$ such that $ 3abc=1$ \nProve that $ \frac{3a^5}{3a^{5}+2bc}+\frac{3b^{5}}{3b^{5}+2ca}+\frac{3c^{5}}{3c^{5}+2ab}\ge 1$ -/
lemma lw_43838_aux1 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    1 ≤ x / (x + 2) + y / (y + 2) + z / (z + 2) := by
  have hp : (x * y) * (y * z) * (z * x) = 1 := by
    calc
      (x * y) * (y * z) * (z * x) = (x * y * z) ^ 2 := by ring
      _ = 1 := by rw [hxyz]; norm_num
  have hm := an_amgm_three_cube (x * y) (y * z) (z * x)
    (by positivity) (by positivity) (by positivity)
  rw [hp] at hm
  have hs : 3 ≤ x * y + y * z + z * x := by
    have hh : (1 : ℝ) ≤ (x * y + y * z + z * x) / 3 :=
      le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (by positivity)
        (by simpa using hm)
    linarith
  have hx2 : x + 2 ≠ 0 := ne_of_gt (by positivity)
  have hy2 : y + 2 ≠ 0 := ne_of_gt (by positivity)
  have hz2 : z + 2 ≠ 0 := ne_of_gt (by positivity)
  calc
    1 ≤ (x * (y + 2) * (z + 2) + y * (x + 2) * (z + 2) +
        z * (x + 2) * (y + 2)) / ((x + 2) * (y + 2) * (z + 2)) := by
      apply (le_div_iff₀ (by positivity : 0 < (x + 2) * (y + 2) * (z + 2))).2
      nlinarith [hs]
    _ = x / (x + 2) + y / (y + 2) + z / (z + 2) := by
      field_simp
      <;> ring

lemma lw_43838_aux2 (a b c : ℝ) (ha : 0 < a) (habc : a * b * c = 1 / 3) :
    3 * a ^ 5 / (3 * a ^ 5 + 2 * b * c) = 9 * a ^ 6 / (9 * a ^ 6 + 2) := by
  have hd : 9 * a ^ 6 + 2 ≠ 0 := ne_of_gt (by positivity)
  have hbc : b * c = 1 / (3 * a) := by
    apply (eq_div_iff (by positivity : 3 * a ≠ 0)).2
    nlinarith [habc]
  rw [mul_assoc (2 : ℝ) b c, hbc]
  field_simp
  <;> ring

theorem lw_43838 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1 / 3) :
    3 * a ^ 5 / (3 * a ^ 5 + 2 * b * c) +
      3 * b ^ 5 / (3 * b ^ 5 + 2 * c * a) +
      3 * c ^ 5 / (3 * c ^ 5 + 2 * a * b) ≥ 1 := by
  have hbca : b * c * a = 1 / 3 := by nlinarith [habc]
  have hcab : c * a * b = 1 / 3 := by nlinarith [habc]
  rw [lw_43838_aux2 a b c ha habc, lw_43838_aux2 b c a hb hbca,
    lw_43838_aux2 c a b hc hcab]
  apply lw_43838_aux1 (9 * a ^ 6) (9 * b ^ 6) (9 * c ^ 6)
    (by positivity) (by positivity) (by positivity)
  calc
    (9 * a ^ 6) * (9 * b ^ 6) * (9 * c ^ 6) = 729 * (a * b * c) ^ 6 := by ring
    _ = 1 := by rw [habc]; norm_num
end

-- forge:entry lw_45998 kind=disproved origin=external
section
/- Let $a,b,c$ be positive real numbers such that $a+b+c=3$ . Prove that $ \sqrt{\frac{a+b}{a+1}}+\sqrt{\frac{b+c}{b+1}}+\sqrt{\frac{c+a}{c+1}}\ge\frac{9}{a^2+b^2+c^2}$ -/
theorem lw_45998_disproof :
    ¬ (∀ (a b c : ℝ),
      a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 3 →
      Real.sqrt ((a + b) / (a + 1)) + Real.sqrt ((b + c) / (b + 1)) +
        Real.sqrt ((a + c) / (a + 1)) ≥ 9 / (a ^ 2 + b ^ 2 + c ^ 2)) := by
  intro h
  have hc := h (9 / 8) 1 (7 / 8) (by norm_num)
  have h₁ : Real.sqrt (15 / 16 : ℝ) ≤ 39 / 40 := by
    rw [Real.sqrt_le_iff]
    norm_num
  have h₂ : Real.sqrt (16 / 17 : ℝ) ≤ 39 / 40 := by
    rw [Real.sqrt_le_iff]
    norm_num
  norm_num at h₁ h₂ hc
  linarith
end

-- forge:entry lw_51626 kind=disproved origin=external
section
/- Where is your General Problem,VASC?Is it: \n\n $\displaystyle \sqrt {ka_1^2+1}+...+\sqrt{ka_n^2+1}\leq \sqrt{1+k}(a_1+...+a_n)$ . \n\n For $k\le n$ ? -/
theorem lw_51626_disproof : ¬ (∀ (n : ℕ) (k : ℝ) (a : ℕ → ℝ),
    (∑ i ∈ Finset.range n, Real.sqrt (k * (a i)^2 + 1)) ≤
      Real.sqrt (1 + k) * (∑ i ∈ Finset.range n, a i)) := by
  intro h
  have hbad := h 1 0 (fun _ => 0)
  norm_num at hbad
end

-- forge:entry lw_48192 kind=proved origin=external
section
/- Let $a,b,c$ are real numbers so that $a+b+c=15$ and $ab+bc+ca=27$ . Prove that $-243\leq abc\leq 13$ -/
lemma lw_48192_aux1 (a b c : ℝ) :
    (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 =
      (a + b + c) ^ 2 * (a * b + b * c + c * a) ^ 2 -
        4 * (a * b + b * c + c * a) ^ 3 -
        4 * (a + b + c) ^ 3 * (a * b * c) - 27 * (a * b * c) ^ 2 +
        18 * (a + b + c) * (a * b + b * c + c * a) * (a * b * c) := by
  ring

theorem lw_48192 (a b c : ℝ) (h1 : a + b + c = 15)
    (h2 : a * b + b * c + c * a = 27) :
    -243 ≤ a * b * c ∧ a * b * c ≤ 13 := by
  have hd : 0 ≤ (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  rw [lw_48192_aux1, h1, h2] at hd
  constructor
  · nlinarith [sq_nonneg (a * b * c + 243)]
  · nlinarith [sq_nonneg (a * b * c - 13)]
end

-- forge:entry lw_6095 kind=proved origin=external
section
/- Let $a$ , $b$ and $c$ be non-negative numbers. Prove that: $a^4b+b^4c+c^4a\geq abc(a^2+b^2+c^2)$ -/
theorem lw_6095 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a^4 * b + b^4 * c + c^4 * a ≥ a * b * c * (a^2 + b^2 + c^2) := by
  have h₁ : 0 ≤ a * b * (a - c)^2 * (2 * a + c) :=
    mul_nonneg (mul_nonneg (mul_nonneg ha hb) (sq_nonneg (a - c))) (by linarith)
  have h₂ : 0 ≤ b * c * (b - a)^2 * (2 * b + a) :=
    mul_nonneg (mul_nonneg (mul_nonneg hb hc) (sq_nonneg (b - a))) (by linarith)
  have h₃ : 0 ≤ c * a * (c - b)^2 * (2 * c + b) :=
    mul_nonneg (mul_nonneg (mul_nonneg hc ha) (sq_nonneg (c - b))) (by linarith)
  nlinarith only [h₁, h₂, h₃]
end

-- forge:entry lw_48587 kind=proved origin=external
section
/- prove that : $a^2+b^2+c^2 \leq 5$ given $a,b,c \in [0;2]$ and $a+b+c=3$. -/
theorem lw_48587 (a b c : ℝ)
    (h1 : a ∈ Set.Icc 0 2 ∧ b ∈ Set.Icc 0 2 ∧ c ∈ Set.Icc 0 2)
    (h2 : a + b + c = 3) : a ^ 2 + b ^ 2 + c ^ 2 ≤ 5 := by
  rcases h1 with ⟨⟨ha0, ha2⟩, ⟨hb0, hb2⟩, ⟨hc0, hc2⟩⟩
  have hp : 0 ≤ a * b * c := mul_nonneg (mul_nonneg ha0 hb0) hc0
  have hq : 0 ≤ (2 - a) * (2 - b) * (2 - c) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hb2))
      (sub_nonneg.mpr hc2)
  have hs : (a + b + c) ^ 2 = 9 := by
    rw [h2]
    norm_num
  nlinarith
end

-- forge:entry lw_53904 kind=proved origin=external
section
/- Let $a,b,c>0$ such that $a^3+b^3+c^3=a^4+b^4+c^4$ . Prove that: $\frac{a}{a+b^{2} + c^{2} } + \frac{b}{b+c^{2} + a^{2} } + \frac{c}{c+a^{2} + b^{2} } \leq 1$ -/
theorem lw_53904 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1)
    (h : a^3 + b^3 + c^3 = a^4 + b^4 + c^4) :
    a / (a + b^2 + c^2) + b / (b + c^2 + a^2) +
      c / (c + a^2 + b^2) ≤ 1 := by
  have hthree : 3 ≤ a^3 + b^3 + c^3 := by
    nlinarith [lw_37015_aux1 a b c ha.le hb.le hc.le]
  have hpoint : ∀ x : ℝ, 0 ≤ x → (x - 1)^2 ≤ 3*x^4 - 4*x^3 + 1 := by
    intro x hx
    have hp : 0 ≤ x * (3*x + 2) := mul_nonneg hx (by positivity)
    nlinarith [mul_nonneg hp (sq_nonneg (x - 1))]
  have hsum : (a - 1)^2 + (b - 1)^2 + (c - 1)^2 ≤ 0 := by
    nlinarith [hpoint a ha.le, hpoint b hb.le, hpoint c hc.le]
  have ha1 : a = 1 := by nlinarith [sq_nonneg (b - 1), sq_nonneg (c - 1)]
  have hb1 : b = 1 := by nlinarith [sq_nonneg (a - 1), sq_nonneg (c - 1)]
  have hc1 : c = 1 := by nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1)]
  rw [ha1, hb1, hc1]
  norm_num
end

-- forge:entry lw_47416 kind=proved origin=external
section
/- x,y>0 prove that \n $\frac{2xy}{x+y}+\sqrt{\frac{x^2+y^2}{2}}\geq\frac{x+y}{2}+\sqrt{xy}$ -/
lemma lw_47416_aux1 (a b c : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hab : b ≤ a) (hc : 0 ≤ c) (hc2 : c ^ 2 = 2 * a ^ 2 - b ^ 2) :
    b ^ 2 / a + c ≥ a + b := by
  have hf : 0 ≤ (a - b) ^ 3 * (a + b) :=
    mul_nonneg (pow_nonneg (sub_nonneg.mpr hab) 3) (add_nonneg ha.le hb)
  have heq : a ^ 2 * c ^ 2 = a ^ 2 * (2 * a ^ 2 - b ^ 2) := by rw [hc2]
  have hsq : (a ^ 2 + a * b - b ^ 2) ^ 2 ≤ (a * c) ^ 2 := by
    nlinarith [hf, heq]
  have hle : a ^ 2 + a * b - b ^ 2 ≤ a * c :=
    le_of_sq_le_sq hsq (mul_nonneg ha.le hc)
  apply (mul_le_mul_iff_left₀ ha).mp
  have hid : (b ^ 2 / a + c) * a = b ^ 2 + c * a := by
    field_simp [ne_of_gt ha]
  rw [hid]
  nlinarith

theorem lw_47416 (x y : ℝ) : x > 0 ∧ y > 0 →
    2 * x * y / (x + y) + Real.sqrt ((x ^ 2 + y ^ 2) / 2) ≥
      (x + y) / 2 + Real.sqrt (x * y) := by
  rintro ⟨hx, hy⟩
  have hxy : 0 ≤ x * y := by positivity
  have hb : 0 ≤ Real.sqrt (x * y) := Real.sqrt_nonneg _
  have hb2 : Real.sqrt (x * y) ^ 2 = x * y := Real.sq_sqrt hxy
  have ha : 0 < (x + y) / 2 := by positivity
  have hab : Real.sqrt (x * y) ≤ (x + y) / 2 := by
    apply le_of_sq_le_sq _ ha.le
    nlinarith [sq_nonneg (x - y)]
  have hc : 0 ≤ Real.sqrt ((x ^ 2 + y ^ 2) / 2) := Real.sqrt_nonneg _
  have hc2 : Real.sqrt ((x ^ 2 + y ^ 2) / 2) ^ 2 =
      2 * ((x + y) / 2) ^ 2 - Real.sqrt (x * y) ^ 2 := by
    rw [Real.sq_sqrt (by positivity), hb2]
    ring
  have h := lw_47416_aux1 ((x + y) / 2) (Real.sqrt (x * y))
    (Real.sqrt ((x ^ 2 + y ^ 2) / 2)) ha hb hab hc hc2
  have hid : Real.sqrt (x * y) ^ 2 / ((x + y) / 2) = 2 * x * y / (x + y) := by
    rw [hb2]
    field_simp
  simpa only [hid] using h
end

-- forge:entry lw_49653 kind=disproved origin=external
section
/- Prove that for all positive numbers $ p, q$ ,\n\n$ \sqrt {pq} \leq \left(\frac {p + q}{\sqrt {p} + \sqrt {q}} \right)^2$ . -/
theorem lw_49653_disproof :
    ¬ (∀ (p q : ℝ) (hp : p > 0) (hq : q > 0),
      (p * q)^(1 / 2) ≤ ((p + q) / (p^(1 / 2) + q^(1 / 2)))^2) := by
  intro h
  have hbad := h (1 / 2) (1 / 2) (by norm_num) (by norm_num)
  norm_num at hbad
end

-- forge:entry lw_9167 kind=disproved origin=external
section
/- Prove that:\n$$2\,{\frac {a\sqrt {4\,{a}^{2}+ab+ac+3\,bc}}{8\,{a}^{2}+a \left( b+c \right) +8\,bc}}\leq {\frac {a}{\sqrt {4\,{a}^{2}+5\,bc}}}$$ -/
theorem lw_9167_disproof : ¬ (∀ (a b c : ℝ),
    2 * a * Real.sqrt (4 * a ^ 2 + a * b + a * c + 3 * b * c) /
      (8 * a ^ 2 + a * (b + c) + 8 * b * c) ≤
    a / Real.sqrt (4 * a ^ 2 + 5 * b * c)) := by
  intro h
  have h9 : Real.sqrt (9 : ℝ) = 3 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  have h4 : Real.sqrt (4 : ℝ) = 2 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  have hbad := h (-1) 0 (-5)
  norm_num [h9, h4] at hbad
end

-- forge:entry lw_49355 kind=proved origin=external
section
/- prove or disprove $a^3+b^3+c^3\geq{a^2+b^2+c^2}$ given $a,b,c>0$ and $abc=1$ -/
theorem lw_49355 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) : a ^ 3 + b ^ 3 + c ^ 3 ≥ a ^ 2 + b ^ 2 + c ^ 2 := by
  have hs : 0 ≤ a + b + c := by positivity
  have hcube : 3 ≤ a ^ 3 + b ^ 3 + c ^ 3 := by
    nlinarith [mul_nonneg hs (sq_nonneg (a - b)),
      mul_nonneg hs (sq_nonneg (b - c)),
      mul_nonneg hs (sq_nonneg (c - a))]
  have ha' : 0 ≤ (a - 1) ^ 2 * (2 * a + 1) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  have hb' : 0 ≤ (b - 1) ^ 2 * (2 * b + 1) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  have hc' : 0 ≤ (c - 1) ^ 2 * (2 * c + 1) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  nlinarith
end

-- forge:entry lw_11012 kind=proved origin=external
section
/- Let a,b,c be positive real numbers for which a+b+c=1. Prove that $\frac{a-bc}{a+bc}+\frac{b-ca}{b+ca}+\frac{c-ab}{c+ab}\le\frac{3}{2}$ -/
theorem lw_11012 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (hab : a + b + c = 1) :
    (a - b * c) / (a + b * c) + (b - c * a) / (b + c * a) +
      (c - a * b) / (c + a * b) ≤ 3 / 2 := by
  have habp : 0 < a + b := add_pos ha hb
  have hacp : 0 < a + c := add_pos ha hc
  have hbcp : 0 < b + c := add_pos hb hc
  have hda : a + b * c = (a + b) * (a + c) := by
    calc
      a + b * c = a * (a + b + c) + b * c := by rw [hab]; ring
      _ = (a + b) * (a + c) := by ring
  have hdb : b + c * a = (a + b) * (b + c) := by
    calc
      b + c * a = b * (a + b + c) + c * a := by rw [hab]; ring
      _ = (a + b) * (b + c) := by ring
  have hdc : c + a * b = (a + c) * (b + c) := by
    calc
      c + a * b = c * (a + b + c) + a * b := by rw [hab]; ring
      _ = (a + c) * (b + c) := by ring
  have hna : a - b * c = (a + b) * (a + c) - 2 * b * c := by linarith [hda]
  have hnb : b - c * a = (a + b) * (b + c) - 2 * c * a := by linarith [hdb]
  have hnc : c - a * b = (a + c) * (b + c) - 2 * a * b := by linarith [hdc]
  have hgap : (3 : ℝ) / 2 -
      ((a - b * c) / (a + b * c) + (b - c * a) / (b + c * a) +
        (c - a * b) / (c + a * b)) =
      (a * (b - c) ^ 2 + b * (c - a) ^ 2 + c * (a - b) ^ 2) /
        (2 * (a + b) * (a + c) * (b + c)) := by
    rw [hna, hnb, hnc, hda, hdb, hdc]
    field_simp [ne_of_gt habp, ne_of_gt hacp, ne_of_gt hbcp]
    <;> ring
  have hnon : 0 ≤
      (a * (b - c) ^ 2 + b * (c - a) ^ 2 + c * (a - b) ^ 2) /
        (2 * (a + b) * (a + c) * (b + c)) := by positivity
  linarith [hgap]
end

-- forge:entry lw_54674 kind=proved origin=external
section
/- The following inequality is stronger. \n $ a,b,c>0\Longrightarrow\frac{a^3+b^3+c^3}{abc}+6\ge 9\cdot\frac{a^2+b^2+c^2}{ab+bc+ca} $ -/
lemma lw_54674_aux1 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    9 * (a ^ 2 + b ^ 2 + c ^ 2) * (a * b * c) ≤
      (a ^ 3 + b ^ 3 + c ^ 3 + 6 * (a * b * c)) *
        (a * b + b * c + c * a) := by
  have h : 0 ≤ c * (a - b) ^ 4 + a * (b - c) ^ 4 + b * (c - a) ^ 4 := by
    positivity
  nlinarith only [h]

theorem lw_54674 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 3 + b ^ 3 + c ^ 3) / (a * b * c) + 6 ≥
      9 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) := by
  have hr : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
  have hq : 0 < a * b + b * c + c * a := by positivity
  calc
    9 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) ≤
        (a ^ 3 + b ^ 3 + c ^ 3 + 6 * (a * b * c)) / (a * b * c) :=
      (div_le_div_iff₀ hq hr).2 (lw_54674_aux1 a b c ha.le hb.le hc.le)
    _ = (a ^ 3 + b ^ 3 + c ^ 3) / (a * b * c) + 6 := by
      rw [add_div, mul_div_cancel_right₀ _ hr.ne']
end

-- forge:entry lw_17299 kind=proved origin=external
section
/- Let $a,b,c,d$ be positive real numbers. Prove that \n $$ \frac{(a^2+b^2+2c^2+3d^2)(a^2+b^2+3c^2+2d^2)}{(a+b)^2(c+d)^2}\ge \frac{5}{2}$$ -/
theorem lw_17299 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) :
    (a^2 + b^2 + 2*c^2 + 3*d^2) * (a^2 + b^2 + 3*c^2 + 2*d^2) /
      (a + b)^2 / (c + d)^2 ≥ 5/2 := by
  have hab : 0 < (a + b)^2 := sq_pos_of_pos (add_pos ha hb)
  have hcd : 0 < (c + d)^2 := sq_pos_of_pos (add_pos hc hd)
  apply (le_div_iff₀ hcd).2
  apply (le_div_iff₀ hab).2
  have hnonneg : 0 ≤ (a^2 + b^2 - 5*c*d)^2 + 6*(c^2 - d^2)^2 +
      (5/2 : ℝ)*(a - b)^2*(c + d)^2 := by
    positivity
  nlinarith only [hnonneg]
end

end Mathlib2
