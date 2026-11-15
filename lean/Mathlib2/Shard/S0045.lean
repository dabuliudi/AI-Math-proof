/- Mathlib2 分片 45（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0044
namespace Mathlib2

-- forge:entry lw_29729 kind=proved origin=external
section
/- Let $a,b,c$ be the side lengths of a triangle. Prove that $\frac{a}{3a-b+c}+\frac{b}{3b-c+a}+\frac{c}{3c-a+b} \geq 1$. -/
lemma lw_29729_aux1 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    3 * x * y * z ≤ x ^ 2 * z + x * y ^ 2 + y * z ^ 2 := by
  have hmin (u v w : ℝ) (hu : 0 ≤ u) (hw : 0 ≤ w)
      (huv : u ≤ v) (huw : u ≤ w) :
      3 * u * v * w ≤ u ^ 2 * w + u * v ^ 2 + v * w ^ 2 := by
    have h1 := mul_nonneg hu (sq_nonneg (v - w))
    have h2 := mul_nonneg hw
      (mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr huw))
    nlinarith
  by_cases hxy : x ≤ y
  · by_cases hxz : x ≤ z
    · exact hmin x y z hx hz hxy hxz
    · have h := hmin z x y hz hy (le_of_not_ge hxz) (by linarith)
      nlinarith
  · by_cases hyz : y ≤ z
    · have h := hmin y z x hy hx hyz (le_of_not_ge hxy)
      nlinarith
    · have h := hmin z x y hz hy (by linarith) (le_of_not_ge hyz)
      nlinarith

theorem lw_29729 (a b c : ℝ) (hx : a > 0 ∧ b > 0 ∧ c > 0)
    (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) :
    a / (3 * a - b + c) + b / (3 * b - c + a) + c / (3 * c - a + b) ≥ 1 := by
  have ha : 0 < 3 * a - b + c := by linarith [hx.1]
  have hb : 0 < 3 * b - c + a := by linarith [hx.2.1]
  have hc : 0 < 3 * c - a + b := by linarith [hx.2.2]
  have hp := lw_29729_aux1 (a + c - b) (a + b - c) (b + c - a)
    (by linarith) (by linarith) (by linarith)
  have heq :
      a / (3 * a - b + c) + b / (3 * b - c + a) + c / (3 * c - a + b) =
      ((a * (3 * b - c + a) + b * (3 * a - b + c)) * (3 * c - a + b) +
        c * ((3 * a - b + c) * (3 * b - c + a))) /
      ((3 * a - b + c) * (3 * b - c + a) * (3 * c - a + b)) := by
    rw [div_add_div a b ha.ne' hb.ne',
      div_add_div _ c (mul_ne_zero ha.ne' hb.ne') hc.ne']
    ring
  rw [heq]
  apply (le_div_iff₀ (mul_pos (mul_pos ha hb) hc)).2
  nlinarith [hp]
end

-- forge:entry lw_37730 kind=disproved origin=external
section
/- $(a+b+c)^2\ge \sqrt{a^4+4abc(b+c)}+\sqrt{b^4+4abc(c+a)}+\sqrt{c^4+4abc(a+b)}$ -/
theorem lw_37730_disproof :
    ¬ (∀ (a b c : ℝ), (a + b + c) ^ 2 ≥
      Real.sqrt (a ^ 4 + 4 * a * b * c * (b + c)) +
      Real.sqrt (b ^ 4 + 4 * a * b * c * (c + a)) +
      Real.sqrt (c ^ 4 + 4 * a * b * c * (a + b))) := by
  intro h
  have hbad := h 1 (-1) 0
  norm_num at hbad
end

-- forge:entry lw_40392 kind=disproved origin=external
section
/- $x^3+y^3+z^3\leq x(x+y)+y(y+z)+z(z+x)$ -/
theorem lw_40392_disproof :
    ¬ (∀ (x y z : ℝ),
      x ^ 3 + y ^ 3 + z ^ 3 ≤
        x * (x + y) + y * (y + z) + z * (z + x)) := by
  intro h
  have hbad := h 2 0 0
  norm_num at hbad
end

-- forge:entry lw_45217 kind=proved origin=external
section
/- If $a, b, c>0$ prove that \n $\frac{a}{c^3-c^2a+a^3}+\frac{b}{a^3-a^2b+b^3}+\frac{c}{b^3-b^2c+c^3}\le\frac{a+b+c}{abc}$ -/
lemma lw_45217_aux1 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x / (y ^ 3 - y ^ 2 * x + x ^ 3) ≤ 1 / (x * y) := by
  have hpoly : x ^ 2 * y ≤ y ^ 3 - y ^ 2 * x + x ^ 3 := by
    have h := mul_nonneg (sq_nonneg (x - y)) (le_of_lt (add_pos hx hy))
    nlinarith
  have hden : 0 < y ^ 3 - y ^ 2 * x + x ^ 3 := by
    have hpos : 0 < x ^ 2 * y := mul_pos (sq_pos_of_pos hx) hy
    linarith
  apply (div_le_div_iff₀ hden (mul_pos hx hy)).2
  nlinarith

theorem lw_45217 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a / (c ^ 3 - c ^ 2 * a + a ^ 3) + b / (a ^ 3 - a ^ 2 * b + b ^ 3) +
      c / (b ^ 3 - b ^ 2 * c + c ^ 3) ≤ (a + b + c) / (a * b * c)) := by
  calc
    _ ≤ 1 / (a * c) + 1 / (b * a) + 1 / (c * b) :=
      add_le_add (add_le_add (lw_45217_aux1 a c ha hc) (lw_45217_aux1 b a hb ha))
        (lw_45217_aux1 c b hc hb)
    _ = (a + b + c) / (a * b * c) := by
      field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc]
      <;> ring
end

-- forge:entry lw_48942 kind=proved origin=external
section
/- a, b are positive reals such that \\(a+b = 1\\) . Prove that \n\\(\\frac{1}{3}\\leq \\frac{a^{2}}{a+1}+\\frac{b^{2}}{b+1}< \\frac{1}{2}\\) -/
theorem lw_48942 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    1 / 3 ≤ a ^ 2 / (a + 1) + b ^ 2 / (b + 1) ∧
      a ^ 2 / (a + 1) + b ^ 2 / (b + 1) < 1 / 2 := by
  have ha1 : 0 < a + 1 := by linarith
  have hb1 : 0 < b + 1 := by linarith
  have hp : 0 < a * b := mul_pos ha hb
  have hd : 0 < 2 + a * b := by positivity
  have hsquare : (a + b) ^ 2 = 1 := by rw [hab]; norm_num
  have hquarter : a * b ≤ 1 / 4 := by
    nlinarith [sq_nonneg (a - b)]
  have hsum : a ^ 2 / (a + 1) + b ^ 2 / (b + 1) =
      (1 - a * b) / (2 + a * b) := by
    have hbeq : b = 1 - a := by linarith
    field_simp [ne_of_gt ha1, ne_of_gt hb1, ne_of_gt hd]
    rw [hbeq]
    ring
  rw [hsum]
  constructor
  · apply (le_div_iff₀ hd).2
    nlinarith
  · apply (div_lt_iff₀ hd).2
    nlinarith
end

-- forge:entry lw_4909 kind=proved origin=external
section
/- If $x^2+y^2+z^2\le{k(xy+yz+zx)},x,y,z\ge0,1\le{k}\le{\frac{11}{8}},$ then \n $x^3+y^3+z^3\ge{\frac{k-1}{3(k+2)}(x+y+z)^3}.$ -/
lemma lw_4909_aux1 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (x + y + z) ^ 3 ≤ 16 * (x ^ 3 + y ^ 3 + z ^ 3) := by
  have h₁ := add_pow_le hx hy 3
  have h₂ := add_pow_le (add_nonneg hx hy) hz 3
  norm_num at h₁ h₂
  nlinarith [pow_nonneg hz 3]

theorem lw_4909 (x y z k : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hxy : 0 < (x * y + y * z + z * x)) (h : 1 ≤ k ∧ k ≤ 11 / 8) :
    x ^ 3 + y ^ 3 + z ^ 3 ≥
      (k - 1) / (3 * (k + 2)) * (x + y + z) ^ 3 := by
  have hd : 0 < 3 * (k + 2) := by linarith [h.1]
  have hc : (k - 1) / (3 * (k + 2)) ≤ 1 / 16 := by
    apply (div_le_iff₀ hd).2
    linarith [h.2]
  calc
    (k - 1) / (3 * (k + 2)) * (x + y + z) ^ 3 ≤
        (1 / 16) * (x + y + z) ^ 3 :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg (by positivity) 3)
    _ ≤ x ^ 3 + y ^ 3 + z ^ 3 := by
      linarith [lw_4909_aux1 x y z hx hy hz]
end

-- forge:entry lw_37717 kind=proved origin=external
section
/- Given $a, b, c, d > 0$, prove that $\frac{a}{b^2 + bc} + \frac{b}{c^2 + cd} + \frac{c}{d^2 + da} + \frac{d}{a^2 + ab} \ge \frac{a + b + c + d}{ac + bd}$. -/
lemma lw_37717_aux1 (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 ≤ (
      a * ((a + b + c) ^ 2 + (a + b + c) * (a + b + c + d)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * a) * (a ^ 2 + a * (a + b)) +
      (a + b) * ((a + b) ^ 2 + (a + b) * (a + b + c)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * a) * (a ^ 2 + a * (a + b)) +
      (a + b + c) * ((a + b) ^ 2 + (a + b) * (a + b + c)) * ((a + b + c) ^ 2 + (a + b + c) * (a + b + c + d)) * (a ^ 2 + a * (a + b)) +
      (a + b + c + d) * ((a + b) ^ 2 + (a + b) * (a + b + c)) * ((a + b + c) ^ 2 + (a + b + c) * (a + b + c + d)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * a)) * (a * (a + b + c) + (a + b) * (a + b + c + d)) -
    (a + (a + b) + (a + b + c) + (a + b + c + d)) * (((a + b) ^ 2 + (a + b) * (a + b + c)) * ((a + b + c) ^ 2 + (a + b + c) * (a + b + c + d)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * a) * (a ^ 2 + a * (a + b))) := by
  have hid : (
      a * ((a + b + c) ^ 2 + (a + b + c) * (a + b + c + d)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * a) * (a ^ 2 + a * (a + b)) +
      (a + b) * ((a + b) ^ 2 + (a + b) * (a + b + c)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * a) * (a ^ 2 + a * (a + b)) +
      (a + b + c) * ((a + b) ^ 2 + (a + b) * (a + b + c)) * ((a + b + c) ^ 2 + (a + b + c) * (a + b + c + d)) * (a ^ 2 + a * (a + b)) +
      (a + b + c + d) * ((a + b) ^ 2 + (a + b) * (a + b + c)) * ((a + b + c) ^ 2 + (a + b + c) * (a + b + c + d)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * a)) * (a * (a + b + c) + (a + b) * (a + b + c + d)) -
    (a + (a + b) + (a + b + c) + (a + b + c + d)) * (((a + b) ^ 2 + (a + b) * (a + b + c)) * ((a + b + c) ^ 2 + (a + b + c) * (a + b + c + d)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * a) * (a ^ 2 + a * (a + b))) =
      a * (a * (a * (a * (a * (a * (a * (b * (b * (24) + c * (24) + d * (24)) + c * (c * (24) + d * (24)) + d ^ 2 * (24)) + b * (b * (b * (136) + c * (250) + d * (198)) + c * (c * (230) + d * (292)) + d ^ 2 * (178)) + c * (c * (c * (84) + d * (146)) + d ^ 2 * (126)) + d ^ 3 * (32)) + b * (b * (b * (b * (326) + c * (867) + d * (627)) + c * (c * (993) + d * (1317)) + d ^ 2 * (588)) + c * (c * (c * (554) + d * (1044)) + d ^ 2 * (795)) + d ^ 3 * (185)) + c * (c * (c * (c * (116) + d * (282)) + d ^ 2 * (279)) + d ^ 3 * (113)) + d ^ 4 * (14)) + b * (b * (b * (b * (b * (428) + c * (1482) + d * (1029)) + c * (c * (2146) + d * (2859)) + d ^ 2 * (1073)) + c * (c * (c * (1594) + d * (3090)) + d ^ 2 * (2133)) + d ^ 3 * (457)) + c * (c * (c * (c * (584) + d * (1471)) + d ^ 2 * (1407)) + d ^ 3 * (550)) + d ^ 4 * (67)) + c * (c * (c * (c * (c * (80) + d * (244)) + d ^ 2 * (287)) + d ^ 3 * (153)) + d ^ 4 * (34)) + d ^ 5 * (2)) + b * (b * (b * (b * (b * (b * (332) + c * (1410) + d * (963)) + c * (c * (2504) + d * (3343)) + d ^ 2 * (1144)) + c * (c * (c * (2349) + d * (4612)) + d ^ 2 * (3006)) + d ^ 3 * (607)) + c * (c * (c * (c * (1199) + d * (3073)) + d ^ 2 * (2863)) + d ^ 3 * (1086)) + d ^ 4 * (130)) + c * (c * (c * (c * (c * (304) + d * (946)) + d ^ 2 * (1113)) + d ^ 3 * (592)) + d ^ 4 * (132)) + d ^ 5 * (8)) + c * (c * (c * (c * (c * (c * (28) + d * (100)) + d ^ 2 * (137)) + d ^ 3 * (89)) + d ^ 4 * (27)) + d ^ 5 * (3))) + b * (b * (b * (b * (b * (b * (b * (152) + c * (762) + d * (519)) + c * (c * (1608) + d * (2160)) + d ^ 2 * (707)) + c * (c * (c * (1830) + d * (3634)) + d ^ 2 * (2309)) + d ^ 3 * (451)) + c * (c * (c * (c * (1190) + d * (3094)) + d ^ 2 * (2857)) + d ^ 3 * (1069)) + d ^ 4 * (127)) + c * (c * (c * (c * (c * (428) + d * (1355)) + d ^ 2 * (1605)) + d ^ 3 * (858)) + d ^ 4 * (193)) + d ^ 5 * (12)) + c * (c * (c * (c * (c * (c * (74) + d * (270)) + d ^ 2 * (379)) + d ^ 3 * (253)) + d ^ 4 * (79)) + d ^ 5 * (9))) + c ^ 2 * (c * (c * (c * (c * (c * (4) + d * (16)) + d ^ 2 * (25)) + d ^ 3 * (19)) + d ^ 4 * (7)) + d ^ 5)) + b * (b * (b * (b * (b * (b * (b * (b * (38) + c * (219) + d * (150)) + c * (c * (535) + d * (726)) + d ^ 2 * (234)) + c * (c * (c * (715) + d * (1439)) + d ^ 2 * (911)) + d ^ 3 * (176)) + c * (c * (c * (c * (561) + d * (1483)) + d ^ 2 * (1379)) + d ^ 3 * (518)) + d ^ 4 * (62)) + c * (c * (c * (c * (c * (256) + d * (828)) + d ^ 2 * (999)) + d ^ 3 * (544)) + d ^ 4 * (125)) + d ^ 5 * (8)) + c * (c * (c * (c * (c * (c * (62) + d * (233)) + d ^ 2 * (338)) + d ^ 3 * (234)) + d ^ 4 * (76)) + d ^ 5 * (9))) + c ^ 2 * (c * (c * (c * (c * (c * (6) + d * (25)) + d ^ 2 * (41)) + d ^ 3 * (33)) + d ^ 4 * (13)) + d ^ 5 * (2)))) + b ^ 2 * (b * (b * (b * (b * (b * (b * (b * (4) + c * (26) + d * (18)) + c * (c * (72) + d * (99)) + d ^ 2 * (32)) + c * (c * (c * (110) + d * (225)) + d ^ 2 * (144)) + d ^ 3 * (28)) + c * (c * (c * (c * (100) + d * (270)) + d ^ 2 * (256)) + d ^ 3 * (98)) + d ^ 4 * (12)) + c * (c * (c * (c * (c * (54) + d * (180)) + d ^ 2 * (224)) + d ^ 3 * (126)) + d ^ 4 * (30)) + d ^ 5 * (2)) + c * (c * (c * (c * (c * (c * (16) + d * (63)) + d ^ 2 * (96)) + d ^ 3 * (70)) + d ^ 4 * (24)) + d ^ 5 * (3))) + c ^ 2 * (c * (c * (c * (c * (c * (2) + d * (9)) + d ^ 2 * (16)) + d ^ 3 * (14)) + d ^ 4 * (6)) + d ^ 5)) := by ring
  rw [hid]
  positivity

lemma lw_37717_aux2 (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 ≤ (
      a * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b + c)) * ((a + b + c) ^ 2 + (a + b + c) * a) * (a ^ 2 + a * (a + b)) +
      (a + b) * ((a + b) ^ 2 + (a + b) * (a + b + c + d)) * ((a + b + c) ^ 2 + (a + b + c) * a) * (a ^ 2 + a * (a + b)) +
      (a + b + c + d) * ((a + b) ^ 2 + (a + b) * (a + b + c + d)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b + c)) * (a ^ 2 + a * (a + b)) +
      (a + b + c) * ((a + b) ^ 2 + (a + b) * (a + b + c + d)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b + c)) * ((a + b + c) ^ 2 + (a + b + c) * a)) * (a * (a + b + c + d) + (a + b) * (a + b + c)) -
    (a + (a + b) + (a + b + c + d) + (a + b + c)) * (((a + b) ^ 2 + (a + b) * (a + b + c + d)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b + c)) * ((a + b + c) ^ 2 + (a + b + c) * a) * (a ^ 2 + a * (a + b))) := by
  have hid : (
      a * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b + c)) * ((a + b + c) ^ 2 + (a + b + c) * a) * (a ^ 2 + a * (a + b)) +
      (a + b) * ((a + b) ^ 2 + (a + b) * (a + b + c + d)) * ((a + b + c) ^ 2 + (a + b + c) * a) * (a ^ 2 + a * (a + b)) +
      (a + b + c + d) * ((a + b) ^ 2 + (a + b) * (a + b + c + d)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b + c)) * (a ^ 2 + a * (a + b)) +
      (a + b + c) * ((a + b) ^ 2 + (a + b) * (a + b + c + d)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b + c)) * ((a + b + c) ^ 2 + (a + b + c) * a)) * (a * (a + b + c + d) + (a + b) * (a + b + c)) -
    (a + (a + b) + (a + b + c + d) + (a + b + c)) * (((a + b) ^ 2 + (a + b) * (a + b + c + d)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b + c)) * ((a + b + c) ^ 2 + (a + b + c) * a) * (a ^ 2 + a * (a + b))) =
      a * (a * (a * (a * (a * (a * (a * (b * (b * (24) + c * (24)) + c * (c * (24) + d * (24)) + d ^ 2 * (24)) + b * (b * (b * (136) + c * (250) + d * (52)) + c * (c * (230) + d * (168)) + d ^ 2 * (116)) + c * (c * (c * (84) + d * (106)) + d ^ 2 * (86)) + d ^ 3 * (32)) + b * (b * (b * (b * (326) + c * (867) + d * (240)) + c * (c * (993) + d * (669)) + d ^ 2 * (264)) + c * (c * (c * (554) + d * (618)) + d ^ 2 * (369)) + d ^ 3 * (120)) + c * (c * (c * (c * (116) + d * (182)) + d ^ 2 * (129)) + d ^ 3 * (63)) + d ^ 4 * (14)) + b * (b * (b * (b * (b * (428) + c * (1482) + d * (453)) + c * (c * (2146) + d * (1433)) + d ^ 2 * (360)) + c * (c * (c * (1594) + d * (1692)) + d ^ 2 * (735)) + d ^ 3 * (180)) + c * (c * (c * (c * (584) + d * (865)) + d ^ 2 * (498)) + d ^ 3 * (187)) + d ^ 4 * (37)) + c * (c * (c * (c * (c * (80) + d * (156)) + d ^ 2 * (111)) + d ^ 3 * (44)) + d ^ 4 * (13)) + d ^ 5 * (2)) + b * (b * (b * (b * (b * (b * (332) + c * (1410) + d * (447)) + c * (c * (2504) + d * (1665)) + d ^ 2 * (305)) + c * (c * (c * (2349) + d * (2435)) + d ^ 2 * (829)) + d ^ 3 * (136)) + c * (c * (c * (c * (1199) + d * (1723)) + d ^ 2 * (838)) + d ^ 3 * (217)) + d ^ 4 * (33)) + c * (c * (c * (c * (c * (304) + d * (574)) + d ^ 2 * (369)) + d ^ 3 * (111)) + d ^ 4 * (23)) + d ^ 5 * (3)) + c ^ 2 * (c * (c * (c * (c * (28) + d * (68)) + d ^ 2 * (57)) + d ^ 3 * (19)) + d ^ 4 * (2))) + b * (b * (b * (b * (b * (b * (b * (152) + c * (762) + d * (243)) + c * (c * (1608) + d * (1056)) + d ^ 2 * (155)) + c * (c * (c * (1830) + d * (1856)) + d ^ 2 * (531)) + d ^ 3 * (54)) + c * (c * (c * (c * (1190) + d * (1666)) + d ^ 2 * (715)) + d ^ 3 * (123)) + d ^ 4 * (11)) + c * (c * (c * (c * (c * (428) + d * (785)) + d ^ 2 * (465)) + d ^ 3 * (107)) + d ^ 4 * (12)) + d ^ 5) + c ^ 2 * (c * (c * (c * (c * (74) + d * (174)) + d ^ 2 * (139)) + d ^ 3 * (43)) + d ^ 4 * (4))) + c ^ 3 * (c * (c * (c * (c * (4) + d * (12)) + d ^ 2 * (13)) + d ^ 3 * (6)) + d ^ 4)) + b * (b * (b * (b * (b * (b * (b * (b * (38) + c * (219) + d * (69)) + c * (c * (535) + d * (344)) + d ^ 2 * (43)) + c * (c * (c * (715) + d * (706)) + d ^ 2 * (178)) + d ^ 3 * (11)) + c * (c * (c * (c * (561) + d * (761)) + d ^ 2 * (296)) + d ^ 3 * (35)) + d ^ 4) + c * (c * (c * (c * (c * (256) + d * (452)) + d ^ 2 * (247)) + d ^ 3 * (45)) + d ^ 4 * (2))) + c ^ 2 * (c * (c * (c * (c * (62) + d * (139)) + d ^ 2 * (103)) + d ^ 3 * (28)) + d ^ 4 * (2))) + c ^ 3 * (c * (c * (c * (c * (6) + d * (17)) + d ^ 2 * (17)) + d ^ 3 * (7)) + d ^ 4))) + b ^ 2 * (b * (b * (b * (b * (b * (b * (b * (4) + c * (26) + d * (8)) + c * (c * (72) + d * (45)) + d ^ 2 * (5)) + c * (c * (c * (110) + d * (105)) + d ^ 2 * (24)) + d ^ 3) + c * (c * (c * (c * (100) + d * (130)) + d ^ 2 * (46)) + d ^ 3 * (4))) + c ^ 2 * (c * (c * (c * (54) + d * (90)) + d ^ 2 * (44)) + d ^ 3 * (6))) + c ^ 3 * (c * (c * (c * (16) + d * (33)) + d ^ 2 * (21)) + d ^ 3 * (4))) + c ^ 4 * (c * (c * (c * (2) + d * (5)) + d ^ 2 * (4)) + d ^ 3)) := by ring
  rw [hid]
  positivity

lemma lw_37717_aux3 (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 ≤ (
      a * ((a + b) ^ 2 + (a + b) * (a + b + c + d)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * a) * (a ^ 2 + a * (a + b + c)) +
      (a + b + c) * ((a + b + c) ^ 2 + (a + b + c) * (a + b)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * a) * (a ^ 2 + a * (a + b + c)) +
      (a + b) * ((a + b + c) ^ 2 + (a + b + c) * (a + b)) * ((a + b) ^ 2 + (a + b) * (a + b + c + d)) * (a ^ 2 + a * (a + b + c)) +
      (a + b + c + d) * ((a + b + c) ^ 2 + (a + b + c) * (a + b)) * ((a + b) ^ 2 + (a + b) * (a + b + c + d)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * a)) * (a * (a + b) + (a + b + c) * (a + b + c + d)) -
    (a + (a + b + c) + (a + b) + (a + b + c + d)) * (((a + b + c) ^ 2 + (a + b + c) * (a + b)) * ((a + b) ^ 2 + (a + b) * (a + b + c + d)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * a) * (a ^ 2 + a * (a + b + c))) := by
  have hid : (
      a * ((a + b) ^ 2 + (a + b) * (a + b + c + d)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * a) * (a ^ 2 + a * (a + b + c)) +
      (a + b + c) * ((a + b + c) ^ 2 + (a + b + c) * (a + b)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * a) * (a ^ 2 + a * (a + b + c)) +
      (a + b) * ((a + b + c) ^ 2 + (a + b + c) * (a + b)) * ((a + b) ^ 2 + (a + b) * (a + b + c + d)) * (a ^ 2 + a * (a + b + c)) +
      (a + b + c + d) * ((a + b + c) ^ 2 + (a + b + c) * (a + b)) * ((a + b) ^ 2 + (a + b) * (a + b + c + d)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * a)) * (a * (a + b) + (a + b + c) * (a + b + c + d)) -
    (a + (a + b + c) + (a + b) + (a + b + c + d)) * (((a + b + c) ^ 2 + (a + b + c) * (a + b)) * ((a + b) ^ 2 + (a + b) * (a + b + c + d)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * a) * (a ^ 2 + a * (a + b + c))) =
      a * (a * (a * (a * (a * (a * (a * (b * (b * (24) + c * (48) + d * (24)) + c * (c * (48) + d * (48)) + d ^ 2 * (24)) + b * (b * (b * (136) + c * (356) + d * (198)) + c * (c * (420) + d * (460)) + d ^ 2 * (178)) + c * (c * (c * (168) + d * (252)) + d ^ 2 * (148)) + d ^ 3 * (32)) + b * (b * (b * (b * (326) + c * (1064) + d * (627)) + c * (c * (1500) + d * (1740)) + d ^ 2 * (588)) + c * (c * (c * (992) + d * (1608)) + d ^ 2 * (936)) + d ^ 3 * (185)) + c * (c * (c * (c * (244) + d * (488)) + d ^ 2 * (372)) + d ^ 3 * (128)) + d ^ 4 * (14)) + b * (b * (b * (b * (b * (428) + c * (1687) + d * (1029)) + c * (c * (2828) + d * (3403)) + d ^ 2 * (1073)) + c * (c * (c * (2462) + d * (4230)) + d ^ 2 * (2457)) + d ^ 3 * (457)) + c * (c * (c * (c * (1085) + d * (2328)) + d ^ 2 * (1854)) + d ^ 3 * (632)) + d ^ 4 * (67)) + c * (c * (c * (c * (c * (190) + d * (475)) + d ^ 2 * (458)) + d ^ 3 * (212)) + d ^ 4 * (43)) + d ^ 5 * (2)) + b * (b * (b * (b * (b * (b * (332) + c * (1545) + d * (963)) + c * (c * (3050) + d * (3760)) + d ^ 2 * (1144)) + c * (c * (c * (3254) + d * (5831)) + d ^ 2 * (3391)) + d ^ 3 * (607)) + c * (c * (c * (c * (1965) + d * (4478)) + d ^ 2 * (3694)) + d ^ 3 * (1255)) + d ^ 4 * (130)) + c * (c * (c * (c * (c * (632) + d * (1696)) + d ^ 2 * (1742)) + d ^ 3 * (833)) + d ^ 4 * (168)) + d ^ 5 * (8)) + c * (c * (c * (c * (c * (c * (84) + d * (252)) + d ^ 2 * (297)) + d ^ 3 * (174)) + d ^ 4 * (50)) + d ^ 5 * (5))) + b * (b * (b * (b * (b * (b * (b * (152) + c * (821) + d * (519)) + c * (c * (1889) + d * (2368)) + d ^ 2 * (707)) + c * (c * (c * (2396) + d * (4424)) + d ^ 2 * (2579)) + d ^ 3 * (451)) + c * (c * (c * (c * (1805) + d * (4317)) + d ^ 2 * (3658)) + d ^ 3 * (1243)) + d ^ 4 * (127)) + c * (c * (c * (c * (c * (805) + d * (2309)) + d ^ 2 * (2501)) + d ^ 3 * (1229)) + d ^ 4 * (248)) + d ^ 5 * (12)) + c * (c * (c * (c * (c * (c * (196) + d * (637)) + d ^ 2 * (813)) + d ^ 3 * (506)) + d ^ 4 * (149)) + d ^ 5 * (15))) + c ^ 2 * (c * (c * (c * (c * (c * (20) + d * (70)) + d ^ 2 * (98)) + d ^ 3 * (70)) + d ^ 4 * (26)) + d ^ 5 * (4))) + b * (b * (b * (b * (b * (b * (b * (b * (38) + c * (235) + d * (150)) + c * (c * (624) + d * (792)) + d ^ 2 * (234)) + c * (c * (c * (926) + d * (1747)) + d ^ 2 * (1021)) + d ^ 3 * (176)) + c * (c * (c * (c * (836) + d * (2074)) + d ^ 2 * (1792)) + d ^ 3 * (610)) + d ^ 4 * (62)) + c * (c * (c * (c * (c * (467) + d * (1418)) + d ^ 2 * (1601)) + d ^ 3 * (804)) + d ^ 4 * (163)) + d ^ 5 * (8)) + c * (c * (c * (c * (c * (c * (156) + d * (550)) + d ^ 2 * (753)) + d ^ 3 * (492)) + d ^ 4 * (148)) + d ^ 5 * (15))) + c ^ 2 * (c * (c * (c * (c * (c * (28) + d * (109)) + d ^ 2 * (170)) + d ^ 3 * (133)) + d ^ 4 * (52)) + d ^ 5 * (8))) + c ^ 3 * (c * (c * (c * (c * (c * (2) + d * (8)) + d ^ 2 * (13)) + d ^ 3 * (11)) + d ^ 4 * (5)) + d ^ 5)) + b * (b * (b * (b * (b * (b * (b * (b * (b * (4) + c * (28) + d * (18)) + c * (c * (85) + d * (109)) + d ^ 2 * (32)) + c * (c * (c * (146) + d * (280)) + d ^ 2 * (164)) + d ^ 3 * (28)) + c * (c * (c * (c * (155) + d * (395)) + d ^ 2 * (346)) + d ^ 3 * (118)) + d ^ 4 * (12)) + c * (c * (c * (c * (c * (104) + d * (330)) + d ^ 2 * (384)) + d ^ 3 * (196)) + d ^ 4 * (40)) + d ^ 5 * (2)) + c * (c * (c * (c * (c * (c * (43) + d * (163)) + d ^ 2 * (236)) + d ^ 3 * (160)) + d ^ 4 * (49)) + d ^ 5 * (5))) + c ^ 2 * (c * (c * (c * (c * (c * (10) + d * (44)) + d ^ 2 * (76)) + d ^ 3 * (64)) + d ^ 4 * (26)) + d ^ 5 * (4))) + c ^ 3 * (c * (c * (c * (c * (c + d * (5)) + d ^ 2 * (10)) + d ^ 3 * (10)) + d ^ 4 * (5)) + d ^ 5)) := by ring
  rw [hid]
  clear hid
  positivity

lemma lw_37717_aux4 (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 ≤ (
      a * ((a + b) ^ 2 + (a + b) * (a + b + c)) * ((a + b + c) ^ 2 + (a + b + c) * a) * (a ^ 2 + a * (a + b + c + d)) +
      (a + b + c + d) * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b)) * ((a + b + c) ^ 2 + (a + b + c) * a) * (a ^ 2 + a * (a + b + c + d)) +
      (a + b) * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b)) * ((a + b) ^ 2 + (a + b) * (a + b + c)) * (a ^ 2 + a * (a + b + c + d)) +
      (a + b + c) * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b)) * ((a + b) ^ 2 + (a + b) * (a + b + c)) * ((a + b + c) ^ 2 + (a + b + c) * a)) * (a * (a + b) + (a + b + c + d) * (a + b + c)) -
    (a + (a + b + c + d) + (a + b) + (a + b + c)) * (((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b)) * ((a + b) ^ 2 + (a + b) * (a + b + c)) * ((a + b + c) ^ 2 + (a + b + c) * a) * (a ^ 2 + a * (a + b + c + d))) := by
  have hid : (
      a * ((a + b) ^ 2 + (a + b) * (a + b + c)) * ((a + b + c) ^ 2 + (a + b + c) * a) * (a ^ 2 + a * (a + b + c + d)) +
      (a + b + c + d) * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b)) * ((a + b + c) ^ 2 + (a + b + c) * a) * (a ^ 2 + a * (a + b + c + d)) +
      (a + b) * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b)) * ((a + b) ^ 2 + (a + b) * (a + b + c)) * (a ^ 2 + a * (a + b + c + d)) +
      (a + b + c) * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b)) * ((a + b) ^ 2 + (a + b) * (a + b + c)) * ((a + b + c) ^ 2 + (a + b + c) * a)) * (a * (a + b) + (a + b + c + d) * (a + b + c)) -
    (a + (a + b + c + d) + (a + b) + (a + b + c)) * (((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b)) * ((a + b) ^ 2 + (a + b) * (a + b + c)) * ((a + b + c) ^ 2 + (a + b + c) * a) * (a ^ 2 + a * (a + b + c + d))) =
      a * (a * (a * (a * (a * (a * (a * (b * (b * (24) + c * (48) + d * (24)) + c * (c * (48) + d * (48)) + d ^ 2 * (24)) + b * (b * (b * (136) + c * (356) + d * (158)) + c * (c * (420) + d * (380)) + d ^ 2 * (138)) + c * (c * (c * (168) + d * (252)) + d ^ 2 * (148)) + d ^ 3 * (32)) + b * (b * (b * (b * (326) + c * (1064) + d * (437)) + c * (c * (1500) + d * (1260)) + d ^ 2 * (348)) + c * (c * (c * (992) + d * (1368)) + d ^ 2 * (696)) + d ^ 3 * (135)) + c * (c * (c * (c * (244) + d * (488)) + d ^ 2 * (372)) + d ^ 3 * (128)) + d ^ 4 * (14)) + b * (b * (b * (b * (b * (428) + c * (1687) + d * (658)) + c * (c * (2828) + d * (2253)) + d ^ 2 * (498)) + c * (c * (c * (2462) + d * (3156)) + d ^ 2 * (1383)) + d ^ 3 * (232)) + c * (c * (c * (c * (1085) + d * (2012)) + d ^ 2 * (1380)) + d ^ 3 * (432)) + d ^ 4 * (46)) + c * (c * (c * (c * (c * (190) + d * (475)) + d ^ 2 * (458)) + d ^ 3 * (212)) + d ^ 4 * (43)) + d ^ 5 * (2)) + b * (b * (b * (b * (b * (b * (332) + c * (1545) + d * (582)) + c * (c * (3050) + d * (2340)) + d ^ 2 * (434)) + c * (c * (c * (3254) + d * (3931)) + d ^ 2 * (1491)) + d ^ 3 * (207)) + c * (c * (c * (c * (1965) + d * (3382)) + d ^ 2 * (2050)) + d ^ 3 * (559)) + d ^ 4 * (56)) + c * (c * (c * (c * (c * (632) + d * (1464)) + d ^ 2 * (1278)) + d ^ 3 * (537)) + d ^ 4 * (104)) + d ^ 5 * (5)) + c * (c * (c * (c * (c * (c * (84) + d * (252)) + d ^ 2 * (297)) + d ^ 3 * (174)) + d ^ 4 * (50)) + d ^ 5 * (5))) + b * (b * (b * (b * (b * (b * (b * (152) + c * (821) + d * (302)) + c * (c * (1889) + d * (1410)) + d ^ 2 * (228)) + c * (c * (c * (2396) + d * (2764)) + d ^ 2 * (919)) + d ^ 3 * (100)) + c * (c * (c * (c * (1805) + d * (2903)) + d ^ 2 * (1537)) + d ^ 3 * (342)) + d ^ 4 * (30)) + c * (c * (c * (c * (c * (805) + d * (1716)) + d ^ 2 * (1315)) + d ^ 3 * (470)) + d ^ 4 * (82)) + d ^ 5 * (4)) + c * (c * (c * (c * (c * (c * (196) + d * (539)) + d ^ 2 * (568)) + d ^ 3 * (296)) + d ^ 4 * (79)) + d ^ 5 * (8))) + c ^ 2 * (c * (c * (c * (c * (c * (20) + d * (70)) + d ^ 2 * (98)) + d ^ 3 * (70)) + d ^ 4 * (26)) + d ^ 5 * (4))) + b * (b * (b * (b * (b * (b * (b * (b * (38) + c * (235) + d * (85)) + c * (c * (624) + d * (456)) + d ^ 2 * (66)) + c * (c * (c * (926) + d * (1031)) + d ^ 2 * (305)) + d ^ 3 * (24)) + c * (c * (c * (c * (836) + d * (1270)) + d ^ 2 * (586)) + d ^ 3 * (96)) + d ^ 4 * (6)) + c * (c * (c * (c * (c * (467) + d * (917)) + d ^ 2 * (599)) + d ^ 3 * (161)) + d ^ 4 * (21)) + d ^ 5) + c * (c * (c * (c * (c * (c * (156) + d * (386)) + d ^ 2 * (343)) + d ^ 3 * (140)) + d ^ 4 * (30)) + d ^ 5 * (3))) + c ^ 2 * (c * (c * (c * (c * (c * (28) + d * (87)) + d ^ 2 * (104)) + d ^ 3 * (62)) + d ^ 4 * (20)) + d ^ 5 * (3))) + c ^ 3 * (c * (c * (c * (c * (c * (2) + d * (8)) + d ^ 2 * (13)) + d ^ 3 * (11)) + d ^ 4 * (5)) + d ^ 5)) + b * (b * (b * (b * (b * (b * (b * (b * (b * (4) + c * (28) + d * (10)) + c * (c * (85) + d * (61)) + d ^ 2 * (8)) + c * (c * (c * (146) + d * (158)) + d ^ 2 * (42)) + d ^ 3 * (2)) + c * (c * (c * (c * (155) + d * (225)) + d ^ 2 * (91)) + d ^ 3 * (9))) + c ^ 2 * (c * (c * (c * (104) + d * (190)) + d ^ 2 * (104)) + d ^ 3 * (16))) + c ^ 3 * (c * (c * (c * (43) + d * (95)) + d ^ 2 * (66)) + d ^ 3 * (14))) + c ^ 4 * (c * (c * (c * (10) + d * (26)) + d ^ 2 * (22)) + d ^ 3 * (6))) + c ^ 5 * (c * (c * (c + d * (3)) + d ^ 2 * (3)) + d ^ 3)) := by ring
  rw [hid]
  clear hid
  positivity

lemma lw_37717_aux5 (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 ≤ (
      a * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b)) * ((a + b) ^ 2 + (a + b) * a) * (a ^ 2 + a * (a + b + c)) +
      (a + b + c) * ((a + b + c) ^ 2 + (a + b + c) * (a + b + c + d)) * ((a + b) ^ 2 + (a + b) * a) * (a ^ 2 + a * (a + b + c)) +
      (a + b + c + d) * ((a + b + c) ^ 2 + (a + b + c) * (a + b + c + d)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b)) * (a ^ 2 + a * (a + b + c)) +
      (a + b) * ((a + b + c) ^ 2 + (a + b + c) * (a + b + c + d)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b)) * ((a + b) ^ 2 + (a + b) * a)) * (a * (a + b + c + d) + (a + b + c) * (a + b)) -
    (a + (a + b + c) + (a + b + c + d) + (a + b)) * (((a + b + c) ^ 2 + (a + b + c) * (a + b + c + d)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b)) * ((a + b) ^ 2 + (a + b) * a) * (a ^ 2 + a * (a + b + c))) := by
  have hid : (
      a * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b)) * ((a + b) ^ 2 + (a + b) * a) * (a ^ 2 + a * (a + b + c)) +
      (a + b + c) * ((a + b + c) ^ 2 + (a + b + c) * (a + b + c + d)) * ((a + b) ^ 2 + (a + b) * a) * (a ^ 2 + a * (a + b + c)) +
      (a + b + c + d) * ((a + b + c) ^ 2 + (a + b + c) * (a + b + c + d)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b)) * (a ^ 2 + a * (a + b + c)) +
      (a + b) * ((a + b + c) ^ 2 + (a + b + c) * (a + b + c + d)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b)) * ((a + b) ^ 2 + (a + b) * a)) * (a * (a + b + c + d) + (a + b + c) * (a + b)) -
    (a + (a + b + c) + (a + b + c + d) + (a + b)) * (((a + b + c) ^ 2 + (a + b + c) * (a + b + c + d)) * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b)) * ((a + b) ^ 2 + (a + b) * a) * (a ^ 2 + a * (a + b + c))) =
      a * (a * (a * (a * (a * (a * (a * (b * (b * (24) + c * (24)) + c * (c * (24) + d * (24)) + d ^ 2 * (24)) + b * (b * (b * (136) + c * (210) + d * (52)) + c * (c * (190) + d * (168)) + d ^ 2 * (116)) + c * (c * (c * (84) + d * (146)) + d ^ 2 * (126)) + d ^ 3 * (32)) + b * (b * (b * (b * (326) + c * (677) + d * (240)) + c * (c * (663) + d * (579)) + d ^ 2 * (264)) + c * (c * (c * (414) + d * (678)) + d ^ 2 * (519)) + d ^ 3 * (120)) + c * (c * (c * (c * (116) + d * (282)) + d ^ 2 * (279)) + d ^ 3 * (113)) + d ^ 4 * (14)) + b * (b * (b * (b * (b * (428) + c * (1111) + d * (453)) + c * (c * (1237) + d * (1099)) + d ^ 2 * (360)) + c * (c * (c * (868) + d * (1341)) + d ^ 2 * (885)) + d ^ 3 * (180)) + c * (c * (c * (c * (396) + d * (915)) + d ^ 2 * (849)) + d ^ 3 * (321)) + d ^ 4 * (37)) + c * (c * (c * (c * (c * (80) + d * (244)) + d ^ 2 * (287)) + d ^ 3 * (153)) + d ^ 4 * (34)) + d ^ 5 * (2)) + b * (b * (b * (b * (b * (b * (332) + c * (1029) + d * (447)) + c * (c * (1309) + d * (1180)) + d ^ 2 * (305)) + c * (c * (c * (979) + d * (1435)) + d ^ 2 * (799)) + d ^ 3 * (136)) + c * (c * (c * (c * (523) + d * (1129)) + d ^ 2 * (952)) + d ^ 3 * (323)) + d ^ 4 * (33)) + c * (c * (c * (c * (c * (184) + d * (530)) + d ^ 2 * (583)) + d ^ 3 * (287)) + d ^ 4 * (58)) + d ^ 5 * (3)) + c * (c * (c * (c * (c * (c * (28) + d * (100)) + d ^ 2 * (137)) + d ^ 3 * (89)) + d ^ 4 * (27)) + d ^ 5 * (3))) + b * (b * (b * (b * (b * (b * (b * (152) + c * (545) + d * (243)) + c * (c * (785) + d * (712)) + d ^ 2 * (155)) + c * (c * (c * (619) + d * (871)) + d ^ 2 * (406)) + d ^ 3 * (54)) + c * (c * (c * (c * (333) + d * (663)) + d ^ 2 * (486)) + d ^ 3 * (137)) + d ^ 4 * (11)) + c * (c * (c * (c * (c * (140) + d * (371)) + d ^ 2 * (366)) + d ^ 3 * (156)) + d ^ 4 * (26)) + d ^ 5) + c * (c * (c * (c * (c * (c * (38) + d * (126)) + d ^ 2 * (157)) + d ^ 3 * (90)) + d ^ 4 * (23)) + d ^ 5 * (2))) + c ^ 2 * (c * (c * (c * (c * (c * (4) + d * (16)) + d ^ 2 * (25)) + d ^ 3 * (19)) + d ^ 4 * (7)) + d ^ 5)) + b * (b * (b * (b * (b * (b * (b * (b * (38) + c * (154) + d * (69)) + c * (c * (248) + d * (225)) + d ^ 2 * (43)) + c * (c * (c * (206) + d * (284)) + d ^ 2 * (113)) + d ^ 3 * (11)) + c * (c * (c * (c * (102) + d * (190)) + d ^ 2 * (117)) + d ^ 3 * (24)) + d ^ 4) + c * (c * (c * (c * (c * (38) + d * (90)) + d ^ 2 * (74)) + d ^ 3 * (23)) + d ^ 4 * (2))) + c ^ 2 * (c * (c * (c * (c * (12) + d * (35)) + d ^ 2 * (36)) + d ^ 3 * (15)) + d ^ 4 * (2))) + c ^ 3 * (c * (c * (c * (c * (2) + d * (7)) + d ^ 2 * (9)) + d ^ 3 * (5)) + d ^ 4))) + b ^ 4 * (b * (b * (b * (b * (b * (4) + c * (18) + d * (8)) + c * (c * (32) + d * (29)) + d ^ 2 * (5)) + c * (c * (c * (28) + d * (39)) + d ^ 2 * (14)) + d ^ 3) + c * (c * (c * (c * (12) + d * (23)) + d ^ 2 * (13)) + d ^ 3 * (2))) + c ^ 2 * (c * (c * (c * (2) + d * (5)) + d ^ 2 * (4)) + d ^ 3)) := by ring
  rw [hid]
  positivity

lemma lw_37717_aux6 (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 ≤ (
      a * ((a + b + c) ^ 2 + (a + b + c) * (a + b)) * ((a + b) ^ 2 + (a + b) * a) * (a ^ 2 + a * (a + b + c + d)) +
      (a + b + c + d) * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b + c)) * ((a + b) ^ 2 + (a + b) * a) * (a ^ 2 + a * (a + b + c + d)) +
      (a + b + c) * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b + c)) * ((a + b + c) ^ 2 + (a + b + c) * (a + b)) * (a ^ 2 + a * (a + b + c + d)) +
      (a + b) * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b + c)) * ((a + b + c) ^ 2 + (a + b + c) * (a + b)) * ((a + b) ^ 2 + (a + b) * a)) * (a * (a + b + c) + (a + b + c + d) * (a + b)) -
    (a + (a + b + c + d) + (a + b + c) + (a + b)) * (((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b + c)) * ((a + b + c) ^ 2 + (a + b + c) * (a + b)) * ((a + b) ^ 2 + (a + b) * a) * (a ^ 2 + a * (a + b + c + d))) := by
  have hid : (
      a * ((a + b + c) ^ 2 + (a + b + c) * (a + b)) * ((a + b) ^ 2 + (a + b) * a) * (a ^ 2 + a * (a + b + c + d)) +
      (a + b + c + d) * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b + c)) * ((a + b) ^ 2 + (a + b) * a) * (a ^ 2 + a * (a + b + c + d)) +
      (a + b + c) * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b + c)) * ((a + b + c) ^ 2 + (a + b + c) * (a + b)) * (a ^ 2 + a * (a + b + c + d)) +
      (a + b) * ((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b + c)) * ((a + b + c) ^ 2 + (a + b + c) * (a + b)) * ((a + b) ^ 2 + (a + b) * a)) * (a * (a + b + c) + (a + b + c + d) * (a + b)) -
    (a + (a + b + c + d) + (a + b + c) + (a + b)) * (((a + b + c + d) ^ 2 + (a + b + c + d) * (a + b + c)) * ((a + b + c) ^ 2 + (a + b + c) * (a + b)) * ((a + b) ^ 2 + (a + b) * a) * (a ^ 2 + a * (a + b + c + d))) =
      a * (a * (a * (a * (a * (a * (a * (b * (b * (24) + c * (24) + d * (24)) + c * (c * (24) + d * (24)) + d ^ 2 * (24)) + b * (b * (b * (136) + c * (210) + d * (158)) + c * (c * (190) + d * (212)) + d ^ 2 * (138)) + c * (c * (c * (84) + d * (106)) + d ^ 2 * (86)) + d ^ 3 * (32)) + b * (b * (b * (b * (326) + c * (677) + d * (437)) + c * (c * (663) + d * (747)) + d ^ 2 * (348)) + c * (c * (c * (414) + d * (564)) + d ^ 2 * (405)) + d ^ 3 * (135)) + c * (c * (c * (c * (116) + d * (182)) + d ^ 2 * (129)) + d ^ 3 * (63)) + d ^ 4 * (14)) + b * (b * (b * (b * (b * (428) + c * (1111) + d * (658)) + c * (c * (1237) + d * (1375)) + d ^ 2 * (498)) + c * (c * (c * (868) + d * (1263)) + d ^ 2 * (807)) + d ^ 3 * (232)) + c * (c * (c * (c * (396) + d * (669)) + d ^ 2 * (480)) + d ^ 3 * (216)) + d ^ 4 * (46)) + c * (c * (c * (c * (c * (80) + d * (156)) + d ^ 2 * (111)) + d ^ 3 * (44)) + d ^ 4 * (13)) + d ^ 5 * (2)) + b * (b * (b * (b * (b * (b * (332) + c * (1029) + d * (582)) + c * (c * (1309) + d * (1438)) + d ^ 2 * (434)) + c * (c * (c * (979) + d * (1502)) + d ^ 2 * (866)) + d ^ 3 * (207)) + c * (c * (c * (c * (523) + d * (963)) + d ^ 2 * (703)) + d ^ 3 * (286)) + d ^ 4 * (56)) + c * (c * (c * (c * (c * (184) + d * (390)) + d ^ 2 * (303)) + d ^ 3 * (122)) + d ^ 4 * (33)) + d ^ 5 * (5)) + c ^ 2 * (c * (c * (c * (c * (28) + d * (68)) + d ^ 2 * (57)) + d ^ 3 * (19)) + d ^ 4 * (2))) + b * (b * (b * (b * (b * (b * (b * (152) + c * (545) + d * (302)) + c * (c * (785) + d * (858)) + d ^ 2 * (228)) + c * (c * (c * (619) + d * (986)) + d ^ 2 * (521)) + d ^ 3 * (100)) + c * (c * (c * (c * (333) + d * (669)) + d ^ 2 * (495)) + d ^ 3 * (178)) + d ^ 4 * (30)) + c * (c * (c * (c * (c * (140) + d * (329)) + d ^ 2 * (282)) + d ^ 3 * (116)) + d ^ 4 * (28)) + d ^ 5 * (4)) + c ^ 2 * (c * (c * (c * (c * (38) + d * (102)) + d ^ 2 * (97)) + d ^ 3 * (38)) + d ^ 4 * (5))) + c ^ 3 * (c * (c * (c * (c * (4) + d * (12)) + d ^ 2 * (13)) + d ^ 3 * (6)) + d ^ 4)) + b * (b * (b * (b * (b * (b * (b * (b * (38) + c * (154) + d * (85)) + c * (c * (248) + d * (271)) + d ^ 2 * (66)) + c * (c * (c * (206) + d * (334)) + d ^ 2 * (163)) + d ^ 3 * (24)) + c * (c * (c * (c * (102) + d * (218)) + d ^ 2 * (159)) + d ^ 3 * (48)) + d ^ 4 * (6)) + c * (c * (c * (c * (c * (38) + d * (100)) + d ^ 2 * (94)) + d ^ 3 * (39)) + d ^ 4 * (8)) + d ^ 5) + c ^ 2 * (c * (c * (c * (c * (12) + d * (37)) + d ^ 2 * (41)) + d ^ 3 * (19)) + d ^ 4 * (3))) + c ^ 3 * (c * (c * (c * (c * (2) + d * (7)) + d ^ 2 * (9)) + d ^ 3 * (5)) + d ^ 4))) + b ^ 4 * (b * (b * (b * (b * (b * (4) + c * (18) + d * (10)) + c * (c * (32) + d * (35)) + d ^ 2 * (8)) + c * (c * (c * (28) + d * (45)) + d ^ 2 * (20)) + d ^ 3 * (2)) + c * (c * (c * (c * (12) + d * (25)) + d ^ 2 * (16)) + d ^ 3 * (3))) + c ^ 2 * (c * (c * (c * (2) + d * (5)) + d ^ 2 * (4)) + d ^ 3)) := by ring
  rw [hid]
  positivity

lemma lw_37717_aux7 (a b c d : ℝ) (ha : 0 ≤ a)
    (hab : a ≤ b) (hac : a ≤ c) (had : a ≤ d) :
    0 ≤ (
      a * (c ^ 2 + c * d) * (d ^ 2 + d * a) * (a ^ 2 + a * b) +
      b * (b ^ 2 + b * c) * (d ^ 2 + d * a) * (a ^ 2 + a * b) +
      c * (b ^ 2 + b * c) * (c ^ 2 + c * d) * (a ^ 2 + a * b) +
      d * (b ^ 2 + b * c) * (c ^ 2 + c * d) * (d ^ 2 + d * a)) * (a * c + b * d) -
    (a + b + c + d) * ((b ^ 2 + b * c) * (c ^ 2 + c * d) * (d ^ 2 + d * a) * (a ^ 2 + a * b)) := by
  rcases le_total b c with hbc | hcb
  · rcases le_total c d with hcd | hdc
    · convert lw_37717_aux1 a (b - a) (c - b) (d - c) ha
        (sub_nonneg.mpr hab) (sub_nonneg.mpr hbc) (sub_nonneg.mpr hcd) using 1 <;> ring
    · rcases le_total b d with hbd | hdb
      · convert lw_37717_aux2 a (b - a) (d - b) (c - d) ha
          (sub_nonneg.mpr hab) (sub_nonneg.mpr hbd) (sub_nonneg.mpr hdc) using 1 <;> ring
      · convert lw_37717_aux5 a (d - a) (b - d) (c - b) ha
          (sub_nonneg.mpr had) (sub_nonneg.mpr hdb) (sub_nonneg.mpr hbc) using 1 <;> ring
  · rcases le_total b d with hbd | hdb
    · convert lw_37717_aux3 a (c - a) (b - c) (d - b) ha
        (sub_nonneg.mpr hac) (sub_nonneg.mpr hcb) (sub_nonneg.mpr hbd) using 1 <;> ring
    · rcases le_total c d with hcd | hdc
      · convert lw_37717_aux4 a (c - a) (d - c) (b - d) ha
          (sub_nonneg.mpr hac) (sub_nonneg.mpr hcd) (sub_nonneg.mpr hdb) using 1 <;> ring
      · convert lw_37717_aux6 a (d - a) (c - d) (b - c) ha
          (sub_nonneg.mpr had) (sub_nonneg.mpr hdc) (sub_nonneg.mpr hcb) using 1 <;> ring

lemma lw_37717_aux8 (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 ≤ (
      a * (c ^ 2 + c * d) * (d ^ 2 + d * a) * (a ^ 2 + a * b) +
      b * (b ^ 2 + b * c) * (d ^ 2 + d * a) * (a ^ 2 + a * b) +
      c * (b ^ 2 + b * c) * (c ^ 2 + c * d) * (a ^ 2 + a * b) +
      d * (b ^ 2 + b * c) * (c ^ 2 + c * d) * (d ^ 2 + d * a)) * (a * c + b * d) -
    (a + b + c + d) * ((b ^ 2 + b * c) * (c ^ 2 + c * d) * (d ^ 2 + d * a) * (a ^ 2 + a * b)) := by
  rcases le_total a b with hab | hba
  · rcases le_total a c with hac | hca
    · rcases le_total a d with had | hda
      · exact lw_37717_aux7 a b c d ha hab hac had
      · convert lw_37717_aux7 d a b c hd hda (hda.trans hab) (hda.trans hac) using 1 <;> ring
    · rcases le_total c d with hcd | hdc
      · convert lw_37717_aux7 c d a b hc hcd hca (hca.trans hab) using 1 <;> ring
      · convert lw_37717_aux7 d a b c hd (hdc.trans hca)
          ((hdc.trans hca).trans hab) hdc using 1 <;> ring
  · rcases le_total b c with hbc | hcb
    · rcases le_total b d with hbd | hdb
      · convert lw_37717_aux7 b c d a hb hbc hbd hba using 1 <;> ring
      · convert lw_37717_aux7 d a b c hd (hdb.trans hba) hdb
          (hdb.trans hbc) using 1 <;> ring
    · rcases le_total c d with hcd | hdc
      · convert lw_37717_aux7 c d a b hc hcd (hcb.trans hba) hcb using 1 <;> ring
      · convert lw_37717_aux7 d a b c hd ((hdc.trans hcb).trans hba)
          (hdc.trans hcb) hdc using 1 <;> ring

theorem lw_37717 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) :
    (a / (b ^ 2 + b * c) + b / (c ^ 2 + c * d) +
      c / (d ^ 2 + d * a) + d / (a ^ 2 + a * b)) ≥
      (a + b + c + d) / (a * c + b * d) := by
  have h1 : 0 < b ^ 2 + b * c := by positivity
  have h2 : 0 < c ^ 2 + c * d := by positivity
  have h3 : 0 < d ^ 2 + d * a := by positivity
  have h4 : 0 < a ^ 2 + a * b := by positivity
  have hq : 0 < a * c + b * d := by positivity
  have heq :
      a / (b ^ 2 + b * c) + b / (c ^ 2 + c * d) +
      c / (d ^ 2 + d * a) + d / (a ^ 2 + a * b) =
      (
      a * (c ^ 2 + c * d) * (d ^ 2 + d * a) * (a ^ 2 + a * b) +
      b * (b ^ 2 + b * c) * (d ^ 2 + d * a) * (a ^ 2 + a * b) +
      c * (b ^ 2 + b * c) * (c ^ 2 + c * d) * (a ^ 2 + a * b) +
      d * (b ^ 2 + b * c) * (c ^ 2 + c * d) * (d ^ 2 + d * a)) / ((b ^ 2 + b * c) * (c ^ 2 + c * d) * (d ^ 2 + d * a) * (a ^ 2 + a * b)) := by
    field_simp
    <;> ring
  rw [heq]
  apply (div_le_div_iff₀ hq (mul_pos (mul_pos (mul_pos h1 h2) h3) h4)).2
  have hp := lw_37717_aux8 a b c d ha.le hb.le hc.le hd.le
  nlinarith only [hp]
end

-- forge:entry lw_50334 kind=proved origin=external
section
/- Let $n$ be a random natural number. $\alpha$ is a number such that $0 < \alpha < \frac{\pi}{n}$ . \n $$sin\alpha sin 2\alpha\cdots sin n\alpha < \frac{1}{n sin^n \frac{\alpha}{2}}$$ -/
theorem lw_50334_aux1 {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∏ i ∈ s, Real.sin (f i)) ≤ 1 := by
  calc
    (∏ i ∈ s, Real.sin (f i)) ≤ |∏ i ∈ s, Real.sin (f i)| := le_abs_self _
    _ = ∏ i ∈ s, |Real.sin (f i)| := Finset.abs_prod _ _
    _ ≤ 1 := Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => Real.abs_sin_le_one _)

theorem lw_50334_aux2 (n : ℕ) : (n : ℝ) * (1 / 2 : ℝ) ^ n < 1 := by
  have hn : (n : ℝ) < (2 : ℝ) ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n))
  calc
    (n : ℝ) * (1 / 2 : ℝ) ^ n = (n : ℝ) / (2 : ℝ) ^ n := by
      simp [div_pow, div_eq_mul_inv]
    _ < 1 := (div_lt_one (by positivity)).2 hn

theorem lw_50334 (n : ℕ) (α : ℝ) (hn : 0 < n)
    (hα : α > 0 ∧ α < Real.pi / n) :
    (∏ i ∈ Finset.Icc 1 n, (Real.sin (i * α))) <
      1 / (n * (Real.sin (α / 2)) ^ n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ham : α * (n : ℝ) < Real.pi := (lt_div_iff₀ hnpos).mp hα.2
  have hap : α < Real.pi := by
    have := mul_le_mul_of_nonneg_left hn1 (le_of_lt hα.1)
    nlinarith
  have hspos : 0 < Real.sin (α / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hα.1]) (by linarith [Real.pi_pos])
  have hdenpos : 0 < (n : ℝ) * Real.sin (α / 2) ^ n := mul_pos hnpos (pow_pos hspos _)
  have hdenlt : (n : ℝ) * Real.sin (α / 2) ^ n < 1 := by
    by_cases hn3 : 3 ≤ n
    · have hn3r : (3 : ℝ) ≤ n := by exact_mod_cast hn3
      have ha : α / 2 < Real.pi / 6 := by
        have := mul_le_mul_of_nonneg_left hn3r (le_of_lt hα.1)
        nlinarith
      have hsle : Real.sin (α / 2) ≤ (1 / 2 : ℝ) := by
        rw [← Real.sin_pi_div_six]
        exact Real.sin_le_sin_of_le_of_le_pi_div_two
          (by linarith [Real.pi_pos, hα.1]) (by linarith [Real.pi_pos]) (le_of_lt ha)
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt hspos) hsle n) (le_of_lt hnpos))
        (lw_50334_aux2 n)
    · have hnle : n ≤ 2 := by omega
      interval_cases n
      · norm_num only [Nat.cast_one, pow_one, one_mul]
        have hs := Real.sin_lt_sin_of_lt_of_le_pi_div_two
          (x := α / 2) (y := Real.pi / 2)
          (by linarith [Real.pi_pos, hα.1]) (le_refl _) (by linarith)
        simpa only [Real.sin_pi_div_two] using hs
      · norm_num only [Nat.cast_ofNat] at hα ⊢
        have hc : 0 < Real.cos α :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hα.1], hα.2⟩
        have hs := Real.sin_sq_eq_half_sub (α / 2)
        rw [show 2 * (α / 2) = α by ring] at hs
        nlinarith
  exact lt_of_le_of_lt (lw_50334_aux1 (Finset.Icc 1 n) (fun i : ℕ => i * α))
    ((one_lt_div hdenpos).2 hdenlt)
end

-- forge:entry lw_51345 kind=disproved origin=external
section
/- Show that $(\sum x^5y-\sum x^4 y^2) + (\sum x^4yz - 3 x^2 y^2 z^2) \ge 0$ -/
theorem lw_51345_disproof : ¬ (∀ (x y z : ℝ),
    (x ^ 5 * y - x ^ 4 * y ^ 2 + y ^ 5 * z - y ^ 4 * z ^ 2 +
      z ^ 5 * x - z ^ 4 * x ^ 2) +
      (x ^ 4 * y * z - 3 * x ^ 2 * y ^ 2 * z ^ 2) ≥ 0) := by
  intro h
  have h1 := h 1 1 1
  norm_num at h1
end

-- forge:entry lw_5175 kind=proved origin=external
section
/- Let $x$ , $y$ and $z$ be three real numbers such that : \n\n $\rightarrow \hspace{2mm} |x| \geq |y+z| $ \n\n $\rightarrow \hspace{2mm} |y| \geq |x+z| $ \n\n $\rightarrow \hspace{2mm} |z| \geq |x+y| $ \n\nProve that $ x+y+z=0$ -/
theorem lw_5175 (x y z : ℝ)
    (hx : abs x ≥ abs (y + z))
    (hy : abs y ≥ abs (x + z))
    (hz : abs z ≥ abs (x + y)) : x + y + z = 0 := by
  have hx' := abs_le.mp hx
  have hy' := abs_le.mp hy
  have hz' := abs_le.mp hz
  rcases le_total 0 x with hx0 | hx0 <;>
    rcases le_total 0 y with hy0 | hy0 <;>
      rcases le_total 0 z with hz0 | hz0 <;>
        simp_all only [abs_of_nonneg, abs_of_nonpos] <;> linarith
end

-- forge:entry lw_50424 kind=proved origin=external
section
/- Let $a, b, c$ be positive real numbers. Prove that: $a(a+b)(a+c)+b(b+a)(b+c)+c(c+a)(c+b)\geq \frac{4}{9}(a+b+c)^3$ -/
theorem lw_50424 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a * (a + b) * (a + c) + b * (b + a) * (b + c) +
      c * (c + a) * (c + b) ≥ (4 / 9) * (a + b + c) ^ 3 := by
  have hs := an_schur_deg_one a b c ha.le hb.le hc.le
  have hab := mul_nonneg (sq_nonneg (a - b)) (add_nonneg ha.le hb.le)
  have hbc := mul_nonneg (sq_nonneg (b - c)) (add_nonneg hb.le hc.le)
  have hca := mul_nonneg (sq_nonneg (c - a)) (add_nonneg hc.le ha.le)
  nlinarith
end

-- forge:entry lw_53148 kind=proved origin=external
section
/- Let $a,b,c>0$ . Prove that $\frac{a}{b}+\frac{b}{c}+\frac{c}{a} \ge \left(\frac{a^2+b^2+c^2}{ab+bc+ca}\right)^{\frac{5}{7}}$ . -/
theorem lw_53148 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a / b + b / c + c / a) ≥
      ((a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a)) ^ (5 / 7) := by
  norm_num
  have hab : 0 ≤ a / b := le_of_lt (div_pos ha hb)
  have hbc : 0 ≤ b / c := le_of_lt (div_pos hb hc)
  have hca : 0 ≤ c / a := le_of_lt (div_pos hc ha)
  by_cases h : b ≤ a
  · have hratio : 1 ≤ a / b := (le_div_iff₀ hb).2 (by simpa using h)
    linarith
  · by_cases h' : c ≤ b
    · have hratio : 1 ≤ b / c := (le_div_iff₀ hc).2 (by simpa using h')
      linarith
    · have hac : a ≤ c := le_trans (le_of_not_ge h) (le_of_not_ge h')
      have hratio : 1 ≤ c / a := (le_div_iff₀ ha).2 (by simpa using hac)
      linarith
end

-- forge:entry lw_54171 kind=disproved origin=external
section
/- Use Schur's inequality we have $ab(a+b)+bc(b+c)+ca(c+a)-3abc\leq a^{3}+b^{3}+c^{3}$ -/
theorem lw_54171_disproof :
    ¬ (∀ (a b c : ℝ),
      a * b * (a + b) + b * c * (b + c) + c * a * (c + a) -
        3 * a * b * c ≤ a ^ 3 + b ^ 3 + c ^ 3) := by
  intro h
  have hcounter := h (-1) 0 0
  norm_num at hcounter
end

-- forge:entry lw_53416 kind=proved origin=external
section
/- For $x, y, z \ge 1$ , prove that: $\sqrt{z(xy+1)} \ge\sqrt{x-1}+\sqrt{y-1}+\sqrt{z-1}$ . -/
lemma lw_53416_aux1 (a b : ℝ) :
    (a + b) ^ 2 ≤ (a ^ 2 + 1) * (b ^ 2 + 1) := by
  nlinarith only [sq_nonneg (a * b - 1)]

theorem lw_53416 (x y z : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) :
    Real.sqrt (z * (x * y + 1)) ≥
      Real.sqrt (x - 1) + Real.sqrt (y - 1) + Real.sqrt (z - 1) := by
  have ha : Real.sqrt (x - 1) ^ 2 = x - 1 := Real.sq_sqrt (by linarith)
  have hb : Real.sqrt (y - 1) ^ 2 = y - 1 := Real.sq_sqrt (by linarith)
  have hc : Real.sqrt (z - 1) ^ 2 = z - 1 := Real.sq_sqrt (by linarith)
  have hab : (Real.sqrt (x - 1) + Real.sqrt (y - 1)) ^ 2 ≤ x * y := by
    have h := lw_53416_aux1 (Real.sqrt (x - 1)) (Real.sqrt (y - 1))
    rw [ha, hb] at h
    nlinarith only [h]
  apply Real.le_sqrt_of_sq_le
  calc
    (Real.sqrt (x - 1) + Real.sqrt (y - 1) + Real.sqrt (z - 1)) ^ 2 ≤
        ((Real.sqrt (x - 1) + Real.sqrt (y - 1)) ^ 2 + 1) *
          (Real.sqrt (z - 1) ^ 2 + 1) :=
      lw_53416_aux1 _ _
    _ = ((Real.sqrt (x - 1) + Real.sqrt (y - 1)) ^ 2 + 1) * z := by
      rw [hc]
      ring
    _ ≤ (x * y + 1) * z :=
      mul_le_mul_of_nonneg_right (add_le_add hab (le_refl 1)) (by linarith)
    _ = z * (x * y + 1) := mul_comm _ _
end

-- forge:entry lw_55475 kind=proved origin=external
section
/- If $x{\in}R$ then prove: $x^4-8x+8{\ge}0$ -/
theorem lw_55475 (x : ℝ) : x^4 - 8 * x + 8 ≥ 0 := by
  nlinarith [sq_nonneg (x ^ 2 - 2), sq_nonneg (x - 1)]
end

-- forge:entry lw_54636 kind=proved origin=external
section
/- Let $a$ , $b$ and $c$ are positive real numbers such that: $a+b+c\geq 3$ . Prove the inequality \n $$\frac{a}{a^2+b+c}+\frac{b}{b^2+c+a}+\frac{c}{c^2+a+b}\leq1.$$ -/
lemma lw_54636_aux1 (a s : ℝ) (ha : 0 ≤ a) (hs : 3 ≤ s)
    (hd : 0 < a ^ 2 + s - a) :
    a / (a ^ 2 + s - a) ≤ (6 * a + s) / (9 * s) := by
  have hspos : 0 < s := by linarith
  have hs3 : 0 ≤ s - 3 := by linarith
  have hcert : 0 ≤ (s - 3) * a ^ 2 * (6 * a + s) +
      (3 * a - s) ^ 2 * (2 * a + s) := by positivity
  apply (div_le_div_iff₀ hd (by positivity : 0 < 9 * s)).2
  apply (mul_le_mul_iff_right₀ hspos).mp
  nlinarith only [hcert]

theorem lw_54636 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (hab : a + b + c ≥ 3) :
    a / (a ^ 2 + b + c) + b / (b ^ 2 + c + a) + c / (c ^ 2 + a + b) ≤ 1 := by
  have hs : 0 < a + b + c := by positivity
  have hda : 0 < a ^ 2 + (a + b + c) - a := by nlinarith [sq_nonneg a]
  have hdb : 0 < b ^ 2 + (a + b + c) - b := by nlinarith [sq_nonneg b]
  have hdc : 0 < c ^ 2 + (a + b + c) - c := by nlinarith [sq_nonneg c]
  have h₁ := lw_54636_aux1 a (a + b + c) (le_of_lt ha) hab hda
  have h₂ := lw_54636_aux1 b (a + b + c) (le_of_lt hb) hab hdb
  have h₃ := lw_54636_aux1 c (a + b + c) (le_of_lt hc) hab hdc
  have e₁ : a ^ 2 + (a + b + c) - a = a ^ 2 + b + c := by ring
  have e₂ : b ^ 2 + (a + b + c) - b = b ^ 2 + c + a := by ring
  have e₃ : c ^ 2 + (a + b + c) - c = c ^ 2 + a + b := by ring
  rw [e₁] at h₁
  rw [e₂] at h₂
  rw [e₃] at h₃
  have heq : (6 * a + (a + b + c)) / (9 * (a + b + c)) +
      (6 * b + (a + b + c)) / (9 * (a + b + c)) +
      (6 * c + (a + b + c)) / (9 * (a + b + c)) = 1 := by
    field_simp
    <;> ring
  linarith
end

-- forge:entry lw_6005 kind=proved origin=external
section
/- By the Cauchy Schwatz İnequality; $ (\frac{1}{a+b}.1+\frac{1}{a+2b}.1+\ldots+\frac{1}{a+nb})^{2}\leg(\frac{1}{a+b}^{2}+\ldots+\frac{1}{a+nb}^{2}).(1^{2}+\ldots+1^{2})$ -/
open scoped BigOperators

theorem lw_6005 (a b : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.Icc 1 n, (1 / (a + (i : ℕ) * b))) ^ 2 ≤
      (∑ i ∈ Finset.Icc 1 n, (1 / (a + (i : ℕ) * b)) ^ 2) *
        (∑ i ∈ Finset.Icc 1 n, (1 ^ 2)) := by
  simpa using
    (Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 n)
      (fun i : ℕ => 1 / (a + (i : ℕ) * b)) (fun _ : ℕ => (1 : ℝ)))
end

-- forge:entry lw_56038 kind=proved origin=external
section
/- For $ a, b, c >0 $ and $ ab+bc+ca=3 $ , prove that:\n\n$ \sqrt{a}+\sqrt{b}+\sqrt{c} \ge 3\sqrt{abc} \ \ ; $\n\nGreetings! -/
lemma lw_56038_aux1 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 = 3) :
    3 * x * y * z ≤ x + y + z := by
  have h₁ : 0 ≤ x * ((y * z - 1) ^ 2 * (y * z + 2)) :=
    mul_nonneg hx (mul_nonneg (sq_nonneg _) (by positivity))
  have h₂ : 0 ≤ y * ((z * x - 1) ^ 2 * (z * x + 2)) :=
    mul_nonneg hy (mul_nonneg (sq_nonneg _) (by positivity))
  have h₃ : 0 ≤ z * ((x * y - 1) ^ 2 * (x * y + 2)) :=
    mul_nonneg hz (mul_nonneg (sq_nonneg _) (by positivity))
  have h₄ := congrArg (fun t : ℝ => t * (x * y * z)) h
  nlinarith only [h₁, h₂, h₃, h₄]

theorem lw_56038 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a * b + b * c + c * a = 3) :
    Real.sqrt a + Real.sqrt b + Real.sqrt c ≥ 3 * Real.sqrt (a * b * c) := by
  have h := lw_56038_aux1 (Real.sqrt a) (Real.sqrt b) (Real.sqrt c)
    (Real.sqrt_nonneg a) (Real.sqrt_nonneg b) (Real.sqrt_nonneg c)
    (by simpa only [Real.sq_sqrt ha.le, Real.sq_sqrt hb.le, Real.sq_sqrt hc.le] using hab)
  rw [Real.sqrt_mul (mul_nonneg ha.le hb.le), Real.sqrt_mul ha.le]
  nlinarith only [h]
end

-- forge:entry lw_7219 kind=disproved origin=external
section
/- Let $a,b,c>0$ . Prove that $\frac{1}{\sqrt{20a+23b}}+\frac{1}{\sqrt{20b+23c}} + \frac{1}{\sqrt{20c+23a}} \geq \frac{9\sqrt{86}}{86\sqrt{a+b+c}}$ -/
theorem lw_7219_disproof : ¬ (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c),
    (1 / Real.sqrt (20 * a + 23 * b) + 1 / Real.sqrt (20 * b + 23 * c) +
      1 / Real.sqrt (20 * c + 23 * a)) ≥
      (9 * Real.sqrt 86) / (86 * Real.sqrt (a + b + c))) := by
  intro h
  have hbad := h 1 1 1 (by norm_num) (by norm_num) (by norm_num)
  norm_num at hbad
  have h43 : (6 : ℝ) < Real.sqrt 43 :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have h86 : (9 : ℝ) < Real.sqrt 86 :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have h3 : Real.sqrt 3 < (7 / 4 : ℝ) :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  have hinv : (1 : ℝ) / Real.sqrt 43 < 1 / 6 :=
    one_div_lt_one_div_of_lt (by norm_num) h43
  simp only [one_div] at hinv
  have hright : (1 / 2 : ℝ) < (9 * Real.sqrt 86) / (86 * Real.sqrt 3) := by
    apply (lt_div_iff₀ (by positivity)).2
    nlinarith
  linarith
end

-- forge:entry lw_9203 kind=disproved origin=external
section
/- Prove that $60\sum_{cyc}a^4bc+42\left(\sum_{cyc}a^3b^2c+\sum_{cyc}a^3bc^2\right)\geq 432a^2b^2c^2$ -/
theorem lw_9203_disproof : ¬ (∀ (a b c : ℝ),
    60 * (a^4 * b * c + b^4 * c * a + c^4 * a * b) +
      42 * (a^3 * b^2 * c + a^3 * b * c^2 + b^3 * c^2 * a +
        b^3 * c * a^2 + c^3 * a^2 * b + c^3 * a * b^2) ≥
      432 * a^2 * b^2 * c^2) := by
  intro h
  have hbad := h 1 1 (-1)
  norm_num at hbad
end

end Mathlib2
