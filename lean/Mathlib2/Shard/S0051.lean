/- Mathlib2 分片 51（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0050
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry lw_25864 kind=proved origin=external
section
/- show that the equation $x^{4}-x^{2}+1=7y$ has no integer solution. -/
theorem lw_25864 : ¬ (∃ x : ℤ, ∃ y : ℤ, x^4 - x^2 + 1 = 7*y) := by
  rintro ⟨x, y, h⟩
  have hmod := congrArg (fun z : ℤ => (z : ZMod 7)) h
  have hnonzero : ∀ z : ZMod 7, z ^ 4 - z ^ 2 + 1 ≠ 0 := by decide
  have h7 : (7 : ZMod 7) = 0 := by decide
  apply hnonzero (x : ZMod 7)
  simpa [h7] using hmod
end

-- forge:entry lw_29127 kind=proved origin=external
section
/- Prove that $(1+x^2)(1+y^2)^{n-1} \geq (\frac{n}{n-1})^{n-1}(x+(n-1)y)^2/n$ for $x>0, y>0, n \geq 4$. -/
lemma lw_29127_aux1 {a b p : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hp : 1 ≤ p) :
    a ^ p * (1 + p * (b / a - 1)) ≤ b ^ p := by
  have hs : -1 ≤ b / a - 1 := by
    have : 0 ≤ b / a := div_nonneg hb ha.le
    linarith
  have h := one_add_mul_self_le_rpow_one_add hs hp
  rw [show 1 + (b / a - 1) = b / a by ring, Real.div_rpow hb ha.le] at h
  have h' := (le_div_iff₀ (Real.rpow_pos_of_pos ha p)).mp h
  simpa only [mul_comm] using h'

lemma lw_29127_aux2 (x a : ℝ) :
    (x + a) ^ 2 ≤ (1 + x ^ 2) * (1 + a ^ 2) := by
  nlinarith [sq_nonneg (x * a - 1)]

theorem lw_29127 {n x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hn : 4 ≤ n) :
    (1 + x^2) * (1 + y^2)^(n - 1) ≥
      (n / (n - 1))^(n - 1) * (x + (n - 1) * y)^2 / n := by
  have hn0 : 0 < n := by linarith
  have hp0 : 0 < n - 1 := by linarith
  have ha : 0 < n / (n - 1) := div_pos hn0 hp0
  have hb : 0 ≤ 1 + y ^ 2 := by positivity
  have hp : 1 ≤ n - 1 := by linarith
  have h := lw_29127_aux1 ha hb hp
  have hid : 1 + (n - 1) * ((1 + y ^ 2) / (n / (n - 1)) - 1) =
      (1 + ((n - 1) * y) ^ 2) / n := by
    field_simp
    <;> ring
  rw [hid] at h
  calc
    (n / (n - 1)) ^ (n - 1) * (x + (n - 1) * y) ^ 2 / n =
        ((n / (n - 1)) ^ (n - 1) / n) * (x + (n - 1) * y) ^ 2 := by ring
    _ ≤ ((n / (n - 1)) ^ (n - 1) / n) *
        ((1 + x ^ 2) * (1 + ((n - 1) * y) ^ 2)) :=
      mul_le_mul_of_nonneg_left (lw_29127_aux2 x ((n - 1) * y)) (by positivity)
    _ = (1 + x ^ 2) * ((n / (n - 1)) ^ (n - 1) *
        ((1 + ((n - 1) * y) ^ 2) / n)) := by ring
    _ ≤ (1 + x ^ 2) * (1 + y ^ 2) ^ (n - 1) :=
      mul_le_mul_of_nonneg_left h (by positivity)
end

-- forge:entry lw_29949 kind=proved origin=external
section
/- Let $ z = \frac {1 + \sqrt {3}i}{1 - \sqrt {3}i} = \frac {(1 + \sqrt {3}i)^2}{4} = \frac { - 1 + \sqrt {3}i}{2}$ , we have $ 2z + 1 = \sqrt {3}i$ . Squaring both sides and arranging the equation gives $ z^2 + z + 1 = 0\ \therefore z^3 - 1 = (z - 1)(z^2 + z + 1) = 0$ , yielding $ z^3 = 1$ . Thus $ \left(\frac {1 + \sqrt {3}i}{1 - \sqrt {3}i}\right)^{20} = z^{20} = \frac {z^{21}}{z} = \frac {(z^3)^7}{z} = \frac {1}{z} = \boxed{\frac { - 1 - \sqrt {3}i}{2}}$ . -/
theorem lw_29949 : (1 + Real.sqrt 3 * Complex.I)^(20) / (1 - Real.sqrt 3 * Complex.I)^(20) = (-1 - Real.sqrt 3 * Complex.I) / 2 := by
  have hs : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hmul : (1 - (Real.sqrt 3 : ℂ) * Complex.I) *
      (1 + (Real.sqrt 3 : ℂ) * Complex.I) = 4 := by
    calc
      _ = 1 - (Real.sqrt 3 : ℂ) ^ 2 * Complex.I ^ 2 := by ring
      _ = 4 := by rw [hs, Complex.I_sq]; norm_num
  have hd : (1 - (Real.sqrt 3 : ℂ) * Complex.I) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    norm_num at hmul
  have hz : (1 + (Real.sqrt 3 : ℂ) * Complex.I) /
      (1 - (Real.sqrt 3 : ℂ) * Complex.I) =
      (-1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2 := by
    apply (div_eq_iff hd).2
    field_simp
    ring_nf
    simp [hs, Complex.I_sq]
    ring
  have hz2 : ((-1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2) ^ 2 =
      (-1 - (Real.sqrt 3 : ℂ) * Complex.I) / 2 := by
    ring_nf
    simp [hs, Complex.I_sq]
    ring
  have hz3 : ((-1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2) ^ 3 = 1 := by
    rw [pow_succ, hz2]
    ring_nf
    norm_num [hs, Complex.I_sq]
  rw [← div_pow, hz]
  calc
    _ = (((-1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2) ^ 3) ^ 6 *
        ((-1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2) ^ 2 := by ring
    _ = (-1 - (Real.sqrt 3 : ℂ) * Complex.I) / 2 := by rw [hz3, hz2]; norm_num
end

-- forge:entry lw_31873 kind=proved origin=external
section
/- Let $x,y,z>0$ and $xy+yz+xz=xyz$. Prove that: $\sum\frac{xy}{z^3(1+x)(1+y)}\ge \frac{1}{16}$ -/
lemma lw_31873_aux1 (t : ℝ) (ht : 0 ≤ t) :
    13 * t - 3 ≤ 27 * (t ^ 3 + t ^ 4) := by
  have hp : 0 ≤ 3 * t ^ 2 + 5 * t + 3 := by positivity
  nlinarith [mul_nonneg (sq_nonneg (3 * t - 1)) hp]

lemma lw_31873_aux2 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : a + b + c = 1) : (1 + a) * (1 + b) * (1 + c) ≤ 64 / 27 := by
  have hab : a + b = 1 - c := by linarith
  have hcab : c * (a + b) ^ 2 = c * (1 - c) ^ 2 := by rw [hab]
  have hc1 : 0 ≤ 4 - 3 * c := by linarith
  have hp : a * b * c ≤ 1 / 27 := by
    nlinarith [mul_nonneg hc (sq_nonneg (a - b)),
      mul_nonneg (sq_nonneg (3 * c - 1)) hc1]
  have hq : a * b + b * c + c * a ≤ 1 / 3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a + b + c - 1)]
  have he : (1 + a) * (1 + b) * (1 + c) =
      2 + (a * b + b * c + c * a) + a * b * c := by
    nlinarith [hs]
  linarith

lemma lw_31873_aux3 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hs : a + b + c = 1) :
    1 / 16 ≤ c ^ 3 / ((1 + a) * (1 + b)) +
      a ^ 3 / ((1 + b) * (1 + c)) + b ^ 3 / ((1 + c) * (1 + a)) := by
  have hden := lw_31873_aux2 a b c ha.le hb.le hc.le hs
  have hnum : 4 / 27 ≤ a ^ 3 + a ^ 4 + b ^ 3 + b ^ 4 + c ^ 3 + c ^ 4 := by
    have h1 := lw_31873_aux1 a ha.le
    have h2 := lw_31873_aux1 b hb.le
    have h3 := lw_31873_aux1 c hc.le
    linarith
  have ha1 : 0 < 1 + a := by positivity
  have hb1 : 0 < 1 + b := by positivity
  have hc1 : 0 < 1 + c := by positivity
  have hid : c ^ 3 / ((1 + a) * (1 + b)) +
      a ^ 3 / ((1 + b) * (1 + c)) + b ^ 3 / ((1 + c) * (1 + a)) =
      (a ^ 3 + a ^ 4 + b ^ 3 + b ^ 4 + c ^ 3 + c ^ 4) /
        ((1 + a) * (1 + b) * (1 + c)) := by
    field_simp
    <;> ring
  rw [hid]
  apply (le_div_iff₀ (by positivity : 0 < (1 + a) * (1 + b) * (1 + c))).2
  linarith

theorem lw_31873 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y + y * z + z * x = x * y * z) :
    (x * y / (z ^ 3 * (1 + x) * (1 + y))) +
      (y * z / (x ^ 3 * (1 + y) * (1 + z))) +
      (z * x / (y ^ 3 * (1 + z) * (1 + x))) ≥ 1 / 16 := by
  have hs : 1 / x + 1 / y + 1 / z = 1 := by
    field_simp
    nlinarith [h]
  have hp := lw_31873_aux3 (1 / x) (1 / y) (1 / z)
    (by positivity) (by positivity) (by positivity) hs
  have hx0 := ne_of_gt hx
  have hy0 := ne_of_gt hy
  have hz0 := ne_of_gt hz
  have hid : (1 / z) ^ 3 / ((1 + 1 / x) * (1 + 1 / y)) +
      (1 / x) ^ 3 / ((1 + 1 / y) * (1 + 1 / z)) +
      (1 / y) ^ 3 / ((1 + 1 / z) * (1 + 1 / x)) =
      x * y / (z ^ 3 * (1 + x) * (1 + y)) +
      y * z / (x ^ 3 * (1 + y) * (1 + z)) +
      z * x / (y ^ 3 * (1 + z) * (1 + x)) := by
    field_simp
    <;> ring
  rwa [hid] at hp
end

-- forge:entry lw_34106 kind=proved origin=external
section
/- Prove that: \n${\left( {\frac{a}{{a + b}}} \right)^2} + {\left( {\frac{b}{{b + c}}} \right)^2} + {\left( {\frac{c}{{c + a}}} \right)^2} + \frac{{4abc}}{{\left( {a + b} \right)\left( {b + c} \right)\left( {c + a} \right)}} \ge \frac{a}{{a + b}} + \frac{b}{{b + c}} + \frac{c}{{c + a}} - \frac{1}{4}$\nGiven: $\left( {a + b} \right)\left( {b + c} \right)\left( {c + a} \right) \ne 0$ -/
theorem lw_34106 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a + b ≠ 0) (hbc : b + c ≠ 0) (hca : c + a ≠ 0)
    (habc : a + b + c ≠ 0) :
    (a / (a + b))^2 + (b / (b + c))^2 + (c / (c + a))^2 +
      (4 * a * b * c) / ((a + b) * (b + c) * (c + a)) ≥
      a / (a + b) + b / (b + c) + c / (c + a) - 1 / 4 := by
  have hid :
      (a / (a + b))^2 + (b / (b + c))^2 + (c / (c + a))^2 +
        (4 * a * b * c) / ((a + b) * (b + c) * (c + a)) -
        (a / (a + b) + b / (b + c) + c / (c + a) - 1 / 4) =
        (a / (a + b) + b / (b + c) + c / (c + a) - 3 / 2)^2 := by
    field_simp [hab, hbc, hca]
    <;> ring
  nlinarith [sq_nonneg (a / (a + b) + b / (b + c) + c / (c + a) - 3 / 2)]
end

-- forge:entry lw_36337 kind=proved origin=external
section
/- Prove that: \((a+b+c+d+1)^{2}\geq 4(a^{2}+b^{2}+c^{2}+d^{2})\) where \(a,b,c,d \in [0,1]\) -/
theorem lw_36337 (a b c d : ℝ) (ha : a ∈ Set.Icc 0 1)
    (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1)
    (hd : d ∈ Set.Icc 0 1) :
    (a + b + c + d + 1) ^ 2 ≥ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  have ha' : 0 ≤ a * (1 - a) := mul_nonneg ha.1 (sub_nonneg.mpr ha.2)
  have hb' : 0 ≤ b * (1 - b) := mul_nonneg hb.1 (sub_nonneg.mpr hb.2)
  have hc' : 0 ≤ c * (1 - c) := mul_nonneg hc.1 (sub_nonneg.mpr hc.2)
  have hd' : 0 ≤ d * (1 - d) := mul_nonneg hd.1 (sub_nonneg.mpr hd.2)
  nlinarith [sq_nonneg (a + b + c + d - 1)]
end

-- forge:entry lw_24500 kind=proved origin=external
section
/- Let $ x;y;z$ be poaitive real numbers satisfying $ xyz = 1$ \nProve that: \n $ \frac {x}{y^4 + 2} + \frac{y}{z^4 + 2} + \frac {z}{x^4 + 2} \geq 1$ -/
lemma lw_24500_aux1 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (0 : ℝ) ≤ x ^ 2 * (x + y + z) ^ 5 * (x ^ 4 + 2 * (x + y) ^ 4) * ((x + y + z) ^ 4 + 2 * x ^ 4) +
      (x + y) ^ 2 * x ^ 5 * ((x + y) ^ 4 + 2 * (x + y + z) ^ 4) * (x ^ 4 + 2 * (x + y) ^ 4) +
      (x + y + z) ^ 2 * (x + y) ^ 5 * ((x + y + z) ^ 4 + 2 * x ^ 4) * ((x + y) ^ 4 + 2 * (x + y + z) ^ 4) -
      x * (x + y) * (x + y + z) * (x ^ 4 + 2 * (x + y) ^ 4) * ((x + y) ^ 4 + 2 * (x + y + z) ^ 4) * ((x + y + z) ^ 4 + 2 * x ^ 4) := by
  have h0 : (0 : ℝ) ≤ (((5 * (x ^ 13 * y ^ 2) +
      5 * (x ^ 13 * y * z)) +
      (5 * (x ^ 13 * z ^ 2) +
      (43 * (x ^ 12 * y ^ 3) +
      122 * (x ^ 12 * y ^ 2 * z)))) +
      ((123 * (x ^ 12 * y * z ^ 2) +
      22 * (x ^ 12 * z ^ 3)) +
      (204 * (x ^ 11 * y ^ 4) +
      (868 * (x ^ 11 * y ^ 3 * z) +
      1182 * (x ^ 11 * y ^ 2 * z ^ 2))))) := by positivity
  have h1 : (0 : ℝ) ≤ (((518 * (x ^ 11 * y * z ^ 3) +
      78 * (x ^ 11 * z ^ 4)) +
      (689 * (x ^ 10 * y ^ 5) +
      (3470 * (x ^ 10 * y ^ 4 * z) +
      5878 * (x ^ 10 * y ^ 3 * z ^ 2)))) +
      ((4082 * (x ^ 10 * y ^ 2 * z ^ 3) +
      1279 * (x ^ 10 * y * z ^ 4)) +
      (147 * (x ^ 10 * z ^ 5) +
      (1728 * (x ^ 9 * y ^ 6) +
      9346 * (x ^ 9 * y ^ 5 * z))))) := by positivity
  have h2 : (0 : ℝ) ≤ (((18439 * (x ^ 9 * y ^ 4 * z ^ 2) +
      17078 * (x ^ 9 * y ^ 3 * z ^ 3)) +
      (8174 * (x ^ 9 * y ^ 2 * z ^ 4) +
      (1917 * (x ^ 9 * y * z ^ 5) +
      173 * (x ^ 9 * z ^ 6)))) +
      ((3225 * (x ^ 8 * y ^ 7) +
      18182 * (x ^ 8 * y ^ 6 * z)) +
      (40191 * (x ^ 8 * y ^ 5 * z ^ 2) +
      (45490 * (x ^ 8 * y ^ 4 * z ^ 3) +
      28963 * (x ^ 8 * y ^ 3 * z ^ 4))))) := by positivity
  have h3 : (0 : ℝ) ≤ (((10320 * (x ^ 8 * y ^ 2 * z ^ 5) +
      1877 * (x ^ 8 * y * z ^ 6)) +
      (132 * (x ^ 8 * z ^ 7) +
      (4491 * (x ^ 7 * y ^ 8) +
      26308 * (x ^ 7 * y ^ 7 * z)))) +
      ((63784 * (x ^ 7 * y ^ 6 * z ^ 2) +
      83926 * (x ^ 7 * y ^ 5 * z ^ 3)) +
      (65797 * (x ^ 7 * y ^ 4 * z ^ 4) +
      (31198 * (x ^ 7 * y ^ 3 * z ^ 5) +
      8560 * (x ^ 7 * y ^ 2 * z ^ 6))))) := by positivity
  have h4 : (0 : ℝ) ≤ (((1200 * (x ^ 7 * y * z ^ 7) +
      63 * (x ^ 7 * z ^ 8)) +
      (4678 * (x ^ 6 * y ^ 9) +
      (28616 * (x ^ 6 * y ^ 8 * z) +
      75256 * (x ^ 6 * y ^ 7 * z ^ 2)))) +
      ((111718 * (x ^ 6 * y ^ 6 * z ^ 3) +
      102842 * (x ^ 6 * y ^ 5 * z ^ 4)) +
      (60169 * (x ^ 6 * y ^ 4 * z ^ 5) +
      (21880 * (x ^ 6 * y ^ 3 * z ^ 6) +
      4596 * (x ^ 6 * y ^ 2 * z ^ 7))))) := by positivity
  have h5 : (0 : ℝ) ≤ (((477 * (x ^ 6 * y * z ^ 8) +
      17 * (x ^ 6 * z ^ 9)) +
      (3632 * (x ^ 5 * y ^ 10) +
      (23351 * (x ^ 5 * y ^ 9 * z) +
      66255 * (x ^ 5 * y ^ 8 * z ^ 2)))) +
      ((108998 * (x ^ 5 * y ^ 7 * z ^ 3) +
      114325 * (x ^ 5 * y ^ 6 * z ^ 4)) +
      (78759 * (x ^ 5 * y ^ 5 * z ^ 5) +
      (35258 * (x ^ 5 * y ^ 4 * z ^ 6) +
      9768 * (x ^ 5 * y ^ 3 * z ^ 7))))) := by positivity
  have h6 : (0 : ℝ) ≤ (((1512 * (x ^ 5 * y ^ 2 * z ^ 8) +
      106 * (x ^ 5 * y * z ^ 9)) +
      (2 * (x ^ 5 * z ^ 10) +
      (2073 * (x ^ 4 * y ^ 11) +
      14086 * (x ^ 4 * y ^ 10 * z)))) +
      ((43017 * (x ^ 4 * y ^ 9 * z ^ 2) +
      77600 * (x ^ 4 * y ^ 8 * z ^ 3)) +
      (91002 * (x ^ 4 * y ^ 7 * z ^ 4) +
      (71676 * (x ^ 4 * y ^ 6 * z ^ 5) +
      37762 * (x ^ 4 * y ^ 5 * z ^ 6))))) := by positivity
  have h7 : (0 : ℝ) ≤ (((12840 * (x ^ 4 * y ^ 4 * z ^ 7) +
      2610 * (x ^ 4 * y ^ 3 * z ^ 8)) +
      (272 * (x ^ 4 * y ^ 2 * z ^ 9) +
      (10 * (x ^ 4 * y * z ^ 10) +
      845 * (x ^ 3 * y ^ 12)))) +
      ((6092 * (x ^ 3 * y ^ 11 * z) +
      19998 * (x ^ 3 * y ^ 10 * z ^ 2)) +
      (39300 * (x ^ 3 * y ^ 9 * z ^ 3) +
      (50913 * (x ^ 3 * y ^ 8 * z ^ 4) +
      45000 * (x ^ 3 * y ^ 7 * z ^ 5))))) := by positivity
  have h8 : (0 : ℝ) ≤ (((27132 * (x ^ 3 * y ^ 6 * z ^ 6) +
      10848 * (x ^ 3 * y ^ 5 * z ^ 7)) +
      (2700 * (x ^ 3 * y ^ 4 * z ^ 8) +
      (368 * (x ^ 3 * y ^ 3 * z ^ 9) +
      20 * (x ^ 3 * y ^ 2 * z ^ 10)))) +
      ((233 * (x ^ 2 * y ^ 13) +
      1786 * (x ^ 2 * y ^ 12 * z)) +
      (6294 * (x ^ 2 * y ^ 11 * z ^ 2) +
      (13412 * (x ^ 2 * y ^ 10 * z ^ 3) +
      19037 * (x ^ 2 * y ^ 9 * z ^ 4))))) := by positivity
  have h9 : (0 : ℝ) ≤ (((18648 * (x ^ 2 * y ^ 8 * z ^ 5) +
      12636 * (x ^ 2 * y ^ 7 * z ^ 6)) +
      (5784 * (x ^ 2 * y ^ 6 * z ^ 7) +
      (1692 * (x ^ 2 * y ^ 5 * z ^ 8) +
      282 * (x ^ 2 * y ^ 4 * z ^ 9)))) +
      ((20 * (x ^ 2 * y ^ 3 * z ^ 10) +
      39 * (x * y ^ 14)) +
      (318 * (x * y ^ 13 * z) +
      (1201 * (x * y ^ 12 * z ^ 2) +
      2764 * (x * y ^ 11 * z ^ 3))))) := by positivity
  have h10 : (0 : ℝ) ≤ (((4271 * (x * y ^ 10 * z ^ 4) +
      4594 * (x * y ^ 9 * z ^ 5)) +
      (3453 * (x * y ^ 8 * z ^ 6) +
      (1776 * (x * y ^ 7 * z ^ 7) +
      594 * (x * y ^ 6 * z ^ 8)))) +
      ((116 * (x * y ^ 5 * z ^ 9) +
      10 * (x * y ^ 4 * z ^ 10)) +
      (3 * (y ^ 15) +
      (26 * (y ^ 14 * z) +
      105 * (y ^ 13 * z ^ 2))))) := by positivity
  have h11 : (0 : ℝ) ≤ (((260 * (y ^ 12 * z ^ 3) +
      435 * (y ^ 11 * z ^ 4)) +
      (510 * (y ^ 10 * z ^ 5) +
      421 * (y ^ 9 * z ^ 6))) +
      ((240 * (y ^ 8 * z ^ 7) +
      90 * (y ^ 7 * z ^ 8)) +
      (20 * (y ^ 6 * z ^ 9) +
      2 * (y ^ 5 * z ^ 10)))) := by positivity
  linear_combination h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8 + h9 + h10 + h11

lemma lw_24500_aux2 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (0 : ℝ) ≤ x ^ 2 * (x + y) ^ 5 * (x ^ 4 + 2 * (x + y + z) ^ 4) * ((x + y) ^ 4 + 2 * x ^ 4) +
      (x + y + z) ^ 2 * x ^ 5 * ((x + y + z) ^ 4 + 2 * (x + y) ^ 4) * (x ^ 4 + 2 * (x + y + z) ^ 4) +
      (x + y) ^ 2 * (x + y + z) ^ 5 * ((x + y) ^ 4 + 2 * x ^ 4) * ((x + y + z) ^ 4 + 2 * (x + y) ^ 4) -
      x * (x + y + z) * (x + y) * (x ^ 4 + 2 * (x + y + z) ^ 4) * ((x + y + z) ^ 4 + 2 * (x + y) ^ 4) * ((x + y) ^ 4 + 2 * x ^ 4) := by
  have h0 : (0 : ℝ) ≤ (((1 * (z ^ 7) * ((1 / 16 : ℝ) * (x ^ 4) - (y ^ 3 * z)) ^ 2 +
      9 * (y * z ^ 4) * ((1 / 16 : ℝ) * (x ^ 5) - (y ^ 3 * z ^ 2)) ^ 2) +
      (36 * (z ^ 5) * ((1 / 16 : ℝ) * (x ^ 5) - (y ^ 4 * z)) ^ 2 +
      (84 * (y * z ^ 2) * ((1 / 16 : ℝ) * (x ^ 6) - (y ^ 4 * z ^ 2)) ^ 2 +
      (44037902321543417383100460475649 / 2365017011986167779802560593920 : ℝ) * (x ^ 11) * (2 * (y ^ 2) - (z ^ 2)) ^ 2))) +
      ((136 * (y ^ 11 * z ^ 4) +
      104 * (y ^ 12 * z ^ 3)) +
      (56 * (y ^ 13 * z ^ 2) +
      (19 * (y ^ 14 * z) +
      3 * (y ^ 15))))) := by positivity
  have h1 : (0 : ℝ) ≤ (((4 * (x * y * z ^ 7) * ((1 / 16 : ℝ) * (x ^ 3) - (y ^ 2 * z)) ^ 2 +
      (737251741184251667320524405543 / 2052966156237992864411944960 : ℝ) * (x ^ 7 * z ^ 2) * ((1 / 16 : ℝ) * (x ^ 2 * z) - (y ^ 3)) ^ 2) +
      ((2148016161884982138657714180243 / 20213820615266391280363765760 : ℝ) * (x ^ 10 * y) * ((4 / 3 : ℝ) * (y ^ 2) - (z ^ 2)) ^ 2 +
      (588 * (x * z ^ 6) * ((1 / 16 : ℝ) * (x ^ 4) - (y ^ 4)) ^ 2 +
      1024 * (x * y * z ^ 3) * ((1 / 16 : ℝ) * (x ^ 5) - (y ^ 4 * z)) ^ 2))) +
      (((17980564792356062595164725729723 / 18846229314264774495301654732800 : ℝ) * (x ^ 5 * z ^ 2) * (16 * (x * y ^ 3) - (z ^ 4)) ^ 2 +
      1040 * (x * y ^ 11 * z ^ 3)) +
      (616 * (x * y ^ 12 * z ^ 2) +
      (228 * (x * y ^ 13 * z) +
      39 * (x * y ^ 14))))) := by positivity
  have h2 : (0 : ℝ) ≤ (((1688 * (x ^ 4 * y ^ 2 * z ^ 3) * ((1 / 16 : ℝ) * (x ^ 2 * z) - (y ^ 3)) ^ 2 +
      (2596158150874371152454458423 / 32077596191218638506436640 : ℝ) * (x ^ 2 * y * z ^ 4) * ((1 / 16 : ℝ) * (x ^ 4) - (y ^ 2 * z ^ 2)) ^ 2) +
      ((142393903 / 32640 : ℝ) * (x ^ 8 * z) * ((1 / 16 : ℝ) * (x ^ 2 * z) - (y ^ 3)) ^ 2 +
      (1680 * (x ^ 2 * y * z ^ 6) * ((1 / 16 : ℝ) * (x ^ 3) - (y ^ 3)) ^ 2 +
      (106267 / 240 : ℝ) * (x ^ 8 * y ^ 2 * z) * ((1 / 16 : ℝ) * (x ^ 2) - (z ^ 2)) ^ 2))) +
      ((4762 * (x ^ 2 * y * z ^ 4) * ((1 / 16 : ℝ) * (x ^ 4) - (y ^ 4)) ^ 2 +
      4584 * (x ^ 2 * z ^ 3) * ((1 / 16 : ℝ) * (x ^ 4 * z) - (y ^ 5)) ^ 2) +
      (3036 * (x ^ 2 * y ^ 11 * z ^ 2) +
      (1243 * (x ^ 2 * y ^ 12 * z) +
      233 * (x ^ 2 * y ^ 13))))) := by positivity
  have h3 : (0 : ℝ) ≤ (((21 * (x ^ 3 * y ^ 2 * z ^ 8) * ((1 / 16 : ℝ) * (x) - (y)) ^ 2 +
      314 * (x ^ 3 * y * z ^ 5) * ((1 / 16 : ℝ) * (x ^ 3) - (y ^ 2 * z)) ^ 2) +
      ((170475491368745397894787744993 / 57739673144193549311585952 : ℝ) * (x ^ 5 * z ^ 4) * ((1 / 16 : ℝ) * (x ^ 3) - (y ^ 3)) ^ 2 +
      (6144 * (x ^ 3 * y * z ^ 5) * ((1 / 16 : ℝ) * (x ^ 2 * z) - (y ^ 3)) ^ 2 +
      10218 * (x ^ 3 * z ^ 4) * ((1 / 16 : ℝ) * (x ^ 2 * z ^ 2) - (y ^ 4)) ^ 2))) +
      (((560949753226556659556228847607 / 64155192382437277012873280 : ℝ) * (x ^ 3 * y * z ^ 3) * ((1 / 16 : ℝ) * (x ^ 3 * z) - (y ^ 4)) ^ 2 +
      8756 * (x ^ 3 * z ^ 2) * ((1 / 16 : ℝ) * (x ^ 3 * z ^ 2) - (y ^ 5)) ^ 2) +
      (4048 * (x ^ 3 * y ^ 11 * z) +
      (845 * (x ^ 3 * y ^ 12) +
      24 * (x ^ 3 * z ^ 8) * ((1 / 16 : ℝ) * (x * z) - (y ^ 2)) ^ 2)))) := by positivity
  have h4 : (0 : ℝ) ≤ ((((9477383515860262406836891958299 / 739067816245677431188300185600 : ℝ) * (x ^ 10 * y) * ((1 / 4 : ℝ) * (x * y) - (z ^ 2)) ^ 2 +
      (53266870491600411314572811 / 4009699523902329813304580 : ℝ) * (x ^ 5 * y * z ^ 5) * ((1 / 16 : ℝ) * (y ^ 2) - (z ^ 2)) ^ 2) +
      ((75492438359401644178325868646127 / 73906781624567743118830018560 : ℝ) * (x ^ 9) * ((1 / 8 : ℝ) * (x * z ^ 2) - (y ^ 3)) ^ 2 +
      (3632 * (x ^ 5) * ((1 / 16 : ℝ) * (x * z ^ 4) - (y ^ 5)) ^ 2 +
      1224 * (x * z ^ 4) * ((1 / 16 : ℝ) * (x ^ 5) - (y ^ 5)) ^ 2))) +
      (((15186848442826095328248284573 / 18404520814711693843068022200 : ℝ) * (x ^ 5 * z ^ 2) * ((1 / 16 : ℝ) * (x * y ^ 3) - (z ^ 4)) ^ 2 +
      (3737080862503878932632546320567 / 513241539059498216102986240 : ℝ) * (x ^ 6 * y ^ 5 * z ^ 4)) +
      (8717 * (x ^ 4 * z) * ((1 / 16 : ℝ) * (x ^ 2 * z ^ 3) - (y ^ 5)) ^ 2 +
      (2073 * (x ^ 4 * y ^ 11) +
      (253195936814099369279631233 / 128310384764874554025746560 : ℝ) * (x ^ 5 * y * z ^ 3) * (16 * (y ^ 3) - (z ^ 3)) ^ 2)))) := by positivity
  have h5 : (0 : ℝ) ≤ ((((323813 / 3840 : ℝ) * (x ^ 8 * y ^ 2 * z) * ((1 / 4 : ℝ) * (x ^ 2) - (z ^ 2)) ^ 2 +
      (6891 / 256 : ℝ) * (x ^ 5 * y ^ 2) * ((1 / 16 : ℝ) * (x ^ 3 * y) - (z ^ 4)) ^ 2) +
      ((178118063019120771632071337993 / 64155192382437277012873280 : ℝ) * (x ^ 3 * y * z ^ 3) * ((1 / 16 : ℝ) * (x ^ 4) - (y ^ 4)) ^ 2 +
      (4352 * (x ^ 4 * z ^ 3) * ((1 / 16 : ℝ) * (x * z ^ 3) - (y ^ 4)) ^ 2 +
      45 * (x * y ^ 2 * z ^ 4) * ((1 / 16 : ℝ) * (x ^ 4) - (y ^ 2 * z ^ 2)) ^ 2))) +
      ((6778 * (x ^ 6 * z ^ 3) * ((1 / 16 : ℝ) * (x ^ 2 * z) - (y ^ 3)) ^ 2 +
      14736 * (x ^ 6 * y * z ^ 2) * ((1 / 16 : ℝ) * (x ^ 2 * z) - (y ^ 3)) ^ 2) +
      ((13435667988451261221559880676 / 1002424880975582453326145 : ℝ) * (x ^ 5 * z ^ 2) * ((1 / 16 : ℝ) * (x ^ 2 * z ^ 2) - (y ^ 4)) ^ 2 +
      ((37256657 / 32640 : ℝ) * (x ^ 6 * z) * ((1 / 16 : ℝ) * (x ^ 3 * z) - (y ^ 4)) ^ 2 +
      5 * (x ^ 2 * y ^ 2 * z ^ 5) * ((1 / 16 : ℝ) * (x ^ 3) - (y * z ^ 2)) ^ 2)))) := by positivity
  have h6 : (0 : ℝ) ≤ ((((19078735201535537842744634333 / 4009699523902329813304580 : ℝ) * (x ^ 5 * y ^ 4 * z ^ 6) +
      (21503 / 64 : ℝ) * (x ^ 7 * y * z) * ((1 / 16 : ℝ) * (x * y ^ 2) - (z ^ 3)) ^ 2) +
      ((2171 / 32 : ℝ) * (x ^ 6 * y) * ((1 / 16 : ℝ) * (x ^ 2 * y ^ 2) - (z ^ 4)) ^ 2 +
      (190 * (x ^ 3 * y * z ^ 7) * ((1 / 16 : ℝ) * (x * z) - (y ^ 2)) ^ 2 +
      216 * (x * y * z ^ 5) * ((1 / 16 : ℝ) * (x ^ 4) - (y ^ 3 * z)) ^ 2))) +
      ((16172 * (x ^ 4 * y * z ^ 2) * ((1 / 16 : ℝ) * (x ^ 2 * z ^ 2) - (y ^ 4)) ^ 2 +
      1344 * (x ^ 4 * y * z ^ 6) * ((1 / 16 : ℝ) * (x ^ 2) - (y ^ 2)) ^ 2) +
      (12969 * (x ^ 5 * y * z) * ((1 / 16 : ℝ) * (x ^ 2 * z ^ 2) - (y ^ 4)) ^ 2 +
      ((402926383 / 32640 : ℝ) * (x ^ 6 * z) * ((1 / 16 : ℝ) * (x ^ 2 * z ^ 2) - (y ^ 4)) ^ 2 +
      4678 * (x ^ 6 * y) * ((1 / 16 : ℝ) * (x ^ 2 * z ^ 2) - (y ^ 4)) ^ 2)))) := by positivity
  have h7 : (0 : ℝ) ≤ ((((752 / 3 : ℝ) * (x ^ 7 * y ^ 2) * ((1 / 8 : ℝ) * (x ^ 3) - (z ^ 3)) ^ 2 +
      4730 * (x ^ 5 * y ^ 4) * ((1 / 16 : ℝ) * (x ^ 3) - (y * z ^ 2)) ^ 2) +
      ((243948476447811516652921927487 / 1154793462883870986231719040 : ℝ) * (x ^ 9) * ((1 / 16 : ℝ) * (x ^ 2 * z) - (y ^ 3)) ^ 2 +
      ((1877432966672346800296321727 / 14781356324913548623766003712 : ℝ) * (x ^ 5 * z ^ 4) * (16 * (y ^ 3) - (z ^ 3)) ^ 2 +
      (413048704612969402192012176071 / 1847669540614193577970750464 : ℝ) * (x ^ 9 * y * z) * ((1 / 16 : ℝ) * (x * z) - (y ^ 2)) ^ 2))) +
      ((11688 * (x ^ 4 * z ^ 3) * ((1 / 16 : ℝ) * (x ^ 2 * z ^ 2) - (y ^ 4)) ^ 2 +
      (11123769145892110882966841201933 / 9238347703070967889853752320 : ℝ) * (x ^ 5 * y * z ^ 3) * ((1 / 16 : ℝ) * (x ^ 3) - (y ^ 2 * z)) ^ 2) +
      ((27 / 32 : ℝ) * (x ^ 4 * y ^ 2 * z ^ 5) * (16 * (x * z) - (y ^ 2)) ^ 2 +
      (1280 * (x ^ 5 * y * z) * ((1 / 16 : ℝ) * (x ^ 4) - (y ^ 3 * z)) ^ 2 +
      (4965 / 128 : ℝ) * (x ^ 8 * z) * ((1 / 16 : ℝ) * (y ^ 3) - (z ^ 3)) ^ 2)))) := by positivity
  have h8 : (0 : ℝ) ≤ ((((166243103518432260243422613929 / 3284745849980788583059111936 : ℝ) * (x ^ 8 * y) * ((1 / 4 : ℝ) * (x ^ 2 * y) - (z ^ 3)) ^ 2 +
      (1854080135576559107119525311791 / 543432217827703993520808960 : ℝ) * (x ^ 7 * z ^ 2) * ((1 / 16 : ℝ) * (x * z ^ 2) - (y ^ 3)) ^ 2) +
      (504 * (x ^ 2 * z ^ 5) * ((1 / 16 : ℝ) * (x ^ 4) - (y ^ 3 * z)) ^ 2 +
      ((1169593682431981462812440436595 / 230958692576774197246343808 : ℝ) * (x ^ 5 * z ^ 2) * ((1 / 16 : ℝ) * (x ^ 3 * z) - (y ^ 4)) ^ 2 +
      (84286985679276992585543604503 / 57739673144193549311585952 : ℝ) * (x ^ 3 * y ^ 4) * ((1 / 16 : ℝ) * (x ^ 4) - (y * z ^ 3)) ^ 2))) +
      (((34477318423352567476145781815519 / 1071648333556232275223035269120 : ℝ) * (x ^ 9 * y ^ 2) * ((3 / 2 : ℝ) * (y ^ 2) - (z ^ 2)) ^ 2 +
      (14537115864927203680989466415327 / 4619173851535483944926876160 : ℝ) * (x ^ 8 * y) * ((1 / 16 : ℝ) * (x * z ^ 2) - (y ^ 3)) ^ 2) +
      ((15554992578751353876370872332249 / 262779667998463086644728954880 : ℝ) * (x ^ 9) * ((4 / 3 : ℝ) * (x * y ^ 2) - (z ^ 3)) ^ 2 +
      ((7578385301773969653024338389171 / 16423729249903942915295559680 : ℝ) * (x ^ 8 * y) * (1 * (x * y ^ 2) - (z ^ 3)) ^ 2 +
      (14495898895052368257919823604 / 1002424880975582453326145 : ℝ) * (x ^ 5 * y * z ^ 3) * ((1 / 16 : ℝ) * (x ^ 2 * z) - (y ^ 3)) ^ 2)))) := by positivity
  have h9 : (0 : ℝ) ≤ ((((273110296558441717432330272673 / 3753078754372580705253086880 : ℝ) * (x ^ 8 * y) * ((1 / 8 : ℝ) * (x ^ 2 * z) - (y ^ 3)) ^ 2 +
      9620 * (x ^ 7 * y * z) * ((1 / 16 : ℝ) * (x ^ 2 * z) - (y ^ 3)) ^ 2) +
      ((7351705762212801232479801805897 / 16423729249903942915295559680 : ℝ) * (x ^ 9 * y * z) * ((4 / 3 : ℝ) * (y ^ 2) - (z ^ 2)) ^ 2 +
      (128 * (z ^ 3) * ((1 / 16 : ℝ) * (x ^ 6) - (y ^ 5 * z)) ^ 2 +
      (200276796233533494405906093193 / 577396731441935493115859520 : ℝ) * (x ^ 5 * y ^ 5 * z) * ((1 / 16 : ℝ) * (x ^ 2) - (z ^ 2)) ^ 2))) +
      (((253099877 / 8355840 : ℝ) * (x ^ 8 * z) * (1 * (x * z ^ 2) - (y ^ 3)) ^ 2 +
      (43547 / 8192 : ℝ) * (x ^ 7 * z ^ 2) * (16 * (y ^ 3) - (z ^ 3)) ^ 2) +
      ((236445604111878813619473193153 / 6158898468713978593235834880 : ℝ) * (x ^ 10 * y) * ((1 / 3 : ℝ) * (x * z) - (y ^ 2)) ^ 2 +
      (3456 * (x ^ 2 * z ^ 5) * ((1 / 16 : ℝ) * (x ^ 3 * z) - (y ^ 4)) ^ 2 +
      (832 / 3 : ℝ) * (x ^ 7 * y ^ 2) * ((1 / 16 : ℝ) * (x ^ 3) - (z ^ 3)) ^ 2)))) := by positivity
  have h10 : (0 : ℝ) ≤ ((((180197 / 32 : ℝ) * (x ^ 4 * z ^ 5) * ((1 / 16 : ℝ) * (x ^ 3) - (y ^ 3)) ^ 2 +
      (2127140614338566566909417 / 32077596191218638506436640 : ℝ) * (x ^ 2 * y * z ^ 6) * (16 * (x ^ 3) - (y ^ 2 * z)) ^ 2) +
      ((11246691728812730980450771 / 115479346288387098623171904 : ℝ) * (x ^ 7) * ((1 / 16 : ℝ) * (x * y ^ 3) - (z ^ 4)) ^ 2 +
      ((51516725555866235395306554601 / 57739673144193549311585952 : ℝ) * (x ^ 3 * z ^ 6) * ((1 / 16 : ℝ) * (x ^ 2 * z) - (y ^ 3)) ^ 2 +
      (102197578878816353092978415327 / 20016420023320430428016463360 : ℝ) * (x ^ 8 * y) * ((2 / 3 : ℝ) * (x ^ 2 * z) - (y ^ 3)) ^ 2))) +
      (((429490788140334200262248116709 / 144349182860483873278964880 : ℝ) * (x ^ 7) * ((1 / 16 : ℝ) * (x * z ^ 3) - (y ^ 4)) ^ 2 +
      72 * (x ^ 4 * y ^ 2 * z ^ 5) * ((1 / 16 : ℝ) * (x ^ 2) - (y * z)) ^ 2) +
      ((1770349233926398426808368166161 / 1071648333556232275223035269120 : ℝ) * (x ^ 9 * y ^ 2) * (16 * (y ^ 2) - (z ^ 2)) ^ 2 +
      ((218781392086098874633583159371 / 144349182860483873278964880 : ℝ) * (x ^ 7) * ((1 / 16 : ℝ) * (x ^ 2 * z ^ 2) - (y ^ 4)) ^ 2 +
      (115399143942379637923985886900119 / 1313898339992315433223644774400 : ℝ) * (x ^ 10 * y) * ((2 / 3 : ℝ) * (x * y) - (z ^ 2)) ^ 2)))) := by positivity
  have h11 : (0 : ℝ) ≤ (12584 * (x ^ 4 * y * z ^ 4) * ((1 / 16 : ℝ) * (x * z ^ 2) - (y ^ 3)) ^ 2 +
      (1234187156043543345723678443713 / 1154793462883870986231719040 : ℝ) * (x ^ 5 * z ^ 2) * ((1 / 16 : ℝ) * (x ^ 4) - (y ^ 4)) ^ 2) := by positivity
  linear_combination h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8 + h9 + h10 + h11

lemma lw_24500_aux3 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (0 : ℝ) ≤ a ^ 2 * c ^ 5 * (a ^ 4 + 2 * b ^ 4) * (c ^ 4 + 2 * a ^ 4) +
      b ^ 2 * a ^ 5 * (b ^ 4 + 2 * c ^ 4) * (a ^ 4 + 2 * b ^ 4) +
      c ^ 2 * b ^ 5 * (c ^ 4 + 2 * a ^ 4) * (b ^ 4 + 2 * c ^ 4) -
      a * b * c * (a ^ 4 + 2 * b ^ 4) * (b ^ 4 + 2 * c ^ 4) * (c ^ 4 + 2 * a ^ 4) := by
  have h₁ : ∀ (a b c : ℝ), 0 ≤ a → a ≤ b → b ≤ c →
      (0 : ℝ) ≤ a ^ 2 * c ^ 5 * (a ^ 4 + 2 * b ^ 4) * (c ^ 4 + 2 * a ^ 4) +
      b ^ 2 * a ^ 5 * (b ^ 4 + 2 * c ^ 4) * (a ^ 4 + 2 * b ^ 4) +
      c ^ 2 * b ^ 5 * (c ^ 4 + 2 * a ^ 4) * (b ^ 4 + 2 * c ^ 4) -
      a * b * c * (a ^ 4 + 2 * b ^ 4) * (b ^ 4 + 2 * c ^ 4) * (c ^ 4 + 2 * a ^ 4) := by
    intro a b c ha hab hbc
    convert lw_24500_aux1 a (b - a) (c - b) ha
      (sub_nonneg.mpr hab) (sub_nonneg.mpr hbc) using 1 <;> ring
  have h₂ : ∀ (a b c : ℝ), 0 ≤ a → a ≤ c → c ≤ b →
      (0 : ℝ) ≤ a ^ 2 * c ^ 5 * (a ^ 4 + 2 * b ^ 4) * (c ^ 4 + 2 * a ^ 4) +
      b ^ 2 * a ^ 5 * (b ^ 4 + 2 * c ^ 4) * (a ^ 4 + 2 * b ^ 4) +
      c ^ 2 * b ^ 5 * (c ^ 4 + 2 * a ^ 4) * (b ^ 4 + 2 * c ^ 4) -
      a * b * c * (a ^ 4 + 2 * b ^ 4) * (b ^ 4 + 2 * c ^ 4) * (c ^ 4 + 2 * a ^ 4) := by
    intro a b c ha hac hcb
    convert lw_24500_aux2 a (c - a) (b - c) ha
      (sub_nonneg.mpr hac) (sub_nonneg.mpr hcb) using 1 <;> ring
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · exact h₁ a b c ha hab hbc
    · rcases le_total a c with hac | hca
      · exact h₂ a b c ha hac hcb
      · convert h₁ c a b hc hca hab using 1 <;> ring
  · rcases le_total a c with hac | hca
    · convert h₂ b c a hb hba hac using 1 <;> ring
    · rcases le_total b c with hbc | hcb
      · convert h₁ b c a hb hbc hca using 1 <;> ring
      · convert h₂ c a b hc hcb hba using 1 <;> ring

lemma lw_24500_aux4 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 ≤ (a / b) / ((b / c) ^ 4 + 2) +
      (b / c) / ((c / a) ^ 4 + 2) + (c / a) / ((a / b) ^ 4 + 2) := by
  have h := lw_24500_aux3 a b c ha.le hb.le hc.le
  let D := a * b * c * (a ^ 4 + 2 * b ^ 4) *
    (b ^ 4 + 2 * c ^ 4) * (c ^ 4 + 2 * a ^ 4)
  have hD : 0 < D := by dsimp [D]; positivity
  have hA : a ^ 4 + 2 * b ^ 4 ≠ 0 := by positivity
  have hB : b ^ 4 + 2 * c ^ 4 ≠ 0 := by positivity
  have hC : c ^ 4 + 2 * a ^ 4 ≠ 0 := by positivity
  have he :
      ((a / b) / ((b / c) ^ 4 + 2) +
        (b / c) / ((c / a) ^ 4 + 2) + (c / a) / ((a / b) ^ 4 + 2) - 1) * D =
      a ^ 2 * c ^ 5 * (a ^ 4 + 2 * b ^ 4) * (c ^ 4 + 2 * a ^ 4) +
      b ^ 2 * a ^ 5 * (b ^ 4 + 2 * c ^ 4) * (a ^ 4 + 2 * b ^ 4) +
      c ^ 2 * b ^ 5 * (c ^ 4 + 2 * a ^ 4) * (b ^ 4 + 2 * c ^ 4) -
      a * b * c * (a ^ 4 + 2 * b ^ 4) * (b ^ 4 + 2 * c ^ 4) * (c ^ 4 + 2 * a ^ 4) := by
    dsimp [D]
    field_simp
    <;> ring
  rw [← he] at h
  nlinarith

theorem lw_24500 (x y z : ℝ)
    (hx : x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y * z = 1) :
    x / (y ^ 4 + 2) + y / (z ^ 4 + 2) + z / (x ^ 4 + 2) ≥ 1 := by
  rcases hx with ⟨hx, hy, hz, hxyz⟩
  have h := lw_24500_aux4 (x * y) y 1 (mul_pos hx hy) hy (by norm_num)
  have hz' : 1 / (x * y) = z := by
    apply (div_eq_iff (ne_of_gt (mul_pos hx hy))).2
    nlinarith [hxyz]
  simpa only [mul_div_cancel_right₀ x (ne_of_gt hy), div_one, hz'] using h
end

-- forge:entry lw_36700 kind=disproved origin=external
section
/- Prove that for non-negative real numbers $a, b, c$,\n1) $\frac{a^2}{b^2-bc+c^2} + \frac{b^2}{c^2-ca+a^2} + \frac{c^2}{a^2-ab+b^2} \geq 2$ -/
theorem lw_36700_disproof :
    ¬ (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c),
      a^2/(b^2 - b*c + c^2) + b^2/(c^2 - c*a + a^2) +
        c^2/(a^2 - a*b + b^2) ≥ 2) := by
  intro h
  have hz := h 0 0 0 (by norm_num) (by norm_num) (by norm_num)
  norm_num at hz
end

-- forge:entry lw_37351 kind=proved origin=external
section
/- Let $a,b,c>0:abc=1.$ Prove that: $$\frac{a}{b(a+b)}+\frac{b}{c(b+c)}+\frac{c}{a(c+a)}\ge\frac{3(ab+bc+ca)}{2(a+b+c)}$$ -/
lemma lw_37351_aux1 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x + y + z) / 2 ≤ x ^ 2 / (x + y) + y ^ 2 / (y + z) + z ^ 2 / (z + x) := by
  have hxy : (3 * x - y) / 4 ≤ x ^ 2 / (x + y) := by
    apply (le_div_iff₀ (add_pos hx hy)).2
    nlinarith [sq_nonneg (x - y)]
  have hyz : (3 * y - z) / 4 ≤ y ^ 2 / (y + z) := by
    apply (le_div_iff₀ (add_pos hy hz)).2
    nlinarith [sq_nonneg (y - z)]
  have hzx : (3 * z - x) / 4 ≤ z ^ 2 / (z + x) := by
    apply (le_div_iff₀ (add_pos hz hx)).2
    nlinarith [sq_nonneg (z - x)]
  linarith

lemma lw_37351_aux2 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) : 3 ≤ a + b + c := by
  have h := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := (1 / 3 : ℝ)) (w₂ := (1 / 3 : ℝ)) (w₃ := (1 / 3 : ℝ))
    (p₁ := a) (p₂ := b) (p₃ := c)
    (by norm_num) (by norm_num) (by norm_num) ha.le hb.le hc.le (by norm_num)
  rw [← Real.mul_rpow ha.le hb.le,
    ← Real.mul_rpow (mul_pos ha hb).le hc.le, habc, Real.one_rpow] at h
  linarith

lemma lw_37351_aux3 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a * b + b * c + c * a) / 2 ≤
      a / (b * (a + b)) + b / (c * (b + c)) + c / (a * (c + a)) := by
  have h := lw_37351_aux1 (c * a) (b * c) (a * b)
    (mul_pos hc ha) (mul_pos hb hc) (mul_pos ha hb)
  have h1 : (c * a) ^ 2 / (c * a + b * c) = a / (b * (a + b)) := by
    apply (div_eq_div_iff (ne_of_gt (add_pos (mul_pos hc ha) (mul_pos hb hc)))
      (ne_of_gt (mul_pos hb (add_pos ha hb)))).2
    calc
      (c * a) ^ 2 * (b * (a + b)) = (a * b * c) * (a * (c * a + b * c)) := by ring
      _ = a * (c * a + b * c) := by rw [habc, one_mul]
  have h2 : (b * c) ^ 2 / (b * c + a * b) = c / (a * (c + a)) := by
    apply (div_eq_div_iff (ne_of_gt (add_pos (mul_pos hb hc) (mul_pos ha hb)))
      (ne_of_gt (mul_pos ha (add_pos hc ha)))).2
    calc
      (b * c) ^ 2 * (a * (c + a)) = (a * b * c) * (c * (b * c + a * b)) := by ring
      _ = c * (b * c + a * b) := by rw [habc, one_mul]
  have h3 : (a * b) ^ 2 / (a * b + c * a) = b / (c * (b + c)) := by
    apply (div_eq_div_iff (ne_of_gt (add_pos (mul_pos ha hb) (mul_pos hc ha)))
      (ne_of_gt (mul_pos hc (add_pos hb hc)))).2
    calc
      (a * b) ^ 2 * (c * (b + c)) = (a * b * c) * (b * (a * b + c * a)) := by ring
      _ = b * (a * b + c * a) := by rw [habc, one_mul]
  rw [h1, h2, h3] at h
  linarith

theorem lw_37351 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a / (b * (a + b)) + b / (c * (b + c)) + c / (a * (c + a))) ≥
      3 * (a * b + b * c + c * a) / (2 * (a + b + c)) := by
  have hp := lw_37351_aux2 a b c ha hb hc habc
  have hq : 0 ≤ a * b + b * c + c * a := by positivity
  have hs := lw_37351_aux3 a b c ha hb hc habc
  apply le_trans ?_ hs
  apply (div_le_iff₀ (by positivity : 0 < 2 * (a + b + c))).2
  nlinarith [mul_nonneg hq (show 0 ≤ a + b + c - 3 by linarith)]
end

-- forge:entry lw_38777 kind=disproved origin=external
section
/- Let $x+y+z=3u$ , $xy+xz+yz=3v^2$ , where $v>0$ and $xyz=w^3$ .\n\nHence, we need to prove that $\sum_{cyc}\frac{v+x}{y+z}\geq3$ , which is linear inequality of $w^3$ .\n\nHence, by $uvw$ it remains to check two cases only.\n\n1. $z\rightarrow0^+$ ;\n2. $y=z$ ,\n\nwhich gives that your inequality is indeed true. -/
theorem lw_38777_disproof :
    ¬ (∀ (x y z u v w : ℝ),
      0 < v → 0 < w →
      x + y + z = 3 * u →
      x * y + x * z + y * z = 3 * v ^ 2 →
      x * y * z = w ^ 3 →
      (v + x) / (y + z) + (v + y) / (z + x) +
        (v + z) / (x + y) ≥ 3) := by
  intro h
  have hbad := h (-2) (-2) (1 / 4) (-5 / 4) 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hbad
end

-- forge:entry lw_37809 kind=proved origin=external
section
/- Let $a\ge b\ge c\ge d\ge e>0$ . $(a-b+c-d+e)(\frac{1}{a}-\frac{1}{b}+\frac{1}{c}-\frac{1}{d}+\frac{1}{e})\ge 1.$ Let $x_1\geq x_2\geq...\geq x_{2n-1}>0$ for all $n\in\mathbb N$ . Prove that: $$\left(x_1-x_2+...+x_{2n-1}\right)\left(\frac{1}{x_1}-\frac{1}{x_2}+...+\frac{1}{x_{2n-1}}\right)\geq1$$ Kazakhstan 2017: -/
lemma lw_37809_aux1 (a b c : ℝ) (hab : b ≤ a) (hbc : c ≤ b) (hc : 0 < c) :
    1 ≤ (a - b + c) * (1 / a - 1 / b + 1 / c) := by
  have hb : 0 < b := lt_of_lt_of_le hc hbc
  have ha : 0 < a := lt_of_lt_of_le hb hab
  have hden : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
  have hnum : 0 ≤ (a - b) * (b - c) * (a + c) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hbc))
      (by positivity)
  have hid : (a - b + c) * (1 / a - 1 / b + 1 / c) - 1 =
      (a - b) * (b - c) * (a + c) / (a * b * c) := by
    field_simp
    <;> ring
  have hquot := div_nonneg hnum (le_of_lt hden)
  linarith

theorem lw_37809 (a b c d e : ℝ) (ha : a >= b) (hb : b >= c)
    (hc : c >= d) (hd : d >= e) (he : e > 0) :
    (a - b + c - d + e) * (1 / a - 1 / b + 1 / c - 1 / d + 1 / e) >= 1 := by
  have htail := lw_37809_aux1 c d e hc hd he
  have ht : 0 < c - d + e := by linarith
  have hbt : c - d + e ≤ b := by linarith
  have hinv : 1 / (c - d + e) ≤ 1 / c - 1 / d + 1 / e := by
    apply (div_le_iff₀ ht).2
    nlinarith [htail]
  have hthree := lw_37809_aux1 a b (c - d + e) ha hbt ht
  have hsum : 0 ≤ a - b + (c - d + e) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hinv hsum
  nlinarith [hthree, hmul]
end

-- forge:entry lw_41789 kind=disproved origin=external
section
/- Note that $t+1-s=(x-1)(y-1) \ge 0 \implies t+1 \ge s=\frac{13t-t^2-1}{t+1} \implies t \ge \frac{11+\sqrt{105}}4=t_0$ -/
theorem lw_41789_disproof :
    ¬ (∀ (t : ℝ) (ht : t ≥ (11 + Real.sqrt 105) / 4),
      13 * t - t^2 - 1 ≤ t + 1) := by
  intro h
  have hsquare : (Real.sqrt (105 : ℝ)) ^ 2 = 105 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt : Real.sqrt (105 : ℝ) ≤ 13 := by
    nlinarith [Real.sqrt_nonneg (105 : ℝ)]
  have ht : (6 : ℝ) ≥ (11 + Real.sqrt 105) / 4 := by
    linarith
  have hfalse := h 6 ht
  norm_num at hfalse
end

-- forge:entry x2611_15210_s kind=definition origin=definition
section
noncomputable def x2611_15210_s (L : ℕ) (G : Type*) [AddCommMonoid G] : ℕ :=
  sInf {s : ℕ | ∀ a : Fin s → G, ∃ I : Finset (Fin s), I.card = L ∧ ∑ i ∈ I, a i = 0}
end

-- forge:entry x2611_11972_euler kind=definition origin=definition
section
noncomputable def x2611_11972_euler (k : List ℤ) : ℝ := by
  classical
  exact ∑' n : Fin k.length → ℕ, if StrictMono n then
    ∏ j : Fin k.length,
      (if k.get j < 0 then (-1 : ℝ) ^ (n j + 1) else 1) /
        ((n j + 1 : ℕ) : ℝ) ^ (k.get j).natAbs
    else 0
end

-- forge:entry x2611_11287_lattice_count kind=definition origin=definition
section
noncomputable def x2611_11287_lattice_count {n : ℕ}
    (S : Submodule ℤ (Matrix (Fin n) (Fin n) ℤ)) (H : ℤ) : ℕ :=
  Set.ncard {A : Matrix (Fin n) (Fin n) ℤ | A ∈ S ∧ ∀ i j, |A i j| ≤ H}
end

-- forge:entry x2611_16923_li kind=definition origin=definition
section
noncomputable def x2611_16923_li (r : ℕ) (weak : Bool) (lower : ℕ)
    (upper : Option ℕ) (L : List (ℕ × (Fin r →₀ ℕ))) : MvPowerSeries (Fin r) ℚ :=
  fun e =>
    ∑ n : Fin L.length → Fin (e.sum (fun _ a => a) + 1),
      if (∀ i, lower ≤ (n i).val) ∧
          (List.ofFn (fun i => (n i).val)).Pairwise
            (fun a b => if weak then a ≤ b else a < b) ∧
          (∀ M ∈ upper, ∀ i, (n i).val < M) ∧
          (∑ i : Fin L.length, (n i).val • (L.get i).2) = e then
        ∏ i : Fin L.length, (((n i).val : ℚ) ^ (L.get i).1)⁻¹
      else 0
end

-- forge:entry x2611_10200_Q kind=definition origin=definition
section
noncomputable def x2611_10200_Q (g : ℕ) : PowerSeries ℤ :=
  1 - (Finset.Icc 1 g).sum (fun j => PowerSeries.X ^ j)
end

-- forge:entry x2611_10667_torus_regular kind=definition origin=definition
section
noncomputable def x2611_10667_torus_regular {K : Type*} [Field K]
    (P : MvPolynomial (Fin 2) K) : Prop :=
  ∀ z : Fin 2 → AlgebraicClosure K,
    (∀ i, z i ≠ 0) →
    MvPolynomial.eval₂ (algebraMap K (AlgebraicClosure K)) z P = 0 →
    ∃ i, MvPolynomial.eval₂ (algebraMap K (AlgebraicClosure K)) z
      (MvPolynomial.pderiv i P) ≠ 0
end

-- forge:entry x2611_15379_G kind=definition origin=definition
section
noncomputable def x2611_15379_G (k a b c : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  (∏ i ∈ Finset.range (k + 1), f (b + a * (n + i * c))) /
    f ((Finset.range (k + 1)).lcm (fun i => b + a * (n + i * c)))
end

-- forge:entry x2611_11287_centralizer_dim kind=definition origin=definition
section
noncomputable def x2611_11287_centralizer_dim {F : Type*} [Field F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) : ℕ :=
  Module.finrank F (Subalgebra.centralizer F ({A} : Set (Matrix (Fin n) (Fin n) F)))
end

end Mathlib2
