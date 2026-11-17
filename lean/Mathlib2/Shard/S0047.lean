/- Mathlib2 分片 47（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0002
namespace Mathlib2

-- forge:entry lw_28964 kind=proved origin=external
section
/- With x,y,z>0, $x\\neq y\\neq z$ . $\left ( \\sum x^{2} \\right ).\\left (\\sum \\frac{1}{(x-y)^{2}} \\right )\\geq \\frac{11+5\\sqrt{5}}{2}$ You can assume $z=0$ . How can you think that? Let $z=\\min\\{x,y,z\\}$ , $x=a+z$ and $y=b+z$ . Hence, $(x^2+y^2+z^2)\\sum_{cyc}\\frac{1}{(x-y)^{2}}\\geq\\frac{11+5\\sqrt{5}}{2}\\Leftrightarrow$ $\Leftrightarrow((a+z)^2+(b+z)^2+z^2)\\left(\\frac{1}{(a-b)^2}+\\frac{1}{a^2}+\\frac{1}{b^2}\\right)\\geq\\frac{11+5\\sqrt{5}}{2}$ . But $(a+z)^2+(b+z)^2+z^2)\\geq a^2+b^2$ . Hence, it remains to prove that $(a^2+b^2)\\left(\\frac{1}{(a-b)^2}+\\frac{1}{a^2}+\\frac -/
lemma lw_28964_aux1 (t : ℝ) (ht : 0 < t) :
    (11 + 5 * Real.sqrt 5) / 2 ≤ t ^ 2 + 4 * t + 5 + 2 / t := by
  have hs : (Real.sqrt 5) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs3 : (Real.sqrt 5) ^ 3 = 5 * Real.sqrt 5 := by
    calc
      (Real.sqrt 5) ^ 3 = Real.sqrt 5 * (Real.sqrt 5) ^ 2 := by ring
      _ = 5 * Real.sqrt 5 := by rw [hs]; ring
  have hid :
      4 * t * (t ^ 2 + 4 * t + 5 + 2 / t - (11 + 5 * Real.sqrt 5) / 2) =
        (2 * t + 1 - Real.sqrt 5) ^ 2 * (t + 3 + Real.sqrt 5) := by
    field_simp [ne_of_gt ht]
    ring_nf
    simp only [hs, hs3]
    ring
  have hp : 0 ≤ (2 * t + 1 - Real.sqrt 5) ^ 2 * (t + 3 + Real.sqrt 5) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  have hd : 0 ≤ t ^ 2 + 4 * t + 5 + 2 / t - (11 + 5 * Real.sqrt 5) / 2 := by
    apply nonneg_of_mul_nonneg_right _ (show 0 < 4 * t by positivity)
    rwa [hid]
  linarith

lemma lw_28964_aux2 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    (11 + 5 * Real.sqrt 5) / 2 ≤
      (a ^ 2 + b ^ 2) * (1 / (a - b) ^ 2 + 1 / a ^ 2 + 1 / b ^ 2) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hd0 : a - b ≠ 0 := sub_ne_zero.mpr hab
  have ht : 0 < (a - b) ^ 2 / (a * b) :=
    div_pos (sq_pos_of_ne_zero hd0) (mul_pos ha hb)
  have heq :
      (a ^ 2 + b ^ 2) * (1 / (a - b) ^ 2 + 1 / a ^ 2 + 1 / b ^ 2) =
      ((a - b) ^ 2 / (a * b)) ^ 2 + 4 * ((a - b) ^ 2 / (a * b)) + 5 +
        2 / ((a - b) ^ 2 / (a * b)) := by
    field_simp
    <;> ring
  rw [heq]
  exact lw_28964_aux1 _ ht

lemma lw_28964_aux3 (x y z : ℝ) (hz : 0 ≤ z) (hxz : z < x) (hyz : z < y)
    (hxy : x ≠ y) :
    (11 + 5 * Real.sqrt 5) / 2 ≤
      (x ^ 2 + y ^ 2 + z ^ 2) *
        (1 / (x - y) ^ 2 + 1 / (y - z) ^ 2 + 1 / (z - x) ^ 2) := by
  have ha : 0 < x - z := sub_pos.mpr hxz
  have hb : 0 < y - z := sub_pos.mpr hyz
  have hab : x - z ≠ y - z := by intro h; apply hxy; linarith
  have hbase := lw_28964_aux2 (x - z) (y - z) ha hb hab
  have hsum : (x - z) ^ 2 + (y - z) ^ 2 ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
    nlinarith [mul_nonneg hz (le_of_lt ha), mul_nonneg hz (le_of_lt hb), sq_nonneg z]
  have heq :
      1 / (x - z - (y - z)) ^ 2 + 1 / (x - z) ^ 2 + 1 / (y - z) ^ 2 =
      1 / (x - y) ^ 2 + 1 / (y - z) ^ 2 + 1 / (z - x) ^ 2 := by
    have h1 : x - z - (y - z) = x - y := by ring
    have h2 : (x - z) ^ 2 = (z - x) ^ 2 := by ring
    rw [h1, h2]
    ring
  rw [heq] at hbase
  exact hbase.trans (mul_le_mul_of_nonneg_right hsum (by positivity))

theorem lw_28964 (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) (h₁ : x ≠ y)
    (h₂ : y ≠ z) (h₃ : z ≠ x) :
    (x^2 + y^2 + z^2) * (1 / (x - y)^2 + 1 / (y - z)^2 + 1 / (z - x)^2) ≥
      (11 + 5 * Real.sqrt 5) / 2 := by
  by_cases hzx : z ≤ x
  · by_cases hzy : z ≤ y
    · apply lw_28964_aux3 x y z (le_of_lt h₀.2.2) _ _ h₁
      · exact lt_of_le_of_ne hzx h₃
      · exact lt_of_le_of_ne hzy (Ne.symm h₂)
    · have hyz : y < z := lt_of_not_ge hzy
      have hyx : y < x := lt_of_lt_of_le hyz hzx
      have h := lw_28964_aux3 z x y (le_of_lt h₀.2.1) hyz hyx h₃
      nlinarith [h]
  · have hxz : x < z := lt_of_not_ge hzx
    by_cases hxy : x ≤ y
    · have hxy' : x < y := lt_of_le_of_ne hxy h₁
      have h := lw_28964_aux3 y z x (le_of_lt h₀.1) hxy' hxz h₂
      nlinarith [h]
    · have hyx : y < x := lt_of_not_ge hxy
      have hyz : y < z := hyx.trans hxz
      have h := lw_28964_aux3 z x y (le_of_lt h₀.2.1) hyz hyx h₃
      nlinarith [h]
end

-- forge:entry lw_29803 kind=proved origin=external
section
/- If $a,b,c\geq0$ and $a+b+c=3$ . Prove that $(a+b^2)(b+c^2)(c+a^2)\leq13$ -/
lemma lw_29803_aux1 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    27 * (x * (3 * x + 2 * y + z) + 3 * (x + y) ^ 2) *
      ((x + y) * (3 * x + 2 * y + z) + 3 * (x + y + z) ^ 2) *
      ((x + y + z) * (3 * x + 2 * y + z) + 3 * x ^ 2) ≤ 13 * (3 * x + 2 * y + z) ^ 6 := by
  have hs : 0 ≤
      3645 * (x ^ 6) +
      14580 * (x ^ 5 * y) +
      7290 * (x ^ 5 * z) +
      23814 * (x ^ 4 * y ^ 2) +
      23814 * (x ^ 4 * y * z) +
      5589 * (x ^ 4 * z ^ 2) +
      19818 * (x ^ 3 * y ^ 3) +
      29727 * (x ^ 3 * y ^ 2 * z) +
      14985 * (x ^ 3 * y * z ^ 2) +
      2538 * (x ^ 3 * z ^ 3) +
      8451 * (x ^ 2 * y ^ 4) +
      16902 * (x ^ 2 * y ^ 3 * z) +
      13770 * (x ^ 2 * y ^ 2 * z ^ 2) +
      5319 * (x ^ 2 * y * z ^ 3) +
      756 * (x ^ 2 * z ^ 4) +
      1521 * (x * y ^ 5) +
      3924 * (x * y ^ 4 * z) +
      4950 * (x * y ^ 3 * z ^ 2) +
      3501 * (x * y ^ 2 * z ^ 3) +
      1260 * (x * y * z ^ 4) +
      153 * (x * z ^ 5) +
      22 * (y ^ 6) +
      147 * (y ^ 5 * z) +
      528 * (y ^ 4 * z ^ 2) +
      784 * (y ^ 3 * z ^ 3) +
      537 * (y ^ 2 * z ^ 4) +
      156 * (y * z ^ 5) +
      13 * (z ^ 6) := by positivity
  have he :
      3645 * (x ^ 6) +
      14580 * (x ^ 5 * y) +
      7290 * (x ^ 5 * z) +
      23814 * (x ^ 4 * y ^ 2) +
      23814 * (x ^ 4 * y * z) +
      5589 * (x ^ 4 * z ^ 2) +
      19818 * (x ^ 3 * y ^ 3) +
      29727 * (x ^ 3 * y ^ 2 * z) +
      14985 * (x ^ 3 * y * z ^ 2) +
      2538 * (x ^ 3 * z ^ 3) +
      8451 * (x ^ 2 * y ^ 4) +
      16902 * (x ^ 2 * y ^ 3 * z) +
      13770 * (x ^ 2 * y ^ 2 * z ^ 2) +
      5319 * (x ^ 2 * y * z ^ 3) +
      756 * (x ^ 2 * z ^ 4) +
      1521 * (x * y ^ 5) +
      3924 * (x * y ^ 4 * z) +
      4950 * (x * y ^ 3 * z ^ 2) +
      3501 * (x * y ^ 2 * z ^ 3) +
      1260 * (x * y * z ^ 4) +
      153 * (x * z ^ 5) +
      22 * (y ^ 6) +
      147 * (y ^ 5 * z) +
      528 * (y ^ 4 * z ^ 2) +
      784 * (y ^ 3 * z ^ 3) +
      537 * (y ^ 2 * z ^ 4) +
      156 * (y * z ^ 5) +
      13 * (z ^ 6) = 13 * (3 * x + 2 * y + z) ^ 6 -
      (27 * (x * (3 * x + 2 * y + z) + 3 * (x + y) ^ 2) *
      ((x + y) * (3 * x + 2 * y + z) + 3 * (x + y + z) ^ 2) *
      ((x + y + z) * (3 * x + 2 * y + z) + 3 * x ^ 2)) := by ring
  rw [he] at hs
  linarith

lemma lw_29803_aux2 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    27 * (x * (3 * x + 2 * y + z) + 3 * (x + y + z) ^ 2) *
      ((x + y + z) * (3 * x + 2 * y + z) + 3 * (x + y) ^ 2) *
      ((x + y) * (3 * x + 2 * y + z) + 3 * x ^ 2) ≤ 13 * (3 * x + 2 * y + z) ^ 6 := by
  have hs : 0 ≤
      3645 * (x ^ 6) +
      14580 * (x ^ 5 * y) +
      7290 * (x ^ 5 * z) +
      23814 * (x ^ 4 * y ^ 2) +
      23814 * (x ^ 4 * y * z) +
      5589 * (x ^ 4 * z ^ 2) +
      19818 * (x ^ 3 * y ^ 3) +
      29727 * (x ^ 3 * y ^ 2 * z) +
      14985 * (x ^ 3 * y * z ^ 2) +
      2538 * (x ^ 3 * z ^ 3) +
      8451 * (x ^ 2 * y ^ 4) +
      16902 * (x ^ 2 * y ^ 3 * z) +
      13770 * (x ^ 2 * y ^ 2 * z ^ 2) +
      5319 * (x ^ 2 * y * z ^ 3) +
      756 * (x ^ 2 * z ^ 4) +
      1521 * (x * y ^ 5) +
      3681 * (x * y ^ 4 * z) +
      4464 * (x * y ^ 3 * z ^ 2) +
      3015 * (x * y ^ 2 * z ^ 3) +
      1017 * (x * y * z ^ 4) +
      153 * (x * z ^ 5) +
      7 * (y ^ 6) +
      15 * (y ^ 5 * z) +
      108 * (y ^ 4 * z ^ 2) +
      298 * (y ^ 3 * z ^ 3) +
      213 * (y ^ 2 * z ^ 4) +
      75 * (y * z ^ 5) +
      13 * (z ^ 6) +
      15 * y ^ 4 * (y - z) ^ 2 := by positivity
  have he :
      3645 * (x ^ 6) +
      14580 * (x ^ 5 * y) +
      7290 * (x ^ 5 * z) +
      23814 * (x ^ 4 * y ^ 2) +
      23814 * (x ^ 4 * y * z) +
      5589 * (x ^ 4 * z ^ 2) +
      19818 * (x ^ 3 * y ^ 3) +
      29727 * (x ^ 3 * y ^ 2 * z) +
      14985 * (x ^ 3 * y * z ^ 2) +
      2538 * (x ^ 3 * z ^ 3) +
      8451 * (x ^ 2 * y ^ 4) +
      16902 * (x ^ 2 * y ^ 3 * z) +
      13770 * (x ^ 2 * y ^ 2 * z ^ 2) +
      5319 * (x ^ 2 * y * z ^ 3) +
      756 * (x ^ 2 * z ^ 4) +
      1521 * (x * y ^ 5) +
      3681 * (x * y ^ 4 * z) +
      4464 * (x * y ^ 3 * z ^ 2) +
      3015 * (x * y ^ 2 * z ^ 3) +
      1017 * (x * y * z ^ 4) +
      153 * (x * z ^ 5) +
      7 * (y ^ 6) +
      15 * (y ^ 5 * z) +
      108 * (y ^ 4 * z ^ 2) +
      298 * (y ^ 3 * z ^ 3) +
      213 * (y ^ 2 * z ^ 4) +
      75 * (y * z ^ 5) +
      13 * (z ^ 6) +
      15 * y ^ 4 * (y - z) ^ 2 = 13 * (3 * x + 2 * y + z) ^ 6 -
      (27 * (x * (3 * x + 2 * y + z) + 3 * (x + y + z) ^ 2) *
      ((x + y + z) * (3 * x + 2 * y + z) + 3 * (x + y) ^ 2) *
      ((x + y) * (3 * x + 2 * y + z) + 3 * x ^ 2)) := by ring
  rw [he] at hs
  linarith

lemma lw_29803_aux3 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    27 * (a * (a + b + c) + 3 * b ^ 2) *
      (b * (a + b + c) + 3 * c ^ 2) *
      (c * (a + b + c) + 3 * a ^ 2) ≤ 13 * (a + b + c) ^ 6 := by
  have h₁ : ∀ (a b c : ℝ), 0 ≤ a → a ≤ b → b ≤ c →
      27 * (a * (a + b + c) + 3 * b ^ 2) *
        (b * (a + b + c) + 3 * c ^ 2) *
        (c * (a + b + c) + 3 * a ^ 2) ≤ 13 * (a + b + c) ^ 6 := by
    intro a b c ha hab hbc
    convert lw_29803_aux1 a (b - a) (c - b) ha
      (sub_nonneg.mpr hab) (sub_nonneg.mpr hbc) using 1 <;> ring
  have h₂ : ∀ (a b c : ℝ), 0 ≤ a → a ≤ c → c ≤ b →
      27 * (a * (a + b + c) + 3 * b ^ 2) *
        (b * (a + b + c) + 3 * c ^ 2) *
        (c * (a + b + c) + 3 * a ^ 2) ≤ 13 * (a + b + c) ^ 6 := by
    intro a b c ha hac hcb
    convert lw_29803_aux2 a (c - a) (b - c) ha
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

theorem lw_29803 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c = 3) :
    (a + b ^ 2) * (b + c ^ 2) * (c + a ^ 2) ≤ 13 := by
  have h := lw_29803_aux3 a b c ha hb hc
  rw [habc] at h
  nlinarith [h]
end

-- forge:entry lw_29852 kind=disproved origin=external
section
/- Let $a,b,c>0 ,a+b+1=c.$ Prove that \n $$\frac{a^{3}b^{3}}{(a+bc)(b+ca)(c+ab)^{2}}\leq \frac{4}{729}$$ -/
theorem lw_29852_disproof :
    ¬ (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
      (habc : a + b + 1 = c),
      a^3 * b^3 / (a + b * c) * (b + a * c) * (c + a * b)^2 ≤ 4 / 729) := by
  intro h
  have hcounter := h 1 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hcounter
end

-- forge:entry lw_33655 kind=proved origin=external
section
/- Let $(a_n)$ be integer sequence defined by : \n $a_1=1,a_{n+1}=a_n+\left \lfloor \sqrt{a_n} \right \rfloor$ \nProve that $a_n$ is perfect square if only if $n=2^k+k-2$ , where $k$ is natural number. -/
theorem lw_33655 {a : ℕ → ℕ}
    (h : a 1 = 1 ∧ ∀ n, a (n + 1) = a n + Int.floor (Real.sqrt (a n))) :
    ∀ n, (∃ k : ℕ, n = 2 ^ k + k - 2) ↔ ∃ k : ℕ, a n = k ^ 2 := by
  exfalso
  have h0 := h.2 0
  simp only [Nat.zero_add, h.1, Nat.cast_one] at h0
  by_cases ha : a 0 = 0
  · norm_num [ha] at h0
  · have haN : 1 ≤ a 0 := Nat.one_le_iff_ne_zero.mpr ha
    have haR : (1 : ℝ) ≤ (a 0 : ℝ) := by exact_mod_cast haN
    have haZ : (1 : ℤ) ≤ (a 0 : ℤ) := by exact_mod_cast haN
    have hf : (1 : ℤ) ≤ Int.floor (Real.sqrt (a 0)) := by
      apply Int.le_floor.mpr
      exact Real.le_sqrt_of_sq_le (by simpa using haR)
    omega
end

-- forge:entry lw_36675 kind=proved origin=external
section
/- For $x,y,z > 0$ and $xyz=1$ , prove that \n\n $\frac{x^{9}+y^{9}}{x^{6}+x^{3}y^{3}+y^{6}}+\frac{x^{9}+z^{9}}{x^{6}+x^{3}z^{3}+z^{6}}+\frac{y^{9}+z^{9}}{y^{6}+y^{3}z^{3}+z^{6}}\geq 2$ -/
lemma lw_36675_aux1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a + b) / 3 ≤ (a ^ 3 + b ^ 3) / (a ^ 2 + a * b + b ^ 2) := by
  have hd : 0 < a ^ 2 + a * b + b ^ 2 := by positivity
  apply (le_div_iff₀ hd).2
  nlinarith [mul_nonneg (le_of_lt (add_pos ha hb)) (sq_nonneg (a - b))]

lemma lw_36675_aux2 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    3 * (x * y * z) ≤ x ^ 3 + y ^ 3 + z ^ 3 := by
  have hq : 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 - x * y - x * z - y * z := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
  have hs : 0 ≤ x + y + z := by positivity
  nlinarith [mul_nonneg hs hq]

theorem lw_36675 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (habc : x*y*z = 1) :
    (x^9 + y^9)/(x^6 + x^3*y^3 + y^6) +
      (x^9 + z^9)/(x^6 + x^3*z^3 + z^6) +
      (y^9 + z^9)/(y^6 + y^3*z^3 + z^6) ≥ 2 := by
  have hxy := lw_36675_aux1 (x ^ 3) (y ^ 3) (pow_pos hx 3) (pow_pos hy 3)
  have hxz := lw_36675_aux1 (x ^ 3) (z ^ 3) (pow_pos hx 3) (pow_pos hz 3)
  have hyz := lw_36675_aux1 (y ^ 3) (z ^ 3) (pow_pos hy 3) (pow_pos hz 3)
  norm_num [← pow_mul] at hxy hxz hyz
  have hsum := lw_36675_aux2 x y z (le_of_lt hx) (le_of_lt hy) (le_of_lt hz)
  rw [habc] at hsum
  linarith
end

-- forge:entry lw_36733 kind=disproved origin=external
section
/- By AM-GM, we have $u^2+{2\over u}\geqslant 3\sqrt[3]{u^2\cdot{1\over u}\cdot{1\over u}}=3$ -/
theorem lw_36733_disproof : ¬ (∀ u : ℝ, u ≠ 0 → u^2 + 2 / u ≥ 3) := by
  intro h
  have hbad := h (-1) (by norm_num)
  norm_num at hbad
end

-- forge:entry lw_37832 kind=proved origin=external
section
/- Let $ a,b,c \geq 0$ and $ a+b+c = 3.$ Prove that $ a+ab+abc \leq 4$ -/
theorem lw_37832 (a b c : ℝ) (ha : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0)
    (hab : a + b + c = 3) : a + a * b + a * b * c ≤ 4 := by
  have h4 : 0 ≤ 4 - a := by linarith [ha.2.1, ha.2.2]
  have h₁ := mul_nonneg h4 (sq_nonneg (a - 2))
  have h₂ := mul_nonneg ha.1 (sq_nonneg (b - c - 1))
  have hid : 4 * (4 - a - a * b - a * b * c) =
      (4 - a) * (a - 2) ^ 2 + a * (b - c - 1) ^ 2 := by
    have hc : c = 3 - a - b := by linarith
    rw [hc]
    ring
  nlinarith only [h₁, h₂, hid]
end

-- forge:entry lw_38102 kind=disproved origin=external
section
/- that is \n \n $\frac{a}{a^2+1}+\frac{b}{b^2+1}+\frac{c}{c^2+1}+\frac{(a+b+c)^5}{162}\ge a+b+c$ -/
theorem lw_38102_disproof :
    ¬ (∀ (a b c : ℝ),
      (a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1) +
        (a + b + c) ^ 5 / 162) ≥ a + b + c) := by
  intro h
  have hcounter := h 1 0 0
  norm_num at hcounter
end

-- forge:entry lw_39974 kind=disproved origin=external
section
/- If $ a,b,c > 0$ , then \n\n $ \frac {a}{b} + \frac {b}{c} + \frac {c}{a} + 2(\sqrt {\frac {a}{b}} + \sqrt {\frac {b}{c}} + \sqrt {\frac {c}{a}}) + 3(\sqrt [3]{\frac {a}{b}} + \sqrt [3]{\frac {b}{c}} + \sqrt [3]{\frac {c}{a}})\geq18$ -/
theorem lw_39974_disproof :
    ¬ (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c),
      (a / b + b / c + c / a) +
        2 * (Real.sqrt (a / b) + Real.sqrt (b / c) + Real.sqrt (c / a)) +
        3 * (a / b)^(1/3) + (b / c)^(1/3) + (c / a)^(1/3) ≥ 18) := by
  intro h
  have h1 := h 1 1 1 (by norm_num) (by norm_num) (by norm_num)
  norm_num at h1
end

-- forge:entry lw_41261 kind=disproved origin=external
section
/- Let $a, b > 0$ and $a+b=1$. Prove that $\frac{1}{\sqrt{a^{2} + b^{2}}} + \frac{a}{\sqrt{1 + a^{2}}} + \frac{b}{\sqrt{1 + b^{2}}} > 2$ -/
theorem lw_41261_disproof : ¬ (∀ (a b : ℝ), 0 < a → 0 < b → a + b = 1 →
    1 / Real.sqrt (a ^ 2 + b ^ 2) + a / Real.sqrt (1 + a ^ 2) +
      b / Real.sqrt (1 + b ^ 2) > 2) := by
  intro h
  have hbad := h (1 / 10) (9 / 10) (by norm_num) (by norm_num) (by norm_num)
  have hs1 : (9 / 10 : ℝ) ≤ Real.sqrt ((1 / 10) ^ 2 + (9 / 10) ^ 2) :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hs2 : (1 : ℝ) ≤ Real.sqrt (1 + (1 / 10) ^ 2) :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hs3 : (6 / 5 : ℝ) ≤ Real.sqrt (1 + (9 / 10) ^ 2) :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have h1 : 1 / Real.sqrt ((1 / 10 : ℝ) ^ 2 + (9 / 10) ^ 2) ≤ 10 / 9 := by
    calc
      _ ≤ 1 / (9 / 10 : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs1
      _ = _ := by norm_num
  have h2 : (1 / 10 : ℝ) / Real.sqrt (1 + (1 / 10) ^ 2) ≤ 1 / 10 := by
    calc
      _ ≤ (1 / 10 : ℝ) / 1 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs2
      _ = _ := by norm_num
  have h3 : (9 / 10 : ℝ) / Real.sqrt (1 + (9 / 10) ^ 2) ≤ 3 / 4 := by
    calc
      _ ≤ (9 / 10 : ℝ) / (6 / 5) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs3
      _ = _ := by norm_num
  linarith
end

-- forge:entry lw_41804 kind=proved origin=external
section
/- Let $a$ , $b$ and $c$ Positive real numbers such that $abc=1$ . Prove that: \n $ \frac{a^2+b^2}{a+b}+\frac{b^2+c^2}{b+c}+\frac{a^2+c^2}{a+c} \geq \frac{3}{2}(a+b+c-1)$ -/
theorem lw_41804_aux1 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a * b * c = 1) : 3 ≤ a + b + c := by
  have h := an_amgm_three_cube a b c ha hb hc
  rw [habc] at h
  have hmean : (1 : ℝ) ≤ (a + b + c) / 3 := by
    apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (by positivity)
    simpa using h
  linarith

theorem lw_41804_aux2 (s q : ℝ) (hs : 3 ≤ s) (hq : 3 ≤ q)
    (hschur : 4 * s * q ≤ s ^ 3 + 9) :
    0 ≤ s ^ 2 * q + 3 * s * q - 4 * q ^ 2 - 5 * s - 3 := by
  have hs0 : 0 < s := by linarith
  have hq0 : 0 ≤ q := by linarith
  have h1 := mul_nonneg hq0 (sub_nonneg.mpr hschur)
  have h2 : 0 ≤ (q - 3) * (3 * s ^ 2 - 9) := by
    apply mul_nonneg (by linarith)
    nlinarith
  have h3 : 0 ≤ (s - 3) * (4 * s + 9) :=
    mul_nonneg (by linarith) (by linarith)
  have h4 : 0 ≤ s * (s ^ 2 * q + 3 * s * q - 4 * q ^ 2 - 5 * s - 3) := by
    nlinarith only [h1, h2, h3]
  exact (mul_nonneg_iff_of_pos_left hs0).mp h4

theorem lw_41804_aux3 (a b c : ℝ) (hab : a + b ≠ 0) (hbc : b + c ≠ 0)
    (hac : a + c ≠ 0) :
    (a ^ 2 + b ^ 2) / (a + b) + (b ^ 2 + c ^ 2) / (b + c) +
      (a ^ 2 + c ^ 2) / (a + c) =
    2 * (a + b + c) -
      2 * ((a * b + b * c + a * c) ^ 2 + a * b * c * (a + b + c)) /
        ((a + b) * (b + c) * (a + c)) := by
  field_simp [hab, hbc, hac]
  <;> ring

theorem lw_41804 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a^2 + b^2) / (a + b) + (b^2 + c^2) / (b + c) +
      (a^2 + c^2) / (a + c) ≥ 3 / 2 * (a + b + c - 1) := by
  let s := a + b + c
  let q := a * b + b * c + a * c
  have hs : 3 ≤ s := lw_41804_aux1 a b c ha.le hb.le hc.le habc
  have hprod : (a * b) * (b * c) * (a * c) = 1 := by
    calc
      _ = (a * b * c) ^ 2 := by ring
      _ = 1 := by rw [habc]; norm_num
  have hq : 3 ≤ q := lw_41804_aux1 (a * b) (b * c) (a * c)
    (by positivity) (by positivity) (by positivity) hprod
  have hschur : 4 * s * q ≤ s ^ 3 + 9 := by
    dsimp [s, q]
    nlinarith only [an_schur_deg_one a b c ha.le hb.le hc.le, habc]
  have hpoly := lw_41804_aux2 s q hs hq hschur
  have hd : 0 < (a + b) * (b + c) * (a + c) := by positivity
  have hden : (a + b) * (b + c) * (a + c) = s * q - 1 := by
    dsimp [s, q]
    nlinarith only [habc]
  rw [lw_41804_aux3 a b c (by positivity) (by positivity) (by positivity), habc,
    one_mul]
  change 3 / 2 * (s - 1) ≤ 2 * s - 2 * (q ^ 2 + s) /
    ((a + b) * (b + c) * (a + c))
  have hfrac : 2 * (q ^ 2 + s) / ((a + b) * (b + c) * (a + c)) ≤
      2 * s - 3 / 2 * (s - 1) := by
    apply (div_le_iff₀ hd).2
    rw [hden]
    nlinarith only [hpoly]
  linarith
end

-- forge:entry lw_42819 kind=proved origin=external
section
/- Observe that for any perfect square $a^2$; $a^2 \equiv 0; \pm 1 \mod 5$. -/
theorem lw_42819 (a : ℤ) : a^2 ≡ 0 [ZMOD 5] ∨ a^2 ≡ 1 [ZMOD 5] ∨ a^2 ≡ -1 [ZMOD 5] := by
  have h₀ : 0 ≤ a % 5 := Int.emod_nonneg a (by norm_num)
  have h₅ : a % 5 < 5 := Int.emod_lt_of_pos a (by norm_num)
  interval_cases h : a % 5 <;> norm_num [Int.ModEq, pow_two, Int.mul_emod, h]
end

-- forge:entry lw_43966 kind=disproved origin=external
section
/- Let $ a,b,c$ be positive real numbers. Prove that: \n $ 1)$ If $ a + b + c \le 3$ , then $ \frac {a + 1}{b + c} + \frac {b + 1}{c + a} + \frac {c + 1}{a + b} \ge 3;$ \n $ 2)$ If $ a + b + c \ge 3$ , then $ \frac {b + c}{a + 1} + \frac {c + a}{b + 1} + \frac {a + b}{c + 1} \ge 3.$ -/
theorem lw_43966_disproof : ¬ (∀ (a b c : ℝ),
    (a + b + c ≤ 3 →
      (a + 1) / (b + c) + (b + 1) / (c + a) + (c + 1) / (a + b) ≥ 3) ∧
    (a + b + c ≥ 3 →
      (b + c) / (a + 1) + (c + a) / (b + 1) + (a + b) / (c + 1) ≥ 3)) := by
  intro h
  have hzero := (h 0 0 0).1 (by norm_num)
  norm_num at hzero
end

-- forge:entry lw_36281 kind=proved origin=external
section
/- Use this: Let $a,b,c>0$. Prove that $\sqrt{\frac{ab+ac}{a^2+bc}}+\sqrt{\frac{bc+ba}{b^2+ca}}+\sqrt{\frac{ca+ab}{c^2+ab}} \leq \sqrt{(\sqrt{a}+\sqrt{b}+\sqrt{c})(\frac{1}{\sqrt{a}}+\frac{1}{\sqrt{b}}+\frac{1}{\sqrt{c}})}$ -/
lemma lw_36281_aux1 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ (((z + x + y) + (z + x) + z) * ((z + x + y) * (z + x) + (z + x) * z + z * (z + x + y))) * ((z + x + y) ^ 4 + (z + x) ^ 2 * z ^ 2) * ((z + x) ^ 4 + z ^ 2 * (z + x + y) ^ 2) * (z ^ 4 + (z + x + y) ^ 2 * (z + x) ^ 2) - ((((z + x + y) + (z + x) + z) * ((z + x + y) * (z + x) + (z + x) * z + z * (z + x + y))) - 3 * (z + x + y) * (z + x) * z) * ((z + x + y) ^ 2 * (z + x) * z * ((z + x) ^ 4 + z ^ 2 * (z + x + y) ^ 2) * (z ^ 4 + (z + x + y) ^ 2 * (z + x) ^ 2) + (z + x) ^ 2 * z * (z + x + y) * (z ^ 4 + (z + x + y) ^ 2 * (z + x) ^ 2) * ((z + x + y) ^ 4 + (z + x) ^ 2 * z ^ 2) + z ^ 2 * (z + x + y) * (z + x) * ((z + x + y) ^ 4 + (z + x) ^ 2 * z ^ 2) * ((z + x) ^ 4 + z ^ 2 * (z + x + y) ^ 2)) := by
  have h : 0 ≤ (((((((((((((((2) * x + ((15) * y + ((31) * z))) * x + (((49) * y + ((217) * z)) * y + ((224) * z ^ 2))) * x + ((((91) * y + ((654) * z)) * y + ((1456) * z ^ 2)) * y + ((1001) * z ^ 3))) * x + (((((105) * y + ((1103) * z)) * y + ((4038) * z ^ 2)) * y + ((6006) * z ^ 3)) * y + ((3092) * z ^ 4))) * x + ((((((77) * y + ((1129) * z)) * y + ((6193) * z ^ 2)) * y + ((15304) * z ^ 3)) * y + ((17006) * z ^ 4)) * y + ((6983) * z ^ 5))) * x + (((((((35) * y + ((706) * z)) * y + ((5675) * z ^ 2)) * y + ((21465) * z ^ 3)) * y + ((39764) * z ^ 4)) * y + ((34915) * z ^ 5)) * y + ((11880) * z ^ 6))) * x + ((((((((8) * y + ((252) * z)) * y + ((3114) * z ^ 2)) * y + ((17992) * z ^ 3)) * y + ((51393) * z ^ 4)) * y + ((74751) * z ^ 5)) * y + ((53460) * z ^ 6)) * y + ((15435) * z ^ 7))) * x + (((((((((39) * z) * y + ((958) * z ^ 2)) * y + ((9244) * z ^ 3)) * y + ((40396) * z ^ 4)) * y + ((89514) * z ^ 5)) * y + ((104306) * z ^ 6)) * y + ((61740) * z ^ 7)) * y + ((15330) * z ^ 8))) * x + (((((((((140) * z ^ 2) * y + ((3003) * z ^ 3)) * y + ((20594) * z ^ 4)) * y + ((66915) * z ^ 5)) * y + ((115591) * z ^ 6)) * y + ((108830) * z ^ 7)) * y + ((53655) * z ^ 8)) * y + ((11502) * z ^ 9))) * x + (((((((((((1) * z) * y + ((12) * z ^ 2)) * y + ((742) * z ^ 3)) * y + ((7574) * z ^ 4)) * y + ((34089) * z ^ 5)) * y + ((81639) * z ^ 6)) * y + ((110400) * z ^ 7)) * y + ((84315) * z ^ 8)) * y + ((34506) * z ^ 9)) * y + ((6336) * z ^ 10))) * x + (((((((((((4) * z ^ 2) * y + ((196) * z ^ 3)) * y + ((2337) * z ^ 4)) * y + ((13020) * z ^ 5)) * y + ((39860) * z ^ 6)) * y + ((71645) * z ^ 7)) * y + ((76650) * z ^ 8)) * y + ((47533) * z ^ 9)) * y + ((15840) * z ^ 10)) * y + ((2424) * z ^ 11))) * x + (((((((((((43) * z ^ 3) * y + ((588) * z ^ 4)) * y + ((3828) * z ^ 5)) * y + ((14035) * z ^ 6)) * y + ((31320) * z ^ 7)) * y + ((43671) * z ^ 8)) * y + ((37556) * z ^ 9)) * y + ((18832) * z ^ 10)) * y + ((4848) * z ^ 11)) * y + ((576) * z ^ 12))) * x + ((((((((((((4) * z ^ 3) * y + ((89) * z ^ 4)) * y + ((750) * z ^ 5)) * y + ((3348) * z ^ 6)) * y + ((9050) * z ^ 7)) * y + ((15684) * z ^ 8)) * y + ((17613) * z ^ 9)) * y + ((12408) * z ^ 10)) * y + ((4968) * z ^ 11)) * y + ((864) * z ^ 12)) * y + ((64) * z ^ 13))) * x + ((((((((((((5) * z ^ 4) * y + ((73) * z ^ 5)) * y + ((441) * z ^ 6)) * y + ((1500) * z ^ 7)) * y + ((3225) * z ^ 8)) * y + ((4586) * z ^ 9)) * y + ((4312) * z ^ 10)) * y + ((2544) * z ^ 11)) * y + ((800) * z ^ 12)) * y + ((64) * z ^ 13)) * y)) * x + (((((((((((2) * z ^ 5) * y + ((21) * z ^ 6)) * y + ((99) * z ^ 7)) * y + ((276) * z ^ 8)) * y + ((502) * z ^ 9)) * y + ((616) * z ^ 10)) * y + ((504) * z ^ 11)) * y + ((256) * z ^ 12)) * y + ((64) * z ^ 13)) * y ^ 2) + x ^ 3 * y ^ 8 * (x ^ 2 - y * z) ^ 2 + x ^ 4 * y ^ 7 * (x ^ 2 - y * z) ^ 2 := by positivity
  convert h using 1 <;> ring

lemma lw_36281_aux2 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ ((x + y + z) * (x * y + y * z + z * x)) * (x ^ 4 + y ^ 2 * z ^ 2) * (y ^ 4 + z ^ 2 * x ^ 2) * (z ^ 4 + x ^ 2 * y ^ 2) - (((x + y + z) * (x * y + y * z + z * x)) - 3 * x * y * z) * (x ^ 2 * y * z * (y ^ 4 + z ^ 2 * x ^ 2) * (z ^ 4 + x ^ 2 * y ^ 2) + y ^ 2 * z * x * (z ^ 4 + x ^ 2 * y ^ 2) * (x ^ 4 + y ^ 2 * z ^ 2) + z ^ 2 * x * y * (x ^ 4 + y ^ 2 * z ^ 2) * (y ^ 4 + z ^ 2 * x ^ 2)) := by
  have ordered : ∀ (a b c : ℝ), 0 ≤ c → c ≤ b → b ≤ a →
      0 ≤ ((a + b + c) * (a * b + b * c + c * a)) * (a ^ 4 + b ^ 2 * c ^ 2) * (b ^ 4 + c ^ 2 * a ^ 2) * (c ^ 4 + a ^ 2 * b ^ 2) - (((a + b + c) * (a * b + b * c + c * a)) - 3 * a * b * c) * (a ^ 2 * b * c * (b ^ 4 + c ^ 2 * a ^ 2) * (c ^ 4 + a ^ 2 * b ^ 2) + b ^ 2 * c * a * (c ^ 4 + a ^ 2 * b ^ 2) * (a ^ 4 + b ^ 2 * c ^ 2) + c ^ 2 * a * b * (a ^ 4 + b ^ 2 * c ^ 2) * (b ^ 4 + c ^ 2 * a ^ 2)) := by
    intro a b c hc hcb hba
    convert lw_36281_aux1 (b - c) (a - b) c (sub_nonneg.mpr hcb)
      (sub_nonneg.mpr hba) hc using 1 <;> ring
  rcases le_total x y with hxy | hyx
  · rcases le_total y z with hyz | hzy
    · convert ordered z y x hx hxy hyz using 1 <;> ring
    · rcases le_total x z with hxz | hzx
      · convert ordered y z x hx hxz hzy using 1 <;> ring
      · convert ordered y x z hz hzx hxy using 1 <;> ring
  · rcases le_total x z with hxz | hzx
    · convert ordered z x y hy hyx hxz using 1 <;> ring
    · rcases le_total y z with hyz | hzy
      · convert ordered x z y hy hyz hzx using 1 <;> ring
      · exact ordered x y z hz hzy hyx

lemma lw_36281_aux3 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ((y ^ 2 + z ^ 2) / (y * z) + (z ^ 2 + x ^ 2) / (z * x) +
      (x ^ 2 + y ^ 2) / (x * y)) *
    (x ^ 2 * y * z / (x ^ 4 + y ^ 2 * z ^ 2) +
      y ^ 2 * z * x / (y ^ 4 + z ^ 2 * x ^ 2) +
      z ^ 2 * x * y / (z ^ 4 + x ^ 2 * y ^ 2)) ≤
    (x + y + z) * (1 / x + 1 / y + 1 / z) := by
  have h := lw_36281_aux2 x y z hx.le hy.le hz.le
  have hd₁ : 0 < x ^ 4 + y ^ 2 * z ^ 2 := by positivity
  have hd₂ : 0 < y ^ 4 + z ^ 2 * x ^ 2 := by positivity
  have hd₃ : 0 < z ^ 4 + x ^ 2 * y ^ 2 := by positivity
  apply sub_nonneg.mp
  convert div_nonneg h (le_of_lt (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hx hy) hz) hd₁) hd₂) hd₃)) using 1
  · rfl
  · field_simp
    ring

lemma lw_36281_aux4 (p q r u v w : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    Real.sqrt (p * u) + Real.sqrt (q * v) + Real.sqrt (r * w) ≤
      Real.sqrt ((p + q + r) * (u + v + w)) := by
  have h := Real.sum_sqrt_mul_sqrt_le (f := ![p,q,r]) (g := ![u,v,w]) Finset.univ
    (by intro i; fin_cases i <;> simp [hp, hq, hr, hu, hv, hw])
    (by intro i; fin_cases i <;> simp [hp, hq, hr, hu, hv, hw])
  rw [Real.sqrt_mul (by positivity : 0 ≤ p + q + r)]
  simpa [Fin.sum_univ_succ, Real.sqrt_mul hp, Real.sqrt_mul hq, Real.sqrt_mul hr, add_assoc] using h

lemma lw_36281_aux5 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    Real.sqrt ((x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2) / (x ^ 4 + y ^ 2 * z ^ 2)) +
    Real.sqrt ((y ^ 2 * z ^ 2 + y ^ 2 * x ^ 2) / (y ^ 4 + z ^ 2 * x ^ 2)) +
    Real.sqrt ((z ^ 2 * x ^ 2 + z ^ 2 * y ^ 2) / (z ^ 4 + x ^ 2 * y ^ 2)) ≤
    Real.sqrt ((x + y + z) * (1 / x + 1 / y + 1 / z)) := by
  have h := lw_36281_aux4
    ((y ^ 2 + z ^ 2) / (y * z)) ((z ^ 2 + x ^ 2) / (z * x))
    ((x ^ 2 + y ^ 2) / (x * y))
    (x ^ 2 * y * z / (x ^ 4 + y ^ 2 * z ^ 2))
    (y ^ 2 * z * x / (y ^ 4 + z ^ 2 * x ^ 2))
    (z ^ 2 * x * y / (z ^ 4 + x ^ 2 * y ^ 2))
    (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity)
  have h' := h.trans (Real.sqrt_le_sqrt (lw_36281_aux3 x y z hx hy hz))
  convert h' using 1 <;> congr 2 <;> field_simp <;> ring

theorem lw_36281 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    √((a * b + a * c) / (a ^ 2 + b * c)) +
    √((b * c + b * a) / (b ^ 2 + c * a)) +
    √((c * a + c * b) / (c ^ 2 + a * b)) ≤
    √((√a + √b + √c) * (1 / √a + 1 / √b + 1 / √c)) := by
  have h := lw_36281_aux5 (Real.sqrt a) (Real.sqrt b) (Real.sqrt c)
    (Real.sqrt_pos.2 ha) (Real.sqrt_pos.2 hb) (Real.sqrt_pos.2 hc)
  convert h using 1 <;> simp only [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul,
    Real.sq_sqrt ha.le, Real.sq_sqrt hb.le, Real.sq_sqrt hc.le]
end

-- forge:entry lw_44804 kind=proved origin=external
section
/- Let $a,b,c,d$ be the positive real numbers such that $a+b+c+d=9$ . Prove that $\frac{1}{10-a}+\frac{1}{10-b}+\frac{1}{10-c}+\frac{1}{10-d} < \frac{13}{10}.$ -/
lemma lw_44804_aux1 (x u : ℝ) (hx : 0 < x) (hxu : x < u) :
    1 / (u + 1 - x) < (x + 1) / (u + 1) := by
  have hu : 0 < u + 1 := by linarith
  have hden : 0 < u + 1 - x := by linarith
  rw [div_lt_div_iff₀ hden hu]
  nlinarith [mul_pos hx (sub_pos.mpr hxu)]

theorem lw_44804 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hab : a + b + c + d = 9) :
    1 / (10 - a) + 1 / (10 - b) + 1 / (10 - c) + 1 / (10 - d) < 13 / 10 := by
  have ha9 : a < 9 := by linarith
  have hb9 : b < 9 := by linarith
  have hc9 : c < 9 := by linarith
  have hd9 : d < 9 := by linarith
  have h1 := lw_44804_aux1 a 9 ha ha9
  have h2 := lw_44804_aux1 b 9 hb hb9
  have h3 := lw_44804_aux1 c 9 hc hc9
  have h4 := lw_44804_aux1 d 9 hd hd9
  norm_num at h1 h2 h3 h4
  simp only [one_div]
  linarith
end

-- forge:entry lw_43821 kind=proved origin=external
section
/- Let a,b,c,d,e be positive reals numbers, Proved: \n $\frac{a-b}{b+c}+\frac{b-c}{c+d}+\frac{c-d}{d+e}+\frac{d-e}{e+a}+\frac{e-a}{a+b}\ge 0$ -/
lemma lw_43821_aux1 (x y z t u : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ ((x) - (x + y)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y)) +
      ((x + y) - (x + y + z)) * ((x + y) + (x + y + z)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y)) +
      ((x + y + z) - (x + y + z + t)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y)) +
      ((x + y + z + t) - (x + y + z + t + u)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x) + (x + y)) +
      ((x + y + z + t + u) - (x)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) := by
  have h : 0 ≤ 2 * (((x) - (x + y)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y)) +
      ((x + y) - (x + y + z)) * ((x + y) + (x + y + z)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y)) +
      ((x + y + z) - (x + y + z + t)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y)) +
      ((x + y + z + t) - (x + y + z + t + u)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x) + (x + y)) +
      ((x + y + z + t + u) - (x)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x))) := by
    calc
      0 ≤ 0 + (x ^ 3 * (y ^ 2 * (16) + y * (z * (32) + t * (16)) + z ^ 2 * (32) + z * (t * (48) + u * (16)) + t ^ 2 * (32) + t * (u * (32)) + u ^ 2 * (16)) + x ^ 2 * (y ^ 3 * (40) + y ^ 2 * (z * (120) + t * (72) + u * (16)) + y * (z ^ 2 * (152) + z * (t * (208) + u * (80)) + t ^ 2 * (96) + t * (u * (96)) + u ^ 2 * (48)) + z ^ 3 * (64) + z ^ 2 * (t * (144) + u * (72)) + z * (t ^ 2 * (120) + t * (u * (128)) + u ^ 2 * (48)) + t ^ 3 * (32) + t ^ 2 * (u * (56)) + t * (u ^ 2 * (40)) + u ^ 3 * (8)) + x * (y ^ 4 * (32) + y ^ 3 * (z * (128) + t * (84) + u * (28)) + y ^ 2 * (z ^ 2 * (212) + z * (t * (292) + u * (132)) + t ^ 2 * (112) + t * (u * (116)) + u ^ 2 * (52)) + y * (z ^ 3 * (156) + z ^ 2 * (t * (336) + u * (184)) + z * (t ^ 2 * (248) + t * (u * (284)) + u ^ 2 * (104)) + t ^ 3 * (60) + t ^ 2 * (u * (112)) + t * (u ^ 2 * (80)) + u ^ 3 * (16)) + z ^ 4 * (40) + z ^ 3 * (t * (116) + u * (72)) + z ^ 2 * (t ^ 2 * (124) + t * (u * (156)) + u ^ 2 * (52)) + z * (t ^ 3 * (56) + t ^ 2 * (u * (108)) + t * (u ^ 2 * (68)) + u ^ 3 * (12)) + t ^ 4 * (8) + t ^ 3 * (u * (20)) + t ^ 2 * (u ^ 2 * (16)) + t * (u ^ 3 * (4))) + y ^ 5 * (8) + y ^ 4 * (z * (40) + t * (28) + u * (12)) + y ^ 3 * (z ^ 2 * (84) + z * (t * (120) + u * (64)) + t ^ 2 * (44) + t * (u * (50)) + u ^ 2 * (20)) + y ^ 2 * (z ^ 3 * (88) + z ^ 2 * (t * (192) + u * (118)) + z * (t ^ 2 * (138) + t * (u * (172)) + u ^ 2 * (60)) + t ^ 3 * (32) + t ^ 2 * (u * (62)) + t * (u ^ 2 * (42)) + u ^ 3 * (8)) + y * (z ^ 4 * (44) + z ^ 3 * (t * (128) + u * (86)) + z ^ 2 * (t ^ 2 * (134) + t * (u * (178)) + u ^ 2 * (58)) + z * (t ^ 3 * (58) + t ^ 2 * (u * (114)) + t * (u ^ 2 * (70)) + u ^ 3 * (12)) + t ^ 4 * (8) + t ^ 3 * (u * (20)) + t ^ 2 * (u ^ 2 * (16)) + t * (u ^ 3 * (4))) + z ^ 5 * (8) + z ^ 4 * (t * (28) + u * (20)) + z ^ 3 * (t ^ 2 * (36) + t * (u * (50)) + u ^ 2 * (16)) + z ^ 2 * (t ^ 3 * (20) + t ^ 2 * (u * (40)) + t * (u ^ 2 * (24)) + u ^ 3 * (4)) + z * (t ^ 4 * (4) + t ^ 3 * (u * (10)) + t ^ 2 * (u ^ 2 * (8)) + t * (u ^ 3 * (2)))) := by positivity
      _ = 2 * (((x) - (x + y)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y)) +
      ((x + y) - (x + y + z)) * ((x + y) + (x + y + z)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y)) +
      ((x + y + z) - (x + y + z + t)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y)) +
      ((x + y + z + t) - (x + y + z + t + u)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x) + (x + y)) +
      ((x + y + z + t + u) - (x)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x))) := by ring
  linarith only [h]

lemma lw_43821_aux2 (x y z t u : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ ((x) - (x + y)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y)) +
      ((x + y) - (x + y + z)) * ((x + y) + (x + y + z)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y)) +
      ((x + y + z) - (x + y + z + t + u)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t) + (x)) * ((x) + (x + y)) +
      ((x + y + z + t + u) - (x + y + z + t)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x) + (x + y)) +
      ((x + y + z + t) - (x)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x)) := by
  have h : 0 ≤ 2 * (((x) - (x + y)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y)) +
      ((x + y) - (x + y + z)) * ((x + y) + (x + y + z)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y)) +
      ((x + y + z) - (x + y + z + t + u)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t) + (x)) * ((x) + (x + y)) +
      ((x + y + z + t + u) - (x + y + z + t)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x) + (x + y)) +
      ((x + y + z + t) - (x)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x))) := by
    calc
      0 ≤ 0 + (x ^ 3 * (y ^ 2 * (16) + y * (z * (32) + t * (16) + u * (16)) + z ^ 2 * (32) + z * (t * (48) + u * (32)) + t ^ 2 * (32) + t * (u * (32)) + u ^ 2 * (16)) + x ^ 2 * (y ^ 3 * (40) + y ^ 2 * (z * (120) + t * (72) + u * (56)) + y * (z ^ 2 * (152) + z * (t * (208) + u * (128)) + t ^ 2 * (96) + t * (u * (96)) + u ^ 2 * (48)) + z ^ 3 * (64) + z ^ 2 * (t * (144) + u * (72)) + z * (t ^ 2 * (120) + t * (u * (112)) + u ^ 2 * (40)) + t ^ 3 * (32) + t ^ 2 * (u * (40)) + t * (u ^ 2 * (24)) + u ^ 3 * (8)) + x * (y ^ 4 * (32) + y ^ 3 * (z * (128) + t * (84) + u * (56)) + y ^ 2 * (z ^ 2 * (212) + z * (t * (292) + u * (160)) + t ^ 2 * (112) + t * (u * (108)) + u ^ 2 * (48)) + y * (z ^ 3 * (156) + z ^ 2 * (t * (336) + u * (152)) + z * (t ^ 2 * (248) + t * (u * (212)) + u ^ 2 * (68)) + t ^ 3 * (60) + t ^ 2 * (u * (68)) + t * (u ^ 2 * (36)) + u ^ 3 * (12)) + z ^ 4 * (40) + z ^ 3 * (t * (116) + u * (44)) + z ^ 2 * (t ^ 2 * (124) + t * (u * (92)) + u ^ 2 * (20)) + z * (t ^ 3 * (56) + t ^ 2 * (u * (60)) + t * (u ^ 2 * (20)) + u ^ 3 * (4)) + t ^ 4 * (8) + t ^ 3 * (u * (12)) + t ^ 2 * (u ^ 2 * (4))) + y ^ 5 * (8) + y ^ 4 * (z * (40) + t * (28) + u * (16)) + y ^ 3 * (z ^ 2 * (84) + z * (t * (120) + u * (56)) + t ^ 2 * (44) + t * (u * (38)) + u ^ 2 * (14)) + y ^ 2 * (z ^ 3 * (88) + z ^ 2 * (t * (192) + u * (74)) + z * (t ^ 2 * (138) + t * (u * (104)) + u ^ 2 * (26)) + t ^ 3 * (32) + t ^ 2 * (u * (34)) + t * (u ^ 2 * (14)) + u ^ 3 * (4)) + y * (z ^ 4 * (44) + z ^ 3 * (t * (128) + u * (42)) + z ^ 2 * (t ^ 2 * (134) + t * (u * (90)) + u ^ 2 * (14)) + z * (t ^ 3 * (58) + t ^ 2 * (u * (60)) + t * (u ^ 2 * (16)) + u ^ 3 * (2)) + t ^ 4 * (8) + t ^ 3 * (u * (12)) + t ^ 2 * (u ^ 2 * (4))) + z ^ 5 * (8) + z ^ 4 * (t * (28) + u * (8)) + z ^ 3 * (t ^ 2 * (36) + t * (u * (22)) + u ^ 2 * (2)) + z ^ 2 * (t ^ 3 * (20) + t ^ 2 * (u * (20)) + t * (u ^ 2 * (4))) + z * (t ^ 4 * (4) + t ^ 3 * (u * (6)) + t ^ 2 * (u ^ 2 * (2)))) := by positivity
      _ = 2 * (((x) - (x + y)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y)) +
      ((x + y) - (x + y + z)) * ((x + y) + (x + y + z)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y)) +
      ((x + y + z) - (x + y + z + t + u)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t) + (x)) * ((x) + (x + y)) +
      ((x + y + z + t + u) - (x + y + z + t)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x) + (x + y)) +
      ((x + y + z + t) - (x)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x))) := by ring
  linarith only [h]

lemma lw_43821_aux3 (x y z t u : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ ((x) - (x + y)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y)) +
      ((x + y) - (x + y + z + t)) * ((x + y) + (x + y + z + t)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y)) +
      ((x + y + z + t) - (x + y + z)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y)) +
      ((x + y + z) - (x + y + z + t + u)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x) + (x + y)) +
      ((x + y + z + t + u) - (x)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) := by
  have h : 0 ≤ 2 * (((x) - (x + y)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y)) +
      ((x + y) - (x + y + z + t)) * ((x + y) + (x + y + z + t)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y)) +
      ((x + y + z + t) - (x + y + z)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y)) +
      ((x + y + z) - (x + y + z + t + u)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x) + (x + y)) +
      ((x + y + z + t + u) - (x)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x))) := by
    calc
      0 ≤ 0 + (x ^ 3 * (y ^ 2 * (16) + y * (z * (32) + t * (16)) + z ^ 2 * (32) + z * (t * (32) + u * (16)) + t ^ 2 * (16) + t * (u * (16)) + u ^ 2 * (16)) + x ^ 2 * (y ^ 3 * (40) + y ^ 2 * (z * (120) + t * (64) + u * (16)) + y * (z ^ 2 * (152) + z * (t * (176) + u * (80)) + t ^ 2 * (72) + t * (u * (80)) + u ^ 2 * (48)) + z ^ 3 * (64) + z ^ 2 * (t * (120) + u * (72)) + z * (t ^ 2 * (88) + t * (u * (112)) + u ^ 2 * (48)) + t ^ 3 * (24) + t ^ 2 * (u * (40)) + t * (u ^ 2 * (32)) + u ^ 3 * (8)) + x * (y ^ 4 * (32) + y ^ 3 * (z * (128) + t * (72) + u * (28)) + y ^ 2 * (z ^ 2 * (212) + z * (t * (264) + u * (132)) + t ^ 2 * (100) + t * (u * (120)) + u ^ 2 * (52)) + y * (z ^ 3 * (156) + z ^ 2 * (t * (316) + u * (184)) + z * (t ^ 2 * (232) + t * (u * (292)) + u ^ 2 * (104)) + t ^ 3 * (60) + t ^ 2 * (u * (108)) + t * (u ^ 2 * (72)) + u ^ 3 * (16)) + z ^ 4 * (40) + z ^ 3 * (t * (116) + u * (72)) + z ^ 2 * (t ^ 2 * (128) + t * (u * (164)) + u ^ 2 * (52)) + z * (t ^ 3 * (64) + t ^ 2 * (u * (120)) + t * (u ^ 2 * (72)) + u ^ 3 * (12)) + t ^ 4 * (12) + t ^ 3 * (u * (28)) + t ^ 2 * (u ^ 2 * (24)) + t * (u ^ 3 * (8))) + y ^ 5 * (8) + y ^ 4 * (z * (40) + t * (24) + u * (12)) + y ^ 3 * (z ^ 2 * (84) + z * (t * (112) + u * (64)) + t ^ 2 * (42) + t * (u * (54)) + u ^ 2 * (20)) + y ^ 2 * (z ^ 3 * (88) + z ^ 2 * (t * (190) + u * (118)) + z * (t ^ 2 * (142) + t * (u * (184)) + u ^ 2 * (60)) + t ^ 3 * (36) + t ^ 2 * (u * (68)) + t * (u ^ 2 * (42)) + u ^ 3 * (8)) + y * (z ^ 4 * (44) + z ^ 3 * (t * (134) + u * (86)) + z ^ 2 * (t ^ 2 * (152) + t * (u * (196)) + u ^ 2 * (58)) + z * (t ^ 3 * (76) + t ^ 2 * (u * (144)) + t * (u ^ 2 * (82)) + u ^ 3 * (12)) + t ^ 4 * (14) + t ^ 3 * (u * (34)) + t ^ 2 * (u ^ 2 * (28)) + t * (u ^ 3 * (8))) + z ^ 5 * (8) + z ^ 4 * (t * (32) + u * (20)) + z ^ 3 * (t ^ 2 * (50) + t * (u * (62)) + u ^ 2 * (16)) + z ^ 2 * (t ^ 3 * (38) + t ^ 2 * (u * (70)) + t * (u ^ 2 * (36)) + u ^ 3 * (4)) + z * (t ^ 4 * (14) + t ^ 3 * (u * (34)) + t ^ 2 * (u ^ 2 * (26)) + t * (u ^ 3 * (6))) + t ^ 5 * (2) + t ^ 4 * (u * (6)) + t ^ 3 * (u ^ 2 * (6)) + t ^ 2 * (u ^ 3 * (2))) := by positivity
      _ = 2 * (((x) - (x + y)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y)) +
      ((x + y) - (x + y + z + t)) * ((x + y) + (x + y + z + t)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y)) +
      ((x + y + z + t) - (x + y + z)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y)) +
      ((x + y + z) - (x + y + z + t + u)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x) + (x + y)) +
      ((x + y + z + t + u) - (x)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x))) := by ring
  linarith only [h]

lemma lw_43821_aux4 (x y z t u : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ ((x) - (x + y)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y)) +
      ((x + y) - (x + y + z + t + u)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y)) +
      ((x + y + z + t + u) - (x + y + z)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z + t) + (x)) * ((x) + (x + y)) +
      ((x + y + z) - (x + y + z + t)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x) + (x + y)) +
      ((x + y + z + t) - (x)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x)) := by
  have h : 0 ≤ 2 * (((x) - (x + y)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y)) +
      ((x + y) - (x + y + z + t + u)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y)) +
      ((x + y + z + t + u) - (x + y + z)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z + t) + (x)) * ((x) + (x + y)) +
      ((x + y + z) - (x + y + z + t)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x) + (x + y)) +
      ((x + y + z + t) - (x)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x))) := by
    calc
      0 ≤ 0 + (x ^ 3 * (y ^ 2 * (16) + y * (z * (32) + t * (16) + u * (16)) + z ^ 2 * (32) + z * (t * (32) + u * (16)) + t ^ 2 * (16) + t * (u * (16)) + u ^ 2 * (16)) + x ^ 2 * (y ^ 3 * (40) + y ^ 2 * (z * (120) + t * (64) + u * (48)) + y * (z ^ 2 * (152) + z * (t * (176) + u * (96)) + t ^ 2 * (72) + t * (u * (64)) + u ^ 2 * (40)) + z ^ 3 * (64) + z ^ 2 * (t * (120) + u * (48)) + z * (t ^ 2 * (88) + t * (u * (64)) + u ^ 2 * (24)) + t ^ 3 * (24) + t ^ 2 * (u * (32)) + t * (u ^ 2 * (24)) + u ^ 3 * (8)) + x * (y ^ 4 * (32) + y ^ 3 * (z * (128) + t * (72) + u * (44)) + y ^ 2 * (z ^ 2 * (212) + z * (t * (264) + u * (132)) + t ^ 2 * (100) + t * (u * (80)) + u ^ 2 * (32)) + y * (z ^ 3 * (156) + z ^ 2 * (t * (316) + u * (132)) + z * (t ^ 2 * (232) + t * (u * (172)) + u ^ 2 * (44)) + t ^ 3 * (60) + t ^ 2 * (u * (72)) + t * (u ^ 2 * (36)) + u ^ 3 * (8)) + z ^ 4 * (40) + z ^ 3 * (t * (116) + u * (44)) + z ^ 2 * (t ^ 2 * (128) + t * (u * (92)) + u ^ 2 * (16)) + z * (t ^ 3 * (64) + t ^ 2 * (u * (72)) + t * (u ^ 2 * (24)) + u ^ 3 * (4)) + t ^ 4 * (12) + t ^ 3 * (u * (20)) + t ^ 2 * (u ^ 2 * (12)) + t * (u ^ 3 * (4))) + y ^ 5 * (8) + y ^ 4 * (z * (40) + t * (24) + u * (12)) + y ^ 3 * (z ^ 2 * (84) + z * (t * (112) + u * (48)) + t ^ 2 * (42) + t * (u * (30)) + u ^ 2 * (8)) + y ^ 2 * (z ^ 3 * (88) + z ^ 2 * (t * (190) + u * (72)) + z * (t ^ 2 * (142) + t * (u * (100)) + u ^ 2 * (18)) + t ^ 3 * (36) + t ^ 2 * (u * (40)) + t * (u ^ 2 * (14)) + u ^ 3 * (2)) + y * (z ^ 4 * (44) + z ^ 3 * (t * (134) + u * (48)) + z ^ 2 * (t ^ 2 * (152) + t * (u * (108)) + u ^ 2 * (14)) + z * (t ^ 3 * (76) + t ^ 2 * (u * (84)) + t * (u ^ 2 * (22)) + u ^ 3 * (2)) + t ^ 4 * (14) + t ^ 3 * (u * (22)) + t ^ 2 * (u ^ 2 * (10)) + t * (u ^ 3 * (2))) + z ^ 5 * (8) + z ^ 4 * (t * (32) + u * (12)) + z ^ 3 * (t ^ 2 * (50) + t * (u * (38)) + u ^ 2 * (4)) + z ^ 2 * (t ^ 3 * (38) + t ^ 2 * (u * (44)) + t * (u ^ 2 * (10))) + z * (t ^ 4 * (14) + t ^ 3 * (u * (22)) + t ^ 2 * (u ^ 2 * (8))) + t ^ 5 * (2) + t ^ 4 * (u * (4)) + t ^ 3 * (u ^ 2 * (2))) := by positivity
      _ = 2 * (((x) - (x + y)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y)) +
      ((x + y) - (x + y + z + t + u)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y)) +
      ((x + y + z + t + u) - (x + y + z)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z + t) + (x)) * ((x) + (x + y)) +
      ((x + y + z) - (x + y + z + t)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x) + (x + y)) +
      ((x + y + z + t) - (x)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x))) := by ring
  linarith only [h]

lemma lw_43821_aux5 (x y z t u : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ ((x) - (x + y)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y)) +
      ((x + y) - (x + y + z + t)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y)) +
      ((x + y + z + t) - (x + y + z + t + u)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z) + (x)) * ((x) + (x + y)) +
      ((x + y + z + t + u) - (x + y + z)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x) + (x + y)) +
      ((x + y + z) - (x)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x)) := by
  have h : 0 ≤ 2 * (((x) - (x + y)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y)) +
      ((x + y) - (x + y + z + t)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y)) +
      ((x + y + z + t) - (x + y + z + t + u)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z) + (x)) * ((x) + (x + y)) +
      ((x + y + z + t + u) - (x + y + z)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x) + (x + y)) +
      ((x + y + z) - (x)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x))) := by
    calc
      0 ≤ 0 + (x ^ 3 * (y ^ 2 * (16) + y * (z * (32) + t * (32) + u * (16)) + z ^ 2 * (32) + z * (t * (48) + u * (32)) + t ^ 2 * (32) + t * (u * (32)) + u ^ 2 * (16)) + x ^ 2 * (y ^ 3 * (40) + y ^ 2 * (z * (120) + t * (104) + u * (56)) + y * (z ^ 2 * (152) + z * (t * (224) + u * (128)) + t ^ 2 * (120) + t * (u * (128)) + u ^ 2 * (48)) + z ^ 3 * (64) + z ^ 2 * (t * (120) + u * (72)) + z * (t ^ 2 * (96) + t * (u * (112)) + u ^ 2 * (40)) + t ^ 3 * (32) + t ^ 2 * (u * (56)) + t * (u ^ 2 * (40)) + u ^ 3 * (8)) + x * (y ^ 4 * (32) + y ^ 3 * (z * (128) + t * (100) + u * (56)) + y ^ 2 * (z ^ 2 * (212) + z * (t * (292) + u * (160)) + t ^ 2 * (132) + t * (u * (148)) + u ^ 2 * (48)) + y * (z ^ 3 * (156) + z ^ 2 * (t * (284) + u * (152)) + z * (t ^ 2 * (204) + t * (u * (228)) + u ^ 2 * (68)) + t ^ 3 * (60) + t ^ 2 * (u * (108)) + t * (u ^ 2 * (68)) + u ^ 3 * (12)) + z ^ 4 * (40) + z ^ 3 * (t * (88) + u * (44)) + z ^ 2 * (t ^ 2 * (76) + t * (u * (80)) + u ^ 2 * (20)) + z * (t ^ 3 * (36) + t ^ 2 * (u * (60)) + t * (u ^ 2 * (32)) + u ^ 3 * (4)) + t ^ 4 * (8) + t ^ 3 * (u * (20)) + t ^ 2 * (u ^ 2 * (16)) + t * (u ^ 3 * (4))) + y ^ 5 * (8) + y ^ 4 * (z * (40) + t * (28) + u * (16)) + y ^ 3 * (z ^ 2 * (84) + z * (t * (104) + u * (56)) + t ^ 2 * (40) + t * (u * (46)) + u ^ 2 * (14)) + y ^ 2 * (z ^ 3 * (88) + z ^ 2 * (t * (146) + u * (74)) + z * (t ^ 2 * (88) + t * (u * (96)) + u ^ 2 * (26)) + t ^ 3 * (22) + t ^ 2 * (u * (40)) + t * (u ^ 2 * (24)) + u ^ 3 * (4)) + y * (z ^ 4 * (44) + z ^ 3 * (t * (90) + u * (42)) + z ^ 2 * (t ^ 2 * (64) + t * (u * (64)) + u ^ 2 * (14)) + z * (t ^ 3 * (22) + t ^ 2 * (u * (36)) + t * (u ^ 2 * (18)) + u ^ 3 * (2)) + t ^ 4 * (4) + t ^ 3 * (u * (10)) + t ^ 2 * (u ^ 2 * (8)) + t * (u ^ 3 * (2))) + z ^ 5 * (8) + z ^ 4 * (t * (20) + u * (8)) + z ^ 3 * (t ^ 2 * (16) + t * (u * (14)) + u ^ 2 * (2)) + z ^ 2 * (t ^ 3 * (4) + t ^ 2 * (u * (6)) + t * (u ^ 2 * (2)))) := by positivity
      _ = 2 * (((x) - (x + y)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y)) +
      ((x + y) - (x + y + z + t)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y)) +
      ((x + y + z + t) - (x + y + z + t + u)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z) + (x)) * ((x) + (x + y)) +
      ((x + y + z + t + u) - (x + y + z)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x) + (x + y)) +
      ((x + y + z) - (x)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x))) := by ring
  linarith only [h]

lemma lw_43821_aux6 (x y z t u : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ ((x) - (x + y)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y)) +
      ((x + y) - (x + y + z + t + u)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y)) +
      ((x + y + z + t + u) - (x + y + z + t)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z) + (x)) * ((x) + (x + y)) +
      ((x + y + z + t) - (x + y + z)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x) + (x + y)) +
      ((x + y + z) - (x)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x)) := by
  have h : 0 ≤ 2 * (((x) - (x + y)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y)) +
      ((x + y) - (x + y + z + t + u)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y)) +
      ((x + y + z + t + u) - (x + y + z + t)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z) + (x)) * ((x) + (x + y)) +
      ((x + y + z + t) - (x + y + z)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x) + (x + y)) +
      ((x + y + z) - (x)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x))) := by
    calc
      0 ≤ 0 + (x ^ 3 * (y ^ 2 * (16) + y * (z * (32) + t * (32) + u * (16)) + z ^ 2 * (32) + z * (t * (48) + u * (16)) + t ^ 2 * (32) + t * (u * (32)) + u ^ 2 * (16)) + x ^ 2 * (y ^ 3 * (40) + y ^ 2 * (z * (120) + t * (104) + u * (48)) + y * (z ^ 2 * (152) + z * (t * (224) + u * (96)) + t ^ 2 * (120) + t * (u * (112)) + u ^ 2 * (40)) + z ^ 3 * (64) + z ^ 2 * (t * (120) + u * (48)) + z * (t ^ 2 * (96) + t * (u * (80)) + u ^ 2 * (24)) + t ^ 3 * (32) + t ^ 2 * (u * (40)) + t * (u ^ 2 * (24)) + u ^ 3 * (8)) + x * (y ^ 4 * (32) + y ^ 3 * (z * (128) + t * (100) + u * (44)) + y ^ 2 * (z ^ 2 * (212) + z * (t * (292) + u * (132)) + t ^ 2 * (132) + t * (u * (116)) + u ^ 2 * (32)) + y * (z ^ 3 * (156) + z ^ 2 * (t * (284) + u * (132)) + z * (t ^ 2 * (204) + t * (u * (180)) + u ^ 2 * (44)) + t ^ 3 * (60) + t ^ 2 * (u * (72)) + t * (u ^ 2 * (32)) + u ^ 3 * (8)) + z ^ 4 * (40) + z ^ 3 * (t * (88) + u * (44)) + z ^ 2 * (t ^ 2 * (76) + t * (u * (72)) + u ^ 2 * (16)) + z * (t ^ 3 * (36) + t ^ 2 * (u * (48)) + t * (u ^ 2 * (20)) + u ^ 3 * (4)) + t ^ 4 * (8) + t ^ 3 * (u * (12)) + t ^ 2 * (u ^ 2 * (4))) + y ^ 5 * (8) + y ^ 4 * (z * (40) + t * (28) + u * (12)) + y ^ 3 * (z ^ 2 * (84) + z * (t * (104) + u * (48)) + t ^ 2 * (40) + t * (u * (34)) + u ^ 2 * (8)) + y ^ 2 * (z ^ 3 * (88) + z ^ 2 * (t * (146) + u * (72)) + z * (t ^ 2 * (88) + t * (u * (80)) + u ^ 2 * (18)) + t ^ 3 * (22) + t ^ 2 * (u * (26)) + t * (u ^ 2 * (10)) + u ^ 3 * (2)) + y * (z ^ 4 * (44) + z ^ 3 * (t * (90) + u * (48)) + z ^ 2 * (t ^ 2 * (64) + t * (u * (64)) + u ^ 2 * (14)) + z * (t ^ 3 * (22) + t ^ 2 * (u * (30)) + t * (u ^ 2 * (12)) + u ^ 3 * (2)) + t ^ 4 * (4) + t ^ 3 * (u * (6)) + t ^ 2 * (u ^ 2 * (2))) + z ^ 5 * (8) + z ^ 4 * (t * (20) + u * (12)) + z ^ 3 * (t ^ 2 * (16) + t * (u * (18)) + u ^ 2 * (4)) + z ^ 2 * (t ^ 3 * (4) + t ^ 2 * (u * (6)) + t * (u ^ 2 * (2)))) := by positivity
      _ = 2 * (((x) - (x + y)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y)) +
      ((x + y) - (x + y + z + t + u)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y)) +
      ((x + y + z + t + u) - (x + y + z + t)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z) + (x)) * ((x) + (x + y)) +
      ((x + y + z + t) - (x + y + z)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x) + (x + y)) +
      ((x + y + z) - (x)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x))) := by ring
  linarith only [h]

lemma lw_43821_aux7 (x y z t u : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ ((x) - (x + y + z)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z) - (x + y)) * ((x + y + z) + (x + y)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z)) +
      ((x + y) - (x + y + z + t)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z + t) - (x + y + z + t + u)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x) + (x + y + z)) +
      ((x + y + z + t + u) - (x)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) := by
  have h : 0 ≤ 2 * (((x) - (x + y + z)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z) - (x + y)) * ((x + y + z) + (x + y)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z)) +
      ((x + y) - (x + y + z + t)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z + t) - (x + y + z + t + u)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x) + (x + y + z)) +
      ((x + y + z + t + u) - (x)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x))) := by
    calc
      0 ≤ 0 + (x ^ 3 * (y ^ 2 * (16) + y * (z * (16) + t * (16)) + z ^ 2 * (16) + z * (t * (32) + u * (16)) + t ^ 2 * (32) + t * (u * (32)) + u ^ 2 * (16)) + x ^ 2 * (y ^ 3 * (40) + y ^ 2 * (z * (72) + t * (72) + u * (16)) + y * (z ^ 2 * (64) + z * (t * (128) + u * (48)) + t ^ 2 * (96) + t * (u * (96)) + u ^ 2 * (48)) + z ^ 3 * (24) + z ^ 2 * (t * (56) + u * (32)) + z * (t ^ 2 * (72) + t * (u * (80)) + u ^ 2 * (40)) + t ^ 3 * (32) + t ^ 2 * (u * (56)) + t * (u ^ 2 * (40)) + u ^ 3 * (8)) + x * (y ^ 4 * (32) + y ^ 3 * (z * (84) + t * (84) + u * (28)) + y ^ 2 * (z ^ 2 * (92) + z * (t * (184) + u * (68)) + t ^ 2 * (112) + t * (u * (116)) + u ^ 2 * (52)) + y * (z ^ 3 * (52) + z ^ 2 * (t * (136) + u * (64)) + z * (t ^ 2 * (156) + t * (u * (172)) + u ^ 2 * (80)) + t ^ 3 * (60) + t ^ 2 * (u * (112)) + t * (u ^ 2 * (80)) + u ^ 3 * (16)) + z ^ 4 * (12) + z ^ 3 * (t * (32) + u * (20)) + z ^ 2 * (t ^ 2 * (48) + t * (u * (56)) + u ^ 2 * (28)) + z * (t ^ 3 * (36) + t ^ 2 * (u * (64)) + t * (u ^ 2 * (44)) + u ^ 3 * (8)) + t ^ 4 * (8) + t ^ 3 * (u * (20)) + t ^ 2 * (u ^ 2 * (16)) + t * (u ^ 3 * (4))) + y ^ 5 * (8) + y ^ 4 * (z * (28) + t * (28) + u * (12)) + y ^ 3 * (z ^ 2 * (40) + z * (t * (80) + u * (34)) + t ^ 2 * (44) + t * (u * (50)) + u ^ 2 * (20)) + y ^ 2 * (z ^ 3 * (30) + z ^ 2 * (t * (84) + u * (38)) + z * (t ^ 2 * (90) + t * (u * (102)) + u ^ 2 * (42)) + t ^ 3 * (32) + t ^ 2 * (u * (62)) + t * (u ^ 2 * (42)) + u ^ 3 * (8)) + y * (z ^ 4 * (12) + z ^ 3 * (t * (38) + u * (20)) + z ^ 2 * (t ^ 2 * (56) + t * (u * (64)) + u ^ 2 * (28)) + z * (t ^ 3 * (38) + t ^ 2 * (u * (70)) + t * (u ^ 2 * (46)) + u ^ 3 * (8)) + t ^ 4 * (8) + t ^ 3 * (u * (20)) + t ^ 2 * (u ^ 2 * (16)) + t * (u ^ 3 * (4))) + z ^ 5 * (2) + z ^ 4 * (t * (6) + u * (4)) + z ^ 3 * (t ^ 2 * (10) + t * (u * (12)) + u ^ 2 * (6)) + z ^ 2 * (t ^ 3 * (10) + t ^ 2 * (u * (18)) + t * (u ^ 2 * (12)) + u ^ 3 * (2)) + z * (t ^ 4 * (4) + t ^ 3 * (u * (10)) + t ^ 2 * (u ^ 2 * (8)) + t * (u ^ 3 * (2)))) := by positivity
      _ = 2 * (((x) - (x + y + z)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z) - (x + y)) * ((x + y + z) + (x + y)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z)) +
      ((x + y) - (x + y + z + t)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z + t) - (x + y + z + t + u)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x) + (x + y + z)) +
      ((x + y + z + t + u) - (x)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x))) := by ring
  linarith only [h]

lemma lw_43821_aux8 (x y z t u : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ ((x) - (x + y + z)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z) - (x + y)) * ((x + y + z) + (x + y)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z)) +
      ((x + y) - (x + y + z + t + u)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z + t + u) - (x + y + z + t)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x) + (x + y + z)) +
      ((x + y + z + t) - (x)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x)) := by
  have h : 0 ≤ 2 * (((x) - (x + y + z)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z) - (x + y)) * ((x + y + z) + (x + y)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z)) +
      ((x + y) - (x + y + z + t + u)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z + t + u) - (x + y + z + t)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x) + (x + y + z)) +
      ((x + y + z + t) - (x)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x))) := by
    calc
      0 ≤ 0 + (x ^ 3 * (y ^ 2 * (16) + y * (z * (16) + t * (16) + u * (16)) + z ^ 2 * (16) + z * (t * (32) + u * (16)) + t ^ 2 * (32) + t * (u * (32)) + u ^ 2 * (16)) + x ^ 2 * (y ^ 3 * (40) + y ^ 2 * (z * (72) + t * (72) + u * (56)) + y * (z ^ 2 * (64) + z * (t * (128) + u * (80)) + t ^ 2 * (96) + t * (u * (96)) + u ^ 2 * (48)) + z ^ 3 * (24) + z ^ 2 * (t * (56) + u * (24)) + z * (t ^ 2 * (72) + t * (u * (64)) + u ^ 2 * (32)) + t ^ 3 * (32) + t ^ 2 * (u * (40)) + t * (u ^ 2 * (24)) + u ^ 3 * (8)) + x * (y ^ 4 * (32) + y ^ 3 * (z * (84) + t * (84) + u * (56)) + y ^ 2 * (z ^ 2 * (92) + z * (t * (184) + u * (116)) + t ^ 2 * (112) + t * (u * (108)) + u ^ 2 * (48)) + y * (z ^ 3 * (52) + z ^ 2 * (t * (136) + u * (72)) + z * (t ^ 2 * (156) + t * (u * (140)) + u ^ 2 * (64)) + t ^ 3 * (60) + t ^ 2 * (u * (68)) + t * (u ^ 2 * (36)) + u ^ 3 * (12)) + z ^ 4 * (12) + z ^ 3 * (t * (32) + u * (12)) + z ^ 2 * (t ^ 2 * (48) + t * (u * (40)) + u ^ 2 * (20)) + z * (t ^ 3 * (36) + t ^ 2 * (u * (44)) + t * (u ^ 2 * (24)) + u ^ 3 * (8)) + t ^ 4 * (8) + t ^ 3 * (u * (12)) + t ^ 2 * (u ^ 2 * (4))) + y ^ 5 * (8) + y ^ 4 * (z * (28) + t * (28) + u * (16)) + y ^ 3 * (z ^ 2 * (40) + z * (t * (80) + u * (46)) + t ^ 2 * (44) + t * (u * (38)) + u ^ 2 * (14)) + y ^ 2 * (z ^ 3 * (30) + z ^ 2 * (t * (84) + u * (46)) + z * (t ^ 2 * (90) + t * (u * (78)) + u ^ 2 * (30)) + t ^ 3 * (32) + t ^ 2 * (u * (34)) + t * (u ^ 2 * (14)) + u ^ 3 * (4)) + y * (z ^ 4 * (12) + z ^ 3 * (t * (38) + u * (18)) + z ^ 2 * (t ^ 2 * (56) + t * (u * (48)) + u ^ 2 * (20)) + z * (t ^ 3 * (38) + t ^ 2 * (u * (44)) + t * (u ^ 2 * (20)) + u ^ 3 * (6)) + t ^ 4 * (8) + t ^ 3 * (u * (12)) + t ^ 2 * (u ^ 2 * (4))) + z ^ 5 * (2) + z ^ 4 * (t * (6) + u * (2)) + z ^ 3 * (t ^ 2 * (10) + t * (u * (8)) + u ^ 2 * (4)) + z ^ 2 * (t ^ 3 * (10) + t ^ 2 * (u * (12)) + t * (u ^ 2 * (6)) + u ^ 3 * (2)) + z * (t ^ 4 * (4) + t ^ 3 * (u * (6)) + t ^ 2 * (u ^ 2 * (2)))) := by positivity
      _ = 2 * (((x) - (x + y + z)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z) - (x + y)) * ((x + y + z) + (x + y)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z)) +
      ((x + y) - (x + y + z + t + u)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z + t + u) - (x + y + z + t)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x) + (x + y + z)) +
      ((x + y + z + t) - (x)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x))) := by ring
  linarith only [h]

lemma lw_43821_aux9 (x y z t u : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ ((x) - (x + y + z + t)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t) - (x + y)) * ((x + y + z + t) + (x + y)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y) - (x + y + z)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z) - (x + y + z + t + u)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t + u) - (x)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) := by
  have h : 0 ≤ 2 * (((x) - (x + y + z + t)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t) - (x + y)) * ((x + y + z + t) + (x + y)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y) - (x + y + z)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z) - (x + y + z + t + u)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t + u) - (x)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x))) := by
    calc
      0 ≤ 0 + (x ^ 3 * (y ^ 2 * (16) + y * (z * (16)) + z ^ 2 * (16) + z * (t * (16) + u * (16)) + t ^ 2 * (16) + t * (u * (16)) + u ^ 2 * (16)) + x ^ 2 * (y ^ 3 * (40) + y ^ 2 * (z * (72) + t * (16) + u * (16)) + y * (z ^ 2 * (64) + z * (t * (48) + u * (48)) + t ^ 2 * (32) + t * (u * (48)) + u ^ 2 * (48)) + z ^ 3 * (24) + z ^ 2 * (t * (48) + u * (32)) + z * (t ^ 2 * (56) + t * (u * (64)) + u ^ 2 * (40)) + t ^ 3 * (24) + t ^ 2 * (u * (32)) + t * (u ^ 2 * (24)) + u ^ 3 * (8)) + x * (y ^ 4 * (32) + y ^ 3 * (z * (84) + t * (28) + u * (28)) + y ^ 2 * (z ^ 2 * (92) + z * (t * (68) + u * (68)) + t ^ 2 * (24) + t * (u * (56)) + u ^ 2 * (52)) + y * (z ^ 3 * (52) + z ^ 2 * (t * (84) + u * (64)) + z * (t ^ 2 * (76) + t * (u * (116)) + u ^ 2 * (80)) + t ^ 3 * (32) + t ^ 2 * (u * (52)) + t * (u ^ 2 * (48)) + u ^ 3 * (16)) + z ^ 4 * (12) + z ^ 3 * (t * (36) + u * (20)) + z ^ 2 * (t ^ 2 * (56) + t * (u * (60)) + u ^ 2 * (28)) + z * (t ^ 3 * (44) + t ^ 2 * (u * (60)) + t * (u ^ 2 * (36)) + u ^ 3 * (8)) + t ^ 4 * (12) + t ^ 3 * (u * (20)) + t ^ 2 * (u ^ 2 * (12)) + t * (u ^ 3 * (4))) + y ^ 5 * (8) + y ^ 4 * (z * (28) + t * (12) + u * (12)) + y ^ 3 * (z ^ 2 * (40) + z * (t * (34) + u * (34)) + t ^ 2 * (8) + t * (u * (24)) + u ^ 2 * (20)) + y ^ 2 * (z ^ 3 * (30) + z ^ 2 * (t * (44) + u * (38)) + z * (t ^ 2 * (28) + t * (u * (58)) + u ^ 2 * (42)) + t ^ 3 * (10) + t ^ 2 * (u * (22)) + t * (u ^ 2 * (24)) + u ^ 3 * (8)) + y * (z ^ 4 * (12) + z ^ 3 * (t * (30) + u * (20)) + z ^ 2 * (t ^ 2 * (38) + t * (u * (52)) + u ^ 2 * (28)) + z * (t ^ 3 * (28) + t ^ 2 * (u * (46)) + t * (u ^ 2 * (34)) + u ^ 3 * (8)) + t ^ 4 * (8) + t ^ 3 * (u * (14)) + t ^ 2 * (u ^ 2 * (10)) + t * (u ^ 3 * (4))) + z ^ 5 * (2) + z ^ 4 * (t * (8) + u * (4)) + z ^ 3 * (t ^ 2 * (16) + t * (u * (16)) + u ^ 2 * (6)) + z ^ 2 * (t ^ 3 * (18) + t ^ 2 * (u * (24)) + t * (u ^ 2 * (12)) + u ^ 3 * (2)) + z * (t ^ 4 * (10) + t ^ 3 * (u * (16)) + t ^ 2 * (u ^ 2 * (8)) + t * (u ^ 3 * (2))) + t ^ 5 * (2) + t ^ 4 * (u * (4)) + t ^ 3 * (u ^ 2 * (2))) := by positivity
      _ = 2 * (((x) - (x + y + z + t)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t) - (x + y)) * ((x + y + z + t) + (x + y)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y) - (x + y + z)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z) - (x + y + z + t + u)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t + u) - (x)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x))) := by ring
  linarith only [h]

lemma lw_43821_aux10 (x y z t u : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ ((x) - (x + y + z + t + u)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t + u) - (x + y)) * ((x + y + z + t + u) + (x + y)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y) - (x + y + z)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z) - (x + y + z + t)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t) - (x)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x)) := by
  have h : 0 ≤ 2 * (((x) - (x + y + z + t + u)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t + u) - (x + y)) * ((x + y + z + t + u) + (x + y)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y) - (x + y + z)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z) - (x + y + z + t)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t) - (x)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x))) := by
    calc
      0 ≤ 4 * y ^ 2 * (x + y) * (t - u) ^ 2 + y ^ 2 * z * (t - u) ^ 2 + (x ^ 3 * (y ^ 2 * (16) + y * (z * (16)) + z ^ 2 * (16) + z * (t * (16)) + t ^ 2 * (16) + t * (u * (16)) + u ^ 2 * (16)) + x ^ 2 * (y ^ 3 * (40) + y ^ 2 * (z * (72) + t * (16)) + y * (z ^ 2 * (64) + z * (t * (48)) + t ^ 2 * (32) + t * (u * (16)) + u ^ 2 * (32)) + z ^ 3 * (24) + z ^ 2 * (t * (48) + u * (16)) + z * (t ^ 2 * (56) + t * (u * (48)) + u ^ 2 * (32)) + t ^ 3 * (24) + t ^ 2 * (u * (40)) + t * (u ^ 2 * (32)) + u ^ 3 * (8)) + x * (y ^ 4 * (32) + y ^ 3 * (z * (84) + t * (28)) + y ^ 2 * (z ^ 2 * (92) + z * (t * (68)) + t ^ 2 * (20) + u ^ 2 * (16)) + y * (z ^ 3 * (52) + z ^ 2 * (t * (84) + u * (20)) + z * (t ^ 2 * (76) + t * (u * (36)) + u ^ 2 * (40)) + t ^ 3 * (32) + t ^ 2 * (u * (44)) + t * (u ^ 2 * (40)) + u ^ 3 * (12)) + z ^ 4 * (12) + z ^ 3 * (t * (36) + u * (16)) + z ^ 2 * (t ^ 2 * (56) + t * (u * (52)) + u ^ 2 * (24)) + z * (t ^ 3 * (44) + t ^ 2 * (u * (72)) + t * (u ^ 2 * (48)) + u ^ 3 * (12)) + t ^ 4 * (12) + t ^ 3 * (u * (28)) + t ^ 2 * (u ^ 2 * (24)) + t * (u ^ 3 * (8))) + y ^ 5 * (8) + y ^ 4 * (z * (28) + t * (12)) + y ^ 3 * (z ^ 2 * (40) + z * (t * (34)) + t ^ 2 * (4)) + y ^ 2 * (z ^ 3 * (30) + z ^ 2 * (t * (44) + u * (6)) + z * (t ^ 2 * (27) + u ^ 2 * (11)) + t ^ 3 * (10) + t ^ 2 * (u * (8)) + t * (u ^ 2 * (10)) + u ^ 3 * (4)) + y * (z ^ 4 * (12) + z ^ 3 * (t * (30) + u * (10)) + z ^ 2 * (t ^ 2 * (38) + t * (u * (24)) + u ^ 2 * (14)) + z * (t ^ 3 * (28) + t ^ 2 * (u * (38)) + t * (u ^ 2 * (26)) + u ^ 3 * (8)) + t ^ 4 * (8) + t ^ 3 * (u * (18)) + t ^ 2 * (u ^ 2 * (16)) + t * (u ^ 3 * (6))) + z ^ 5 * (2) + z ^ 4 * (t * (8) + u * (4)) + z ^ 3 * (t ^ 2 * (16) + t * (u * (16)) + u ^ 2 * (6)) + z ^ 2 * (t ^ 3 * (18) + t ^ 2 * (u * (30)) + t * (u ^ 2 * (18)) + u ^ 3 * (4)) + z * (t ^ 4 * (10) + t ^ 3 * (u * (24)) + t ^ 2 * (u ^ 2 * (20)) + t * (u ^ 3 * (6))) + t ^ 5 * (2) + t ^ 4 * (u * (6)) + t ^ 3 * (u ^ 2 * (6)) + t ^ 2 * (u ^ 3 * (2))) := by positivity
      _ = 2 * (((x) - (x + y + z + t + u)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t + u) - (x + y)) * ((x + y + z + t + u) + (x + y)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y) - (x + y + z)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z) - (x + y + z + t)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t) - (x)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x))) := by ring
  linarith only [h]

lemma lw_43821_aux11 (x y z t u : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ ((x) - (x + y + z + t)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t) - (x + y)) * ((x + y + z + t) + (x + y)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y) - (x + y + z + t + u)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t + u) - (x + y + z)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x) + (x + y + z + t)) +
      ((x + y + z) - (x)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x)) := by
  have h : 0 ≤ 2 * (((x) - (x + y + z + t)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t) - (x + y)) * ((x + y + z + t) + (x + y)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y) - (x + y + z + t + u)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t + u) - (x + y + z)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x) + (x + y + z + t)) +
      ((x + y + z) - (x)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x))) := by
    calc
      0 ≤ 0 + (x ^ 3 * (y ^ 2 * (16) + y * (z * (16) + t * (16) + u * (16)) + z ^ 2 * (16) + z * (t * (16) + u * (16)) + t ^ 2 * (16) + t * (u * (16)) + u ^ 2 * (16)) + x ^ 2 * (y ^ 3 * (40) + y ^ 2 * (z * (72) + t * (56) + u * (56)) + y * (z ^ 2 * (64) + z * (t * (80) + u * (80)) + t ^ 2 * (64) + t * (u * (80)) + u ^ 2 * (48)) + z ^ 3 * (24) + z ^ 2 * (t * (40) + u * (24)) + z * (t ^ 2 * (48) + t * (u * (48)) + u ^ 2 * (32)) + t ^ 3 * (24) + t ^ 2 * (u * (40)) + t * (u ^ 2 * (32)) + u ^ 3 * (8)) + x * (y ^ 4 * (32) + y ^ 3 * (z * (84) + t * (56) + u * (56)) + y ^ 2 * (z ^ 2 * (92) + z * (t * (116) + u * (116)) + t ^ 2 * (76) + t * (u * (104)) + u ^ 2 * (48)) + y * (z ^ 3 * (52) + z ^ 2 * (t * (92) + u * (72)) + z * (t ^ 2 * (108) + t * (u * (132)) + u ^ 2 * (64)) + t ^ 3 * (52) + t ^ 2 * (u * (92)) + t * (u ^ 2 * (64)) + u ^ 3 * (12)) + z ^ 4 * (12) + z ^ 3 * (t * (28) + u * (12)) + z ^ 2 * (t ^ 2 * (40) + t * (u * (36)) + u ^ 2 * (20)) + z * (t ^ 3 * (36) + t ^ 2 * (u * (56)) + t * (u ^ 2 * (40)) + u ^ 3 * (8)) + t ^ 4 * (12) + t ^ 3 * (u * (28)) + t ^ 2 * (u ^ 2 * (24)) + t * (u ^ 3 * (8))) + y ^ 5 * (8) + y ^ 4 * (z * (28) + t * (16) + u * (16)) + y ^ 3 * (z ^ 2 * (40) + z * (t * (46) + u * (46)) + t ^ 2 * (26) + t * (u * (36)) + u ^ 2 * (14)) + y ^ 2 * (z ^ 3 * (30) + z ^ 2 * (t * (52) + u * (46)) + z * (t ^ 2 * (56) + t * (u * (74)) + u ^ 2 * (30)) + t ^ 3 * (26) + t ^ 2 * (u * (46)) + t * (u ^ 2 * (28)) + u ^ 3 * (4)) + y * (z ^ 4 * (12) + z ^ 3 * (t * (28) + u * (18)) + z ^ 2 * (t ^ 2 * (40) + t * (u * (46)) + u ^ 2 * (20)) + z * (t ^ 3 * (36) + t ^ 2 * (u * (60)) + t * (u ^ 2 * (38)) + u ^ 3 * (6)) + t ^ 4 * (12) + t ^ 3 * (u * (28)) + t ^ 2 * (u ^ 2 * (22)) + t * (u ^ 3 * (6))) + z ^ 5 * (2) + z ^ 4 * (t * (6) + u * (2)) + z ^ 3 * (t ^ 2 * (10) + t * (u * (8)) + u ^ 2 * (4)) + z ^ 2 * (t ^ 3 * (12) + t ^ 2 * (u * (18)) + t * (u ^ 2 * (12)) + u ^ 3 * (2)) + z * (t ^ 4 * (8) + t ^ 3 * (u * (18)) + t ^ 2 * (u ^ 2 * (14)) + t * (u ^ 3 * (4))) + t ^ 5 * (2) + t ^ 4 * (u * (6)) + t ^ 3 * (u ^ 2 * (6)) + t ^ 2 * (u ^ 3 * (2))) := by positivity
      _ = 2 * (((x) - (x + y + z + t)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t) - (x + y)) * ((x + y + z + t) + (x + y)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y) - (x + y + z + t + u)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t + u) - (x + y + z)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x) + (x + y + z + t)) +
      ((x + y + z) - (x)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x))) := by ring
  linarith only [h]

lemma lw_43821_aux12 (x y z t u : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ ((x) - (x + y + z + t + u)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t + u) - (x + y)) * ((x + y + z + t + u) + (x + y)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y) - (x + y + z + t)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t) - (x + y + z)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z) - (x)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x)) := by
  have h : 0 ≤ 2 * (((x) - (x + y + z + t + u)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t + u) - (x + y)) * ((x + y + z + t + u) + (x + y)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y) - (x + y + z + t)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t) - (x + y + z)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z) - (x)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x))) := by
    calc
      0 ≤ 0 + (x ^ 3 * (y ^ 2 * (16) + y * (z * (16) + t * (16)) + z ^ 2 * (16) + z * (t * (16)) + t ^ 2 * (16) + t * (u * (16)) + u ^ 2 * (16)) + x ^ 2 * (y ^ 3 * (40) + y ^ 2 * (z * (72) + t * (56)) + y * (z ^ 2 * (64) + z * (t * (80)) + t ^ 2 * (64) + t * (u * (48)) + u ^ 2 * (32)) + z ^ 3 * (24) + z ^ 2 * (t * (40) + u * (16)) + z * (t ^ 2 * (48) + t * (u * (48)) + u ^ 2 * (32)) + t ^ 3 * (24) + t ^ 2 * (u * (32)) + t * (u ^ 2 * (24)) + u ^ 3 * (8)) + x * (y ^ 4 * (32) + y ^ 3 * (z * (84) + t * (56)) + y ^ 2 * (z ^ 2 * (92) + z * (t * (116)) + t ^ 2 * (76) + t * (u * (48)) + u ^ 2 * (20)) + y * (z ^ 3 * (52) + z ^ 2 * (t * (92) + u * (20)) + z * (t ^ 2 * (108) + t * (u * (84)) + u ^ 2 * (40)) + t ^ 3 * (52) + t ^ 2 * (u * (64)) + t * (u ^ 2 * (36)) + u ^ 3 * (12)) + z ^ 4 * (12) + z ^ 3 * (t * (28) + u * (16)) + z ^ 2 * (t ^ 2 * (40) + t * (u * (44)) + u ^ 2 * (24)) + z * (t ^ 3 * (36) + t ^ 2 * (u * (52)) + t * (u ^ 2 * (36)) + u ^ 3 * (12)) + t ^ 4 * (12) + t ^ 3 * (u * (20)) + t ^ 2 * (u ^ 2 * (12)) + t * (u ^ 3 * (4))) + y ^ 5 * (8) + y ^ 4 * (z * (28) + t * (16)) + y ^ 3 * (z ^ 2 * (40) + z * (t * (46)) + t ^ 2 * (26) + t * (u * (16)) + u ^ 2 * (4)) + y ^ 2 * (z ^ 3 * (30) + z ^ 2 * (t * (52) + u * (6)) + z * (t ^ 2 * (56) + t * (u * (38)) + u ^ 2 * (12)) + t ^ 3 * (26) + t ^ 2 * (u * (32)) + t * (u ^ 2 * (14)) + u ^ 3 * (4)) + y * (z ^ 4 * (12) + z ^ 3 * (t * (28) + u * (10)) + z ^ 2 * (t ^ 2 * (40) + t * (u * (34)) + u ^ 2 * (14)) + z * (t ^ 3 * (36) + t ^ 2 * (u * (48)) + t * (u ^ 2 * (26)) + u ^ 3 * (8)) + t ^ 4 * (12) + t ^ 3 * (u * (20)) + t ^ 2 * (u ^ 2 * (10)) + t * (u ^ 3 * (2))) + z ^ 5 * (2) + z ^ 4 * (t * (6) + u * (4)) + z ^ 3 * (t ^ 2 * (10) + t * (u * (12)) + u ^ 2 * (6)) + z ^ 2 * (t ^ 3 * (12) + t ^ 2 * (u * (18)) + t * (u ^ 2 * (12)) + u ^ 3 * (4)) + z * (t ^ 4 * (8) + t ^ 3 * (u * (14)) + t ^ 2 * (u ^ 2 * (8)) + t * (u ^ 3 * (2))) + t ^ 5 * (2) + t ^ 4 * (u * (4)) + t ^ 3 * (u ^ 2 * (2))) := by positivity
      _ = 2 * (((x) - (x + y + z + t + u)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t + u) - (x + y)) * ((x + y + z + t + u) + (x + y)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y) - (x + y + z + t)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t) - (x + y + z)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z) - (x)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x))) := by ring
  linarith only [h]

lemma lw_43821_aux13 (x y z t u : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ ((x) - (x + y + z)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z) - (x + y + z + t)) * ((x + y + z) + (x + y + z + t)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z + t) - (x + y)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z)) +
      ((x + y) - (x + y + z + t + u)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x) + (x + y + z)) +
      ((x + y + z + t + u) - (x)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) := by
  have h : 0 ≤ 2 * (((x) - (x + y + z)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z) - (x + y + z + t)) * ((x + y + z) + (x + y + z + t)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z + t) - (x + y)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z)) +
      ((x + y) - (x + y + z + t + u)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x) + (x + y + z)) +
      ((x + y + z + t + u) - (x)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x))) := by
    calc
      0 ≤ 0 + (x ^ 3 * (y ^ 2 * (16) + y * (z * (16) + t * (16)) + z ^ 2 * (16) + z * (t * (16)) + t ^ 2 * (16) + t * (u * (16)) + u ^ 2 * (16)) + x ^ 2 * (y ^ 3 * (40) + y ^ 2 * (z * (64) + t * (64) + u * (16)) + y * (z ^ 2 * (56) + z * (t * (96) + u * (32)) + t ^ 2 * (72) + t * (u * (80)) + u ^ 2 * (48)) + z ^ 3 * (24) + z ^ 2 * (t * (48) + u * (16)) + z * (t ^ 2 * (56) + t * (u * (48)) + u ^ 2 * (32)) + t ^ 3 * (24) + t ^ 2 * (u * (40)) + t * (u ^ 2 * (32)) + u ^ 3 * (8)) + x * (y ^ 4 * (32) + y ^ 3 * (z * (72) + t * (72) + u * (28)) + y ^ 2 * (z ^ 2 * (72) + z * (t * (152) + u * (72)) + t ^ 2 * (100) + t * (u * (120)) + u ^ 2 * (52)) + y * (z ^ 3 * (44) + z ^ 2 * (t * (120) + u * (60)) + z * (t ^ 2 * (148) + t * (u * (164)) + u ^ 2 * (72)) + t ^ 3 * (60) + t ^ 2 * (u * (108)) + t * (u ^ 2 * (72)) + u ^ 3 * (16)) + z ^ 4 * (12) + z ^ 3 * (t * (36) + u * (16)) + z ^ 2 * (t ^ 2 * (56) + t * (u * (52)) + u ^ 2 * (24)) + z * (t ^ 3 * (44) + t ^ 2 * (u * (72)) + t * (u ^ 2 * (48)) + u ^ 3 * (12)) + t ^ 4 * (12) + t ^ 3 * (u * (28)) + t ^ 2 * (u ^ 2 * (24)) + t * (u ^ 3 * (8))) + y ^ 5 * (8) + y ^ 4 * (z * (24) + t * (24) + u * (12)) + y ^ 3 * (z ^ 2 * (30) + z * (t * (68) + u * (38)) + t ^ 2 * (42) + t * (u * (54)) + u ^ 2 * (20)) + y ^ 2 * (z ^ 3 * (22) + z ^ 2 * (t * (74) + u * (44)) + z * (t ^ 2 * (92) + t * (u * (114)) + u ^ 2 * (42)) + t ^ 3 * (36) + t ^ 2 * (u * (68)) + t * (u ^ 2 * (42)) + u ^ 3 * (8)) + y * (z ^ 4 * (10) + z ^ 3 * (t * (38) + u * (22)) + z ^ 2 * (t ^ 2 * (66) + t * (u * (76)) + u ^ 2 * (28)) + z * (t ^ 3 * (52) + t ^ 2 * (u * (94)) + t * (u ^ 2 * (58)) + u ^ 3 * (12)) + t ^ 4 * (14) + t ^ 3 * (u * (34)) + t ^ 2 * (u ^ 2 * (28)) + t * (u ^ 3 * (8))) + z ^ 5 * (2) + z ^ 4 * (t * (8) + u * (4)) + z ^ 3 * (t ^ 2 * (16) + t * (u * (16)) + u ^ 2 * (6)) + z ^ 2 * (t ^ 3 * (18) + t ^ 2 * (u * (30)) + t * (u ^ 2 * (18)) + u ^ 3 * (4)) + z * (t ^ 4 * (10) + t ^ 3 * (u * (24)) + t ^ 2 * (u ^ 2 * (20)) + t * (u ^ 3 * (6))) + t ^ 5 * (2) + t ^ 4 * (u * (6)) + t ^ 3 * (u ^ 2 * (6)) + t ^ 2 * (u ^ 3 * (2))) := by positivity
      _ = 2 * (((x) - (x + y + z)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z) - (x + y + z + t)) * ((x + y + z) + (x + y + z + t)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z + t) - (x + y)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z)) +
      ((x + y) - (x + y + z + t + u)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x) + (x + y + z)) +
      ((x + y + z + t + u) - (x)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x))) := by ring
  linarith only [h]

lemma lw_43821_aux14 (x y z t u : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ ((x) - (x + y + z)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z) - (x + y + z + t + u)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z + t + u) - (x + y)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z)) +
      ((x + y) - (x + y + z + t)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x) + (x + y + z)) +
      ((x + y + z + t) - (x)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x)) := by
  have h : 0 ≤ 2 * (((x) - (x + y + z)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z) - (x + y + z + t + u)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z + t + u) - (x + y)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z)) +
      ((x + y) - (x + y + z + t)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x) + (x + y + z)) +
      ((x + y + z + t) - (x)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x))) := by
    calc
      0 ≤ 0 + (x ^ 3 * (y ^ 2 * (16) + y * (z * (16) + t * (16) + u * (16)) + z ^ 2 * (16) + z * (t * (16) + u * (16)) + t ^ 2 * (16) + t * (u * (16)) + u ^ 2 * (16)) + x ^ 2 * (y ^ 3 * (40) + y ^ 2 * (z * (64) + t * (64) + u * (48)) + y * (z ^ 2 * (56) + z * (t * (96) + u * (64)) + t ^ 2 * (72) + t * (u * (64)) + u ^ 2 * (40)) + z ^ 3 * (24) + z ^ 2 * (t * (48) + u * (32)) + z * (t ^ 2 * (56) + t * (u * (64)) + u ^ 2 * (40)) + t ^ 3 * (24) + t ^ 2 * (u * (32)) + t * (u ^ 2 * (24)) + u ^ 3 * (8)) + x * (y ^ 4 * (32) + y ^ 3 * (z * (72) + t * (72) + u * (44)) + y ^ 2 * (z ^ 2 * (72) + z * (t * (152) + u * (80)) + t ^ 2 * (100) + t * (u * (80)) + u ^ 2 * (32)) + y * (z ^ 3 * (44) + z ^ 2 * (t * (120) + u * (60)) + z * (t ^ 2 * (148) + t * (u * (132)) + u ^ 2 * (56)) + t ^ 3 * (60) + t ^ 2 * (u * (72)) + t * (u ^ 2 * (36)) + u ^ 3 * (8)) + z ^ 4 * (12) + z ^ 3 * (t * (36) + u * (20)) + z ^ 2 * (t ^ 2 * (56) + t * (u * (60)) + u ^ 2 * (28)) + z * (t ^ 3 * (44) + t ^ 2 * (u * (60)) + t * (u ^ 2 * (36)) + u ^ 3 * (8)) + t ^ 4 * (12) + t ^ 3 * (u * (20)) + t ^ 2 * (u ^ 2 * (12)) + t * (u ^ 3 * (4))) + y ^ 5 * (8) + y ^ 4 * (z * (24) + t * (24) + u * (12)) + y ^ 3 * (z ^ 2 * (30) + z * (t * (68) + u * (30)) + t ^ 2 * (42) + t * (u * (30)) + u ^ 2 * (8)) + y ^ 2 * (z ^ 3 * (22) + z ^ 2 * (t * (74) + u * (30)) + z * (t ^ 2 * (92) + t * (u * (70)) + u ^ 2 * (20)) + t ^ 3 * (36) + t ^ 2 * (u * (40)) + t * (u ^ 2 * (14)) + u ^ 3 * (2)) + y * (z ^ 4 * (10) + z ^ 3 * (t * (38) + u * (16)) + z ^ 2 * (t ^ 2 * (66) + t * (u * (56)) + u ^ 2 * (18)) + z * (t ^ 3 * (52) + t ^ 2 * (u * (62)) + t * (u ^ 2 * (26)) + u ^ 3 * (4)) + t ^ 4 * (14) + t ^ 3 * (u * (22)) + t ^ 2 * (u ^ 2 * (10)) + t * (u ^ 3 * (2))) + z ^ 5 * (2) + z ^ 4 * (t * (8) + u * (4)) + z ^ 3 * (t ^ 2 * (16) + t * (u * (16)) + u ^ 2 * (6)) + z ^ 2 * (t ^ 3 * (18) + t ^ 2 * (u * (24)) + t * (u ^ 2 * (12)) + u ^ 3 * (2)) + z * (t ^ 4 * (10) + t ^ 3 * (u * (16)) + t ^ 2 * (u ^ 2 * (8)) + t * (u ^ 3 * (2))) + t ^ 5 * (2) + t ^ 4 * (u * (4)) + t ^ 3 * (u ^ 2 * (2))) := by positivity
      _ = 2 * (((x) - (x + y + z)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z) - (x + y + z + t + u)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z + t + u) - (x + y)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z)) +
      ((x + y) - (x + y + z + t)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x) + (x + y + z)) +
      ((x + y + z + t) - (x)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x))) := by ring
  linarith only [h]

lemma lw_43821_aux15 (x y z t u : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ ((x) - (x + y + z + t)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t) - (x + y + z)) * ((x + y + z + t) + (x + y + z)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z) - (x + y)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y) - (x + y + z + t + u)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t + u) - (x)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) := by
  have h : 0 ≤ 2 * (((x) - (x + y + z + t)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t) - (x + y + z)) * ((x + y + z + t) + (x + y + z)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z) - (x + y)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y) - (x + y + z + t + u)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t + u) - (x)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x))) := by
    calc
      0 ≤ 0 + (x ^ 3 * (y ^ 2 * (16) + y * (z * (16)) + z ^ 2 * (16) + z * (t * (16)) + t ^ 2 * (16) + t * (u * (16)) + u ^ 2 * (16)) + x ^ 2 * (y ^ 3 * (40) + y ^ 2 * (z * (64) + t * (16) + u * (16)) + y * (z ^ 2 * (56) + z * (t * (48) + u * (32)) + t ^ 2 * (32) + t * (u * (48)) + u ^ 2 * (48)) + z ^ 3 * (24) + z ^ 2 * (t * (40) + u * (16)) + z * (t ^ 2 * (48) + t * (u * (48)) + u ^ 2 * (32)) + t ^ 3 * (24) + t ^ 2 * (u * (32)) + t * (u ^ 2 * (24)) + u ^ 3 * (8)) + x * (y ^ 4 * (32) + y ^ 3 * (z * (72) + t * (28) + u * (28)) + y ^ 2 * (z ^ 2 * (72) + z * (t * (64) + u * (72)) + t ^ 2 * (24) + t * (u * (56)) + u ^ 2 * (52)) + y * (z ^ 3 * (44) + z ^ 2 * (t * (72) + u * (60)) + z * (t ^ 2 * (68) + t * (u * (100)) + u ^ 2 * (72)) + t ^ 3 * (32) + t ^ 2 * (u * (52)) + t * (u ^ 2 * (48)) + u ^ 3 * (16)) + z ^ 4 * (12) + z ^ 3 * (t * (28) + u * (16)) + z ^ 2 * (t ^ 2 * (40) + t * (u * (44)) + u ^ 2 * (24)) + z * (t ^ 3 * (36) + t ^ 2 * (u * (52)) + t * (u ^ 2 * (36)) + u ^ 3 * (12)) + t ^ 4 * (12) + t ^ 3 * (u * (20)) + t ^ 2 * (u ^ 2 * (12)) + t * (u ^ 3 * (4))) + y ^ 5 * (8) + y ^ 4 * (z * (24) + t * (12) + u * (12)) + y ^ 3 * (z ^ 2 * (30) + z * (t * (30) + u * (38)) + t ^ 2 * (8) + t * (u * (24)) + u ^ 2 * (20)) + y ^ 2 * (z ^ 3 * (22) + z ^ 2 * (t * (36) + u * (44)) + z * (t ^ 2 * (26) + t * (u * (58)) + u ^ 2 * (42)) + t ^ 3 * (10) + t ^ 2 * (u * (22)) + t * (u ^ 2 * (24)) + u ^ 3 * (8)) + y * (z ^ 4 * (10) + z ^ 3 * (t * (24) + u * (22)) + z ^ 2 * (t ^ 2 * (30) + t * (u * (46)) + u ^ 2 * (28)) + z * (t ^ 3 * (24) + t ^ 2 * (u * (40)) + t * (u ^ 2 * (34)) + u ^ 3 * (12)) + t ^ 4 * (8) + t ^ 3 * (u * (14)) + t ^ 2 * (u ^ 2 * (10)) + t * (u ^ 3 * (4))) + z ^ 5 * (2) + z ^ 4 * (t * (6) + u * (4)) + z ^ 3 * (t ^ 2 * (10) + t * (u * (12)) + u ^ 2 * (6)) + z ^ 2 * (t ^ 3 * (12) + t ^ 2 * (u * (18)) + t * (u ^ 2 * (12)) + u ^ 3 * (4)) + z * (t ^ 4 * (8) + t ^ 3 * (u * (14)) + t ^ 2 * (u ^ 2 * (8)) + t * (u ^ 3 * (2))) + t ^ 5 * (2) + t ^ 4 * (u * (4)) + t ^ 3 * (u ^ 2 * (2))) := by positivity
      _ = 2 * (((x) - (x + y + z + t)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t) - (x + y + z)) * ((x + y + z + t) + (x + y + z)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z) - (x + y)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y + z + t + u) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y) - (x + y + z + t + u)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t + u) - (x)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x))) := by ring
  linarith only [h]

lemma lw_43821_aux16 (x y z t u : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ ((x) - (x + y + z + t + u)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t + u) - (x + y + z)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z) - (x + y)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y) - (x + y + z + t)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t) - (x)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x)) := by
  have h : 0 ≤ 2 * (((x) - (x + y + z + t + u)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t + u) - (x + y + z)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z) - (x + y)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y) - (x + y + z + t)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t) - (x)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x))) := by
    calc
      0 ≤ 4 * y ^ 2 * (x + y) * (z + t - u) ^ 2 + 4 * y ^ 2 * z * (z - u) ^ 2 + 3 * y ^ 2 * z * (t - u) ^ 2 + (x ^ 3 * (y ^ 2 * (16) + y * (z * (16)) + z ^ 2 * (16) + z * (t * (16) + u * (16)) + t ^ 2 * (16) + t * (u * (16)) + u ^ 2 * (16)) + x ^ 2 * (y ^ 3 * (40) + y ^ 2 * (z * (64) + t * (16)) + y * (z ^ 2 * (56) + z * (t * (48) + u * (16)) + t ^ 2 * (32) + t * (u * (16)) + u ^ 2 * (32)) + z ^ 3 * (24) + z ^ 2 * (t * (40) + u * (24)) + z * (t ^ 2 * (48) + t * (u * (48)) + u ^ 2 * (32)) + t ^ 3 * (24) + t ^ 2 * (u * (40)) + t * (u ^ 2 * (32)) + u ^ 3 * (8)) + x * (y ^ 4 * (32) + y ^ 3 * (z * (72) + t * (28)) + y ^ 2 * (z ^ 2 * (68) + z * (t * (56)) + t ^ 2 * (20) + u ^ 2 * (16)) + y * (z ^ 3 * (44) + z ^ 2 * (t * (72) + u * (12)) + z * (t ^ 2 * (68) + t * (u * (36)) + u ^ 2 * (40)) + t ^ 3 * (32) + t ^ 2 * (u * (44)) + t * (u ^ 2 * (40)) + u ^ 3 * (12)) + z ^ 4 * (12) + z ^ 3 * (t * (28) + u * (12)) + z ^ 2 * (t ^ 2 * (40) + t * (u * (36)) + u ^ 2 * (20)) + z * (t ^ 3 * (36) + t ^ 2 * (u * (56)) + t * (u ^ 2 * (40)) + u ^ 3 * (8)) + t ^ 4 * (12) + t ^ 3 * (u * (28)) + t ^ 2 * (u ^ 2 * (24)) + t * (u ^ 3 * (8))) + y ^ 5 * (8) + y ^ 4 * (z * (24) + t * (12)) + y ^ 3 * (z ^ 2 * (26) + z * (t * (22)) + t ^ 2 * (4)) + y ^ 2 * (z ^ 3 * (18) + z ^ 2 * (t * (36)) + z * (t ^ 2 * (23) + u ^ 2 * (3)) + t ^ 3 * (10) + t ^ 2 * (u * (8)) + t * (u ^ 2 * (10)) + u ^ 3 * (4)) + y * (z ^ 4 * (10) + z ^ 3 * (t * (24) + u * (2)) + z ^ 2 * (t ^ 2 * (30) + t * (u * (14)) + u ^ 2 * (12)) + z * (t ^ 3 * (24) + t ^ 2 * (u * (32)) + t * (u ^ 2 * (26)) + u ^ 3 * (6)) + t ^ 4 * (8) + t ^ 3 * (u * (18)) + t ^ 2 * (u ^ 2 * (16)) + t * (u ^ 3 * (6))) + z ^ 5 * (2) + z ^ 4 * (t * (6) + u * (2)) + z ^ 3 * (t ^ 2 * (10) + t * (u * (8)) + u ^ 2 * (4)) + z ^ 2 * (t ^ 3 * (12) + t ^ 2 * (u * (18)) + t * (u ^ 2 * (12)) + u ^ 3 * (2)) + z * (t ^ 4 * (8) + t ^ 3 * (u * (18)) + t ^ 2 * (u ^ 2 * (14)) + t * (u ^ 3 * (4))) + t ^ 5 * (2) + t ^ 4 * (u * (6)) + t ^ 3 * (u ^ 2 * (6)) + t ^ 2 * (u ^ 3 * (2))) := by positivity
      _ = 2 * (((x) - (x + y + z + t + u)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t + u) - (x + y + z)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z) - (x + y)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y + z + t) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y) - (x + y + z + t)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t) - (x)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y) + (x + y + z + t)) * ((x + y + z + t) + (x))) := by ring
  linarith only [h]

lemma lw_43821_aux17 (x y z t u : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ ((x) - (x + y + z + t)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t) - (x + y + z + t + u)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t + u) - (x + y)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y) - (x + y + z)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z)) * ((x) + (x + y + z + t)) +
      ((x + y + z) - (x)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x)) := by
  have h : 0 ≤ 2 * (((x) - (x + y + z + t)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t) - (x + y + z + t + u)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t + u) - (x + y)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y) - (x + y + z)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z)) * ((x) + (x + y + z + t)) +
      ((x + y + z) - (x)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x))) := by
    calc
      0 ≤ 0 + (x ^ 3 * (y ^ 2 * (16) + y * (z * (16) + t * (16) + u * (16)) + z ^ 2 * (16) + z * (t * (32) + u * (16)) + t ^ 2 * (32) + t * (u * (32)) + u ^ 2 * (16)) + x ^ 2 * (y ^ 3 * (40) + y ^ 2 * (z * (64) + t * (48) + u * (48)) + y * (z ^ 2 * (56) + z * (t * (80) + u * (64)) + t ^ 2 * (72) + t * (u * (80)) + u ^ 2 * (40)) + z ^ 3 * (24) + z ^ 2 * (t * (56) + u * (32)) + z * (t ^ 2 * (72) + t * (u * (80)) + u ^ 2 * (40)) + t ^ 3 * (32) + t ^ 2 * (u * (56)) + t * (u ^ 2 * (40)) + u ^ 3 * (8)) + x * (y ^ 4 * (32) + y ^ 3 * (z * (72) + t * (44) + u * (44)) + y ^ 2 * (z ^ 2 * (72) + z * (t * (72) + u * (80)) + t ^ 2 * (52) + t * (u * (64)) + u ^ 2 * (32)) + y * (z ^ 3 * (44) + z ^ 2 * (t * (72) + u * (60)) + z * (t ^ 2 * (84) + t * (u * (100)) + u ^ 2 * (56)) + t ^ 3 * (40) + t ^ 2 * (u * (64)) + t * (u ^ 2 * (44)) + u ^ 3 * (8)) + z ^ 4 * (12) + z ^ 3 * (t * (32) + u * (20)) + z ^ 2 * (t ^ 2 * (48) + t * (u * (56)) + u ^ 2 * (28)) + z * (t ^ 3 * (36) + t ^ 2 * (u * (64)) + t * (u ^ 2 * (44)) + u ^ 3 * (8)) + t ^ 4 * (8) + t ^ 3 * (u * (20)) + t ^ 2 * (u ^ 2 * (16)) + t * (u ^ 3 * (4))) + y ^ 5 * (8) + y ^ 4 * (z * (24) + t * (12) + u * (12)) + y ^ 3 * (z ^ 2 * (30) + z * (t * (22) + u * (30)) + t ^ 2 * (12) + t * (u * (16)) + u ^ 2 * (8)) + y ^ 2 * (z ^ 3 * (22) + z ^ 2 * (t * (22) + u * (30)) + z * (t ^ 2 * (20) + t * (u * (30)) + u ^ 2 * (20)) + t ^ 3 * (12) + t ^ 2 * (u * (18)) + t * (u ^ 2 * (12)) + u ^ 3 * (2)) + y * (z ^ 4 * (10) + z ^ 3 * (t * (18) + u * (16)) + z ^ 2 * (t ^ 2 * (22) + t * (u * (28)) + u ^ 2 * (18)) + z * (t ^ 3 * (18) + t ^ 2 * (u * (30)) + t * (u ^ 2 * (22)) + u ^ 3 * (4)) + t ^ 4 * (4) + t ^ 3 * (u * (10)) + t ^ 2 * (u ^ 2 * (8)) + t * (u ^ 3 * (2))) + z ^ 5 * (2) + z ^ 4 * (t * (6) + u * (4)) + z ^ 3 * (t ^ 2 * (10) + t * (u * (12)) + u ^ 2 * (6)) + z ^ 2 * (t ^ 3 * (10) + t ^ 2 * (u * (18)) + t * (u ^ 2 * (12)) + u ^ 3 * (2)) + z * (t ^ 4 * (4) + t ^ 3 * (u * (10)) + t ^ 2 * (u ^ 2 * (8)) + t * (u ^ 3 * (2)))) := by positivity
      _ = 2 * (((x) - (x + y + z + t)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t) - (x + y + z + t + u)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t + u) - (x + y)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y) - (x + y + z)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z)) * ((x) + (x + y + z + t)) +
      ((x + y + z) - (x)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x))) := by ring
  linarith only [h]

lemma lw_43821_aux18 (x y z t u : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ ((x) - (x + y + z + t + u)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t + u) - (x + y + z + t)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t) - (x + y)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y) - (x + y + z)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z) - (x)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x)) := by
  have h : 0 ≤ 2 * (((x) - (x + y + z + t + u)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t + u) - (x + y + z + t)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t) - (x + y)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y) - (x + y + z)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z) - (x)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x))) := by
    calc
      0 ≤ 4 * y ^ 2 * (x + y + z) * (z - u) ^ 2 + (x ^ 3 * (y ^ 2 * (16) + y * (z * (16) + t * (16)) + z ^ 2 * (16) + z * (t * (32) + u * (16)) + t ^ 2 * (32) + t * (u * (32)) + u ^ 2 * (16)) + x ^ 2 * (y ^ 3 * (40) + y ^ 2 * (z * (64) + t * (48)) + y * (z ^ 2 * (56) + z * (t * (80) + u * (16)) + t ^ 2 * (72) + t * (u * (64)) + u ^ 2 * (32)) + z ^ 3 * (24) + z ^ 2 * (t * (56) + u * (24)) + z * (t ^ 2 * (72) + t * (u * (64)) + u ^ 2 * (32)) + t ^ 3 * (32) + t ^ 2 * (u * (40)) + t * (u ^ 2 * (24)) + u ^ 3 * (8)) + x * (y ^ 4 * (32) + y ^ 3 * (z * (72) + t * (44)) + y ^ 2 * (z ^ 2 * (68) + z * (t * (72)) + t ^ 2 * (52) + t * (u * (40)) + u ^ 2 * (16)) + y * (z ^ 3 * (44) + z ^ 2 * (t * (72) + u * (12)) + z * (t ^ 2 * (84) + t * (u * (68)) + u ^ 2 * (40)) + t ^ 3 * (40) + t ^ 2 * (u * (56)) + t * (u ^ 2 * (36)) + u ^ 3 * (12)) + z ^ 4 * (12) + z ^ 3 * (t * (32) + u * (12)) + z ^ 2 * (t ^ 2 * (48) + t * (u * (40)) + u ^ 2 * (20)) + z * (t ^ 3 * (36) + t ^ 2 * (u * (44)) + t * (u ^ 2 * (24)) + u ^ 3 * (8)) + t ^ 4 * (8) + t ^ 3 * (u * (12)) + t ^ 2 * (u ^ 2 * (4))) + y ^ 5 * (8) + y ^ 4 * (z * (24) + t * (12)) + y ^ 3 * (z ^ 2 * (26) + z * (t * (22)) + t ^ 2 * (12) + t * (u * (8))) + y ^ 2 * (z ^ 3 * (18) + z ^ 2 * (t * (22)) + z * (t ^ 2 * (20) + t * (u * (10)) + u ^ 2 * (6)) + t ^ 3 * (12) + t ^ 2 * (u * (18)) + t * (u ^ 2 * (12)) + u ^ 3 * (4)) + y * (z ^ 4 * (10) + z ^ 3 * (t * (18) + u * (2)) + z ^ 2 * (t ^ 2 * (22) + t * (u * (16)) + u ^ 2 * (12)) + z * (t ^ 3 * (18) + t ^ 2 * (u * (24)) + t * (u ^ 2 * (16)) + u ^ 3 * (6)) + t ^ 4 * (4) + t ^ 3 * (u * (6)) + t ^ 2 * (u ^ 2 * (2))) + z ^ 5 * (2) + z ^ 4 * (t * (6) + u * (2)) + z ^ 3 * (t ^ 2 * (10) + t * (u * (8)) + u ^ 2 * (4)) + z ^ 2 * (t ^ 3 * (10) + t ^ 2 * (u * (12)) + t * (u ^ 2 * (6)) + u ^ 3 * (2)) + z * (t ^ 4 * (4) + t ^ 3 * (u * (6)) + t ^ 2 * (u ^ 2 * (2)))) := by positivity
      _ = 2 * (((x) - (x + y + z + t + u)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t + u) - (x + y + z + t)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t) - (x + y)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y + z) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y) - (x + y + z)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z) - (x)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x + y + z)) * ((x + y + z) + (x))) := by ring
  linarith only [h]

lemma lw_43821_aux19 (x y z t u : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ ((x) - (x + y + z)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z) - (x + y + z + t)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z + t) - (x + y + z + t + u)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z + t + u) - (x + y)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x) + (x + y + z)) +
      ((x + y) - (x)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x)) := by
  have h : 0 ≤ 2 * (((x) - (x + y + z)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z) - (x + y + z + t)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z + t) - (x + y + z + t + u)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z + t + u) - (x + y)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x) + (x + y + z)) +
      ((x + y) - (x)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x))) := by
    calc
      0 ≤ 0 + (x ^ 3 * (y ^ 2 * (16) + y * (z * (32) + t * (32) + u * (16)) + z ^ 2 * (32) + z * (t * (48) + u * (16)) + t ^ 2 * (32) + t * (u * (32)) + u ^ 2 * (16)) + x ^ 2 * (y ^ 3 * (40) + y ^ 2 * (z * (104) + t * (104) + u * (56)) + y * (z ^ 2 * (136) + z * (t * (224) + u * (112)) + t ^ 2 * (120) + t * (u * (128)) + u ^ 2 * (48)) + z ^ 3 * (64) + z ^ 2 * (t * (144) + u * (72)) + z * (t ^ 2 * (120) + t * (u * (128)) + u ^ 2 * (48)) + t ^ 3 * (32) + t ^ 2 * (u * (56)) + t * (u ^ 2 * (40)) + u ^ 3 * (8)) + x * (y ^ 4 * (32) + y ^ 3 * (z * (100) + t * (100) + u * (56)) + y ^ 2 * (z ^ 2 * (160) + z * (t * (272) + u * (156)) + t ^ 2 * (132) + t * (u * (148)) + u ^ 2 * (48)) + y * (z ^ 3 * (132) + z ^ 2 * (t * (300) + u * (176)) + z * (t ^ 2 * (240) + t * (u * (284)) + u ^ 2 * (96)) + t ^ 3 * (60) + t ^ 2 * (u * (108)) + t * (u ^ 2 * (68)) + u ^ 3 * (12)) + z ^ 4 * (40) + z ^ 3 * (t * (116) + u * (72)) + z ^ 2 * (t ^ 2 * (124) + t * (u * (156)) + u ^ 2 * (52)) + z * (t ^ 3 * (56) + t ^ 2 * (u * (108)) + t * (u ^ 2 * (68)) + u ^ 3 * (12)) + t ^ 4 * (8) + t ^ 3 * (u * (20)) + t ^ 2 * (u ^ 2 * (16)) + t * (u ^ 3 * (4))) + y ^ 5 * (8) + y ^ 4 * (z * (28) + t * (28) + u * (16)) + y ^ 3 * (z ^ 2 * (52) + z * (t * (88) + u * (54)) + t ^ 2 * (40) + t * (u * (46)) + u ^ 2 * (14)) + y ^ 2 * (z ^ 3 * (60) + z ^ 2 * (t * (132) + u * (84)) + z * (t ^ 2 * (98) + t * (u * (122)) + u ^ 2 * (40)) + t ^ 3 * (22) + t ^ 2 * (u * (40)) + t * (u ^ 2 * (24)) + u ^ 3 * (4)) + y * (z ^ 4 * (36) + z ^ 3 * (t * (100) + u * (66)) + z ^ 2 * (t ^ 2 * (98) + t * (u * (128)) + u ^ 2 * (42)) + z * (t ^ 3 * (38) + t ^ 2 * (u * (74)) + t * (u ^ 2 * (46)) + u ^ 3 * (8)) + t ^ 4 * (4) + t ^ 3 * (u * (10)) + t ^ 2 * (u ^ 2 * (8)) + t * (u ^ 3 * (2))) + z ^ 5 * (8) + z ^ 4 * (t * (28) + u * (20)) + z ^ 3 * (t ^ 2 * (36) + t * (u * (50)) + u ^ 2 * (16)) + z ^ 2 * (t ^ 3 * (20) + t ^ 2 * (u * (40)) + t * (u ^ 2 * (24)) + u ^ 3 * (4)) + z * (t ^ 4 * (4) + t ^ 3 * (u * (10)) + t ^ 2 * (u ^ 2 * (8)) + t * (u ^ 3 * (2)))) := by positivity
      _ = 2 * (((x) - (x + y + z)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z) - (x + y + z + t)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z + t) - (x + y + z + t + u)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z + t + u) - (x + y)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x) + (x + y + z)) +
      ((x + y) - (x)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x))) := by ring
  linarith only [h]

lemma lw_43821_aux20 (x y z t u : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ ((x) - (x + y + z)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z) - (x + y + z + t + u)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z + t + u) - (x + y + z + t)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z + t) - (x + y)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x) + (x + y + z)) +
      ((x + y) - (x)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x)) := by
  have h : 0 ≤ 2 * (((x) - (x + y + z)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z) - (x + y + z + t + u)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z + t + u) - (x + y + z + t)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z + t) - (x + y)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x) + (x + y + z)) +
      ((x + y) - (x)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x))) := by
    calc
      0 ≤ 0 + (x ^ 3 * (y ^ 2 * (16) + y * (z * (32) + t * (32) + u * (16)) + z ^ 2 * (32) + z * (t * (48) + u * (32)) + t ^ 2 * (32) + t * (u * (32)) + u ^ 2 * (16)) + x ^ 2 * (y ^ 3 * (40) + y ^ 2 * (z * (104) + t * (104) + u * (48)) + y * (z ^ 2 * (136) + z * (t * (224) + u * (112)) + t ^ 2 * (120) + t * (u * (112)) + u ^ 2 * (40)) + z ^ 3 * (64) + z ^ 2 * (t * (144) + u * (72)) + z * (t ^ 2 * (120) + t * (u * (112)) + u ^ 2 * (40)) + t ^ 3 * (32) + t ^ 2 * (u * (40)) + t * (u ^ 2 * (24)) + u ^ 3 * (8)) + x * (y ^ 4 * (32) + y ^ 3 * (z * (100) + t * (100) + u * (44)) + y ^ 2 * (z ^ 2 * (160) + z * (t * (272) + u * (116)) + t ^ 2 * (132) + t * (u * (116)) + u ^ 2 * (32)) + y * (z ^ 3 * (132) + z ^ 2 * (t * (300) + u * (124)) + z * (t ^ 2 * (240) + t * (u * (196)) + u ^ 2 * (52)) + t ^ 3 * (60) + t ^ 2 * (u * (72)) + t * (u ^ 2 * (32)) + u ^ 3 * (8)) + z ^ 4 * (40) + z ^ 3 * (t * (116) + u * (44)) + z ^ 2 * (t ^ 2 * (124) + t * (u * (92)) + u ^ 2 * (20)) + z * (t ^ 3 * (56) + t ^ 2 * (u * (60)) + t * (u ^ 2 * (20)) + u ^ 3 * (4)) + t ^ 4 * (8) + t ^ 3 * (u * (12)) + t ^ 2 * (u ^ 2 * (4))) + y ^ 5 * (8) + y ^ 4 * (z * (28) + t * (28) + u * (12)) + y ^ 3 * (z ^ 2 * (52) + z * (t * (88) + u * (34)) + t ^ 2 * (40) + t * (u * (34)) + u ^ 2 * (8)) + y ^ 2 * (z ^ 3 * (60) + z ^ 2 * (t * (132) + u * (48)) + z * (t ^ 2 * (98) + t * (u * (74)) + u ^ 2 * (16)) + t ^ 3 * (22) + t ^ 2 * (u * (26)) + t * (u ^ 2 * (10)) + u ^ 3 * (2)) + y * (z ^ 4 * (36) + z ^ 3 * (t * (100) + u * (34)) + z ^ 2 * (t ^ 2 * (98) + t * (u * (68)) + u ^ 2 * (12)) + z * (t ^ 3 * (38) + t ^ 2 * (u * (40)) + t * (u ^ 2 * (12)) + u ^ 3 * (2)) + t ^ 4 * (4) + t ^ 3 * (u * (6)) + t ^ 2 * (u ^ 2 * (2))) + z ^ 5 * (8) + z ^ 4 * (t * (28) + u * (8)) + z ^ 3 * (t ^ 2 * (36) + t * (u * (22)) + u ^ 2 * (2)) + z ^ 2 * (t ^ 3 * (20) + t ^ 2 * (u * (20)) + t * (u ^ 2 * (4))) + z * (t ^ 4 * (4) + t ^ 3 * (u * (6)) + t ^ 2 * (u ^ 2 * (2)))) := by positivity
      _ = 2 * (((x) - (x + y + z)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z) - (x + y + z + t + u)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z + t + u) - (x + y + z + t)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y) + (x)) * ((x) + (x + y + z)) +
      ((x + y + z + t) - (x + y)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x) + (x + y + z)) +
      ((x + y) - (x)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x))) := by ring
  linarith only [h]

lemma lw_43821_aux21 (x y z t u : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ ((x) - (x + y + z + t)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t) - (x + y + z)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z) - (x + y + z + t + u)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t + u) - (x + y)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x) + (x + y + z + t)) +
      ((x + y) - (x)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x)) := by
  have h : 0 ≤ 2 * (((x) - (x + y + z + t)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t) - (x + y + z)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z) - (x + y + z + t + u)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t + u) - (x + y)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x) + (x + y + z + t)) +
      ((x + y) - (x)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x))) := by
    calc
      0 ≤ 0 + (x ^ 3 * (y ^ 2 * (16) + y * (z * (32) + t * (16) + u * (16)) + z ^ 2 * (32) + z * (t * (32) + u * (16)) + t ^ 2 * (16) + t * (u * (16)) + u ^ 2 * (16)) + x ^ 2 * (y ^ 3 * (40) + y ^ 2 * (z * (104) + t * (56) + u * (56)) + y * (z ^ 2 * (136) + z * (t * (160) + u * (112)) + t ^ 2 * (64) + t * (u * (80)) + u ^ 2 * (48)) + z ^ 3 * (64) + z ^ 2 * (t * (120) + u * (72)) + z * (t ^ 2 * (88) + t * (u * (112)) + u ^ 2 * (48)) + t ^ 3 * (24) + t ^ 2 * (u * (40)) + t * (u ^ 2 * (32)) + u ^ 3 * (8)) + x * (y ^ 4 * (32) + y ^ 3 * (z * (100) + t * (56) + u * (56)) + y ^ 2 * (z ^ 2 * (160) + z * (t * (204) + u * (156)) + t ^ 2 * (76) + t * (u * (104)) + u ^ 2 * (48)) + y * (z ^ 3 * (132) + z ^ 2 * (t * (272) + u * (176)) + z * (t ^ 2 * (200) + t * (u * (260)) + u ^ 2 * (96)) + t ^ 3 * (52) + t ^ 2 * (u * (92)) + t * (u ^ 2 * (64)) + u ^ 3 * (12)) + z ^ 4 * (40) + z ^ 3 * (t * (116) + u * (72)) + z ^ 2 * (t ^ 2 * (128) + t * (u * (164)) + u ^ 2 * (52)) + z * (t ^ 3 * (64) + t ^ 2 * (u * (120)) + t * (u ^ 2 * (72)) + u ^ 3 * (12)) + t ^ 4 * (12) + t ^ 3 * (u * (28)) + t ^ 2 * (u ^ 2 * (24)) + t * (u ^ 3 * (8))) + y ^ 5 * (8) + y ^ 4 * (z * (28) + t * (16) + u * (16)) + y ^ 3 * (z ^ 2 * (52) + z * (t * (70) + u * (54)) + t ^ 2 * (26) + t * (u * (36)) + u ^ 2 * (14)) + y ^ 2 * (z ^ 3 * (60) + z ^ 2 * (t * (132) + u * (84)) + z * (t ^ 2 * (100) + t * (u * (126)) + u ^ 2 * (40)) + t ^ 3 * (26) + t ^ 2 * (u * (46)) + t * (u ^ 2 * (28)) + u ^ 3 * (4)) + y * (z ^ 4 * (36) + z ^ 3 * (t * (110) + u * (66)) + z ^ 2 * (t ^ 2 * (126) + t * (u * (154)) + u ^ 2 * (42)) + z * (t ^ 3 * (64) + t ^ 2 * (u * (116)) + t * (u ^ 2 * (62)) + u ^ 3 * (8)) + t ^ 4 * (12) + t ^ 3 * (u * (28)) + t ^ 2 * (u ^ 2 * (22)) + t * (u ^ 3 * (6))) + z ^ 5 * (8) + z ^ 4 * (t * (32) + u * (20)) + z ^ 3 * (t ^ 2 * (50) + t * (u * (62)) + u ^ 2 * (16)) + z ^ 2 * (t ^ 3 * (38) + t ^ 2 * (u * (70)) + t * (u ^ 2 * (36)) + u ^ 3 * (4)) + z * (t ^ 4 * (14) + t ^ 3 * (u * (34)) + t ^ 2 * (u ^ 2 * (26)) + t * (u ^ 3 * (6))) + t ^ 5 * (2) + t ^ 4 * (u * (6)) + t ^ 3 * (u ^ 2 * (6)) + t ^ 2 * (u ^ 3 * (2))) := by positivity
      _ = 2 * (((x) - (x + y + z + t)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t) - (x + y + z)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z) - (x + y + z + t + u)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t + u) - (x + y)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x) + (x + y + z + t)) +
      ((x + y) - (x)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y)) * ((x + y) + (x))) := by ring
  linarith only [h]

lemma lw_43821_aux22 (x y z t u : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ ((x) - (x + y + z + t + u)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t + u) - (x + y + z)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z) - (x + y + z + t)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t) - (x + y)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x) + (x + y + z + t + u)) +
      ((x + y) - (x)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x)) := by
  have h : 0 ≤ 2 * (((x) - (x + y + z + t + u)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t + u) - (x + y + z)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z) - (x + y + z + t)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t) - (x + y)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x) + (x + y + z + t + u)) +
      ((x + y) - (x)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x))) := by
    calc
      0 ≤ 0 + (x ^ 3 * (y ^ 2 * (16) + y * (z * (32) + t * (16)) + z ^ 2 * (32) + z * (t * (32) + u * (16)) + t ^ 2 * (16) + t * (u * (16)) + u ^ 2 * (16)) + x ^ 2 * (y ^ 3 * (40) + y ^ 2 * (z * (104) + t * (56)) + y * (z ^ 2 * (136) + z * (t * (160) + u * (48)) + t ^ 2 * (64) + t * (u * (48)) + u ^ 2 * (32)) + z ^ 3 * (64) + z ^ 2 * (t * (120) + u * (48)) + z * (t ^ 2 * (88) + t * (u * (64)) + u ^ 2 * (24)) + t ^ 3 * (24) + t ^ 2 * (u * (32)) + t * (u ^ 2 * (24)) + u ^ 3 * (8)) + x * (y ^ 4 * (32) + y ^ 3 * (z * (100) + t * (56)) + y ^ 2 * (z ^ 2 * (160) + z * (t * (204) + u * (48)) + t ^ 2 * (76) + t * (u * (48)) + u ^ 2 * (20)) + y * (z ^ 3 * (132) + z ^ 2 * (t * (272) + u * (96)) + z * (t ^ 2 * (200) + t * (u * (140)) + u ^ 2 * (36)) + t ^ 3 * (52) + t ^ 2 * (u * (64)) + t * (u ^ 2 * (36)) + u ^ 3 * (12)) + z ^ 4 * (40) + z ^ 3 * (t * (116) + u * (44)) + z ^ 2 * (t ^ 2 * (128) + t * (u * (92)) + u ^ 2 * (16)) + z * (t ^ 3 * (64) + t ^ 2 * (u * (72)) + t * (u ^ 2 * (24)) + u ^ 3 * (4)) + t ^ 4 * (12) + t ^ 3 * (u * (20)) + t ^ 2 * (u ^ 2 * (12)) + t * (u ^ 3 * (4))) + y ^ 5 * (8) + y ^ 4 * (z * (28) + t * (16)) + y ^ 3 * (z ^ 2 * (52) + z * (t * (70) + u * (16)) + t ^ 2 * (26) + t * (u * (16)) + u ^ 2 * (4)) + y ^ 2 * (z ^ 3 * (60) + z ^ 2 * (t * (132) + u * (48)) + z * (t ^ 2 * (100) + t * (u * (74)) + u ^ 2 * (14)) + t ^ 3 * (26) + t ^ 2 * (u * (32)) + t * (u ^ 2 * (14)) + u ^ 3 * (4)) + y * (z ^ 4 * (36) + z ^ 3 * (t * (110) + u * (44)) + z ^ 2 * (t ^ 2 * (126) + t * (u * (98)) + u ^ 2 * (14)) + z * (t ^ 3 * (64) + t ^ 2 * (u * (76)) + t * (u ^ 2 * (22)) + u ^ 3 * (2)) + t ^ 4 * (12) + t ^ 3 * (u * (20)) + t ^ 2 * (u ^ 2 * (10)) + t * (u ^ 3 * (2))) + z ^ 5 * (8) + z ^ 4 * (t * (32) + u * (12)) + z ^ 3 * (t ^ 2 * (50) + t * (u * (38)) + u ^ 2 * (4)) + z ^ 2 * (t ^ 3 * (38) + t ^ 2 * (u * (44)) + t * (u ^ 2 * (10))) + z * (t ^ 4 * (14) + t ^ 3 * (u * (22)) + t ^ 2 * (u ^ 2 * (8))) + t ^ 5 * (2) + t ^ 4 * (u * (4)) + t ^ 3 * (u ^ 2 * (2))) := by positivity
      _ = 2 * (((x) - (x + y + z + t + u)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t + u) - (x + y + z)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z) - (x + y + z + t)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t) - (x + y)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x) + (x + y + z + t + u)) +
      ((x + y) - (x)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y + z + t)) * ((x + y + z + t) + (x + y)) * ((x + y) + (x))) := by ring
  linarith only [h]

lemma lw_43821_aux23 (x y z t u : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ ((x) - (x + y + z + t)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t) - (x + y + z + t + u)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t + u) - (x + y + z)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z) - (x + y)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x) + (x + y + z + t)) +
      ((x + y) - (x)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y) + (x)) := by
  have h : 0 ≤ 2 * (((x) - (x + y + z + t)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t) - (x + y + z + t + u)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t + u) - (x + y + z)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z) - (x + y)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x) + (x + y + z + t)) +
      ((x + y) - (x)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y) + (x))) := by
    calc
      0 ≤ 0 + (x ^ 3 * (y ^ 2 * (16) + y * (z * (32) + t * (16) + u * (16)) + z ^ 2 * (32) + z * (t * (48) + u * (32)) + t ^ 2 * (32) + t * (u * (32)) + u ^ 2 * (16)) + x ^ 2 * (y ^ 3 * (40) + y ^ 2 * (z * (104) + t * (48) + u * (48)) + y * (z ^ 2 * (136) + z * (t * (160) + u * (112)) + t ^ 2 * (72) + t * (u * (80)) + u ^ 2 * (40)) + z ^ 3 * (64) + z ^ 2 * (t * (120) + u * (72)) + z * (t ^ 2 * (96) + t * (u * (112)) + u ^ 2 * (40)) + t ^ 3 * (32) + t ^ 2 * (u * (56)) + t * (u ^ 2 * (40)) + u ^ 3 * (8)) + x * (y ^ 4 * (32) + y ^ 3 * (z * (100) + t * (44) + u * (44)) + y ^ 2 * (z ^ 2 * (160) + z * (t * (164) + u * (116)) + t ^ 2 * (52) + t * (u * (64)) + u ^ 2 * (32)) + y * (z ^ 3 * (132) + z ^ 2 * (t * (220) + u * (124)) + z * (t ^ 2 * (140) + t * (u * (156)) + u ^ 2 * (52)) + t ^ 3 * (40) + t ^ 2 * (u * (64)) + t * (u ^ 2 * (44)) + u ^ 3 * (8)) + z ^ 4 * (40) + z ^ 3 * (t * (88) + u * (44)) + z ^ 2 * (t ^ 2 * (76) + t * (u * (80)) + u ^ 2 * (20)) + z * (t ^ 3 * (36) + t ^ 2 * (u * (60)) + t * (u ^ 2 * (32)) + u ^ 3 * (4)) + t ^ 4 * (8) + t ^ 3 * (u * (20)) + t ^ 2 * (u ^ 2 * (16)) + t * (u ^ 3 * (4))) + y ^ 5 * (8) + y ^ 4 * (z * (28) + t * (12) + u * (12)) + y ^ 3 * (z ^ 2 * (52) + z * (t * (50) + u * (34)) + t ^ 2 * (12) + t * (u * (16)) + u ^ 2 * (8)) + y ^ 2 * (z ^ 3 * (60) + z ^ 2 * (t * (96) + u * (48)) + z * (t ^ 2 * (52) + t * (u * (54)) + u ^ 2 * (16)) + t ^ 3 * (12) + t ^ 2 * (u * (18)) + t * (u ^ 2 * (12)) + u ^ 3 * (2)) + y * (z ^ 4 * (36) + z ^ 3 * (t * (78) + u * (34)) + z ^ 2 * (t ^ 2 * (60) + t * (u * (58)) + u ^ 2 * (12)) + z * (t ^ 3 * (22) + t ^ 2 * (u * (36)) + t * (u ^ 2 * (18)) + u ^ 3 * (2)) + t ^ 4 * (4) + t ^ 3 * (u * (10)) + t ^ 2 * (u ^ 2 * (8)) + t * (u ^ 3 * (2))) + z ^ 5 * (8) + z ^ 4 * (t * (20) + u * (8)) + z ^ 3 * (t ^ 2 * (16) + t * (u * (14)) + u ^ 2 * (2)) + z ^ 2 * (t ^ 3 * (4) + t ^ 2 * (u * (6)) + t * (u ^ 2 * (2)))) := by positivity
      _ = 2 * (((x) - (x + y + z + t)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t) - (x + y + z + t + u)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z + t + u) - (x + y + z)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y) + (x)) * ((x) + (x + y + z + t)) +
      ((x + y + z) - (x + y)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x) + (x + y + z + t)) +
      ((x + y) - (x)) * ((x + y + z + t) + (x + y + z + t + u)) * ((x + y + z + t + u) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y) + (x))) := by ring
  linarith only [h]

lemma lw_43821_aux24 (x y z t u : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ ((x) - (x + y + z + t + u)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t + u) - (x + y + z + t)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t) - (x + y + z)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z) - (x + y)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x) + (x + y + z + t + u)) +
      ((x + y) - (x)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y) + (x)) := by
  have h : 0 ≤ 2 * (((x) - (x + y + z + t + u)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t + u) - (x + y + z + t)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t) - (x + y + z)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z) - (x + y)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x) + (x + y + z + t + u)) +
      ((x + y) - (x)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y) + (x))) := by
    calc
      0 ≤ 0 + (x ^ 3 * (y ^ 2 * (16) + y * (z * (32) + t * (16)) + z ^ 2 * (32) + z * (t * (48) + u * (16)) + t ^ 2 * (32) + t * (u * (32)) + u ^ 2 * (16)) + x ^ 2 * (y ^ 3 * (40) + y ^ 2 * (z * (104) + t * (48)) + y * (z ^ 2 * (136) + z * (t * (160) + u * (48)) + t ^ 2 * (72) + t * (u * (64)) + u ^ 2 * (32)) + z ^ 3 * (64) + z ^ 2 * (t * (120) + u * (48)) + z * (t ^ 2 * (96) + t * (u * (80)) + u ^ 2 * (24)) + t ^ 3 * (32) + t ^ 2 * (u * (40)) + t * (u ^ 2 * (24)) + u ^ 3 * (8)) + x * (y ^ 4 * (32) + y ^ 3 * (z * (100) + t * (44)) + y ^ 2 * (z ^ 2 * (160) + z * (t * (164) + u * (48)) + t ^ 2 * (52) + t * (u * (40)) + u ^ 2 * (20)) + y * (z ^ 3 * (132) + z ^ 2 * (t * (220) + u * (96)) + z * (t ^ 2 * (140) + t * (u * (124)) + u ^ 2 * (36)) + t ^ 3 * (40) + t ^ 2 * (u * (56)) + t * (u ^ 2 * (36)) + u ^ 3 * (12)) + z ^ 4 * (40) + z ^ 3 * (t * (88) + u * (44)) + z ^ 2 * (t ^ 2 * (76) + t * (u * (72)) + u ^ 2 * (16)) + z * (t ^ 3 * (36) + t ^ 2 * (u * (48)) + t * (u ^ 2 * (20)) + u ^ 3 * (4)) + t ^ 4 * (8) + t ^ 3 * (u * (12)) + t ^ 2 * (u ^ 2 * (4))) + y ^ 5 * (8) + y ^ 4 * (z * (28) + t * (12)) + y ^ 3 * (z ^ 2 * (52) + z * (t * (50) + u * (16)) + t ^ 2 * (12) + t * (u * (8)) + u ^ 2 * (4)) + y ^ 2 * (z ^ 3 * (60) + z ^ 2 * (t * (96) + u * (48)) + z * (t ^ 2 * (52) + t * (u * (50)) + u ^ 2 * (14)) + t ^ 3 * (12) + t ^ 2 * (u * (18)) + t * (u ^ 2 * (12)) + u ^ 3 * (4)) + y * (z ^ 4 * (36) + z ^ 3 * (t * (78) + u * (44)) + z ^ 2 * (t ^ 2 * (60) + t * (u * (62)) + u ^ 2 * (14)) + z * (t ^ 3 * (22) + t ^ 2 * (u * (30)) + t * (u ^ 2 * (12)) + u ^ 3 * (2)) + t ^ 4 * (4) + t ^ 3 * (u * (6)) + t ^ 2 * (u ^ 2 * (2))) + z ^ 5 * (8) + z ^ 4 * (t * (20) + u * (12)) + z ^ 3 * (t ^ 2 * (16) + t * (u * (18)) + u ^ 2 * (4)) + z ^ 2 * (t ^ 3 * (4) + t ^ 2 * (u * (6)) + t * (u ^ 2 * (2)))) := by positivity
      _ = 2 * (((x) - (x + y + z + t + u)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t + u) - (x + y + z + t)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z) + (x + y)) * ((x + y) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z + t) - (x + y + z)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y) + (x)) * ((x) + (x + y + z + t + u)) +
      ((x + y + z) - (x + y)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x) + (x + y + z + t + u)) +
      ((x + y) - (x)) * ((x + y + z + t + u) + (x + y + z + t)) * ((x + y + z + t) + (x + y + z)) * ((x + y + z) + (x + y)) * ((x + y) + (x))) := by ring
  linarith only [h]

lemma lw_43821_aux25 (a b c d e : ℝ) (ha : 0 ≤ a)
    (hab : a ≤ b) (hac : a ≤ c) (had : a ≤ d) (hae : a ≤ e) :
    0 ≤ ((a) - (b)) * ((c) + (d)) * ((d) + (e)) * ((e) + (a)) * ((a) + (b)) +
      ((b) - (c)) * ((b) + (c)) * ((d) + (e)) * ((e) + (a)) * ((a) + (b)) +
      ((c) - (d)) * ((b) + (c)) * ((c) + (d)) * ((e) + (a)) * ((a) + (b)) +
      ((d) - (e)) * ((b) + (c)) * ((c) + (d)) * ((d) + (e)) * ((a) + (b)) +
      ((e) - (a)) * ((b) + (c)) * ((c) + (d)) * ((d) + (e)) * ((e) + (a)) := by
  rcases le_total c b with h1a | h1b
  · rcases le_total d c with h2a | h2b
    · rcases le_total e d with h3a | h3b
      · convert lw_43821_aux24 a (e - a) (d - e) (c - d) (b - c) ha
          (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total e c with h4a | h4b
        · convert lw_43821_aux18 a (d - a) (e - d) (c - e) (b - c) ha
            (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        · rcases le_total e b with h5a | h5b
          · convert lw_43821_aux16 a (d - a) (c - d) (e - c) (b - e) ha
              (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          · convert lw_43821_aux15 a (d - a) (c - d) (b - c) (e - b) ha
              (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total d b with h6a | h6b
      · rcases le_total e c with h7a | h7b
        · convert lw_43821_aux22 a (e - a) (c - e) (d - c) (b - d) ha
            (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        · rcases le_total e d with h8a | h8b
          · convert lw_43821_aux12 a (c - a) (e - c) (d - e) (b - d) ha
              (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          · rcases le_total e b with h9a | h9b
            · convert lw_43821_aux10 a (c - a) (d - c) (e - d) (b - e) ha
                (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            · convert lw_43821_aux9 a (c - a) (d - c) (b - d) (e - b) ha
                (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total e c with h10a | h10b
        · convert lw_43821_aux21 a (e - a) (c - e) (b - c) (d - b) ha
            (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        · rcases le_total e b with h11a | h11b
          · convert lw_43821_aux11 a (c - a) (e - c) (b - e) (d - b) ha
              (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          · rcases le_total e d with h12a | h12b
            · convert lw_43821_aux8 a (c - a) (b - c) (e - b) (d - e) ha
                (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            · convert lw_43821_aux7 a (c - a) (b - c) (d - b) (e - d) ha
                (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
  · rcases le_total d b with h13a | h13b
    · rcases le_total e d with h14a | h14b
      · convert lw_43821_aux23 a (e - a) (d - e) (b - d) (c - b) ha
          (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total e b with h15a | h15b
        · convert lw_43821_aux17 a (d - a) (e - d) (b - e) (c - b) ha
            (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        · rcases le_total e c with h16a | h16b
          · convert lw_43821_aux14 a (d - a) (b - d) (e - b) (c - e) ha
              (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          · convert lw_43821_aux13 a (d - a) (b - d) (c - b) (e - c) ha
              (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total d c with h17a | h17b
      · rcases le_total e b with h18a | h18b
        · convert lw_43821_aux20 a (e - a) (b - e) (d - b) (c - d) ha
            (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        · rcases le_total e d with h19a | h19b
          · convert lw_43821_aux6 a (b - a) (e - b) (d - e) (c - d) ha
              (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          · rcases le_total e c with h20a | h20b
            · convert lw_43821_aux4 a (b - a) (d - b) (e - d) (c - e) ha
                (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            · convert lw_43821_aux3 a (b - a) (d - b) (c - d) (e - c) ha
                (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total e b with h21a | h21b
        · convert lw_43821_aux19 a (e - a) (b - e) (c - b) (d - c) ha
            (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        · rcases le_total e c with h22a | h22b
          · convert lw_43821_aux5 a (b - a) (e - b) (c - e) (d - c) ha
              (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          · rcases le_total e d with h23a | h23b
            · convert lw_43821_aux2 a (b - a) (c - b) (e - c) (d - e) ha
                (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            · convert lw_43821_aux1 a (b - a) (c - b) (d - c) (e - d) ha
                (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring

lemma lw_43821_aux26 (a b c d e : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ ((a) - (b)) * ((c) + (d)) * ((d) + (e)) * ((e) + (a)) * ((a) + (b)) +
      ((b) - (c)) * ((b) + (c)) * ((d) + (e)) * ((e) + (a)) * ((a) + (b)) +
      ((c) - (d)) * ((b) + (c)) * ((c) + (d)) * ((e) + (a)) * ((a) + (b)) +
      ((d) - (e)) * ((b) + (c)) * ((c) + (d)) * ((d) + (e)) * ((a) + (b)) +
      ((e) - (a)) * ((b) + (c)) * ((c) + (d)) * ((d) + (e)) * ((e) + (a)) := by
  rcases le_total a b with h24a | h24b
  · rcases le_total a c with h25a | h25b
    · rcases le_total a d with h26a | h26b
      · rcases le_total a e with h27a | h27b
        · convert lw_43821_aux25 a b c d e ha
            (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        · convert lw_43821_aux25 e a b c d he
            (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total d e with h28a | h28b
        · convert lw_43821_aux25 d e a b c hd
            (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        · convert lw_43821_aux25 e a b c d he
            (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total c d with h29a | h29b
      · rcases le_total c e with h30a | h30b
        · convert lw_43821_aux25 c d e a b hc
            (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        · convert lw_43821_aux25 e a b c d he
            (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total d e with h31a | h31b
        · convert lw_43821_aux25 d e a b c hd
            (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        · convert lw_43821_aux25 e a b c d he
            (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
  · rcases le_total b c with h32a | h32b
    · rcases le_total b d with h33a | h33b
      · rcases le_total b e with h34a | h34b
        · convert lw_43821_aux25 b c d e a hb
            (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        · convert lw_43821_aux25 e a b c d he
            (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total d e with h35a | h35b
        · convert lw_43821_aux25 d e a b c hd
            (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        · convert lw_43821_aux25 e a b c d he
            (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total c d with h36a | h36b
      · rcases le_total c e with h37a | h37b
        · convert lw_43821_aux25 c d e a b hc
            (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        · convert lw_43821_aux25 e a b c d he
            (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total d e with h38a | h38b
        · convert lw_43821_aux25 d e a b c hd
            (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        · convert lw_43821_aux25 e a b c d he
            (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring

theorem lw_43821 (a b c d e : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) :
    (a - b) / (b + c) + (b - c) / (c + d) + (c - d) / (d + e) +
      (d - e) / (e + a) + (e - a) / (a + b) ≥ 0 := by
  have hbc : 0 < b + c := add_pos hb hc
  have hcd : 0 < c + d := add_pos hc hd
  have hde : 0 < d + e := add_pos hd he
  have hea : 0 < e + a := add_pos he ha
  have hab : 0 < a + b := add_pos ha hb
  have h := div_nonneg
    (lw_43821_aux26 a b c d e (le_of_lt ha) (le_of_lt hb) (le_of_lt hc)
      (le_of_lt hd) (le_of_lt he))
    (le_of_lt (mul_pos (mul_pos (mul_pos (mul_pos hbc hcd) hde) hea) hab))
  change 0 ≤ _
  convert h using 1
  · rfl
  · field_simp [ne_of_gt hbc, ne_of_gt hcd, ne_of_gt hde, ne_of_gt hea, ne_of_gt hab]

end

-- forge:entry lw_46297 kind=disproved origin=external
section
/- WLOG: $a\ge b\ge c,$ we have \n $\left(a^{2}-bc+1\right)(b+c)-\left(b^{2}-ca+1\right)(c+a)$ -/
theorem lw_46297_disproof :
    ¬ (∀ {a b c : ℝ}, (a ≥ b ∧ b ≥ c) →
      (a^2 - b * c + 1) * (b + c) -
        (b^2 - c * a + 1) * (c + a) ≥ 0) := by
  intro h
  have hbad := h (a := 1) (b := 0) (c := 0) (by norm_num)
  norm_num at hbad
end

-- forge:entry lw_45468 kind=proved origin=external
section
/- Prove: $[\sum_{i=1}^{n}{a_i}+\sum_{i=1}^{n}{b_i}]^2\geq4n\sum_{i=1}^{n}{a_i}{b_i}$\n$a_1\leq{a_2}\leq\dots\leq{a_n}\leq{b_1}\leq{b_2}\leq\dots\leq{b_n}$ -/
theorem lw_45468 (n : ℕ) (a b : ℕ → ℕ) (hab : a ≤ b) :
    (∑ i ∈ Finset.range n, (a i + ∑ i ∈ Finset.range n, (b i))) ^ 2 ≥
      4 * n * ∑ i ∈ Finset.range n, (a i * b i) := by
  have hprod : (∑ i ∈ Finset.range n, a i * b i) ≤
      (∑ i ∈ Finset.range n, a i) * (∑ i ∈ Finset.range n, b i) := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, a i * (∑ j ∈ Finset.range n, b j) := by
        apply Finset.sum_le_sum
        intro i hi
        exact Nat.mul_le_mul_left (a i)
          (Finset.single_le_sum (fun j hj => Nat.zero_le (b j)) hi)
      _ = _ := (Finset.sum_mul _ _ _).symm
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc
    4 * n * (∑ i ∈ Finset.range n, a i * b i) ≤
        4 * n * ((∑ i ∈ Finset.range n, a i) *
          (∑ i ∈ Finset.range n, b i)) := Nat.mul_le_mul_left _ hprod
    _ = 4 * (∑ i ∈ Finset.range n, a i) *
        (n * (∑ i ∈ Finset.range n, b i)) := by ring
    _ ≤ _ := four_mul_le_sq_add _ _
end

-- forge:entry lw_48244 kind=proved origin=external
section
/- Prove that: $1+a^2+b^2+c^2+4abc\ge a+b+c+ab+bc+ca$ given $a,b,c\ge 0$. -/
lemma lw_48244_aux1 (a b c : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 3 / 4) :
    0 ≤ 1 + a^2 + b^2 + c^2 + 4 * a * b * c -
      (a + b + c + a * b + b * c + c * a) := by
  have h₁ : 0 ≤ 1 + 4 * c := by linarith
  have h₂ : 0 ≤ 3 - 4 * c := by linarith
  have h : 0 ≤ ((1 + 4 * c) * (a + b) - 2 * (1 + c))^2 +
      (1 + 4 * c) * (3 - 4 * c) * (a - b)^2 + 4 * c * (2 * c - 1)^2 := by
    exact add_nonneg
      (add_nonneg (sq_nonneg _)
        (mul_nonneg (mul_nonneg h₁ h₂) (sq_nonneg _)))
      (mul_nonneg (by positivity) (sq_nonneg _))
  have hid : ((1 + 4 * c) * (a + b) - 2 * (1 + c))^2 +
      (1 + 4 * c) * (3 - 4 * c) * (a - b)^2 + 4 * c * (2 * c - 1)^2 =
      (4 * (1 + 4 * c)) * (1 + a^2 + b^2 + c^2 + 4 * a * b * c -
        (a + b + c + a * b + b * c + c * a)) := by ring
  rw [hid] at h
  exact nonneg_of_mul_nonneg_right h (by linarith)

lemma lw_48244_aux2 (a b c : ℝ) (ha : 1 / 2 ≤ a) (hb : 1 / 2 ≤ b)
    (hc : 1 / 2 ≤ c) :
    0 ≤ 1 + a^2 + b^2 + c^2 + 4 * a * b * c -
      (a + b + c + a * b + b * c + c * a) := by
  have ha' : 0 ≤ 2 * a - 1 := by linarith
  have hb' : 0 ≤ 2 * b - 1 := by linarith
  have hc' : 0 ≤ 2 * c - 1 := by linarith
  have hab := mul_nonneg ha' hb'
  have hbc := mul_nonneg hb' hc'
  have hca := mul_nonneg hc' ha'
  have habc := mul_nonneg hab hc'
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

theorem lw_48244 (a b c : ℝ) (ha : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0) :
    1 + a^2 + b^2 + c^2 + 4 * a * b * c ≥
      a + b + c + a * b + b * c + c * a := by
  rcases ha with ⟨ha, hb, hc⟩
  by_cases hca : c ≤ 3 / 4
  · have h := lw_48244_aux1 a b c hc hca
    linarith
  by_cases hba : b ≤ 3 / 4
  · have h := lw_48244_aux1 c a b hb hba
    nlinarith
  by_cases haa : a ≤ 3 / 4
  · have h := lw_48244_aux1 b c a ha haa
    nlinarith
  have h := lw_48244_aux2 a b c (by linarith) (by linarith) (by linarith)
  linarith
end

-- forge:entry lw_54536 kind=proved origin=external
section
/- Let $n\in N^+.$ Prove that $\left(1+\frac{1}{n}\right)^n+\frac{1}{4}\geq \left(1+\frac{1}{n+1}\right)^{n+1}$ -/
theorem lw_54536 (n : ℕ) (hn : 0 < n) :
    (1 + 1 / n)^n + 1 / 4 ≥ (1 + 1 / (n + 1))^(n + 1) := by
  by_cases h : n = 1
  · subst n
    norm_num
  · have hn2 : 1 < n := by omega
    have hn3 : 1 < n + 1 := by omega
    simp [Nat.div_eq_of_lt hn2, Nat.div_eq_of_lt hn3]
end

end Mathlib2
