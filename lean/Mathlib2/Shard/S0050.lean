/- Mathlib2 分片 50（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0002
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry lw_52161 kind=disproved origin=external
section
/- Show that $ a^{4}+b^{4}+c^{4}+a^{2}b^{2}+a^{2}c^{2}+b^{2}c^{2}+16(a+b+c)\geq9(a^{2}+b^{2}+c^{2}+3) $ -/
theorem lw_52161_disproof : ¬ (∀ (a b c : ℝ),
    a ^ 4 + b ^ 4 + c ^ 4 + a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2 +
      16 * (a + b + c) ≥ 9 * (a ^ 2 + b ^ 2 + c ^ 2 + 3)) := by
  intro h
  have hzero := h 0 0 0
  norm_num at hzero
end

-- forge:entry lw_49724 kind=proved origin=external
section
/- Prove that for any real number $x$, the following inequality holds: \n$$\sqrt {(x^2-2)^2+(x-5)^2} + \sqrt{(x^2-3)^2+x^2}\geq \sqrt{26}$$ -/
lemma lw_49724_aux1 (a b c d : ℝ) :
    Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) ≤
      Real.sqrt (a ^ 2 + b ^ 2) + Real.sqrt (c ^ 2 + d ^ 2) := by
  simpa only [Complex.norm_eq_sqrt_sq_add_sq, Complex.sub_re, Complex.sub_im] using
    (norm_sub_le (⟨a, b⟩ : ℂ) (⟨c, d⟩ : ℂ))

theorem lw_49724 (x : ℝ) :
    (Real.sqrt ((x^2 - 2)^2 + (x - 5)^2) +
      Real.sqrt ((x^2 - 3)^2 + x^2)) ≥ Real.sqrt 26 := by
  have h := lw_49724_aux1 (x ^ 2 - 2) (x - 5) (x ^ 2 - 3) x
  have h₁ : x ^ 2 - 2 - (x ^ 2 - 3) = 1 := by ring
  have h₂ : x - 5 - x = -5 := by ring
  norm_num only [h₁, h₂, one_pow] at h
  exact h
end

-- forge:entry lw_50677 kind=proved origin=external
section
/- If $a,b,c>0$ prove that \n\n $a^5+b^5+c^5\geq abc\left(a^2+b^2+c^2+\frac{2}{3}(a-b)^2\right)$ -/
theorem lw_50677 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^5 + b^5 + c^5 ≥ a * b * c * (a^2 + b^2 + c^2 + (2/3) * (a - b)^2) := by
  have hid : a^5 + b^5 + c^5 -
      a * b * c * (a^2 + b^2 + c^2 + (2/3) * (a - b)^2) =
      (c - (a + b) / 2)^2 *
        (c^3 + (a + b) * c^2 + (a + b)^2 * c / 2 + (a + b)^3 / 4) +
      (a - b)^2 *
        ((1/18) * (c - (a + b))^2 * (c + 2 * (a + b)) +
          (7/36) * c^3 + (37/72) * (a + b)^3) +
      (a - b)^4 * ((5/16) * (a + b) + (7/24) * c) := by
    ring
  have h : 0 ≤ a^5 + b^5 + c^5 -
      a * b * c * (a^2 + b^2 + c^2 + (2/3) * (a - b)^2) := by
    rw [hid]
    positivity
  linarith
end

-- forge:entry lw_5698 kind=disproved origin=external
section
/- Prove that for a, b, c > 0:\n\n\( \frac{a^{3}}{(a+b)(a+c)} + \frac{b^{3}}{(b+c)(b+a)} + \frac{c^{3}}{(c+a)(c+b)} \ge \frac{a+b+c}{4} \) -/
theorem lw_5698_disproof :
    ¬ (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c),
      (a^3 / (a + b) * (a + c) + b^3 / (b + c) * (b + a) +
        c^3 / (c + a) * (c + b)) ≥ (a + b + c) / 4) := by
  intro h
  have hf := h (1 / 4) (1 / 4) (1 / 4) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hf
end

-- forge:entry lw_5275 kind=proved origin=external
section
/- Let $x,y,z >0$ such that $x+y+z=1$ , prove that: $\sqrt {{\frac {x+yz}{y+z}}}+\sqrt {{\frac {y+zx}{z+x}}}+\sqrt {{\frac {z+xy}{x+y}}}\geq\sqrt {6}$ -/
lemma lw_5275_aux1 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) :
    Real.sqrt (a * b / c) * Real.sqrt (c * a / b) = a := by
  rw [← Real.sqrt_mul (show 0 ≤ a * b / c by positivity)]
  have heq : a * b / c * (c * a / b) = a ^ 2 := by
    field_simp
    <;> ring
  rw [heq, Real.sqrt_sq ha]

theorem lw_5275 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 1) :
    Real.sqrt ((x + y * z) / (y + z)) + Real.sqrt ((y + z * x) / (z + x)) +
      Real.sqrt ((z + x * y) / (x + y)) ≥ Real.sqrt 6 := by
  have hxid : x + y * z = (x + y) * (z + x) := by
    nlinarith [show x * (x + y + z) = x by rw [h, mul_one]]
  have hyid : y + z * x = (y + z) * (x + y) := by
    nlinarith [show y * (x + y + z) = y by rw [h, mul_one]]
  have hzid : z + x * y = (z + x) * (y + z) := by
    nlinarith [show z * (x + y + z) = z by rw [h, mul_one]]
  rw [hxid, hyid, hzid]
  let a := Real.sqrt ((x + y) * (z + x) / (y + z))
  let b := Real.sqrt ((y + z) * (x + y) / (z + x))
  let c := Real.sqrt ((z + x) * (y + z) / (x + y))
  have hab : a * b = x + y :=
    lw_5275_aux1 (x + y) (z + x) (y + z) (by positivity) (by positivity) (by positivity)
  have hbc : b * c = y + z :=
    lw_5275_aux1 (y + z) (x + y) (z + x) (by positivity) (by positivity) (by positivity)
  have hca : c * a = z + x :=
    lw_5275_aux1 (z + x) (y + z) (x + y) (by positivity) (by positivity) (by positivity)
  change Real.sqrt 6 ≤ a + b + c
  apply Real.sqrt_le_iff.mpr
  constructor
  · dsimp [a, b, c]
    positivity
  · nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
end

-- forge:entry lw_8508 kind=disproved origin=external
section
/- Find all real values of $ x$ , $ y$ and $ z$ such that \n\n $ \begin{cases} (x + 1)yz &= 12 \ (y + 1)zx &= 4 \ (z + 1)xy &= 4 \end{cases}$ -/
theorem lw_8508_disproof :
    ¬ (∀ (x y z : ℝ),
      (x + 1) * y * z = 12 ∧ (y + 1) * z * x = 4 ∧ (z + 1) * x * y = 4 ↔
        x = 2 ∧ y = 1 ∧ z = 3) := by
  intro h
  have hcounter := h 2 1 3
  norm_num at hcounter
end

-- forge:entry lw_5389 kind=proved origin=external
section
/- Let $a, b, c, d$ be real numbers. Prove that \n\n $$(a^2-\frac{3}{2}a+1)(b^2-\frac{3}{2}b+1) (c^2-\frac{3}{2}c+1) (d^2-\frac{3}{2}d+1) \geq\frac{49}{256} (a-b) (b-c) (c-d) (d-a) $$ -/
lemma lw_5389_aux1 (a b k : ℝ) :
    k * (a - b)^2 ≤ (a^2 + k) * (b^2 + k) := by
  nlinarith only [sq_nonneg (a * b + k)]

lemma lw_5389_aux2 (p x y : ℝ) (hx : x^2 ≤ p) (hy : y^2 ≤ p) :
    x * y ≤ p := by
  nlinarith only [hx, hy, sq_nonneg (x - y)]

lemma lw_5389_aux3 (a b c d k : ℝ) (hk : 0 ≤ k) :
    k^2 * (a - b) * (b - c) * (c - d) * (d - a) ≤
      (a^2 + k) * (b^2 + k) * (c^2 + k) * (d^2 + k) := by
  have ha : 0 ≤ a^2 + k := add_nonneg (sq_nonneg a) hk
  have hb : 0 ≤ b^2 + k := add_nonneg (sq_nonneg b) hk
  have hc : 0 ≤ c^2 + k := add_nonneg (sq_nonneg c) hk
  have h₁ := mul_le_mul (lw_5389_aux1 a b k) (lw_5389_aux1 c d k)
    (mul_nonneg hk (sq_nonneg (c - d))) (mul_nonneg ha hb)
  have h₂ := mul_le_mul (lw_5389_aux1 b c k) (lw_5389_aux1 d a k)
    (mul_nonneg hk (sq_nonneg (d - a))) (mul_nonneg hb hc)
  have h₁' : (k * (a - b) * (c - d))^2 ≤
      (a^2 + k) * (b^2 + k) * (c^2 + k) * (d^2 + k) := by
    convert! h₁ using 1 <;> ring
  have h₂' : (k * (b - c) * (d - a))^2 ≤
      (a^2 + k) * (b^2 + k) * (c^2 + k) * (d^2 + k) := by
    convert! h₂ using 1 <;> ring
  have h := lw_5389_aux2
    ((a^2 + k) * (b^2 + k) * (c^2 + k) * (d^2 + k))
    (k * (a - b) * (c - d)) (k * (b - c) * (d - a)) h₁' h₂'
  convert h using 1 <;> ring

theorem lw_5389 (a b c d : ℝ) :
    (a^2 -(3/2)*a + 1)*(b^2 -(3/2)*b + 1)*
      (c^2 -(3/2)*c + 1)*(d^2 -(3/2)*d + 1) ≥
        (49/256) * (a - b)*(b - c)*(c - d)*(d - a) := by
  change (49/256 : ℝ) * (a - b)*(b - c)*(c - d)*(d - a) ≤
    (a^2 -(3/2)*a + 1)*(b^2 -(3/2)*b + 1)*
      (c^2 -(3/2)*c + 1)*(d^2 -(3/2)*d + 1)
  convert lw_5389_aux3 (a - 3/4) (b - 3/4) (c - 3/4) (d - 3/4)
    (7/16) (by norm_num) using 1 <;> ring
end

-- forge:entry lw_7607 kind=proved origin=external
section
/- Let $a,b>0$ and $a+b=a^2+b^2$ . Prove that, \n\n $$1+2\sqrt{a+b}+(a-b)\leq \frac{4}{a+b}+\frac{4+2(b-a)}{\sqrt{a+b}}$$\n\nEquality holds when $a=\frac{\sqrt[3]{2(3\sqrt{78}-4)}}{3}-\frac{7\sqrt[3]{4}}{3\sqrt[3]{3\sqrt{78}-4}}+\frac{4}{3}, b=\frac{\sqrt[3]{27-3\sqrt{78}}}{3}+\frac{\sqrt[3]{9+\sqrt{78}}}{\sqrt[3]{4}}-1$ -/
theorem lw_7607 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = a^2 + b^2) :
    1 + 2 * Real.sqrt (a + b) + (a - b) ≤
      4 / (a + b) + (4 + 2 * (b - a)) / Real.sqrt (a + b) := by
  have hs : 0 < a + b := add_pos ha hb
  set t : ℝ := Real.sqrt (a + b) with htdef
  set d : ℝ := a - b with hddef
  have ht : 0 < t := Real.sqrt_pos.2 hs
  have ht2 : t ^ 2 = a + b := Real.sq_sqrt (le_of_lt hs)
  have hs2 : a + b ≤ 2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2)]
  have htbound : 0 ≤ 2 - t ^ 2 := by linarith
  have hrel : d ^ 2 = t ^ 2 * (2 - t ^ 2) := by
    rw [ht2]
    dsimp [d]
    nlinarith
  have hR : 0 ≤ 4 + 4 * t - t ^ 2 - 2 * t ^ 3 := by
    nlinarith [mul_nonneg (le_of_lt ht) htbound]
  have hid :
      (4 + 4 * t - t ^ 2 - 2 * t ^ 3) ^ 2 -
          (t * (t + 2) * d) ^ 2 =
        (t ^ 4 + 2 * t ^ 3 + t ^ 2 - 4 * t - 4) ^ 2 := by
    linear_combination -(t * (t + 2)) ^ 2 * hrel
  have hsq : (t * (t + 2) * d) ^ 2 ≤
      (4 + 4 * t - t ^ 2 - 2 * t ^ 3) ^ 2 := by
    nlinarith only [hid, sq_nonneg (t ^ 4 + 2 * t ^ 3 + t ^ 2 - 4 * t - 4)]
  have hlin := le_of_sq_le_sq hsq hR
  have hrhs : (4 / t ^ 2 + (4 - 2 * d) / t) * t ^ 2 =
      4 + (4 - 2 * d) * t := by
    field_simp [ne_of_gt ht]
    <;> ring
  have hfinal : 1 + 2 * t + d ≤ 4 / t ^ 2 + (4 - 2 * d) / t := by
    apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos ht)).mp
    rw [hrhs]
    nlinarith only [hlin]
  rw [ht2] at hfinal
  dsimp [t, d] at hfinal
  convert hfinal using 1 <;> ring
end

-- forge:entry lw_10251 kind=disproved origin=external
section
/- $ \frac{a}{c}+\frac{b}{a}+\frac{c}{b} \ge \frac{1}{a}+\frac{1}{b}+\frac{1}{c} $ -/
theorem lw_10251_disproof :
    ¬ (∀ (a b c : ℝ), a / c + b / a + c / b ≥ 1 / a + 1 / b + 1 / c) := by
  intro h
  have hbad := h (1 / 2) (1 / 2) (1 / 2)
  norm_num at hbad
end

-- forge:entry lw_12915 kind=disproved origin=external
section
/- Show that the equation $a^2b=2017(a+b)$ has no solutions for positive integers $a$ and $b$. -/
theorem lw_12915_disproof : ¬ (¬∃ (a b : ℕ), a^2 * b = 2017 * (a + b)) := by
  intro h
  apply h
  exact ⟨0, 0, by norm_num⟩
end

-- forge:entry lw_11887 kind=proved origin=external
section
/- prove that $\sqrt{1+a^2}\le \frac{(a+b)+(a+c)}{2}$ given $a,b,c>0$ and $ab+bc+ca=1$ -/
theorem lw_11887 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b + b * c + c * a = 1) :
    Real.sqrt (1 + a ^ 2) ≤ (a + b + (a + c)) / 2 := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [sq_nonneg (b - c)]
end

-- forge:entry lw_14760 kind=disproved origin=external
section
/- Let $ x,y,a,b,k$ be positive real numbers such that $ x+y=k $. Find the minimal value of $\left(a+\frac{b}{x}\right)\left(a+\frac{b}{y}\right)$ -/
theorem lw_14760_disproof :
    ¬ (∀ (x y a b k : ℝ) (hx : 0 < x ∧ 0 < y)
      (hy : 0 < a ∧ 0 < b) (h : x + y = k),
      (a + b / x) * (a + b / y) ≥ 2 * (a + b / k) ^ 2) := by
  intro hall
  have hbad := hall 1 1 1 1 2 (by norm_num) (by norm_num) (by norm_num)
  norm_num at hbad
end

-- forge:entry lw_1621 kind=disproved origin=external
section
/- Prove that $\sum_{cyc} ((a+b)^3+a^3) \geq (a+b+c)^3$. -/
theorem lw_1621_disproof :
    ¬ (∀ (a b c : ℝ),
      (a + b) ^ 3 + a ^ 3 + (b + c) ^ 3 + b ^ 3 + (c + a) ^ 3 + c ^ 3 ≥
        (a + b + c) ^ 3) := by
  intro h
  have hbad := h (-1) 0 0
  norm_num at hbad
end

-- forge:entry lw_20354 kind=proved origin=external
section
/- Let $ a$ , $ b$ , $ c$ $ \in \mathbb R$ , such that $ \mid{a}\mid \: < 1$ ,and, $ \mid{b}\mid \: < 1$ ,and, $ \mid{c}\mid \: < 1$ , prove that : $ ab+bc+ca +1> 0$ -/
theorem lw_20354 (a b c : ℝ) (h1 : abs a < 1) (h2 : abs b < 1)
    (h3 : abs c < 1) : a * b + b * c + c * a + 1 > 0 := by
  rcases abs_lt.mp h1 with ⟨ha₁, ha₂⟩
  rcases abs_lt.mp h2 with ⟨hb₁, hb₂⟩
  rcases abs_lt.mp h3 with ⟨hc₁, hc₂⟩
  have hp : 0 < (1 + a) * (1 + b) * (1 + c) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hm : 0 < (1 - a) * (1 - b) * (1 - c) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  nlinarith [hp, hm]
end

-- forge:entry lw_1825 kind=proved origin=external
section
/- Let $ a,b,c>0,ab+bc+ca=3 $ . prove that:\n $ 3(a+b+c)+abc\geq 10 $ -/
theorem lw_1825 (a b c : ℝ) (hab : a > 0 ∧ b > 0 ∧ c > 0)
    (habc : a * b + b * c + c * a = 3) :
    3 * (a + b + c) + a * b * c ≥ 10 := by
  rcases hab with ⟨ha, hb, hc⟩
  let p := a + b + c
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp2 : 9 ≤ p ^ 2 := by
    dsimp [p]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hp : 3 ≤ p := by
    by_contra h
    have hm := mul_nonneg hp0 (show 0 ≤ 3 - p by linarith)
    nlinarith
  have hr : 0 ≤ a * b * c := by positivity
  have hs : 12 * p ≤ p ^ 3 + 9 * (a * b * c) := by
    have hschur := an_schur_deg_one a b c ha.le hb.le hc.le
    have heq := congrArg (fun x : ℝ => x * (a + b + c)) habc
    dsimp [p]
    nlinarith [hschur, heq]
  change 10 ≤ 3 * p + a * b * c
  by_cases hlarge : 10 ≤ 3 * p
  · linarith
  · have hp4 : p ≤ 4 := by linarith
    have hp2le : p ^ 2 ≤ 16 := by
      have hm := mul_nonneg (show 0 ≤ 4 - p by linarith)
        (show 0 ≤ 4 + p by linarith)
      nlinarith
    have hf : 0 ≤ 30 - 3 * p - p ^ 2 := by nlinarith
    have hm := mul_nonneg (show 0 ≤ p - 3 by linarith) hf
    nlinarith
end

-- forge:entry lw_21103 kind=proved origin=external
section
/- If $c \geq b \geq a \geq 0$ . Prove that: $(a+3b)(b+4c)(c+2a) \geq 60abc$ -/
theorem lw_21103 (a b c : ℝ) (hab : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0)
    (habc : c ≥ b ∧ b ≥ a) :
    (a + 3 * b) * (b + 4 * c) * (c + 2 * a) ≥ 60 * a * b * c := by
  have ha : 0 ≤ a := hab.1
  have hba : 0 ≤ b - a := sub_nonneg.mpr habc.2
  have hcb : 0 ≤ c - b := sub_nonneg.mpr habc.1
  have h : 0 ≤ 5 * a ^ 2 * (b - a) + 8 * a ^ 2 * (c - b) +
      20 * a * (b - a) ^ 2 + 27 * a * (b - a) * (c - b) +
      16 * a * (c - b) ^ 2 + 15 * (b - a) ^ 3 +
      27 * (b - a) ^ 2 * (c - b) + 12 * (b - a) * (c - b) ^ 2 := by
    positivity
  nlinarith only [h]
end

-- forge:entry lw_19204 kind=proved origin=external
section
/- Prove $\sum\frac{a^2}{(a^2+1)^2}\leq \frac{16}{25}$, given $a,b,c,d>0$ and $a+b+c+d=2$. -/
lemma lw_19204_aux1 (x : ℝ) (hx : (1 : ℝ) / 8 ≤ x) :
    x ^ 2 / (x ^ 2 + 1) ^ 2 ≤ (48 * x - 4) / 125 := by
  have hx0 : 0 ≤ x := by linarith
  have hden : 0 < (x ^ 2 + 1) ^ 2 := by positivity
  apply (div_le_iff₀ hden).2
  have hp : 0 ≤ 12 * x ^ 3 + 11 * x ^ 2 + 32 * x - 4 := by
    have : 0 ≤ x ^ 3 := pow_nonneg hx0 3
    nlinarith [sq_nonneg x]
  have hprod := mul_nonneg (sq_nonneg (2 * x - 1)) hp
  nlinarith [show (2 * x - 1) ^ 2 *
      (12 * x ^ 3 + 11 * x ^ 2 + 32 * x - 4) =
      (48 * x - 4) * (x ^ 2 + 1) ^ 2 - 125 * x ^ 2 by ring]

lemma lw_19204_aux2 (x : ℝ) (hx : 0 ≤ x) :
    x ^ 2 / (x ^ 2 + 1) ^ 2 ≤ (540 * x + 108) / 2197 := by
  have hden : 0 < (x ^ 2 + 1) ^ 2 := by positivity
  apply (div_le_iff₀ hden).2
  have hp : 0 ≤ 60 * x ^ 3 + 92 * x ^ 2 + 216 * x + 27 := by positivity
  have hprod := mul_nonneg (sq_nonneg (3 * x - 2)) hp
  nlinarith [show (3 * x - 2) ^ 2 *
      (60 * x ^ 3 + 92 * x ^ 2 + 216 * x + 27) =
      (540 * x + 108) * (x ^ 2 + 1) ^ 2 - 2197 * x ^ 2 by ring]

lemma lw_19204_aux3 (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1 / 8) :
    x ^ 2 / (x ^ 2 + 1) ^ 2 ≤ 540 * x / 2197 := by
  have hden : 0 < (x ^ 2 + 1) ^ 2 := by positivity
  have hden' : 1 ≤ (x ^ 2 + 1) ^ 2 := by nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]
  have hfrac : x ^ 2 / (x ^ 2 + 1) ^ 2 ≤ x ^ 2 := by
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hden')]
  have hsmall := mul_nonneg hx (sub_nonneg.mpr hx')
  have : x ^ 2 ≤ 540 * x / 2197 := by nlinarith
  exact hfrac.trans this

theorem lw_19204 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (habc : a + b + c + d = 2) :
    a ^ 2 / (a ^ 2 + 1) ^ 2 + b ^ 2 / (b ^ 2 + 1) ^ 2 +
      c ^ 2 / (c ^ 2 + 1) ^ 2 + d ^ 2 / (d ^ 2 + 1) ^ 2 ≤ 16 / 25 := by
  have ha0 := le_of_lt ha
  have hb0 := le_of_lt hb
  have hc0 := le_of_lt hc
  have hd0 := le_of_lt hd
  have ha2 := lw_19204_aux2 a ha0
  have hb2 := lw_19204_aux2 b hb0
  have hc2 := lw_19204_aux2 c hc0
  have hd2 := lw_19204_aux2 d hd0
  by_cases ha' : 1 / 8 ≤ a
  · by_cases hb' : 1 / 8 ≤ b
    · by_cases hc' : 1 / 8 ≤ c
      · by_cases hd' : 1 / 8 ≤ d
        · have ha1 := lw_19204_aux1 a ha'
          have hb1 := lw_19204_aux1 b hb'
          have hc1 := lw_19204_aux1 c hc'
          have hd1 := lw_19204_aux1 d hd'
          linarith
        · have hd3 := lw_19204_aux3 d hd0 (le_of_lt (lt_of_not_ge hd'))
          linarith
      · have hc3 := lw_19204_aux3 c hc0 (le_of_lt (lt_of_not_ge hc'))
        linarith
    · have hb3 := lw_19204_aux3 b hb0 (le_of_lt (lt_of_not_ge hb'))
      linarith
  · have ha3 := lw_19204_aux3 a ha0 (le_of_lt (lt_of_not_ge ha'))
    linarith
end

-- forge:entry lw_23609 kind=proved origin=external
section
/- Prove that the polynomial equation $ x^{8}-x^{7}+x^{2}-x+15=0 $ has no real solution. -/
theorem lw_23609 : ∀ x : ℝ, ¬(x^8 - x^7 + x^2 - x + 15 = 0) := by
  intro x heq
  by_cases hx0 : x ≤ 0
  · have h7 : x ^ 7 ≤ 0 := by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (x ^ 3)) hx0]
    nlinarith [sq_nonneg (x ^ 4), sq_nonneg x]
  · have hx : 0 ≤ x := le_of_lt (lt_of_not_ge hx0)
    by_cases hx1 : x ≤ 1
    · have h7 : x ^ 7 ≤ 1 := pow_le_one₀ hx hx1
      nlinarith [sq_nonneg (x ^ 4), sq_nonneg x]
    · have h1 : 0 ≤ x - 1 := by linarith
      have h7 : 0 ≤ x ^ 7 := pow_nonneg hx 7
      nlinarith [mul_nonneg h7 h1, mul_nonneg hx h1]
end

-- forge:entry lw_22467 kind=proved origin=external
section
/- x^8+x^6*y*z+2*x^3*y^3*z^2-x^5*y^2*z-x^5*y*z^2-2*x^4*y^4+y^8+y^6*z*x+2*y^3*z^3*x^2-y^5*z^2*x-y^5*z*x^2-2*y^4*z^4+z^8+z^6*x*y+2*z^3*x^3*y^2-z^5*x^2*y-z^5*x*y^2-2*z^4*x^4 =F[8][0,1]+F[8][0,2]+F[8][0,3]+4*F[8][1,1]+2*F[8][1,2]\\geq 0. F[8][0,1]=sigma(x^6*(x-y)*(x-z),[x,y,z]) =x^6*(x-y)*(x-z)+y^6*(y-z)*(y-x)+z^6*(z-x)*(z-y)\\geq 0, F[8][0,2]=sigma(x^5*(y+z)*(x-y)*(x-z),[x,y,z])\\geq 0, F[8][0,3]=sigma(x^2*(x+y+z)^2*(y-z)^2*(x-y)*(x-z),[x,y,z])\\geq 0, F[8][1,1]=sigma(x^4*y*z*(y+z)*(x-y)*(x-z),[x,y,z])\\geq 0, F[8][1,2]=sigma(x^3*y*z*(y+z)*(x-y)*(x-z),[x,y,z])\\geq 0 (x\\geq 0,y\\geq 0,z\\geq 0)$ -/
theorem lw_22467_aux1 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ (c + a + b) ^ 8 + (c + b) ^ 8 + c ^ 8 +
      (c + a + b) * (c + b) * c * ((c + a + b) ^ 5 + (c + b) ^ 5 + c ^ 5 -
        (c + a + b) ^ 4 * ((c + b) + c) - (c + b) ^ 4 * ((c + a + b) + c) - c ^ 4 * ((c + a + b) + (c + b))) +
      2 * ((c + a + b) * (c + b) * c) ^ 2 * ((c + a + b) * (c + b) + (c + b) * c + c * (c + a + b)) -
      2 * (((c + a + b) * (c + b)) ^ 4 + ((c + b) * c) ^ 4 + (c * (c + a + b)) ^ 4) := by
  calc
    0 ≤ 11 * c ^ 6 * a ^ 2 +
      11 * c ^ 6 * a * b +
      11 * c ^ 6 * b ^ 2 +
      44 * c ^ 5 * a ^ 3 +
      99 * c ^ 5 * a ^ 2 * b +
      33 * c ^ 5 * a * b ^ 2 +
      22 * c ^ 5 * b ^ 3 +
      71 * c ^ 4 * a ^ 4 +
      252 * c ^ 4 * a ^ 3 * b +
      268 * c ^ 4 * a ^ 2 * b ^ 2 +
      32 * c ^ 4 * a * b ^ 3 +
      16 * c ^ 4 * b ^ 4 +
      60 * c ^ 3 * a ^ 5 +
      292 * c ^ 3 * a ^ 4 * b +
      518 * c ^ 3 * a ^ 3 * b ^ 2 +
      352 * c ^ 3 * a ^ 2 * b ^ 3 +
      10 * c ^ 3 * a * b ^ 4 +
      4 * c ^ 3 * b ^ 5 +
      29 * c ^ 2 * a ^ 6 +
      177 * c ^ 2 * a ^ 5 * b +
      433 * c ^ 2 * a ^ 4 * b ^ 2 +
      512 * c ^ 2 * a ^ 3 * b ^ 3 +
      256 * c ^ 2 * a ^ 2 * b ^ 4 +
      8 * c * a ^ 7 +
      57 * c * a ^ 6 * b +
      173 * c * a ^ 5 * b ^ 2 +
      282 * c * a ^ 4 * b ^ 3 +
      250 * c * a ^ 3 * b ^ 4 +
      100 * c * a ^ 2 * b ^ 5 +
      a ^ 8 +
      8 * a ^ 7 * b +
      28 * a ^ 6 * b ^ 2 +
      56 * a ^ 5 * b ^ 3 +
      68 * a ^ 4 * b ^ 4 +
      48 * a ^ 3 * b ^ 5 +
      16 * a ^ 2 * b ^ 6 := by positivity
    _ = _ := by ring

theorem lw_22467_aux2 (x y z : ℝ) (hz : 0 ≤ z) (hzy : z ≤ y) (hyx : y ≤ x) :
    0 ≤ x ^ 8 + y ^ 8 + z ^ 8 +
      x * y * z * (x ^ 5 + y ^ 5 + z ^ 5 -
        x ^ 4 * (y + z) - y ^ 4 * (x + z) - z ^ 4 * (x + y)) +
      2 * (x * y * z) ^ 2 * (x * y + y * z + z * x) -
      2 * ((x * y) ^ 4 + (y * z) ^ 4 + (z * x) ^ 4) := by
  obtain ⟨b, hb, hby⟩ := exists_nonneg_add_of_le hzy
  obtain ⟨a, ha, hax⟩ := exists_nonneg_add_of_le hyx
  have hx : x = z + a + b := by linarith
  have hy : y = z + b := by linarith
  rw [hx, hy]
  exact lw_22467_aux1 a b z ha hb hz

theorem lw_22467 (x y z : ℝ) (h₀ : 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z) (h₁ : x * y * z = 1) :
    x^8 + x^6 * y * z + 2 * x^3 * y^3 * z^2 - x^5 * y^2 * z - x^5 * y * z^2 - 2 * x^4 * y^4 + y^8 + y^6 * z * x + 2 * y^3 * z^3 * x^2 - y^5 * z^2 * x - y^5 * z * x^2 - 2 * y^4 * z^4 + z^8 + z^6 * x * y + 2 * z^3 * x^3 * y^2 - z^5 * x^2 * y - z^5 * x * y^2 - 2 * z^4 * x^4 ≥ 0 := by
  rcases h₀ with ⟨hx, hy, hz⟩
  rcases le_total x y with hxy | hyx
  · rcases le_total y z with hyz | hzy
    · nlinarith only [lw_22467_aux2 z y x hx hxy hyz]
    · rcases le_total x z with hxz | hzx
      · nlinarith only [lw_22467_aux2 y z x hx hxz hzy]
      · nlinarith only [lw_22467_aux2 y x z hz hzx hxy]
  · rcases le_total x z with hxz | hzx
    · nlinarith only [lw_22467_aux2 z x y hy hyx hxz]
    · rcases le_total y z with hyz | hzy
      · nlinarith only [lw_22467_aux2 x z y hy hyz hzx]
      · nlinarith only [lw_22467_aux2 x y z hz hzy hyx]
end

-- forge:entry lw_26920 kind=proved origin=external
section
/- For $a,b\ge 1$ . Show that $\frac{1}{1+a^2}+\frac{1}{1+b^2}\ge \frac{2}{1+ab}$ -/
theorem lw_26920 (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (1 / (1 + a ^ 2) + 1 / (1 + b ^ 2)) ≥ 2 / (1 + a * b) := by
  have hab : 1 ≤ a * b := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  have ha2 : 0 < 1 + a ^ 2 := by positivity
  have hb2 : 0 < 1 + b ^ 2 := by positivity
  have hab1 : 0 < 1 + a * b := by linarith
  have hidentity :
      1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) - 2 / (1 + a * b) =
        (a - b) ^ 2 * (a * b - 1) /
          ((1 + a ^ 2) * (1 + b ^ 2) * (1 + a * b)) := by
    field_simp
    <;> ring
  have hnonneg :
      0 ≤ (a - b) ^ 2 * (a * b - 1) /
        ((1 + a ^ 2) * (1 + b ^ 2) * (1 + a * b)) :=
    div_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hab))
      (le_of_lt (mul_pos (mul_pos ha2 hb2) hab1))
  rw [← hidentity] at hnonneg
  linarith
end

end Mathlib2
