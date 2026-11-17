/- Mathlib2 分片 43（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0002
import Mathlib2.Shard.S0041
namespace Mathlib2

-- forge:entry lw_47899 kind=disproved origin=external
section
/- Prove that: $\dfrac{bc(b+c)}{a^2+bc}+\dfrac{ca(c+a)}{b^2+ca}+\dfrac{ab(a+b)}{c^2+ab}\ge a+b+c$ -/
theorem lw_47899_disproof :
    ¬ (∀ (a b c : ℝ),
      (b * c * (b + c) / (a ^ 2 + b * c) +
        c * a * (c + a) / (b ^ 2 + c * a) +
        a * b * (a + b) / (c ^ 2 + a * b)) ≥ a + b + c) := by
  intro h
  have hbad := h (-2) (-1) (-1)
  norm_num at hbad
end

-- forge:entry lw_47888 kind=disproved origin=external
section
/- Let $a,b,c,d>0.$ Prove that $$\sum_{cyc}\frac{1}{(a+1)^2}\geq \sum_{cyc}\frac{1}{abc+a+2}$$ -/
theorem lw_47888_disproof : ¬ (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d),
    (1 / (a + 1) ^ 2 + 1 / (b + 1) ^ 2 + 1 / (c + 1) ^ 2 + 1 / (d + 1) ^ 2) ≥
    (1 / (a * b * c * d + a + 2) + 1 / (b * c * d * a + b + 2) +
      1 / (c * d * a * b + c + 2) + 1 / (d * a * b * c + d + 2))) := by
  intro h
  have hbad := h (4 / 5) (4 / 5) (4 / 5) (4 / 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hbad
end

-- forge:entry lw_50073 kind=disproved origin=external
section
/- Prove that $\sum_{cyc}xy(y-z)^{2}\geq 0$. -/
theorem lw_50073_disproof :
    ¬ (∀ (x y z : ℝ),
      x * y * (y - z) ^ 2 + y * z * (z - x) ^ 2 + z * x * (x - y) ^ 2 ≥ 0) := by
  intro h
  have hbad := h 1 0 (-1)
  norm_num at hbad
end

-- forge:entry lw_52288 kind=proved origin=external
section
/- Prove that for all $a,b{\in}R$ there is such a number $c{\in}(0;1)$ such that $|ac+b+\frac{1}{c}|>\frac{1}{24}$ -/
theorem lw_52288 (a b : ℝ) :
    ∃ c ∈ Set.Ioo 0 1, |a*c + b + 1 / c| > 1 / 24 := by
  by_contra h
  push_neg at h
  have h₁ := (abs_le.mp (h (1 / 4) (by norm_num))).2
  have h₂ := (abs_le.mp (h (1 / 2) (by norm_num))).1
  have h₃ := (abs_le.mp (h (3 / 4) (by norm_num))).2
  norm_num at h₁ h₂ h₃
  linarith
end

-- forge:entry lw_46837 kind=proved origin=external
section
/- Let $a,b,c,d$ be non-negative real numbers verifying $a+b+c+d=4$ . Prove that $(2+a^2)(2+b^2)(2+c^2)(2+d^2) \geqslant 81 $ . -/
lemma lw_46837_aux1 (x y : ℝ) (h : (x + y) ^ 2 + 4 * x * y ≤ 16) :
    (2 + ((x + y) / 2) ^ 2) ^ 2 ≤ (2 + x ^ 2) * (2 + y ^ 2) := by
  have hp := mul_nonneg (sq_nonneg (x - y)) (sub_nonneg.mpr h)
  nlinarith only [hp]

lemma lw_46837_aux2 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hs : a + b + c + d = 4)
    (hab : a ≤ b) (hac : a ≤ c) (hbd : b ≤ d) (hcd : c ≤ d) :
    81 ≤ (2 + a ^ 2) * (2 + b ^ 2) * (2 + c ^ 2) * (2 + d ^ 2) := by
  have had : 3 * a + d ≤ 4 := by linarith
  have had2 : (a + d) ^ 2 + 4 * a * d ≤ 16 := by
    have hp := mul_nonneg (show 0 ≤ 4 - (3 * a + d) by linarith)
      (show 0 ≤ 4 + (3 * a + d) by linarith)
    nlinarith [sq_nonneg a]
  have hbc : 3 * (b + c) ≤ 8 := by linarith
  have hbc2 : (b + c) ^ 2 + 4 * b * c ≤ 16 := by
    have hp := mul_nonneg (show 0 ≤ 8 - 3 * (b + c) by linarith)
      (show 0 ≤ 8 + 3 * (b + c) by linarith)
    nlinarith [sq_nonneg (b - c)]
  have h1 := lw_46837_aux1 a d had2
  have h2 := lw_46837_aux1 b c hbc2
  have h3 : 9 ≤ (2 + ((a + d) / 2) ^ 2) * (2 + ((b + c) / 2) ^ 2) := by
    have ht : (a + d) / 2 + (b + c) / 2 = 2 := by linarith
    have hp := sq_nonneg (((a + d) / 2) * ((b + c) / 2) - 1)
    have hq := sq_nonneg ((a + d) / 2 - (b + c) / 2)
    nlinarith [sq_nonneg ((a + d) / 2 + (b + c) / 2 - 2)]
  have h4 : (81 : ℝ) ≤ (2 + ((a + d) / 2) ^ 2) ^ 2 *
      (2 + ((b + c) / 2) ^ 2) ^ 2 := by
    nlinarith [sq_nonneg ((2 + ((a + d) / 2) ^ 2) *
      (2 + ((b + c) / 2) ^ 2) - 9)]
  have h5 := mul_le_mul h1 h2 (by positivity)
    (show 0 ≤ (2 + a ^ 2) * (2 + d ^ 2) by positivity)
  calc
    81 ≤ (2 + ((a + d) / 2) ^ 2) ^ 2 *
      (2 + ((b + c) / 2) ^ 2) ^ 2 := h4
    _ ≤ ((2 + a ^ 2) * (2 + d ^ 2)) * ((2 + b ^ 2) * (2 + c ^ 2)) := h5
    _ = (2 + a ^ 2) * (2 + b ^ 2) * (2 + c ^ 2) * (2 + d ^ 2) := by ring

lemma lw_46837_aux3 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hs : a + b + c + d = 4)
    (hab : a ≤ b) (hac : a ≤ c) (had : a ≤ d) :
    81 ≤ (2 + a ^ 2) * (2 + b ^ 2) * (2 + c ^ 2) * (2 + d ^ 2) := by
  rcases le_total b c with hbc | hcb
  · rcases le_total c d with hcd | hdc
    · exact lw_46837_aux2 a b c d ha hb hc hd hs hab hac (hbc.trans hcd) hcd
    · have h := lw_46837_aux2 a b d c ha hb hd hc (by linarith) hab had hbc hdc
      simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  · rcases le_total b d with hbd | hdb
    · exact lw_46837_aux2 a b c d ha hb hc hd hs hab hac hbd (hcb.trans hbd)
    · have h := lw_46837_aux2 a d c b ha hd hc hb (by linarith) had hac hdb hcb
      simpa only [mul_assoc, mul_left_comm, mul_comm] using h

theorem lw_46837 (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0)
    (hd : d ≥ 0) (habc : a + b + c + d = 4) :
    (2 + a ^ 2) * (2 + b ^ 2) * (2 + c ^ 2) * (2 + d ^ 2) ≥ 81 := by
  rcases le_total a b with hab | hba
  · rcases le_total c d with hcd | hdc
    · rcases le_total a c with hac | hca
      · exact lw_46837_aux3 a b c d ha hb hc hd habc hab hac (hac.trans hcd)
      · have h := lw_46837_aux3 c d a b hc hd ha hb (by linarith) hcd hca (hca.trans hab)
        simpa only [mul_assoc, mul_left_comm, mul_comm] using h
    · rcases le_total a d with had | hda
      · exact lw_46837_aux3 a b c d ha hb hc hd habc hab (had.trans hdc) had
      · have h := lw_46837_aux3 d c a b hd hc ha hb (by linarith) hdc hda (hda.trans hab)
        simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  · rcases le_total c d with hcd | hdc
    · rcases le_total b c with hbc | hcb
      · have h := lw_46837_aux3 b a c d hb ha hc hd (by linarith) hba hbc (hbc.trans hcd)
        simpa only [mul_assoc, mul_left_comm, mul_comm] using h
      · have h := lw_46837_aux3 c d a b hc hd ha hb (by linarith) hcd (hcb.trans hba) hcb
        simpa only [mul_assoc, mul_left_comm, mul_comm] using h
    · rcases le_total b d with hbd | hdb
      · have h := lw_46837_aux3 b a c d hb ha hc hd (by linarith) hba (hbd.trans hdc) hbd
        simpa only [mul_assoc, mul_left_comm, mul_comm] using h
      · have h := lw_46837_aux3 d c a b hd hc ha hb (by linarith) hdc (hdb.trans hba) hdb
        simpa only [mul_assoc, mul_left_comm, mul_comm] using h
end

-- forge:entry lw_51853 kind=proved origin=external
section
/- a,b,c are positive reals and abc=1. Prove that: \n\n1) $\sqrt{\frac{a+b}{c(c+1)}}+\sqrt{\frac{b+c}{a(a+1)}}+\sqrt{\frac{c+a}{b(b+1)}} \ge 3$ \n\nUsing Am-Gm inequality we have: \n\n $LHS \ge 3 \sqrt[6]{\frac{(a+b)(a+c)(b+c)}{(a+1)(b+1)(c+1)}}$ \n\nSo it remains to prove: $(a+b)(a+c)(b+c) \ge (a+1)(b+1)(c+1)$ \n\nLet $a=\frac{x}{y}\ , b=\frac{y}{z} \ ,c=\frac{z}{x}$ \n\nInequality is equal to: \n\n $(x^2+yz)(y^2+xz)(z^2+xy) \ge xyz(x+y)(x+z)(y+z)$ what follows from CS: \n\n $(x^2+yz)(y^2+yz) \ge (xy+yz)^2$ \n$(y^2+xz)(z^2+xz) \ge (yz+xz)^2$ \n$(z^2+xy)(x^2+xy) \ge (xz+xy)^2$ -/
lemma lw_51853_aux1 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hxyz : 1 ≤ x * y * z) : 3 ≤ x + y + z := by
  have h := an_amgm_three_cube x y z hx hy hz
  have hc : (1 : ℝ) ^ 3 ≤ ((x + y + z) / 3) ^ 3 := by
    nlinarith only [h, hxyz]
  have hs : 1 ≤ (x + y + z) / 3 :=
    le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by positivity) hc
  linarith

lemma lw_51853_aux2 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (habc : a * b * c = 1) :
    (a + 1) * (b + 1) * (c + 1) ≤ (a + b) * (b + c) * (a + c) := by
  have hs := lw_51853_aux1 a b c ha hb hc habc.ge
  have hp : (a * b) * (b * c) * (c * a) = 1 := by
    calc
      (a * b) * (b * c) * (c * a) = (a * b * c) ^ 2 := by ring
      _ = 1 := by rw [habc]; norm_num
  have ht := lw_51853_aux1 (a * b) (b * c) (c * a)
    (mul_nonneg ha hb) (mul_nonneg hb hc) (mul_nonneg hc ha) hp.ge
  have hst : 0 ≤ (a + b + c - 3) * (a * b + b * c + c * a - 3) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith only [hs, ht, hst, habc]

theorem lw_51853 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : a * b * c = 1) :
    Real.sqrt ((a + b) / (c * (c + 1))) +
      Real.sqrt ((b + c) / (a * (a + 1))) +
      Real.sqrt ((a + c) / (b * (b + 1))) ≥ 3 := by
  rcases h₀ with ⟨ha, hb, hc⟩
  let x := (a + b) / (c * (c + 1))
  let y := (b + c) / (a * (a + 1))
  let z := (a + c) / (b * (b + 1))
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hden : c * (c + 1) * (a * (a + 1)) * (b * (b + 1)) =
      (a + 1) * (b + 1) * (c + 1) := by
    calc
      _ = (a * b * c) * ((a + 1) * (b + 1) * (c + 1)) := by ring
      _ = _ := by rw [h₁, one_mul]
  have hprod : x * y * z =
      ((a + b) * (b + c) * (a + c)) / ((a + 1) * (b + 1) * (c + 1)) := by
    dsimp [x, y, z]
    rw [div_mul_div_comm, div_mul_div_comm, hden]
  have hp : 1 ≤ x * y * z := by
    rw [hprod]
    apply (le_div_iff₀ (by positivity)).2
    simpa using lw_51853_aux2 a b c ha.le hb.le hc.le h₁
  have hsquare : (Real.sqrt x * Real.sqrt y * Real.sqrt z) ^ 2 = x * y * z := by
    calc
      _ = (Real.sqrt x) ^ 2 * (Real.sqrt y) ^ 2 * (Real.sqrt z) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sq_sqrt hz]
  have hr : 1 ≤ Real.sqrt x * Real.sqrt y * Real.sqrt z := by
    have hpow : (1 : ℝ) ^ 2 ≤ (Real.sqrt x * Real.sqrt y * Real.sqrt z) ^ 2 := by
      rw [hsquare]
      simpa using hp
    exact le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (by positivity) hpow
  exact lw_51853_aux1 (Real.sqrt x) (Real.sqrt y) (Real.sqrt z)
    (Real.sqrt_nonneg x) (Real.sqrt_nonneg y) (Real.sqrt_nonneg z) hr
end

-- forge:entry lw_5456 kind=disproved origin=external
section
/- The function $f : \mathbb{R^+} \to \mathbb{R^+}$ satisfies $2f(x^2) \ge xf(x)+x$ for all positive reals $x.$ Prove that $f(x^3) \ge x^2$ for all positive reals $x.$ -/
theorem lw_5456_aux1 (x : ℝ) :
    2 * ((x ^ 2) ^ 2 + x ^ 2 + 1) ≥ x * (x ^ 2 + x + 1) + x := by
  nlinarith [sq_nonneg (x ^ 2 - x / 4), sq_nonneg (x - (8 / 7 : ℝ))]

theorem lw_5456_aux2 (x : ℝ) :
    2 * (x ^ 2 / Real.log (x ^ 2)) = x * (x / Real.log x) := by
  rw [Real.log_pow]
  by_cases h : Real.log x = 0
  · simp [h]
  · push_cast
    field_simp
    <;> ring

theorem lw_5456_aux3 (c x : ℝ) :
    2 * ((x ^ 2) ^ 2 + x ^ 2 + 1 - c * ((x ^ 2) / Real.log (x ^ 2))) ≥
      x * (x ^ 2 + x + 1 - c * (x / Real.log x)) + x := by
  have h := lw_5456_aux1 x
  have he := congrArg (fun t : ℝ => c * t) (lw_5456_aux2 x)
  nlinarith

theorem lw_5456_disproof : ¬ (∀ (f : ℝ → ℝ),
    (∀ x > 0, 2 * f (x ^ 2) ≥ x * f x + x) →
      ∀ x > 0, f (x ^ 3) ≥ x ^ 2) := by
  intro h
  let f : ℝ → ℝ := fun x => x ^ 2 + x + 1 -
    (10 * Real.log 8) * (x / Real.log x)
  have hf : ∀ x > 0, 2 * f (x ^ 2) ≥ x * f x + x := by
    intro x hx
    exact lw_5456_aux3 (10 * Real.log 8) x
  have hb := h f hf 2 (by norm_num)
  have hl : Real.log (8 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  dsimp [f] at hb
  norm_num at hb
  field_simp at hb
  nlinarith
end

-- forge:entry lw_5514 kind=proved origin=external
section
/- For $a, b, c>0, abc=1$ prove that $\frac{1}{a+b+1}+\frac{1}{b+c+1}+\frac{1}{c+a+1}\le\frac{(a+b+c)^2}{9}$ -/
theorem lw_5514 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) ≤
      (a + b + c) ^ 2 / 9 := by
  have hs := lw_55543_aux1 a b c ha.le hb.le hc.le habc
  have hprod : (a * b) * (b * c) * (c * a) = 1 := by
    calc
      (a * b) * (b * c) * (c * a) = (a * b * c) ^ 2 := by ring
      _ = 1 := by rw [habc]; norm_num
  have hq := lw_55543_aux1 (a * b) (b * c) (c * a)
    (by positivity) (by positivity) (by positivity) hprod
  have hsq : 0 ≤ (a + b + c) * (a * b + b * c + c * a - 3) :=
    mul_nonneg (by positivity) (by linarith)
  have hd : 0 < (a + b + 1) * (b + c + 1) * (c + a + 1) := by positivity
  have hid :
      (1 - (1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1))) *
          ((a + b + 1) * (b + c + 1) * (c + a + 1)) =
        (a + b + c) * (a * b + b * c + c * a) - a * b * c -
          2 * (a + b + c) - 2 := by
    field_simp
    <;> ring
  have hfrac : 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) ≤ 1 := by
    apply sub_nonneg.mp
    apply (mul_nonneg_iff_of_pos_right hd).mp
    rw [hid, habc]
    nlinarith only [hs, hsq]
  calc
    1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) ≤ 1 := hfrac
    _ ≤ (a + b + c) ^ 2 / 9 := by nlinarith [sq_nonneg (a + b + c - 3)]
end

-- forge:entry lw_56214 kind=disproved origin=external
section
/- Let $ {x,y,z}\in {R^{ + }},k\in{N},k\ge{2},$ prove that \n $ (x^k + 1)(y^k + 1)(z^k + 1)\ge{\frac {3^{k - 1}}{4}}(xy + yz + zx)^k,$ \n and determine the condition of equation. \n \n \n \n If you feel difficult, please just to prove the inequality for some specific values of parameter,which is holds. -/
theorem lw_56214_disproof :
    ¬ (∀ (x y z : ℝ) (k : ℕ) (h₁ : 2 ≤ k)
        (hx : 0 < x) (hy : 0 < y) (hz : 0 < z),
        (x^k + 1) * (y^k + 1) * (z^k + 1) ≥
          (3^(k - 1) / 4) * (x * y + y * z + z * x)^k) := by
  intro h
  have hbad := h 1 1 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hbad
end

-- forge:entry lw_55942 kind=proved origin=external
section
/- Let x,y,z>0. Prove that $\frac{x^{2}+y^{2}+z^{2}}{xy+yz+zx}+\frac{8xyz}{(x+y)(y+z)(z+x)}\geq 2$ -/
lemma lw_55942_aux1 (x y z : ℝ) (hz : 0 ≤ z) (hzy : z ≤ y) (hyx : y ≤ x) :
    2 * (x * y + y * z + z * x) * ((x + y) * (y + z) * (z + x)) ≤
      (x ^ 2 + y ^ 2 + z ^ 2) * ((x + y) * (y + z) * (z + x)) +
        8 * x * y * z * (x * y + y * z + z * x) := by
  have ha : 0 ≤ x - y := sub_nonneg.mpr hyx
  have hb : 0 ≤ y - z := sub_nonneg.mpr hzy
  have hid :
      (x ^ 2 + y ^ 2 + z ^ 2) * ((x + y) * (y + z) * (z + x)) +
          8 * x * y * z * (x * y + y * z + z * x) -
          2 * (x * y + y * z + z * x) * ((x + y) * (y + z) * (z + x)) =
      (x - y) ^ 4 * ((y - z) + 2 * z) +
        (x - y) ^ 3 * (3 * (y - z) ^ 2 + 8 * (y - z) * z + 4 * z ^ 2) +
        (x - y) ^ 2 * (2 * (y - z) ^ 3 + 8 * (y - z) ^ 2 * z +
          9 * (y - z) * z ^ 2 + 2 * z ^ 3) +
        (x - y) * (3 * (y - z) ^ 2 * z ^ 2 + 2 * (y - z) * z ^ 3) +
        2 * (y - z) ^ 3 * z ^ 2 + 2 * (y - z) ^ 2 * z ^ 3 := by ring
  have hn : 0 ≤
      (x - y) ^ 4 * ((y - z) + 2 * z) +
        (x - y) ^ 3 * (3 * (y - z) ^ 2 + 8 * (y - z) * z + 4 * z ^ 2) +
        (x - y) ^ 2 * (2 * (y - z) ^ 3 + 8 * (y - z) ^ 2 * z +
          9 * (y - z) * z ^ 2 + 2 * z ^ 3) +
        (x - y) * (3 * (y - z) ^ 2 * z ^ 2 + 2 * (y - z) * z ^ 3) +
        2 * (y - z) ^ 3 * z ^ 2 + 2 * (y - z) ^ 2 * z ^ 3 := by positivity
  linarith only [hid, hn]

lemma lw_55942_aux2 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    2 * (x * y + y * z + z * x) * ((x + y) * (y + z) * (z + x)) ≤
      (x ^ 2 + y ^ 2 + z ^ 2) * ((x + y) * (y + z) * (z + x)) +
        8 * x * y * z * (x * y + y * z + z * x) := by
  rcases le_total x y with hxy | hyx
  · rcases le_total y z with hyz | hzy
    · convert lw_55942_aux1 z y x hx hxy hyz using 1 <;> ring
    · rcases le_total x z with hxz | hzx
      · convert lw_55942_aux1 y z x hx hxz hzy using 1 <;> ring
      · convert lw_55942_aux1 y x z hz hzx hxy using 1 <;> ring
  · rcases le_total x z with hxz | hzx
    · convert lw_55942_aux1 z x y hy hyx hxz using 1 <;> ring
    · rcases le_total y z with hyz | hzy
      · convert lw_55942_aux1 x z y hy hyz hzx using 1 <;> ring
      · exact lw_55942_aux1 x y z hz hzy hyx

theorem lw_55942 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x^2 + y^2 + z^2) / (x * y + y * z + z * x) +
      8 * x * y * z / ((x + y) * (y + z) * (z + x)) ≥ 2 := by
  have hq : 0 < x * y + y * z + z * x := by positivity
  have hd : 0 < (x + y) * (y + z) * (z + x) := by positivity
  rw [div_add_div _ _ (ne_of_gt hq) (ne_of_gt hd)]
  apply (le_div_iff₀ (mul_pos hq hd)).2
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    lw_55942_aux2 x y z hx.le hy.le hz.le

end

-- forge:entry lw_56957 kind=proved origin=external
section
/- Let $a$ , $b$ and $c$ be non-negative numbers such that $a+bc=2$ . Prove that $$\frac{1}{a^2+2}+\frac{1}{b^2+2}+\frac{1}{c^2+2}\leq1+\frac{1}{6}(a-1)^2$$ -/
lemma lw_56957_aux1 (x y : ℝ) (hlo : -2 < x * y) (hhi : x * y ≤ 2) :
    1 / (x ^ 2 + 2) + 1 / (y ^ 2 + 2) ≤ 2 / (x * y + 2) := by
  have hx : 0 < x ^ 2 + 2 := by positivity
  have hy : 0 < y ^ 2 + 2 := by positivity
  have hxy : 0 < x * y + 2 := by linarith
  have hd : 0 < (x * y + 2) * (x ^ 2 + 2) * (y ^ 2 + 2) := by positivity
  have hid :
      (2 / (x * y + 2) - (1 / (x ^ 2 + 2) + 1 / (y ^ 2 + 2))) *
          ((x * y + 2) * (x ^ 2 + 2) * (y ^ 2 + 2)) =
        (2 - x * y) * (x - y) ^ 2 := by
    field_simp [ne_of_gt hx, ne_of_gt hy, ne_of_gt hxy]
    <;> ring
  apply sub_nonneg.mp
  apply (mul_nonneg_iff_of_pos_right hd).mp
  rw [hid]
  exact mul_nonneg (sub_nonneg.mpr hhi) (sq_nonneg (x - y))

lemma lw_56957_aux2 (x : ℝ) (hx : x ≤ 2) :
    1 / (x ^ 2 + 2) + 2 / (4 - x) ≤ 1 + 1 / 6 * (x - 1) ^ 2 := by
  have hx2 : 0 < x ^ 2 + 2 := by positivity
  have hx4 : 0 < 4 - x := by linarith
  have hd : 0 < 6 * (x ^ 2 + 2) * (4 - x) := by positivity
  have hid :
      (1 + 1 / 6 * (x - 1) ^ 2 - (1 / (x ^ 2 + 2) + 2 / (4 - x))) *
          (6 * (x ^ 2 + 2) * (4 - x)) =
        (x - 1) ^ 2 * (2 - x) * ((x - 1) ^ 2 + 3) := by
    field_simp [ne_of_gt hx2, ne_of_gt hx4]
    <;> ring
  apply sub_nonneg.mp
  apply (mul_nonneg_iff_of_pos_right hd).mp
  rw [hid]
  exact mul_nonneg
    (mul_nonneg (sq_nonneg (x - 1)) (sub_nonneg.mpr hx)) (by positivity)

theorem lw_56957 (a b c : ℝ) (ha : a + b * c = 2) (hb : 0 ≤ a)
    (hc : 0 ≤ b) (h : 0 ≤ c) :
    1 / (a ^ 2 + 2) + 1 / (b ^ 2 + 2) + 1 / (c ^ 2 + 2) ≤
      1 + 1 / 6 * (a - 1) ^ 2 := by
  have hbc : 0 ≤ b * c := mul_nonneg hc h
  have ha2 : a ≤ 2 := by linarith
  have hbc2 : b * c ≤ 2 := by linarith
  have hbound := lw_56957_aux1 b c (by linarith) hbc2
  have hden : b * c + 2 = 4 - a := by linarith
  rw [hden] at hbound
  calc
    1 / (a ^ 2 + 2) + 1 / (b ^ 2 + 2) + 1 / (c ^ 2 + 2) =
        1 / (a ^ 2 + 2) + (1 / (b ^ 2 + 2) + 1 / (c ^ 2 + 2)) := by ring
    _ ≤ 1 / (a ^ 2 + 2) + 2 / (4 - a) := add_le_add_right hbound _
    _ ≤ 1 + 1 / 6 * (a - 1) ^ 2 := lw_56957_aux2 a ha2

end

-- forge:entry lw_6411 kind=disproved origin=external
section
/- Let $ a,b,c \ge 0$ such that $ a + b + c = ab + bc + ca$ . \nprove that \n $ \sum \frac {1}{b+c}\geq \frac {1}{a+b+c}+1.$ -/
theorem lw_6411_disproof :
    ¬ (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0)
      (habc : a + b + c = a * b + b * c + c * a),
      1 / a + 1 / b + 1 / c ≥ 1 / (a + b + c) + 1) := by
  intro h
  have hzero := h 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hzero
end

-- forge:entry lw_56987 kind=disproved origin=external
section
/- Prove that for positive real numbers x, y, z, w, and k in the interval [0, 1], the following inequality holds:\n$\frac{x}{{ky + (1 - k)z}} + \frac{y}{{kz + (1 - k)w}} + \frac{z}{{kw + (1 - k)x}} + \frac{w}{{kx + (1 - k)y}} \ge 4$ -/
theorem lw_56987_disproof :
    ¬ (∀ (x y z w k : ℝ)
      (hx0 : 0 < x ∧ 0 < y ∧ 0 < z ∧ 0 < w)
      (hx1 : x ≤ 1 ∧ y ≤ 1 ∧ z ≤ 1 ∧ w ≤ 1)
      (hk0 : 0 < k ∧ 0 < 1 - k),
      4 ≤ x / (k * y + (1 - k) * z) +
        y / (k * z + (1 - k) * w) +
        z / (k * w + (1 - k) * x) +
        w / (k * x + (1 - k) * y)) := by
  intro h
  have hbad := h 1 (1 / 2) 1 (1 / 2) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at hbad
end

-- forge:entry lw_8987 kind=disproved origin=external
section
/- Prove that $3b^2c^3+6ca^4+2b^2a^3+6c^2a^3+3c^3a^2+20ab^4+10ba^4+16bca^3+17a^2b^2c+bc^2a^2-ab^2c^2+4bc^3a+48b^3a^2>0$ -/
theorem lw_8987_disproof : ¬ (∀ a b c : ℝ, 3 * b ^ 2 * c ^ 3 + 6 * c * a ^ 4 + 2 * b ^ 2 * a ^ 3 + 6 * c ^ 2 * a ^ 3 + 3 * c ^ 3 * a ^ 2 + 20 * a * b ^ 4 + 10 * b * a ^ 4 + 16 * b * c * a ^ 3 + 17 * a ^ 2 * b ^ 2 * c + b * c ^ 2 * a ^ 2 - a * b ^ 2 * c ^ 2 + 4 * b * c ^ 3 * a + 48 * b ^ 3 * a ^ 2 > 0) := by
  intro h
  have h0 := h 0 0 0
  norm_num at h0
end

-- forge:entry lw_1026 kind=disproved origin=external
section
/- Prove that $\sqrt[3]{(a^5+2)(b^5+2)(c^5+2)}\ge a^2+b^2+c^2$ given $a,b,c\ge 0$ and $a+b+c=3$. -/
theorem lw_1026_disproof : ¬ (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0)
    (hc : c ≥ 0) (hab : a + b + c = 3),
    ((a ^ 5 + 2) * (b ^ 5 + 2) * (c ^ 5 + 2))^(1 / 3) ≥
      a ^ 2 + b ^ 2 + c ^ 2) := by
  intro h
  have h111 := h 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h111
end

-- forge:entry lw_9953 kind=disproved origin=external
section
/- It's equivalent to \n $5(a+b+c)(ab+bc+ca)\geq (a+b+c)^3+18abc\iff$\n $2\sum_{sym}a^2b\geq a^3+b^3+c^3+9abc$\nSetting $a=y+z$ , $b=z+x$ , $c=x+y$ , the inequality reduces to \n $2(x^3+y^3+z^3+3xyz-\sum_{sym}x^2y)\geq0$\nwhich is Schur. $\blacksquare$ -/
theorem lw_9953_disproof :
    ¬ (∀ {a b c : ℝ},
      5 * (a + b + c) * (a * b + b * c + c * a) ≥
        (a + b + c) ^ 3 + 18 * a * b * c) := by
  intro h
  have hbad := @h 1 0 0
  norm_num at hbad
end

-- forge:entry lw_9135 kind=disproved origin=external
section
/- Prove that $\sqrt{a^2 +b^2 +2} \le \sqrt{2(ab+1)}$ using AM-GM inequality. -/
theorem lw_9135_disproof :
    ¬ (∀ (a b : ℝ), 0 ≤ a ∧ 0 ≤ b →
      Real.sqrt (a ^ 2 + b ^ 2 + 2) ≤ Real.sqrt (2 * (a * b + 1))) := by
  intro h
  have h01 := h 0 1 (by norm_num)
  norm_num at h01
end

-- forge:entry lw_11359 kind=proved origin=external
section
/- Let a,b,c>0 such that $abc = 1$ . Prove that \n $\frac{{a + b}}{{\sqrt {{a^2} + 1} }} + \frac{{b + c}}{{\sqrt {{b^2} + 1} }} + \frac{{c + a}}{{\sqrt {{c^2} + 1} }} \ge 3\sqrt 2 $ \n(NguyenNgocTu, July, 2018) -/
lemma lw_11359_aux1 (p q : ℝ) (hp : 3 ≤ p) (hq : 3 ≤ q) :
    8 * (p ^ 2 + q ^ 2 - 2 * p - 2 * q + 2) ≤ (p * q - 1) ^ 2 := by
  have hp2 : 0 ≤ p ^ 2 - 9 := by nlinarith
  have hq2 : 0 ≤ q ^ 2 - 9 := by nlinarith
  nlinarith only [mul_nonneg hp2 hq2, sq_nonneg (p - q), hp, hq]

lemma lw_11359_aux2 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (habc : a * b * c = 1) :
    8 * ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) ≤
      ((a + b) * (b + c) * (c + a)) ^ 2 := by
  let p := a + b + c
  let q := a * b + b * c + c * a
  have hp : 3 ≤ p := lw_51853_aux1 a b c ha hb hc habc.ge
  have hpair : (a * b) * (b * c) * (c * a) = 1 := by
    calc
      _ = (a * b * c) ^ 2 := by ring
      _ = 1 := by rw [habc]; norm_num
  have hq : 3 ≤ q := lw_51853_aux1 (a * b) (b * c) (c * a)
    (mul_nonneg ha hb) (mul_nonneg hb hc) (mul_nonneg hc ha) hpair.ge
  have hn : (a + b) * (b + c) * (c + a) = p * q - 1 := by
    calc
      _ = p * q - a * b * c := by dsimp [p, q]; ring
      _ = _ := by rw [habc]
  have hd : (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) =
      p ^ 2 + q ^ 2 - 2 * p - 2 * q + 2 := by
    calc
      _ = p ^ 2 + q ^ 2 - 2 * (a * b * c) * p - 2 * q +
          (a * b * c) ^ 2 + 1 := by dsimp [p, q]; ring
      _ = _ := by rw [habc]; ring
  rw [hn, hd]
  exact lw_11359_aux1 p q hp hq

lemma lw_11359_aux3 (x y z t : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hprod : t ^ 3 ≤ x * y * z) :
    3 * t ≤ x + y + z := by
  have ham := an_amgm_three_cube x y z hx hy hz
  have hp : t ^ 3 ≤ ((x + y + z) / 3) ^ 3 := le_trans hprod ham
  have hs : t ≤ (x + y + z) / 3 :=
    le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by positivity) hp
  linarith

theorem lw_11359 (a b c : ℝ) (habc : a * b * c = 1)
    (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    (a + b) / (Real.sqrt (a ^ 2 + 1)) +
      (b + c) / (Real.sqrt (b ^ 2 + 1)) +
      (c + a) / (Real.sqrt (c ^ 2 + 1)) >= 3 * Real.sqrt 2 := by
  let u := Real.sqrt (a ^ 2 + 1)
  let v := Real.sqrt (b ^ 2 + 1)
  let w := Real.sqrt (c ^ 2 + 1)
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hw : 0 < w := by dsimp [w]; positivity
  have hu2 : u ^ 2 = a ^ 2 + 1 := Real.sq_sqrt (by positivity)
  have hv2 : v ^ 2 = b ^ 2 + 1 := Real.sq_sqrt (by positivity)
  have hw2 : w ^ 2 = c ^ 2 + 1 := Real.sq_sqrt (by positivity)
  have ht : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have ht2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hden2 : (u * v * w) ^ 2 =
      (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) := by
    rw [mul_pow, mul_pow, hu2, hv2, hw2]
  have hp := lw_11359_aux2 a b c ha.le hb.le hc.le habc
  have hpow : (2 * Real.sqrt 2 * (u * v * w)) ^ 2 ≤
      ((a + b) * (b + c) * (c + a)) ^ 2 := by
    calc
      _ = 8 * ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) := by
        rw [mul_pow, mul_pow, hden2, ht2]
        ring
      _ ≤ _ := hp
  have hnum : 2 * Real.sqrt 2 * (u * v * w) ≤
      (a + b) * (b + c) * (c + a) :=
    le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (by positivity) hpow
  have hprod : (Real.sqrt 2) ^ 3 ≤
      ((a + b) / u) * ((b + c) / v) * ((c + a) / w) := by
    rw [div_mul_div_comm, div_mul_div_comm]
    apply (le_div_iff₀ (by positivity : 0 < u * v * w)).2
    have ht3 : (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 := by
      calc
        _ = (Real.sqrt 2) ^ 2 * Real.sqrt 2 := by ring
        _ = _ := by rw [ht2]
    rw [ht3]
    exact hnum
  exact lw_11359_aux3 ((a + b) / u) ((b + c) / v) ((c + a) / w)
    (Real.sqrt 2) (by positivity) (by positivity) (by positivity) ht hprod
end

-- forge:entry lw_11443 kind=proved origin=external
section
/- Let $x, y, z$ be positive real numbers. Prove that $\sum_{cyc}{\frac{1}{xy+2z^2}} \leq \frac{xy+yz+zx}{xyz(x+y+z)}.$ -/
lemma lw_11443_aux1 (x y z : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hxz : x ≤ z) :
    0 ≤ (x * y + y * z + z * x) * (x * y + 2 * z ^ 2) *
      (y * z + 2 * x ^ 2) * (z * x + 2 * y ^ 2) -
      x * y * z * (x + y + z) *
        ((x * y + 2 * z ^ 2) * (y * z + 2 * x ^ 2) +
         (y * z + 2 * x ^ 2) * (z * x + 2 * y ^ 2) +
         (z * x + 2 * y ^ 2) * (x * y + 2 * z ^ 2)) := by
  have hb : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hc : 0 ≤ z - x := sub_nonneg.mpr hxz
  have hid :
      (x * y + y * z + z * x) * (x * y + 2 * z ^ 2) *
      (y * z + 2 * x ^ 2) * (z * x + 2 * y ^ 2) -
      x * y * z * (x + y + z) *
        ((x * y + 2 * z ^ 2) * (y * z + 2 * x ^ 2) +
         (y * z + 2 * x ^ 2) * (z * x + 2 * y ^ 2) +
         (z * x + 2 * y ^ 2) * (x * y + 2 * z ^ 2)) =
      9 * x ^ 6 * (((y - x) - (z - x)) ^ 2 + (y - x) * (z - x)) +
      6 * x ^ 5 * ((y - x) + (z - x)) ^ 3 +
      x ^ 4 * (((y - x) + (z - x)) ^ 4 +
        9 * (y - x) * (z - x) * ((y - x) + (z - x)) ^ 2 +
        54 * (y - x) ^ 2 * (z - x) ^ 2) +
      2 * x ^ 3 * (y - x) * (z - x) * ((y - x) + (z - x)) *
        (((y - x) + (z - x)) ^ 2 + 27 * (y - x) * (z - x)) +
      3 * x ^ 2 * (y - x) ^ 2 * (z - x) ^ 2 *
        (5 * ((y - x) + (z - x)) ^ 2 + 7 * (y - x) * (z - x)) +
      14 * x * (y - x) ^ 3 * (z - x) ^ 3 * ((y - x) + (z - x)) +
      4 * (y - x) ^ 4 * (z - x) ^ 4 := by ring
  rw [hid]
  positivity

lemma lw_11443_aux2 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ (x * y + y * z + z * x) * (x * y + 2 * z ^ 2) *
      (y * z + 2 * x ^ 2) * (z * x + 2 * y ^ 2) -
      x * y * z * (x + y + z) *
        ((x * y + 2 * z ^ 2) * (y * z + 2 * x ^ 2) +
         (y * z + 2 * x ^ 2) * (z * x + 2 * y ^ 2) +
         (z * x + 2 * y ^ 2) * (x * y + 2 * z ^ 2)) := by
  rcases le_total x y with hxy | hyx
  · rcases le_total x z with hxz | hzx
    · exact lw_11443_aux1 x y z hx hxy hxz
    · convert lw_11443_aux1 z y x hz (hzx.trans hxy) hzx using 1 <;> ring
  · rcases le_total y z with hyz | hzy
    · convert lw_11443_aux1 y x z hy hyx hyz using 1 <;> ring
    · convert lw_11443_aux1 z x y hz (hzy.trans hyx) hzy using 1 <;> ring

theorem lw_11443 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    1 / (x * y + 2 * z ^ 2) + 1 / (y * z + 2 * x ^ 2) +
      1 / (z * x + 2 * y ^ 2) ≤
      (x * y + y * z + z * x) / (x * y * z * (x + y + z)) := by
  have ha : 0 < x * y + 2 * z ^ 2 := by positivity
  have hb : 0 < y * z + 2 * x ^ 2 := by positivity
  have hc : 0 < z * x + 2 * y ^ 2 := by positivity
  have hd : 0 < x * y * z * (x + y + z) := by positivity
  have heq :
      1 / (x * y + 2 * z ^ 2) + 1 / (y * z + 2 * x ^ 2) +
      1 / (z * x + 2 * y ^ 2) =
      ((x * y + 2 * z ^ 2) * (y * z + 2 * x ^ 2) +
       (y * z + 2 * x ^ 2) * (z * x + 2 * y ^ 2) +
       (z * x + 2 * y ^ 2) * (x * y + 2 * z ^ 2)) /
      ((x * y + 2 * z ^ 2) * (y * z + 2 * x ^ 2) *
       (z * x + 2 * y ^ 2)) := by
    field_simp
    <;> ring
  rw [heq]
  apply (div_le_div_iff₀ (mul_pos (mul_pos ha hb) hc) hd).2
  have hp := lw_11443_aux2 x y z hx.le hy.le hz.le
  nlinarith only [hp]
end

-- forge:entry lw_12465 kind=disproved origin=external
section
/- Prove that for positive reals $x$, $y$, and $z$, the following inequality holds: $\sqrt {x^2 + \frac{1}{{x^2 }}} + \sqrt {y^2 + \frac{1}{{y^2 }}} + \sqrt {z^2 + \frac{1}{{z^2 }}} \geq \sqrt{82}$ -/
theorem lw_12465_disproof :
    ¬ (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z),
      (Real.sqrt (x ^ 2 + 1 / (x ^ 2)) +
        Real.sqrt (y ^ 2 + 1 / (y ^ 2)) +
        Real.sqrt (z ^ 2 + 1 / (z ^ 2))) ≥ Real.sqrt 82) := by
  intro h
  have h1 := h 1 1 1 (by norm_num) (by norm_num) (by norm_num)
  norm_num at h1
  have h2 : Real.sqrt (2 : ℝ) < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg (2 : ℝ)]
  have h82 : 6 < Real.sqrt (82 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 82),
      Real.sqrt_nonneg (82 : ℝ)]
  linarith
end

end Mathlib2
