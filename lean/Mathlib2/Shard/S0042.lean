/- Mathlib2 分片 42（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0041
namespace Mathlib2

-- forge:entry lw_23413 kind=disproved origin=external
section
/- For any positive real numbers $a, b, c$, prove that $\frac{1}{2a^2+bc}\ge \frac{1}{ab+bc+ca}+\frac{2}{a^2+b^2+c^2}$ -/
theorem lw_23413_disproof : ¬ (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c),
    (1 / (2 * a ^ 2 + b * c) : ℝ) ≥
      (1 / (a * b + b * c + c * a) + 2 / (a ^ 2 + b ^ 2 + c ^ 2))) := by
  intro h
  have hfalse := h 1 1 1 (by norm_num) (by norm_num) (by norm_num)
  norm_num at hfalse
end

-- forge:entry lw_23175 kind=proved origin=external
section
/- If $a,b,c$ are nonnegative real numbers such that $a+b+c=3,$ then \n $ \sqrt{2a^2+bc+1}+\sqrt{2b^2+ca+1}+\sqrt{2c^2+ab+1} \geq 6.$ -/
lemma lw_23175_aux1 (q p : ℝ) (hq : 0 ≤ q) (hq3 : q ≤ 3)
    (hp : 0 ≤ p) (hpq : 9 * p ≤ q ^ 2) :
    0 ≤ 39015 + 47304*p + 50544*p^2 + 28764*q - 133488*q*p -
      3006*q^2 - 1944*q^2*p + 8460*q^3 - 81*q^4 := by
  by_cases hq1 : 1 ≤ q
  · have hD : 0 ≤ -5256 + 14832*q - 1032*q^2 := by
      nlinarith [mul_nonneg hq (sub_nonneg.mpr hq3)]
    have hB0 : 0 ≤ 5391 - 327*q := by linarith
    have hB : 0 ≤ 13005 + 13923*q + q^2*(5391-327*q) := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hq3) hB,
      mul_nonneg (sub_nonneg.mpr hpq) hD, sq_nonneg (q^2-9*p)]
  · have hq1' : q ≤ 1 := by linarith
    have hq2 : q^2 ≤ 1 := by nlinarith [mul_nonneg hq (sub_nonneg.mpr hq1')]
    have hp1 : p ≤ 1/9 := by nlinarith
    have hqp : q*p ≤ 1/9 := by nlinarith [mul_nonneg (sub_nonneg.mpr hq1') hp]
    have hq2p : q^2*p ≤ 1/9 := by nlinarith [mul_nonneg (sub_nonneg.mpr hq2) hp]
    have hq4 : q^4 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hq2) (show 0 ≤ 1+q^2 by positivity)]
    have hqcube : 0 ≤ q^3 := by positivity
    nlinarith [sq_nonneg p]

lemma lw_23175_aux2 (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hs : u^2+v^2+w^2 ≤ 21)
    (hc : ((36-(u^2+v^2+w^2))^2 - 4*(u^2*v^2+v^2*w^2+w^2*u^2))^2 ≤
      2304*(u*v*w)^2) : 6 ≤ u+v+w := by
  let t := u+v+w
  let s := u^2+v^2+w^2
  let r := u*v+v*w+w*u
  let A := (36-s)^2-4*(u^2*v^2+v^2*w^2+w^2*u^2)
  have hprod : 0 ≤ u*v*w := mul_nonneg (mul_nonneg hu hv) hw
  have hA : A ≤ 48*(u*v*w) := by
    change A^2 ≤ 2304*(u*v*w)^2 at hc
    nlinarith
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hm : 9*(u*v*w) ≤ r*t := by
    dsimp [r,t]
    nlinarith [mul_nonneg hu (sq_nonneg (v-w)), mul_nonneg hv (sq_nonneg (w-u)),
      mul_nonneg hw (sq_nonneg (u-v))]
  by_contra h
  have ht6 : t < 6 := by dsimp [t]; linarith
  let D := (6+t)*(36-s+2*r)-8*(u*v*w)
  have hmain : 0 < (6+t)*(36-s) := mul_pos (by linarith) (by dsimp [s]; linarith)
  have hD : 0 < D := by dsimp only [D]; nlinarith
  have hid : A-48*(u*v*w) = (6-t)*D := by dsimp [A,D,t,s,r]; ring
  have hpos := mul_pos (show 0 < 6-t by linarith) hD
  linarith

theorem lw_23175 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hab : a + b + c = 3) :
    6 ≤ Real.sqrt (2 * a ^ 2 + b * c + 1) + Real.sqrt (2 * b ^ 2 + c * a + 1) +
      Real.sqrt (2 * c ^ 2 + a * b + 1) := by
  let q := a*b+b*c+c*a
  let p := a*b*c
  let X := 2*a^2+b*c+1
  let Y := 2*b^2+c*a+1
  let Z := 2*c^2+a*b+1
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hsum : (a+b+c)^2 = 9 := by rw [hab]; norm_num
  have hq3 : q ≤ 3 := by
    dsimp [q]
    nlinarith [sq_nonneg (a-b), sq_nonneg (b-c), sq_nonneg (c-a)]
  have hmul : (a+b+c)*(a*b*c) = 3*(a*b*c) := by rw [hab]
  have hpq : 9*p ≤ q^2 := by
    dsimp [p,q]
    nlinarith [sq_nonneg (a*b-b*c), sq_nonneg (b*c-c*a), sq_nonneg (c*a-a*b)]
  have hceq : c = 3-a-b := by linarith
  have hS : X+Y+Z = 21-3*q := by dsimp [X,Y,Z,q]; rw [hceq]; ring
  have hT : X*Y+Y*Z+Z*X = 39-27*p+12*q := by dsimp [X,Y,Z,q,p]; rw [hceq]; ring
  have hP : X*Y*Z = 19+27*p+27*p^2+15*q-54*q*p+4*q^3 := by
    dsimp [X,Y,Z,q,p]; rw [hceq]; ring
  have hcert := lw_23175_aux1 q p hq hq3 hp hpq
  have hpoly : ((36-(X+Y+Z))^2-4*(X*Y+Y*Z+Z*X))^2 ≤ 2304*(X*Y*Z) := by
    rw [hS,hT,hP]
    nlinarith only [hcert]
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hu := Real.sq_sqrt hX
  have hv := Real.sq_sqrt hY
  have hw := Real.sq_sqrt hZ
  apply lw_23175_aux2 (Real.sqrt X) (Real.sqrt Y) (Real.sqrt Z)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · rw [hu,hv,hw,hS]; linarith
  · simpa only [mul_pow, hu, hv, hw] using hpoly
end

-- forge:entry lw_25858 kind=proved origin=external
section
/- Prove that $(a^2-ab+b^2)(b^2-bc+c^2)(c^2-ca+a^2) \leq 8$ for non-negative real numbers $a, b, c$ with $a^2+b^2+c^2=2$. -/
theorem lw_25858 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hab : a^2 + b^2 + c^2 = 2) :
    (a^2 - a * b + b^2) * (b^2 - b * c + c^2) * (c^2 - c * a + a^2) ≤ 8 := by
  have h₁ : a^2 - a * b + b^2 ≤ 2 := by
    nlinarith [mul_nonneg ha hb, sq_nonneg c]
  have h₂ : b^2 - b * c + c^2 ≤ 2 := by
    nlinarith [mul_nonneg hb hc, sq_nonneg a]
  have h₃ : c^2 - c * a + a^2 ≤ 2 := by
    nlinarith [mul_nonneg hc ha, sq_nonneg b]
  have h₂0 : 0 ≤ b^2 - b * c + c^2 := by
    nlinarith [sq_nonneg (b - c), sq_nonneg b, sq_nonneg c]
  have h₃0 : 0 ≤ c^2 - c * a + a^2 := by
    nlinarith [sq_nonneg (c - a), sq_nonneg c, sq_nonneg a]
  have h₁₂ : (a^2 - a * b + b^2) * (b^2 - b * c + c^2) ≤ (2 : ℝ) * 2 :=
    mul_le_mul h₁ h₂ h₂0 (by norm_num)
  calc
    _ ≤ ((2 : ℝ) * 2) * 2 := mul_le_mul h₁₂ h₃ h₃0 (by norm_num)
    _ = 8 := by norm_num
end

-- forge:entry lw_148 kind=proved origin=external
section
/- Let $a,b,c\ge 0, ab+bc+ca>0$ . Prove that : $$\frac{a(a-b)}{a+b}+\frac{b(b-c)}{b+c}+\frac{c(c-a)}{c+a}+\frac{3abc}{ab+bc+ca}\ge \frac{a^2+b^2+c^2}{a+b+c}$$ -/
lemma lw_148_aux1 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ (a + b + c) ^ 2 * (a * b + b * c + c * a) -
      2 * (a * b + b * c + c * a) ^ 2 - 3 * (a + b + c) * a * b * c := by
  have h₁ : 0 ≤ (a + b + c) ^ 2 - 3 * (a * b + b * c + c * a) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have h₂ : 0 ≤ (a * b + b * c + c * a) ^ 2 - 3 * (a + b + c) * a * b * c := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a),
      sq_nonneg (c * a - a * b)]
  have hq : 0 ≤ a * b + b * c + c * a := by positivity
  nlinarith [mul_nonneg hq h₁]

lemma lw_148_aux2 (a b c : ℝ)
    (hab : a + b ≠ 0) (hbc : b + c ≠ 0) (hca : c + a ≠ 0)
    (hs : a + b + c ≠ 0) (hq : a * b + b * c + c * a ≠ 0) :
    a * (a - b) / (a + b) + b * (b - c) / (b + c) +
      c * (c - a) / (c + a) + 3 * a * b * c / (a * b + b * c + c * a) -
      (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) =
    a * b * c * ((a + b + c) ^ 2 * (a * b + b * c + c * a) -
      2 * (a * b + b * c + c * a) ^ 2 - 3 * (a + b + c) * a * b * c) /
      ((a + b + c) * (a * b + b * c + c * a) * (a + b) * (b + c) * (c + a)) := by
  generalize heq : a * b + b * c + c * a = q at *
  field_simp [hab, hbc, hca, hs, hq]
  subst q
  ring

theorem lw_148 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hab : a * b + b * c + c * a > 0) :
    (a * (a - b) / (a + b) + b * (b - c) / (b + c) + c * (c - a) / (c + a) +
      3 * a * b * c / (a * b + b * c + c * a)) ≥
      (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) := by
  have habp : 0 < a + b := by
    by_contra! h
    have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0] at hab
  have hbcp : 0 < b + c := by
    by_contra! h
    have hb0 : b = 0 := by linarith
    have hc0 : c = 0 := by linarith
    simp [hb0, hc0] at hab
  have hcap : 0 < c + a := by
    by_contra! h
    have hc0 : c = 0 := by linarith
    have ha0 : a = 0 := by linarith
    simp [hc0, ha0] at hab
  have hs : 0 < a + b + c := by linarith
  apply sub_nonneg.mp
  rw [lw_148_aux2 a b c (ne_of_gt habp) (ne_of_gt hbcp) (ne_of_gt hcap)
    (ne_of_gt hs) (ne_of_gt hab)]
  exact div_nonneg (mul_nonneg (by positivity) (lw_148_aux1 a b c ha hb hc))
    (by positivity)
end

-- forge:entry lw_27428 kind=proved origin=external
section
/- Let $a,b $ be real numbers such that $(\sqrt{a^2-2a+2}+a-1)(\sqrt{b^2-4b+8}+b-2)=2$ . Prove that: $a^2+b^2\ge\frac{16}{5}.$ -/
lemma lw_27428_aux1 (x y s t k : ℝ) (hk : k ≠ 0)
    (hs : s ^ 2 - x ^ 2 = 1) (ht : t ^ 2 - y ^ 2 = k ^ 2)
    (h : (s + x) * (t + y) = k) : k * x + y = 0 := by
  have hprod : (s + x) * (s - x) = 1 := by nlinarith
  have hp : s + x ≠ 0 := by
    intro hp
    rw [hp, zero_mul] at hprod
    norm_num at hprod
  have hq : t + y ≠ 0 := by
    intro hq
    rw [hq, mul_zero] at h
    exact hk h.symm
  have hqeq : t + y = k * (s - x) := by
    apply mul_left_cancel₀ hp
    calc
      (s + x) * (t + y) = k := h
      _ = k * ((s + x) * (s - x)) := by rw [hprod, mul_one]
      _ = (s + x) * (k * (s - x)) := by ring
  have hueq : t - y = k * (s + x) := by
    apply mul_left_cancel₀ hq
    calc
      (t + y) * (t - y) = k ^ 2 := by nlinarith
      _ = k * ((s + x) * (t + y)) := by rw [h]; ring
      _ = (t + y) * (k * (s + x)) := by ring
  nlinarith [hqeq, hueq]

theorem lw_27428 (a b : ℝ)
    (h : (Real.sqrt (a ^ 2 - 2 * a + 2) + a - 1) *
      (Real.sqrt (b ^ 2 - 4 * b + 8) + b - 2) = 2) :
    a ^ 2 + b ^ 2 ≥ 16 / 5 := by
  have ha : 0 ≤ a ^ 2 - 2 * a + 2 := by nlinarith [sq_nonneg (a - 1)]
  have hb : 0 ≤ b ^ 2 - 4 * b + 8 := by nlinarith [sq_nonneg (b - 2)]
  have hs := Real.sq_sqrt ha
  have ht := Real.sq_sqrt hb
  have hlin : 2 * (a - 1) + (b - 2) = 0 := by
    apply lw_27428_aux1 (a - 1) (b - 2)
      (Real.sqrt (a ^ 2 - 2 * a + 2))
      (Real.sqrt (b ^ 2 - 4 * b + 8)) 2
    · norm_num
    · nlinarith [hs]
    · nlinarith [ht]
    · convert h using 1 <;> ring
  nlinarith [sq_nonneg (a - 2 * b)]
end

-- forge:entry lw_2629 kind=proved origin=external
section
/- By C-S and AM-GM，we have \n\n $\frac{3}{2}\sqrt{(x^2+y^2)(w^2+z^2)}+\sqrt{(x^2+w^2)(y^2+z^2)-3xyzw}-(x+z)(y+w)$ \n\n $\ge{\frac{3}{2}(wx+yz)}+\sqrt{(xy+wz)^2-3xyzw}-(x+z)(y+w)$ \n\n $=\frac{1}{2}(wx+yz)+\sqrt{x^2y^2-xyzw+w^2z^2}-(wz+xy)$ \n\n $\ge{\sqrt{xyzw}+\sqrt{x^2y^2-xyzw+w^2z^2}-(wz+xy)}$ \n\n $=\sqrt{ab}+\sqrt{a^2-ab+b^2}-(a+b)\ge{0}$ \n\n Where $a=xy,b=wz$ -/
lemma lw_2629_aux1 (a b t p : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : 4 * p ≤ a ^ 2) (ht : 4 * p ≤ t ^ 2)
    (hb2 : t ^ 2 - 3 * p ≤ b ^ 2) : t ≤ a / 2 + b := by
  by_cases hat : t ≤ a
  · have htb : t ≤ 2 * b := by
      nlinarith
    linarith
  · have hat' : a ≤ t := by linarith
    have hs : (t - a / 2) ^ 2 ≤ b ^ 2 := by
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hat')]
    have ht0 : 0 ≤ t - a / 2 := by linarith
    have h := (sq_le_sq₀ ht0 hb).mp hs
    linarith

theorem lw_2629 {x y z w : ℝ} :
    (3 / 2 * Real.sqrt ((x ^ 2 + y ^ 2) * (w ^ 2 + z ^ 2)) +
      Real.sqrt ((x ^ 2 + w ^ 2) * (y ^ 2 + z ^ 2) - 3 * x * y * z * w) -
      (x + z) * (y + w)) ≥ 0 := by
  let a := Real.sqrt ((x ^ 2 + y ^ 2) * (w ^ 2 + z ^ 2))
  let b := Real.sqrt ((x ^ 2 + w ^ 2) * (y ^ 2 + z ^ 2) - 3 * x * y * z * w)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = (x ^ 2 + y ^ 2) * (w ^ 2 + z ^ 2) := by
    apply Real.sq_sqrt
    positivity
  have hr : 0 ≤ (x ^ 2 + w ^ 2) * (y ^ 2 + z ^ 2) - 3 * x * y * z * w := by
    nlinarith [sq_nonneg (x * y - w * z), sq_nonneg (x * y + w * z),
      sq_nonneg (x * z - y * w)]
  have hb2 : b ^ 2 = (x ^ 2 + w ^ 2) * (y ^ 2 + z ^ 2) - 3 * x * y * z * w :=
    Real.sq_sqrt hr
  have hA : x * w + y * z ≤ a := by
    nlinarith [sq_nonneg (x * z - y * w)]
  have hp : 4 * (x * y * z * w) ≤ a ^ 2 := by
    nlinarith [sq_nonneg (x * w - y * z), sq_nonneg (x * z - y * w)]
  have ht : 4 * (x * y * z * w) ≤ (x * y + w * z) ^ 2 := by
    nlinarith [sq_nonneg (x * y - w * z)]
  have hbt : (x * y + w * z) ^ 2 - 3 * (x * y * z * w) ≤ b ^ 2 := by
    nlinarith [sq_nonneg (x * z - y * w)]
  have hmain := lw_2629_aux1 a b (x * y + w * z) (x * y * z * w) ha hb hp ht hbt
  change 0 ≤ 3 / 2 * a + b - (x + z) * (y + w)
  nlinarith only [hA, hmain]
end

-- forge:entry lw_33543 kind=disproved origin=external
section
/- prove that \n $ \frac{a(b+c)}{a^{2} + bc}+ \frac{b(c+a)}{b^{2} + ca}+\frac{c(a+b)}{c^{2} + ab}\geq 2+\frac{abc(a+b)(b+c)(c+a)}{(a^2+bc)(b^2+ca)(c^2+ab)}$ -/
theorem lw_33543_disproof : ¬ (∀ (a b c : ℝ),
    (a * (b + c) / (a ^ 2 + b * c) +
      b * (c + a) / (b ^ 2 + c * a) +
      c * (a + b) / (c ^ 2 + a * b) ≥
      2 + a * b * c * (a + b) * (b + c) * (c + a) /
        ((a ^ 2 + b * c) * (b ^ 2 + c * a) * (c ^ 2 + a * b)))) := by
  intro h
  have h0 := h 0 0 0
  norm_num at h0
end

-- forge:entry lw_33218 kind=proved origin=external
section
/- $9|n^2$ iff $3|n$ . $n$ is not necessarily a multiple of 9. -/
theorem lw_33218 (n : ℤ) : 9 ∣ n^2 ↔ 3 ∣ n := by
  constructor
  · intro h
    have hp : Prime (3 : ℤ) := by
      rw [Int.prime_iff_natAbs_prime]
      norm_num
    exact hp.dvd_of_dvd_pow (dvd_trans (by norm_num : (3 : ℤ) ∣ 9) h)
  · rintro ⟨k, rfl⟩
    refine ⟨k ^ 2, ?_⟩
    ring
end

-- forge:entry lw_38393 kind=disproved origin=external
section
/- Prove $(x+y)(x^2 + y^2) + 2 \ge (x+y)$ given $x^2 + y^2 \ge 0$. -/
theorem lw_38393_disproof :
    ¬ (∀ (x y : ℝ) (h : x ^ 2 + y ^ 2 ≥ 0),
      (x + y) * (x ^ 2 + y ^ 2) + 2 ≥ x + y) := by
  intro hall
  have hfalse := hall (-2) 0 (by norm_num)
  norm_num at hfalse
end

-- forge:entry lw_28724 kind=proved origin=external
section
/- Let a,b,c >0 and $ ab + bc + ca = 1$ . Prove that:\n$ \sqrt {a^2 + \frac{1}{{bc}}} + \sqrt {b^2 + \frac{1}{{ca}}} + \sqrt {c^2 + \frac{1}{{ab}}} \ge \sqrt {30}$ -/
lemma lw_28724_aux1 (x : ℝ) (hx : 0 < x) :
    3 * Real.sqrt 3 - 3 * Real.sqrt 3 * x ^ 2 ≤ 2 / x := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hc : (Real.sqrt 3) ^ 3 = 3 * Real.sqrt 3 := by
    calc
      _ = Real.sqrt 3 * (Real.sqrt 3) ^ 2 := by ring
      _ = _ := by rw [hs]; ring
  have hp : 0 ≤ (Real.sqrt 3 * x - 1) ^ 2 * (Real.sqrt 3 * x + 2) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  have hp' : 0 ≤ (Real.sqrt 3 * x) ^ 3 - 3 * (Real.sqrt 3 * x) + 2 := by
    nlinarith only [hp]
  rw [mul_pow, hc] at hp'
  apply (le_div_iff₀ hx).2
  nlinarith only [hp']

lemma lw_28724_aux2 (a x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    a + 3 * x ≤ Real.sqrt 10 * Real.sqrt (a ^ 2 + x ^ 2) := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by positivity)]
  nlinarith [sq_nonneg (3 * a - x)]

theorem lw_28724 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a * b + b * c + c * a = 1) :
    Real.sqrt (a^2 + 1 / (b * c)) + Real.sqrt (b^2 + 1 / (c * a)) +
      Real.sqrt (c^2 + 1 / (a * b)) ≥ Real.sqrt 30 := by
  have hp : 0 < Real.sqrt (b * c) := Real.sqrt_pos.2 (mul_pos hb hc)
  have hq : 0 < Real.sqrt (c * a) := Real.sqrt_pos.2 (mul_pos hc ha)
  have hr : 0 < Real.sqrt (a * b) := Real.sqrt_pos.2 (mul_pos ha hb)
  have hs : 3 * Real.sqrt 3 ≤
      1 / Real.sqrt (b * c) + 1 / Real.sqrt (c * a) + 1 / Real.sqrt (a * b) := by
    have h₁ := lw_28724_aux1 _ hp
    have h₂ := lw_28724_aux1 _ hq
    have h₃ := lw_28724_aux1 _ hr
    rw [Real.sq_sqrt (le_of_lt (mul_pos hb hc))] at h₁
    rw [Real.sq_sqrt (le_of_lt (mul_pos hc ha))] at h₂
    rw [Real.sq_sqrt (le_of_lt (mul_pos ha hb))] at h₃
    have he : 3 * Real.sqrt 3 * (a * b + b * c + c * a) = 3 * Real.sqrt 3 := by
      rw [hab, mul_one]
    simp only [div_eq_mul_inv, one_mul] at h₁ h₂ h₃ ⊢
    nlinarith only [h₁, h₂, h₃, he]
  have ht : Real.sqrt 3 ≤ a + b + c := by
    have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have hnonneg := Real.sqrt_nonneg (3 : ℝ)
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have h₁ := lw_28724_aux2 a (1 / Real.sqrt (b * c)) (le_of_lt ha) (by positivity)
  have h₂ := lw_28724_aux2 b (1 / Real.sqrt (c * a)) (le_of_lt hb) (by positivity)
  have h₃ := lw_28724_aux2 c (1 / Real.sqrt (a * b)) (le_of_lt hc) (by positivity)
  rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt (mul_pos hb hc))] at h₁
  rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt (mul_pos hc ha))] at h₂
  rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt (mul_pos ha hb))] at h₃
  have he : Real.sqrt 10 * Real.sqrt 30 = 10 * Real.sqrt 3 := by
    calc
      _ = Real.sqrt (100 * 3) := by
        rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 10 by norm_num)]
        norm_num
      _ = Real.sqrt 100 * Real.sqrt 3 := Real.sqrt_mul (by norm_num) _
      _ = _ := by norm_num
  have hten : 0 < Real.sqrt (10 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  apply (mul_le_mul_iff_of_pos_left hten).mp
  nlinarith only [h₁, h₂, h₃, hs, ht, he]
end

-- forge:entry lw_37157 kind=proved origin=external
section
/- Let $a, b, c, d > 0$ with $abcd = 1$ . Prove that \n\n $\dfrac{1}{a(1+b)} +$ $\dfrac{1}{b(1+c)} +$ $\dfrac{1}{c(1+d)} +$ $\dfrac{1}{d(1+a)} \ge 2$ -/
lemma lw_37157_aux1 (x u t : ℝ) (hx : 0 ≤ x) (hu : 0 < u) :
    4 * x * (t - u) ≤ x / u * t ^ 2 := by
  rw [div_mul_eq_mul_div, le_div_iff₀ hu]
  nlinarith only [mul_nonneg hx (sq_nonneg (t - 2 * u))]

lemma lw_37157_aux2 (x y z w : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hw : 0 < w) :
    2 ≤ x / (y + z) + y / (z + w) + z / (w + x) + w / (x + y) := by
  let t := x + y + z + w
  let D := x * (y + z) + y * (z + w) + z * (w + x) + w * (x + y)
  have h1 := lw_37157_aux1 x (y + z) t (le_of_lt hx) (by positivity)
  have h2 := lw_37157_aux1 y (z + w) t (le_of_lt hy) (by positivity)
  have h3 := lw_37157_aux1 z (w + x) t (le_of_lt hz) (by positivity)
  have h4 := lw_37157_aux1 w (x + y) t (le_of_lt hw) (by positivity)
  have hs : 4 * t ^ 2 - 4 * D ≤
      (x / (y + z) + y / (z + w) + z / (w + x) + w / (x + y)) * t ^ 2 := by
    dsimp [t, D] at *
    nlinarith only [h1, h2, h3, h4]
  have hD : 2 * D ≤ t ^ 2 := by
    dsimp [D, t]
    nlinarith only [sq_nonneg (x - z), sq_nonneg (y - w)]
  have ht : 0 < t ^ 2 := by dsimp [t]; positivity
  apply (mul_le_mul_iff_of_pos_right ht).mp
  linarith only [hs, hD]

theorem lw_37157 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (habcd : a * b * c * d = 1) :
    1 / (a * (1 + b)) + 1 / (b * (1 + c)) + 1 / (c * (1 + d)) +
      1 / (d * (1 + a)) ≥ 2 := by
  have h := lw_37157_aux2 1 a (a * b) (a * b * c)
    (by norm_num) ha (by positivity) (by positivity)
  have h1 : 1 / (a + a * b) = 1 / (a * (1 + b)) := by
    congr 1 <;> ring
  have h2 : a / (a * b + a * b * c) = 1 / (b * (1 + c)) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).2
    ring
  have h3 : a * b / (a * b * c + 1) = 1 / (c * (1 + d)) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).2
    nlinarith only [habcd]
  have h4 : a * b * c / (1 + a) = 1 / (d * (1 + a)) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).2
    nlinarith only [habcd, congrArg (fun x : ℝ => a * x) habcd]
  norm_num only [one_mul] at h
  rw [h1, h2, h3, h4] at h
  exact h
end

-- forge:entry lw_41705 kind=proved origin=external
section
/- Prove that if $a,b,c >0$ ,then $(\frac{a}{b}+\frac{b}{c}+\frac{c}{a})^{2} \ge 3(\frac{a}{c}+\frac{c}{b}+\frac{b}{a})$ -/
lemma lw_41705_aux1 (x y z : ℝ) :
    3 * (x * y + z * x + y * z) ≤ (x + y + z) ^ 2 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]

theorem lw_41705 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a / b + b / c + c / a) ^ 2 ≥ 3 * (a / c + c / b + b / a) := by
  simpa only [div_mul_div_cancel₀ (ne_of_gt ha),
    div_mul_div_cancel₀ (ne_of_gt hb), div_mul_div_cancel₀ (ne_of_gt hc)] using
    lw_41705_aux1 (a / b) (b / c) (c / a)
end

-- forge:entry lw_42145 kind=disproved origin=external
section
/- If $ 3\not|n$ , then $ \gcd(3,n) = 1$ , and so by Fermat's Little Theorem, $ 3^n\equiv 3\pmod n$ , so $ n\not|3^n - 1$ . -/
theorem lw_42145_disproof : ¬ (∀ {n : ℕ}, (¬ 3 ∣ n) → ¬ n ∣ 3 ^ n - 1) := by
  intro h
  have hn : ¬ (3 : ℕ) ∣ 2 := by norm_num
  have hd : (2 : ℕ) ∣ 3 ^ 2 - 1 := by norm_num
  exact h hn hd
end

-- forge:entry lw_4151 kind=proved origin=external
section
/- For $a, b, c>0, abc=1$ prove that $\frac{a^3}{2a^3+b^3+1}+\frac{b^3}{2b^3+c^3+1}+\frac{c^3}{2c^3+a^3+1}\le\frac{(a^2+b^2+c^2)^2}{12}$ -/
lemma lw_4151_aux1 (x y z : ℝ) (hz : 0 ≤ z) (hzx : z ≤ x) (hzy : z ≤ y) :
    0 ≤ (x+y+z) * ((2*x+y+1)*(2*y+z+1)*(2*z+x+1)) -
      (x+y+z+1) * (x*(2*y+z+1)*(2*z+x+1) +
        y*(2*z+x+1)*(2*x+y+1) + z*(2*x+y+1)*(2*y+z+1)) := by
  rcases le_total y x with h | h
  · have hu : 0 ≤ x-y := sub_nonneg.mpr h
    have hv : 0 ≤ y-z := sub_nonneg.mpr hzy
    have hp : 0 ≤
        (y-z)^2 + 4*(y-z)^2*z + 3*(y-z)^2*z^2 +
        3*(y-z)^3 + 5*(y-z)^3*z + 2*(y-z)^4 +
        (x-y)*(y-z) + 4*(x-y)*(y-z)*z + 3*(x-y)*(y-z)*z^2 +
        3*(x-y)*(y-z)^2 + 6*(x-y)*(y-z)^2*z + 3*(x-y)*(y-z)^3 +
        (x-y)^2 + 4*(x-y)^2*z + 3*(x-y)^2*z^2 +
        2*(x-y)^2*(y-z) + 3*(x-y)^2*(y-z)*z + (x-y)^2*(y-z)^2 +
        (x-y)^3 + (x-y)^3*z := by positivity
    convert hp using 1 <;> ring
  · have hu : 0 ≤ y-x := sub_nonneg.mpr h
    have hv : 0 ≤ x-z := sub_nonneg.mpr hzx
    have hp : 0 ≤
        (x-z)^2 + 4*(x-z)^2*z + 3*(x-z)^2*z^2 +
        3*(x-z)^3 + 5*(x-z)^3*z + 2*(x-z)^4 +
        (y-x)*(x-z) + 4*(y-x)*(x-z)*z + 3*(y-x)*(x-z)*z^2 +
        6*(y-x)*(x-z)^2 + 9*(y-x)*(x-z)^2*z + 5*(y-x)*(x-z)^3 +
        (y-x)^2 + 4*(y-x)^2*z + 3*(y-x)^2*z^2 +
        5*(y-x)^2*(x-z) + 6*(y-x)^2*(x-z)*z + 4*(y-x)^2*(x-z)^2 +
        (y-x)^3 + (y-x)^3*z + (y-x)^3*(x-z) := by positivity
    convert hp using 1 <;> ring

lemma lw_4151_aux2 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ (x+y+z) * ((2*x+y+1)*(2*y+z+1)*(2*z+x+1)) -
      (x+y+z+1) * (x*(2*y+z+1)*(2*z+x+1) +
        y*(2*z+x+1)*(2*x+y+1) + z*(2*x+y+1)*(2*y+z+1)) := by
  by_cases hxy : x ≤ y
  · by_cases hxz : x ≤ z
    · have h := lw_4151_aux1 y z x hx hxy hxz
      convert h using 1 <;> ring
    · exact lw_4151_aux1 x y z hz (le_of_not_ge hxz) (le_trans (le_of_not_ge hxz) hxy)
  · by_cases hyz : y ≤ z
    · have h := lw_4151_aux1 z x y hy hyz (le_of_not_ge hxy)
      convert h using 1 <;> ring
    · exact lw_4151_aux1 x y z hz (le_trans (le_of_not_ge hyz) (le_of_not_ge hxy)) (le_of_not_ge hyz)

lemma lw_4151_aux3 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x/(2*x+y+1) + y/(2*y+z+1) + z/(2*z+x+1) ≤ (x+y+z)/(x+y+z+1) := by
  have hd1 : 0 < 2*x+y+1 := by positivity
  have hd2 : 0 < 2*y+z+1 := by positivity
  have hd3 : 0 < 2*z+x+1 := by positivity
  have hs : 0 < x+y+z+1 := by positivity
  have hp := lw_4151_aux2 x y z hx hy hz
  have he : (x+y+z)/(x+y+z+1) -
      (x/(2*x+y+1) + y/(2*y+z+1) + z/(2*z+x+1)) =
      ((x+y+z) * ((2*x+y+1)*(2*y+z+1)*(2*z+x+1)) -
      (x+y+z+1) * (x*(2*y+z+1)*(2*z+x+1) +
        y*(2*z+x+1)*(2*x+y+1) + z*(2*x+y+1)*(2*y+z+1))) /
      ((2*x+y+1)*(2*y+z+1)*(2*z+x+1)*(x+y+z+1)) := by
    field_simp
    <;> ring
  have hn : 0 ≤ (x+y+z)/(x+y+z+1) -
      (x/(2*x+y+1) + y/(2*y+z+1) + z/(2*z+x+1)) := by
    rw [he]
    exact div_nonneg hp (by positivity)
  linarith

lemma lw_4151_aux4 (a : ℝ) (ha : 0 ≤ a) : 4*a^3 - 1 ≤ 3*a^4 := by
  have h : 0 ≤ (a-1)^2*(3*a^2+2*a+1) := by positivity
  nlinarith only [h]

theorem lw_4151 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a^3 / (2 * a^3 + b^3 + 1) + b^3 / (2 * b^3 + c^3 + 1) +
      c^3 / (2 * c^3 + a^3 + 1)) ≤ (a^2 + b^2 + c^2)^2 / 12 := by
  have hprod3 : a^3*b^3*c^3 = 1 := by
    calc
      _ = (a*b*c)^3 := by ring
      _ = 1 := by rw [habc]; norm_num
  have hT : 3 ≤ a^3+b^3+c^3 :=
    lw_55543_aux1 _ _ _ (by positivity) (by positivity) (by positivity) hprod3
  have hprod2 : (a*b)^2*(b*c)^2*(c*a)^2 = 1 := by
    calc
      _ = (a*b*c)^4 := by ring
      _ = 1 := by rw [habc]; norm_num
  have hQ : 3 ≤ (a*b)^2+(b*c)^2+(c*a)^2 :=
    lw_55543_aux1 _ _ _ (by positivity) (by positivity) (by positivity) hprod2
  have h4 : a^3+b^3+c^3 ≤ a^4+b^4+c^4 := by
    have h1 := lw_4151_aux4 a ha.le
    have h2 := lw_4151_aux4 b hb.le
    have h3 := lw_4151_aux4 c hc.le
    linarith
  have hS : a^3+b^3+c^3+6 ≤ (a^2+b^2+c^2)^2 := by
    nlinarith only [hQ, h4]
  have hrat : (a^3+b^3+c^3)/(a^3+b^3+c^3+1) ≤ (a^3+b^3+c^3+6)/12 := by
    apply (div_le_iff₀ (by positivity : 0 < a^3+b^3+c^3+1)).2
    have h : 0 ≤ (a^3+b^3+c^3-2)*(a^3+b^3+c^3-3) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith only [h]
  exact (lw_4151_aux3 (a^3) (b^3) (c^3) (by positivity) (by positivity) (by positivity)).trans
    (hrat.trans (by linarith))
end

-- forge:entry lw_43521 kind=disproved origin=external
section
/- $\log_2 x\log_3 x\log_4x = 2(\log_2x\log_3x+\log_3\log_4x+\log_2x\log_4x)$ \n\nThis leads to $$1=2(\frac{1}{\log_2 x}+\frac{1}{\log_3 x}+\frac{1}{\log_4 x})=2(\log_x 2+\log_x 3+\log_x 4)=2\log_x 24$$ \n\nThis gives $\frac{1}{2}=\log_x 24\to x=\boxed{576}$ . -/
theorem lw_43521_disproof :
    ¬ (∀ (x : ℝ) (h₀ : 0 < x)
      (h₁ : Real.logb 2 x * Real.logb 3 x * Real.logb 4 x =
        2 * (Real.logb 2 x * Real.logb 3 x +
          Real.logb 3 x * Real.logb 4 x + Real.logb 2 x * Real.logb 4 x)),
      x = 576) := by
  intro h
  have hx : (1 : ℝ) = 576 := h 1 (by norm_num) (by simp [Real.logb])
  norm_num at hx
end

-- forge:entry lw_40072 kind=proved origin=external
section
/- I think the similar inequality also holds: \n\nIf $ a,$ $ b,$ $ c,$ $ p$ are positive real numbers, then \n $ \frac{a^2-bc}{pa^2+p^2b^2+c^2}+\frac{b^2-ca}{pb^2+p^2c^2+a^2}+\frac{c^2-ab}{pc^2+p^2a^2+b^2} \ge 0.$ -/
lemma lw_40072_aux1 (x y z t : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) :
    0 ≤ ((x)^2 - (x + y) * (x + y + z)) * ((t + 1) * (x + y)^2 + (t + 1)^2 * (x + y + z)^2 + (x)^2) * ((t + 1) * (x + y + z)^2 + (t + 1)^2 * (x)^2 + (x + y)^2) +
    ((x + y)^2 - (x + y + z) * (x)) * ((t + 1) * (x + y + z)^2 + (t + 1)^2 * (x)^2 + (x + y)^2) * ((t + 1) * (x)^2 + (t + 1)^2 * (x + y)^2 + (x + y + z)^2) +
    ((x + y + z)^2 - (x) * (x + y)) * ((t + 1) * (x)^2 + (t + 1)^2 * (x + y)^2 + (x + y + z)^2) * ((t + 1) * (x + y)^2 + (t + 1)^2 * (x + y + z)^2 + (x)^2) := by
  have h : 0 ≤ 2 * (((x)^2 - (x + y) * (x + y + z)) * ((t + 1) * (x + y)^2 + (t + 1)^2 * (x + y + z)^2 + (x)^2) * ((t + 1) * (x + y + z)^2 + (t + 1)^2 * (x)^2 + (x + y)^2) +
    ((x + y)^2 - (x + y + z) * (x)) * ((t + 1) * (x + y + z)^2 + (t + 1)^2 * (x)^2 + (x + y)^2) * ((t + 1) * (x)^2 + (t + 1)^2 * (x + y)^2 + (x + y + z)^2) +
    ((x + y + z)^2 - (x) * (x + y)) * ((t + 1) * (x)^2 + (t + 1)^2 * (x + y)^2 + (x + y + z)^2) * ((t + 1) * (x + y)^2 + (t + 1)^2 * (x + y + z)^2 + (x)^2)) := by
    calc
      0 ≤ z ^ 4 * t ^ 2 * (t * (x + y) - z) ^ 2 +
        z ^ 4 * t ^ 2 * (x + y) ^ 2 * (t - 1) ^ 2 +
          (x ^ 4 * (y ^ 2 * (t ^ 4 * (6) + t ^ 3 * (24) + t ^ 2 * (42) + t * (36) + 18) + y * (z * (t ^ 4 * (6) + t ^ 3 * (24) + t ^ 2 * (42) + t * (36) + 18)) + z ^ 2 * (t ^ 4 * (6) + t ^ 3 * (24) + t ^ 2 * (42) + t * (36) + 18)) + x ^ 3 * (y ^ 3 * (t ^ 4 * (18) + t ^ 3 * (78) + t ^ 2 * (126) + t * (96) + 48) + y ^ 2 * (z * (t ^ 4 * (36) + t ^ 3 * (126) + t ^ 2 * (162) + t * (126) + 72)) + y * (z ^ 2 * (t ^ 4 * (30) + t ^ 3 * (84) + t ^ 2 * (120) + t * (126) + 72)) + z ^ 3 * (t ^ 4 * (6) + t ^ 3 * (18) + t ^ 2 * (42) + t * (48) + 24)) + x ^ 2 * (y ^ 4 * (t ^ 4 * (20) + t ^ 3 * (92) + t ^ 2 * (148) + t * (112) + 56) + y ^ 3 * (z * (t ^ 4 * (58) + t ^ 3 * (202) + t ^ 2 * (242) + t * (188) + 112)) + y ^ 2 * (z ^ 2 * (t ^ 4 * (60) + t ^ 3 * (150) + t ^ 2 * (174) + t * (210) + 132)) + y * (z ^ 3 * (t ^ 4 * (22) + t ^ 3 * (40) + t ^ 2 * (80) + t * (134) + 76)) + z ^ 4 * (t ^ 3 * (4) + t ^ 2 * (21) + t * (40) + 20)) + x * (y ^ 5 * (t ^ 4 * (10) + t ^ 3 * (48) + t ^ 2 * (80) + t * (64) + 32) + y ^ 4 * (z * (t ^ 4 * (36) + t ^ 3 * (128) + t ^ 2 * (158) + t * (132) + 80)) + y ^ 3 * (z ^ 2 * (t ^ 4 * (46) + t ^ 3 * (114) + t ^ 2 * (126) + t * (168) + 112)) + y ^ 2 * (z ^ 3 * (t ^ 4 * (24) + t ^ 3 * (34) + t ^ 2 * (58) + t * (138) + 88)) + y * (z ^ 4 * (t ^ 2 * (20) + t * (70) + 40)) + z ^ 5 * (t ^ 2 * (6) + t * (16) + 8)) + y ^ 6 * (t ^ 4 * (2) + t ^ 3 * (10) + t ^ 2 * (18) + t * (16) + 8) + y ^ 5 * (z * (t ^ 4 * (8) + t ^ 3 * (30) + t ^ 2 * (42) + t * (40) + 24)) + y ^ 4 * (z ^ 2 * (t ^ 4 * (12) + t ^ 3 * (32) + t ^ 2 * (42) + t * (60) + 40)) + y ^ 3 * (z ^ 3 * (t ^ 4 * (8) + t ^ 3 * (12) + t ^ 2 * (24) + t * (60) + 40)) + y ^ 2 * (z ^ 4 * (t ^ 2 * (11) + t * (42) + 26)) + y * (z ^ 5 * (t ^ 2 * (6) + t * (18) + 10)) + z ^ 6 * (t ^ 2 + t * (4) + 2)) := by positivity
      _ = 2 * (((x)^2 - (x + y) * (x + y + z)) * ((t + 1) * (x + y)^2 + (t + 1)^2 * (x + y + z)^2 + (x)^2) * ((t + 1) * (x + y + z)^2 + (t + 1)^2 * (x)^2 + (x + y)^2) +
    ((x + y)^2 - (x + y + z) * (x)) * ((t + 1) * (x + y + z)^2 + (t + 1)^2 * (x)^2 + (x + y)^2) * ((t + 1) * (x)^2 + (t + 1)^2 * (x + y)^2 + (x + y + z)^2) +
    ((x + y + z)^2 - (x) * (x + y)) * ((t + 1) * (x)^2 + (t + 1)^2 * (x + y)^2 + (x + y + z)^2) * ((t + 1) * (x + y)^2 + (t + 1)^2 * (x + y + z)^2 + (x)^2)) := by ring
  linarith only [h]

lemma lw_40072_aux2 (x y z t : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t) :
    0 ≤ ((x)^2 - (x + y + z) * (x + y)) * ((t + 1) * (x + y + z)^2 + (t + 1)^2 * (x + y)^2 + (x)^2) * ((t + 1) * (x + y)^2 + (t + 1)^2 * (x)^2 + (x + y + z)^2) +
    ((x + y + z)^2 - (x + y) * (x)) * ((t + 1) * (x + y)^2 + (t + 1)^2 * (x)^2 + (x + y + z)^2) * ((t + 1) * (x)^2 + (t + 1)^2 * (x + y + z)^2 + (x + y)^2) +
    ((x + y)^2 - (x) * (x + y + z)) * ((t + 1) * (x)^2 + (t + 1)^2 * (x + y + z)^2 + (x + y)^2) * ((t + 1) * (x + y + z)^2 + (t + 1)^2 * (x + y)^2 + (x)^2) := by
  have h : 0 ≤ 2 * (((x)^2 - (x + y + z) * (x + y)) * ((t + 1) * (x + y + z)^2 + (t + 1)^2 * (x + y)^2 + (x)^2) * ((t + 1) * (x + y)^2 + (t + 1)^2 * (x)^2 + (x + y + z)^2) +
    ((x + y + z)^2 - (x + y) * (x)) * ((t + 1) * (x + y)^2 + (t + 1)^2 * (x)^2 + (x + y + z)^2) * ((t + 1) * (x)^2 + (t + 1)^2 * (x + y + z)^2 + (x + y)^2) +
    ((x + y)^2 - (x) * (x + y + z)) * ((t + 1) * (x)^2 + (t + 1)^2 * (x + y + z)^2 + (x + y)^2) * ((t + 1) * (x + y + z)^2 + (t + 1)^2 * (x + y)^2 + (x)^2)) := by
    calc
      0 ≤ z ^ 2 * t ^ 4 * (x * z - y ^ 2) ^ 2 +
        z ^ 4 * t ^ 2 * (t * x - y - z) ^ 2 +
          (x ^ 4 * (y ^ 2 * (t ^ 4 * (6) + t ^ 3 * (24) + t ^ 2 * (42) + t * (36) + 18) + y * (z * (t ^ 4 * (6) + t ^ 3 * (24) + t ^ 2 * (42) + t * (36) + 18)) + z ^ 2 * (t ^ 4 * (6) + t ^ 3 * (24) + t ^ 2 * (42) + t * (36) + 18)) + x ^ 3 * (y ^ 3 * (t ^ 4 * (18) + t ^ 3 * (78) + t ^ 2 * (126) + t * (96) + 48) + y ^ 2 * (z * (t ^ 4 * (18) + t ^ 3 * (108) + t ^ 2 * (216) + t * (162) + 72)) + y * (z ^ 2 * (t ^ 4 * (12) + t ^ 3 * (66) + t ^ 2 * (174) + t * (162) + 72)) + z ^ 3 * (t ^ 4 * (6) + t ^ 3 * (18) + t ^ 2 * (42) + t * (48) + 24)) + x ^ 2 * (y ^ 4 * (t ^ 4 * (20) + t ^ 3 * (92) + t ^ 2 * (148) + t * (112) + 56) + y ^ 3 * (z * (t ^ 4 * (22) + t ^ 3 * (166) + t ^ 2 * (350) + t * (260) + 112)) + y ^ 2 * (z ^ 2 * (t ^ 4 * (6) + t ^ 3 * (96) + t ^ 2 * (336) + t * (318) + 132)) + y * (z ^ 3 * (t ^ 4 * (4) + t ^ 3 * (22) + t ^ 2 * (134) + t * (170) + 76)) + z ^ 4 * (t ^ 3 * (2) + t ^ 2 * (22) + t * (40) + 20)) + x * (y ^ 5 * (t ^ 4 * (10) + t ^ 3 * (48) + t ^ 2 * (80) + t * (64) + 32) + y ^ 4 * (z * (t ^ 4 * (14) + t ^ 3 * (112) + t ^ 2 * (242) + t * (188) + 80)) + y ^ 3 * (z ^ 2 * (t ^ 4 * (2) + t ^ 3 * (82) + t ^ 2 * (294) + t * (280) + 112)) + y ^ 2 * (z ^ 3 * (t ^ 3 * (20) + t ^ 2 * (172) + t * (214) + 88)) + y * (z ^ 4 * (t ^ 2 * (52) + t * (90) + 40)) + z ^ 5 * (t ^ 2 * (6) + t * (16) + 8)) + y ^ 6 * (t ^ 4 * (2) + t ^ 3 * (10) + t ^ 2 * (18) + t * (16) + 8) + y ^ 5 * (z * (t ^ 4 * (4) + t ^ 3 * (30) + t ^ 2 * (66) + t * (56) + 24)) + y ^ 4 * (z ^ 2 * (t ^ 4 + t ^ 3 * (32) + t ^ 2 * (102) + t * (100) + 40)) + y ^ 3 * (z ^ 3 * (t ^ 3 * (16) + t ^ 2 * (84) + t * (100) + 40)) + y ^ 2 * (z ^ 4 * (t ^ 3 * (4) + t ^ 2 * (41) + t * (62) + 26)) + y * (z ^ 5 * (t ^ 2 * (10) + t * (22) + 10)) + z ^ 6 * (t ^ 2 + t * (4) + 2)) := by positivity
      _ = 2 * (((x)^2 - (x + y + z) * (x + y)) * ((t + 1) * (x + y + z)^2 + (t + 1)^2 * (x + y)^2 + (x)^2) * ((t + 1) * (x + y)^2 + (t + 1)^2 * (x)^2 + (x + y + z)^2) +
    ((x + y + z)^2 - (x + y) * (x)) * ((t + 1) * (x + y)^2 + (t + 1)^2 * (x)^2 + (x + y + z)^2) * ((t + 1) * (x)^2 + (t + 1)^2 * (x + y + z)^2 + (x + y)^2) +
    ((x + y)^2 - (x) * (x + y + z)) * ((t + 1) * (x)^2 + (t + 1)^2 * (x + y + z)^2 + (x + y)^2) * ((t + 1) * (x + y + z)^2 + (t + 1)^2 * (x + y)^2 + (x)^2)) := by ring
  linarith only [h]

lemma lw_40072_aux3 (a b c p : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hp : 1 ≤ p) :
    0 ≤ ((a)^2 - (b) * (c)) * ((p) * (b)^2 + (p)^2 * (c)^2 + (a)^2) * ((p) * (c)^2 + (p)^2 * (a)^2 + (b)^2) +
    ((b)^2 - (c) * (a)) * ((p) * (c)^2 + (p)^2 * (a)^2 + (b)^2) * ((p) * (a)^2 + (p)^2 * (b)^2 + (c)^2) +
    ((c)^2 - (a) * (b)) * ((p) * (a)^2 + (p)^2 * (b)^2 + (c)^2) * ((p) * (b)^2 + (p)^2 * (c)^2 + (a)^2) := by
  have h₁ : ∀ a b c : ℝ, 0 ≤ a → a ≤ b → b ≤ c →
      0 ≤ ((a)^2 - (b) * (c)) * ((p) * (b)^2 + (p)^2 * (c)^2 + (a)^2) * ((p) * (c)^2 + (p)^2 * (a)^2 + (b)^2) +
    ((b)^2 - (c) * (a)) * ((p) * (c)^2 + (p)^2 * (a)^2 + (b)^2) * ((p) * (a)^2 + (p)^2 * (b)^2 + (c)^2) +
    ((c)^2 - (a) * (b)) * ((p) * (a)^2 + (p)^2 * (b)^2 + (c)^2) * ((p) * (b)^2 + (p)^2 * (c)^2 + (a)^2) := by
    intro a b c ha hab hbc
    convert lw_40072_aux1 a (b - a) (c - b) (p - 1) ha
      (sub_nonneg.mpr hab) (sub_nonneg.mpr hbc) (sub_nonneg.mpr hp) using 1 <;> ring
  have h₂ : ∀ a b c : ℝ, 0 ≤ a → a ≤ c → c ≤ b →
      0 ≤ ((a)^2 - (b) * (c)) * ((p) * (b)^2 + (p)^2 * (c)^2 + (a)^2) * ((p) * (c)^2 + (p)^2 * (a)^2 + (b)^2) +
    ((b)^2 - (c) * (a)) * ((p) * (c)^2 + (p)^2 * (a)^2 + (b)^2) * ((p) * (a)^2 + (p)^2 * (b)^2 + (c)^2) +
    ((c)^2 - (a) * (b)) * ((p) * (a)^2 + (p)^2 * (b)^2 + (c)^2) * ((p) * (b)^2 + (p)^2 * (c)^2 + (a)^2) := by
    intro a b c ha hac hcb
    convert lw_40072_aux2 a (c - a) (b - c) (p - 1) ha
      (sub_nonneg.mpr hac) (sub_nonneg.mpr hcb) (sub_nonneg.mpr hp) using 1 <;> ring
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

lemma lw_40072_aux4 (a b c p : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hp : 0 < p) :
    0 ≤ ((a)^2 - (b) * (c)) * ((p) * (b)^2 + (p)^2 * (c)^2 + (a)^2) * ((p) * (c)^2 + (p)^2 * (a)^2 + (b)^2) +
    ((b)^2 - (c) * (a)) * ((p) * (c)^2 + (p)^2 * (a)^2 + (b)^2) * ((p) * (a)^2 + (p)^2 * (b)^2 + (c)^2) +
    ((c)^2 - (a) * (b)) * ((p) * (a)^2 + (p)^2 * (b)^2 + (c)^2) * ((p) * (b)^2 + (p)^2 * (c)^2 + (a)^2) := by
  by_cases hp₁ : 1 ≤ p
  · exact lw_40072_aux3 a b c p ha hb hc hp₁
  · have hq : 1 ≤ 1 / p := (le_div_iff₀ hp).2 (by linarith)
    have h := mul_nonneg (pow_nonneg (le_of_lt hp) 4)
      (lw_40072_aux3 a c b (1 / p) ha hc hb hq)
    convert h using 1 <;> first | rfl | (field_simp [ne_of_gt hp] <;> ring)

theorem lw_40072 (a b c p : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hp : 0 < p) :
    (a^2 - b * c) / (p * a^2 + p^2 * b^2 + c^2) +
    (b^2 - c * a) / (p * b^2 + p^2 * c^2 + a^2) +
    (c^2 - a * b) / (p * c^2 + p^2 * a^2 + b^2) ≥ 0 := by
  have hA : 0 < p * a^2 + p^2 * b^2 + c^2 := by positivity
  have hB : 0 < p * b^2 + p^2 * c^2 + a^2 := by positivity
  have hC : 0 < p * c^2 + p^2 * a^2 + b^2 := by positivity
  have h := div_nonneg (lw_40072_aux4 a b c p (le_of_lt ha) (le_of_lt hb)
    (le_of_lt hc) hp) (le_of_lt (mul_pos (mul_pos hA hB) hC))
  change 0 ≤ _
  convert h using 1 <;> first
  | rfl
  | (field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hC] <;> ring)
end

-- forge:entry lw_44364 kind=proved origin=external
section
/- prove that: $x\left ( 1-y \right )+y\left ( 1-z \right )+z\left ( 1-x \right )< 1$ if: $0< x;y;z< 1$ -/
theorem lw_44364 (x y z : ℝ) (hx : 0 < x ∧ x < 1)
    (hy : 0 < y ∧ y < 1) (hz : 0 < z ∧ z < 1) :
    x * (1 - y) + y * (1 - z) + z * (1 - x) < 1 := by
  have hxyz : 0 < x * y * z := mul_pos (mul_pos hx.1 hy.1) hz.1
  have hcomp : 0 < (1 - x) * (1 - y) * (1 - z) :=
    mul_pos (mul_pos (sub_pos.mpr hx.2) (sub_pos.mpr hy.2)) (sub_pos.mpr hz.2)
  nlinarith only [hxyz, hcomp]
end

-- forge:entry lw_43833 kind=proved origin=external
section
/- Let $a,b>0,ab=1$ ,prove that: $a^b+b^a \le2.$ -/
lemma lw_43833_aux1 (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 1 ≤ b) :
    a ^ b + b ^ a ≤ 1 + a * b := by
  have h1 : a ^ b ≤ a := by
    simpa using Real.rpow_le_rpow_of_exponent_ge' ha ha1 (by norm_num : (0 : ℝ) ≤ 1) hb
  have h2 : b ^ a ≤ 1 + a * (b - 1) := by
    simpa using rpow_one_add_le_one_add_mul_self (s := b - 1) (p := a)
      (by linarith : -1 ≤ b - 1) ha ha1
  nlinarith

theorem lw_43833 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b = 1) :
    a ^ b + b ^ a ≤ 2 := by
  by_cases ha1 : a ≤ 1
  · have hb1 : 1 ≤ b := by
      nlinarith [mul_le_mul_of_nonneg_right ha1 hb.le]
    have h := lw_43833_aux1 a b ha.le ha1 hb1
    linarith
  · have ha1' : 1 ≤ a := le_of_lt (lt_of_not_ge ha1)
    have hb1 : b ≤ 1 := by
      nlinarith [mul_le_mul_of_nonneg_right ha1' hb.le]
    have h := lw_43833_aux1 b a hb.le hb1 ha1'
    nlinarith
end

-- forge:entry lw_45317 kind=proved origin=external
section
/- Is there an error in the calculation of the infinite sum $\sum_{i=1}^\infty i\left(\frac1i-\frac1{i+1}\right)$? -/
theorem lw_45317 : ∑' i : ℕ, i * (1 / i - 1 / (i + 1)) = 1 := by
  have h : ∀ i : ℕ, i ≠ 1 → i * (1 / i - 1 / (i + 1)) = 0 := by
    intro i hi
    by_cases hzero : i = 0
    · simp [hzero]
    · have hgt : 1 < i := by omega
      simp [Nat.div_eq_of_lt hgt]
  simpa using tsum_eq_single 1 h
end

-- forge:entry lw_47651 kind=proved origin=external
section
/- For positive real numbers $a$ , $b$ , and $c$ with $a+b+c=1$ , prove that:\n\n $$(a-b)^2 + (b-c)^2 + (c-a)^2 \geq \frac{1-27abc}{2}. $$ -/
theorem lw_47651 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a + b + c = 1) :
    (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ (1 - 27 * a * b * c) / 2 := by
  have hs := an_schur_deg_one a b c (le_of_lt ha) (le_of_lt hb) (le_of_lt hc)
  have hschur : 0 ≤ (a + b + c) ^ 3 + 9 * a * b * c -
      4 * (a + b + c) * (a * b + b * c + c * a) := by
    nlinarith [hs]
  rw [hab] at hschur
  have hsum : (a + b + c) ^ 2 = 1 := by rw [hab]; norm_num
  nlinarith [hsum]
end

end Mathlib2
