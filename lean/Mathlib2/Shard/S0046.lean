/- Mathlib2 分片 46（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0045
namespace Mathlib2

-- forge:entry lw_8882 kind=proved origin=external
section
/- Let $a,b,c\ge 0$ such that $a+b+c=6$. Prove that: $\frac{1}{a^2+5}+\frac{1}{b^2+5}+\frac{1}{c^2+5}\ge \frac{1}{3}$ -/
lemma lw_8882_aux1 (q r : ℝ) (hq0 : 0 ≤ q) (hq12 : q ≤ 12)
    (hr0 : 0 ≤ r) (hr8 : r ≤ 8) (hs : 24 * q ≤ 216 + 9 * r) :
    0 ≤ 280 - 10 * q - 2 * q ^ 2 + 24 * r - r ^ 2 := by
  have hr : 0 ≤ r * (8 - r) := mul_nonneg hr0 (by linarith)
  by_cases hq8 : q ≤ 8
  · have hq : 0 ≤ (8 - q) * (q + 13) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  · have hq : 0 ≤ (12 - q) * (q - 8) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

theorem lw_8882 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0)
    (habc : a + b + c = 6) :
    1 / (a ^ 2 + 5) + 1 / (b ^ 2 + 5) + 1 / (c ^ 2 + 5) ≥ 1 / 3 := by
  let q := a * b + b * c + c * a
  let r := a * b * c
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hsum2 : (a + b + c) ^ 2 = (6 : ℝ) ^ 2 := congrArg (fun x : ℝ => x ^ 2) habc
  have hq12 : q ≤ 12 := by
    dsimp [q]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hr8 : r ≤ 8 := by
    have h := an_amgm_three_cube a b c ha hb hc
    rw [habc] at h
    norm_num at h
    exact h
  have hs0 : 0 ≤ (a + b + c) ^ 3 + 9 * r - 4 * (a + b + c) * q := by
    dsimp [q, r]
    nlinarith only [an_schur_deg_one a b c ha hb hc]
  have hs : 24 * q ≤ 216 + 9 * r := by
    rw [habc] at hs0
    nlinarith only [hs0]
  have hF := lw_8882_aux1 q r hq0 hq12 hr0 hr8 hs
  have hsumr : (a + b + c) * (a * b * c) = 6 * (a * b * c) := by rw [habc]
  have hid :
      3 * ((a ^ 2 + 5) * (b ^ 2 + 5) + (b ^ 2 + 5) * (c ^ 2 + 5) +
        (c ^ 2 + 5) * (a ^ 2 + 5)) - (a ^ 2 + 5) * (b ^ 2 + 5) * (c ^ 2 + 5) =
      280 - 10 * q - 2 * q ^ 2 + 24 * r - r ^ 2 := by
    dsimp [q, r]
    nlinarith only [hsum2, hsumr]
  have hpoly : 0 ≤
      3 * ((a ^ 2 + 5) * (b ^ 2 + 5) + (b ^ 2 + 5) * (c ^ 2 + 5) +
        (c ^ 2 + 5) * (a ^ 2 + 5)) - (a ^ 2 + 5) * (b ^ 2 + 5) * (c ^ 2 + 5) := by
    rw [hid]
    exact hF
  have hA : 0 < a ^ 2 + 5 := by positivity
  have hB : 0 < b ^ 2 + 5 := by positivity
  have hC : 0 < c ^ 2 + 5 := by positivity
  have hfrac :
      1 / (a ^ 2 + 5) + 1 / (b ^ 2 + 5) + 1 / (c ^ 2 + 5) - 1 / 3 =
      (3 * ((a ^ 2 + 5) * (b ^ 2 + 5) + (b ^ 2 + 5) * (c ^ 2 + 5) +
        (c ^ 2 + 5) * (a ^ 2 + 5)) - (a ^ 2 + 5) * (b ^ 2 + 5) * (c ^ 2 + 5)) /
      (3 * (a ^ 2 + 5) * (b ^ 2 + 5) * (c ^ 2 + 5)) := by
    field_simp
    <;> ring
  have hnonneg : 0 ≤
      1 / (a ^ 2 + 5) + 1 / (b ^ 2 + 5) + 1 / (c ^ 2 + 5) - 1 / 3 := by
    rw [hfrac]
    exact div_nonneg hpoly (by positivity)
  linarith
end

-- forge:entry lw_9827 kind=disproved origin=external
section
/- Prove that if $p$ is a prime number that $p\equiv5\pmod6$ and $p|a^2+ab+b^2$ when $a,b$ is integers, then $p|a$ and $p|b$ . -/
theorem lw_9827_disproof :
    ¬ (∀ (p a b : ℤ) (hp : Prime p) (h : p ≡ 5 [ZMOD 6]),
      p ∣ a ^ 2 + a * b + b ^ 2 → p ∣ a ∧ p ∣ b) := by
  intro h
  have hp : Prime (-7 : ℤ) := by
    norm_num [Int.prime_iff_natAbs_prime]
  have hm : (-7 : ℤ) ≡ 5 [ZMOD 6] := by decide
  have hd : (-7 : ℤ) ∣ (2 : ℤ) ^ 2 + 2 * 1 + 1 ^ 2 := by norm_num
  have hc := h (-7) 2 1 hp hm hd
  norm_num at hc
end

-- forge:entry lw_9555 kind=proved origin=external
section
/- Prove \n $\dfrac{a}{1+bc}+\dfrac{b}{1+ca}+\dfrac{c}{1+ab}\geq \dfrac{a}{1+a^2}+\dfrac{b}{1+b^2}+\dfrac{c}{1+c^2}$\nwith conditions\n$a,b,c>0$ , $a+b+c=1$ -/
lemma lw_9555_aux1 (x : ℝ) (hx : 0 ≤ x) :
    x / (1 + x ^ 2) ≤ (36 * x + 3) / 50 := by
  apply (div_le_iff₀ (show 0 < 1 + x ^ 2 by positivity)).2
  have h := mul_nonneg (sq_nonneg (3 * x - 1))
    (show 0 ≤ 4 * x + 3 by linarith)
  nlinarith

lemma lw_9555_aux2 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * (99 - 81 * y) / 100 ≤ x / (1 + y) := by
  apply (le_div_iff₀ (show 0 < 1 + y by positivity)).2
  have h := mul_nonneg hx (sq_nonneg (9 * y - 1))
  nlinarith

theorem lw_9555 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a + b + c = 1) :
    a / (1 + b * c) + b / (1 + c * a) + c / (1 + a * b) ≥
      a / (1 + a^2) + b / (1 + b^2) + c / (1 + c^2) := by
  have hp : 27 * (a * b * c) ≤ 1 := by
    have h := lw_56101_aux1 a b c ha.le hb.le hc.le
    simpa [hab] using h
  have h₁ := lw_9555_aux1 a ha.le
  have h₂ := lw_9555_aux1 b hb.le
  have h₃ := lw_9555_aux1 c hc.le
  have h₄ := lw_9555_aux2 a (b * c) ha.le (mul_nonneg hb.le hc.le)
  have h₅ := lw_9555_aux2 b (c * a) hb.le (mul_nonneg hc.le ha.le)
  have h₆ := lw_9555_aux2 c (a * b) hc.le (mul_nonneg ha.le hb.le)
  nlinarith
end

-- forge:entry lw_12329 kind=disproved origin=external
section
/- If $a,b,c\ge0: ab+bc+ca=1$ , prove that $\frac{1}{\sqrt{2a+1}}+\frac{1}{\sqrt{2b+1}}+\frac{1}{\sqrt{2c+1}}\le 1+\frac{2}{\sqrt{3}}$ -/
theorem lw_12329_disproof : ¬ (∀ (a b c : ℝ),
    0 ≤ a → 0 ≤ b → 0 ≤ c → a + b + c = 1 →
    1 / Real.sqrt (2 * a + 1) + 1 / Real.sqrt (2 * b + 1) +
      1 / Real.sqrt (2 * c + 1) ≤ 1 + 2 / Real.sqrt 3) := by
  intro h
  have hcounter := h 1 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hcounter
  have hspos : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsq : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : 1 < Real.sqrt (3 : ℝ) := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hcounter hspos.le
  simp only [add_mul, div_mul_cancel₀ _ hspos.ne', inv_mul_cancel₀ hspos.ne',
    one_mul] at hm
  linarith
end

-- forge:entry lw_14759 kind=disproved origin=external
section
/- By AM-GM, $\sqrt{x^2+y^2+z^2}(xy+yz+zx) \ge \sqrt{3}\sqrt[3]{xyz}\cdot 3\sqrt[3]{x^2y^2z^2}=3\sqrt{3}xyz$ -/
theorem lw_14759_disproof : ¬ (∀ (x y z : ℝ),
    Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) * (x * y + y * z + z * x) ≥
      3 * Real.sqrt 3 * x * y * z) := by
  intro h
  have hcounter := h 1 (-1) 0
  have hpos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  norm_num at hcounter
  linarith
end

-- forge:entry lw_1237 kind=proved origin=external
section
/- Prove \\(\\frac{4a}{b+1}+\\frac{4b}{a+1}+2ab\\ge 4+\\sqrt{7-3ab}\\) for all positive real a and b such that \\(a+b+ab=3\\). -/
theorem lw_1237 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b + a * b = 3) :
    4 * a / (b + 1) + 4 * b / (a + 1) + 2 * a * b ≥
      4 + Real.sqrt (7 - 3 * a * b) := by
  have hprod : (a + 1) * (b + 1) = 4 := by nlinarith
  have ha1 : a + 1 ≠ 0 := ne_of_gt (by linarith)
  have hb1 : b + 1 ≠ 0 := ne_of_gt (by linarith)
  have hsum : 2 ≤ a + b := by
    by_contra h
    have hlt : a + b < 2 := lt_of_not_ge h
    have hpos : 0 < (2 - (a + b)) * (a + b + 6) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [sq_nonneg (a - b)]
  have hdiva : 4 * a / (b + 1) = a * (a + 1) := by
    apply (div_eq_iff hb1).2
    calc
      4 * a = a * 4 := by ring
      _ = a * ((a + 1) * (b + 1)) := by rw [hprod]
      _ = a * (a + 1) * (b + 1) := by ring
  have hdivb : 4 * b / (a + 1) = b * (b + 1) := by
    apply (div_eq_iff ha1).2
    calc
      4 * b = b * 4 := by ring
      _ = b * ((a + 1) * (b + 1)) := by rw [hprod]
      _ = b * (b + 1) * (a + 1) := by ring
  have hsqrt : Real.sqrt (7 - 3 * a * b) ≤ a + b := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith
    · have hmul : 0 ≤ (a + b - 2) * (a + b - 1) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
  have hsquare : 4 ≤ (a + b) ^ 2 := by
    have hmul : 0 ≤ (a + b - 2) * (a + b + 2) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  rw [hdiva, hdivb]
  nlinarith
end

-- forge:entry lw_14880 kind=disproved origin=external
section
/- $\frac{a^2+b^2}{a+b} \geq \sqrt{ab}$ -/
theorem lw_14880_disproof : ¬ (∀ (a b : ℝ),
    (a^2 + b^2) / (a + b) ≥ Real.sqrt (a * b)) := by
  intro h
  have hneg := h (-1) (-1)
  norm_num at hneg
end

-- forge:entry lw_15087 kind=disproved origin=external
section
/- Prove that for any $a, b, c$ such that $a + b + c = 1$, the inequality $\frac{a^2}{b}+\frac{b^2}{c}+\frac{c^2}{a}\ge\frac{ab}{c}+\frac{bc}{a}+\frac{ca}{b}$ holds. -/
theorem lw_15087_disproof :
    ¬ (∀ (a b c : ℝ) (habc : a + b + c = 1),
      a^2 / b + b^2 / c + c^2 / a ≥ a * b / c + b * c / a + c * a / b) := by
  intro h
  have hbad := h (-1) (-1) 3 (by norm_num)
  norm_num at hbad
end

-- forge:entry lw_1488 kind=proved origin=external
section
/- Prove that for the sequence defined with $x_1=19$ , $x_2=27$ , $x_{n+2}=x_n - \frac{1}{x_{n+1}}$ , there is a natural number $k$ , such that $x_k=0$ . Find the value of $k$ . -/
lemma lw_1488_aux1 (x : ℕ → ℝ) (m : ℕ)
    (hinit : x 1 * x 2 = (m : ℝ))
    (hrec : ∀ n, x (n + 2) = x n - 1 / x (n + 1)) :
    ∀ n, n ≤ m → x (n + 1) * x (n + 2) = (m : ℝ) - (n : ℝ) := by
  intro n
  induction n with
  | zero =>
      intro hn
      simpa using hinit
  | succ n ih =>
      intro hn
      have hlt : n < m := by omega
      have hp := ih (by omega)
      have hx : x (n + 2) ≠ 0 := by
        intro hz
        rw [hz, mul_zero] at hp
        have hr : (n : ℝ) < (m : ℝ) := by exact_mod_cast hlt
        linarith
      calc
        x (n + 1 + 1) * x (n + 1 + 2) =
            x (n + 1) * x (n + 2) - 1 := by
          rw [hrec (n + 1)]
          change x (n + 2) * (x (n + 1) - 1 / x (n + 2)) = _
          field_simp [hx]
          <;> nlinarith
        _ = (m : ℝ) - ((n + 1 : ℕ) : ℝ) := by
          rw [hp]
          push_cast
          ring

theorem lw_1488 (x : ℕ → ℝ) (h₁ : x 1 = 19) (h₂ : x 2 = 27)
    (h₃ : ∀ n, x (n + 2) = x n - 1 / x (n + 1)) : ∃ k, x k = 0 := by
  have hinit : x 1 * x 2 = (513 : ℝ) := by rw [h₁, h₂]; norm_num
  have hp := lw_1488_aux1 x 513 hinit h₃
  have hprev := hp 512 (by omega)
  have hlast := hp 513 (by omega)
  norm_num at hprev hlast
  have hx : x 514 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hprev
    norm_num at hprev
  exact ⟨515, hlast.resolve_left hx⟩
end

-- forge:entry lw_15096 kind=disproved origin=external
section
/- Let $p$ be an odd prime and $a$ be any integer which is not congruent to 0 modulo p. Prove that the congruence $x^2=-a^2 mod p$ has solutions if and only if $p$ is congruent to $1 mod 4$ . -/
theorem lw_15096_disproof :
    ¬ (∀ (p : ℕ) (hp : p.Prime) (hp1 : Odd p) {a : ℤ}
      (ha : a ∉ (⊥ : Ideal ℤ)),
      (∃ x : ℤ, x^2 ≡ -(a^2) [ZMOD p]) ↔ p ≡ 1 [ZMOD 4]) := by
  intro h
  have h3 := h 3 (by norm_num) (by norm_num) (a := 3) (by
    norm_num [Ideal.mem_bot])
  have hx : ∃ x : ℤ, x^2 ≡ -((3 : ℤ)^2) [ZMOD (3 : ℕ)] := by
    refine ⟨0, ?_⟩
    norm_num [Int.ModEq]
  have hc := h3.mp hx
  norm_num [Int.ModEq] at hc
end

-- forge:entry lw_17200 kind=disproved origin=external
section
/- By Fermat's Little Theorem, we have $n^{p-1}\equiv 1 (mod p)$ -/
theorem lw_17200_disproof :
    ¬ (∀ (p n : ℕ) (hp : p.Prime), n ^ (p - 1) ≡ 1 [ZMOD p]) := by
  intro h
  have hbad := h 2 0 (by norm_num)
  norm_num [Int.ModEq] at hbad
end

-- forge:entry lw_18048 kind=disproved origin=external
section
/- Prove that $x^4+y^4+z^3\ge{x^3y+y^3z+z^3x}$ for real numbers $x$, $y$, and $z$. -/
theorem lw_18048_disproof :
    ¬ (∀ (x y z : ℝ), x ^ 4 + y ^ 4 + z ^ 3 ≥
      x ^ 3 * y + y ^ 3 * z + z ^ 3 * x) := by
  intro h
  have hbad := h 0 0 (-1)
  norm_num at hbad
end

-- forge:entry lw_19526 kind=disproved origin=external
section
/- Let $n\ge3$ be an integer, and $a_i$ real numbers such that $1 \le a_i \le(n-1)^n$ for every $i\in\{1,2,\cdots, n\}$ . Prove that\n\n $$\frac{\displaystyle\sum_{i=1}^na_i }{(n-1)^{n-1}+1}\le\prod_{i=1}^n\sqrt[n]{a_i}.$$\n\n -/
theorem lw_19526_disproof : ¬ (∀ (n : ℕ) (a : Fin n → ℝ)
    (ha : ∀ i, 1 ≤ a i ∧ a i ≤ (n - 1) ^ n),
    (∑ i, a i) / ((n - 1) ^ (n - 1) + 1) ≤ ∏ i, (a i) ^ (1 / n)) := by
  intro h
  have hbad := h 3 (fun _ => 8) (by intro i; norm_num)
  norm_num [Fin.sum_univ_succ, Fin.prod_univ_succ] at hbad
end

-- forge:entry lw_16565 kind=proved origin=external
section
/- Let $a,b$ are positive numbers such that $a+b=2$ . Prove that : $a^a+b^b\ge 2+\frac{3}{8}(a-b)^2$ -/
lemma lw_16565_aux1 (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    (1 + x ^ 2) / 2 ≤ x ^ x := by
  let f : ℝ → ℝ := fun t => Real.exp (t * Real.log t) - t ^ 2 / 2
  have hd (t : ℝ) (ht : 0 < t) :
      HasDerivAt f (Real.exp (t * Real.log t) * (Real.log t + 1) - t) t := by
    dsimp [f]
    convert (((hasDerivAt_id t).mul (Real.hasDerivAt_log ht.ne')).exp).sub
      (((hasDerivAt_id t).pow 2).div_const 2) using 1 <;>
      first | rfl | (simp only [id_eq, Pi.mul_apply]; field_simp; ring)
  have hf : AntitoneOn f (Set.Icc x 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc x 1)
    · intro t ht
      exact (hd t (lt_of_lt_of_le hx ht.1)).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (lt_of_lt_of_le hx (interior_subset ht).1)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hx (interior_subset ht).1
      have ht1 : t ≤ 1 := (interior_subset ht).2
      rw [(hd t ht0).deriv]
      have he : Real.exp (t * Real.log t) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr
          (mul_nonpos_of_nonneg_of_nonpos ht0.le (Real.log_nonpos ht0.le ht1))
      have hl := Real.log_le_sub_one_of_pos ht0
      have hm := mul_le_mul_of_nonneg_left hl (Real.exp_nonneg (t * Real.log t))
      have hn := mul_le_mul_of_nonneg_right he ht0.le
      nlinarith
  have h := hf (show x ∈ Set.Icc x 1 from ⟨le_rfl, hx1⟩)
    (show (1 : ℝ) ∈ Set.Icc x 1 from ⟨hx1, le_rfl⟩) hx1
  dsimp [f] at h
  rw [Real.log_one, mul_zero, Real.exp_zero] at h
  rw [Real.rpow_def_of_pos hx]
  rw [mul_comm (Real.log x) x]
  norm_num at h
  linarith

lemma lw_16565_aux2 (x : ℝ) (hx : 1 ≤ x) :
    x + (x - 1) ^ 2 ≤ x ^ x := by
  have h := one_add_mul_self_le_rpow_one_add
    (s := x - 1) (p := x) (by linarith) hx
  have he : 1 + (x - 1) = x := by ring
  rw [he] at h
  nlinarith

theorem lw_16565 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 2) :
    a^a + b^b ≥ 2 + 3/8 * (a - b)^2 := by
  by_cases ha1 : a ≤ 1
  · have hb1 : 1 ≤ b := by linarith
    have h₁ := lw_16565_aux1 a ha ha1
    have h₂ := lw_16565_aux2 b hb1
    have he : b = 2 - a := by linarith
    rw [he] at h₂ ⊢
    nlinarith
  · have ha1 : 1 ≤ a := by linarith
    have hb1 : b ≤ 1 := by linarith
    have h₁ := lw_16565_aux1 b hb hb1
    have h₂ := lw_16565_aux2 a ha1
    have he : a = 2 - b := by linarith
    rw [he] at h₂ ⊢
    nlinarith
end

-- forge:entry lw_19170 kind=proved origin=external
section
/- Let $x$ be positive real numbers . Prove that $\sqrt{ \frac{2}{x^2+1}}+\sqrt{ \frac{x}{x+1}}\le \sqrt{2+\sqrt{2}}$ -/
theorem lw_19170_aux1 (x r : ℝ) (hr : r ^ 2 = 2) :
    ((2 + r) * (x ^ 2 + 1) * (x + 1) - 2 * (x + 1) - x * (x ^ 2 + 1)) ^ 2 -
      8 * x * (x ^ 2 + 1) * (x + 1) =
    (x + 1 - r) ^ 2 * ((3 + 2 * r) * x ^ 4 + (10 + 8 * r) * x ^ 3 +
      (11 + 8 * r) * x ^ 2 + (8 + 6 * r) * x + (6 + 4 * r)) := by
  have hr3 : r ^ 3 = 2 * r := by nlinarith [congrArg (fun t : ℝ => t * r) hr]
  ring_nf
  rw [hr, hr3]
  ring

theorem lw_19170 (x : ℝ) (hx : 0 < x) :
    √(2 / (x ^ 2 + 1)) + √(x / (x + 1)) ≤ √(2 + √2) := by
  have hd1 : 0 < x ^ 2 + 1 := by positivity
  have hd2 : 0 < x + 1 := by positivity
  have hr : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hr1 : 1 ≤ Real.sqrt 2 := by nlinarith
  have ha : 0 ≤ 2 / (x ^ 2 + 1) := by positivity
  have hb : 0 ≤ x / (x + 1) := by positivity
  have ha2 : 2 / (x ^ 2 + 1) ≤ 2 := (div_le_iff₀ hd1).2 (by nlinarith [sq_nonneg x])
  have hb1 : x / (x + 1) ≤ 1 := (div_le_iff₀ hd2).2 (by linarith)
  have hc : 0 ≤ 2 + Real.sqrt 2 - 2 / (x ^ 2 + 1) - x / (x + 1) := by linarith
  have hpoly := lw_19170_aux1 x (Real.sqrt 2) hr
  have hq : 0 ≤ (3 + 2 * Real.sqrt 2) * x ^ 4 +
      (10 + 8 * Real.sqrt 2) * x ^ 3 + (11 + 8 * Real.sqrt 2) * x ^ 2 +
      (8 + 6 * Real.sqrt 2) * x + (6 + 4 * Real.sqrt 2) := by positivity
  have hN : 8 * x * (x ^ 2 + 1) * (x + 1) ≤
      ((2 + Real.sqrt 2) * (x ^ 2 + 1) * (x + 1) -
        2 * (x + 1) - x * (x ^ 2 + 1)) ^ 2 := by
    nlinarith only [hpoly, mul_nonneg (sq_nonneg (x + 1 - Real.sqrt 2)) hq]
  have hfrac : 4 * (2 / (x ^ 2 + 1)) * (x / (x + 1)) ≤
      (2 + Real.sqrt 2 - 2 / (x ^ 2 + 1) - x / (x + 1)) ^ 2 := by
    apply (mul_le_mul_iff_right₀ (show 0 < ((x ^ 2 + 1) * (x + 1)) ^ 2 by positivity)).1
    convert hN using 1 <;> first | rfl | (field_simp [ne_of_gt hd1, ne_of_gt hd2] <;> ring)
  have hsqa := Real.sq_sqrt ha
  have hsqb := Real.sq_sqrt hb
  have hsqc := Real.sq_sqrt (show 0 ≤ 2 + Real.sqrt 2 by positivity)
  have hcross_sq : (2 * Real.sqrt (2 / (x ^ 2 + 1)) * Real.sqrt (x / (x + 1))) ^ 2 ≤
      (2 + Real.sqrt 2 - 2 / (x ^ 2 + 1) - x / (x + 1)) ^ 2 := by
    calc
      _ = 4 * (Real.sqrt (2 / (x ^ 2 + 1))) ^ 2 * (Real.sqrt (x / (x + 1))) ^ 2 := by ring
      _ = 4 * (2 / (x ^ 2 + 1)) * (x / (x + 1)) := by rw [hsqa, hsqb]
      _ ≤ _ := hfrac
  have hcross : 2 * Real.sqrt (2 / (x ^ 2 + 1)) * Real.sqrt (x / (x + 1)) ≤
      2 + Real.sqrt 2 - 2 / (x ^ 2 + 1) - x / (x + 1) :=
    (sq_le_sq₀ (by positivity) hc).1 hcross_sq
  nlinarith [Real.sqrt_nonneg (2 + Real.sqrt 2), Real.sqrt_nonneg (2 / (x ^ 2 + 1)),
    Real.sqrt_nonneg (x / (x + 1))]
end

-- forge:entry lw_22707 kind=disproved origin=external
section
/- Lemma: $2x+\dfrac{1}{x}\ge \dfrac{1}{2}x^2+\dfrac{5}{2}$ for $x \le 2$ -/
theorem lw_22707_disproof :
    ¬ (∀ (x : ℝ) (h₀ : x ≤ 2),
      2 * x + 1 / x ≥ 1 / 2 * x^2 + 5 / 2) := by
  intro h
  have hneg := h (-1) (by norm_num)
  norm_num at hneg
end

-- forge:entry lw_223 kind=proved origin=external
section
/- Let $a, b, c> 0$ . Prove that: \n $\left ( 1+\frac{2a}{b} \right )^2+\left ( 1+\frac{2b}{c} \right )^2+\left(1+\frac{2c}{a}\right)^2\geq\frac{9(a+b+c)^2}{ab+bc+ca}$ \n\n $\left( 4+{\frac {a}{b}} \right) ^{2}+ \left( 4+{\frac {b}{c}} \right) ^{2}+ \left( 4+{\frac {c}{a}} \right) ^{2}\geq 25\,{\frac { \left( a+b+c \right) ^{2}}{ab+ac+bc}}$ -/
lemma lw_223_aux1 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c)^2 ≤ (a * b + b * c + a * c) * (a / b + b / c + c / a) := by
  have h1 : 0 ≤ c / b * (a - b)^2 :=
    mul_nonneg (le_of_lt (div_pos hc hb)) (sq_nonneg _)
  have h2 : 0 ≤ a / c * (b - c)^2 :=
    mul_nonneg (le_of_lt (div_pos ha hc)) (sq_nonneg _)
  have h3 : 0 ≤ b / a * (c - a)^2 :=
    mul_nonneg (le_of_lt (div_pos hb ha)) (sq_nonneg _)
  have hid : (a * b + b * c + a * c) * (a / b + b / c + c / a) -
      (a + b + c)^2 =
      c / b * (a - b)^2 + a / c * (b - c)^2 + b / a * (c - a)^2 := by
    field_simp
    <;> ring
  linarith

theorem lw_223 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 →
    (1 + 2 * a / b)^2 + (1 + 2 * b / c)^2 + (1 + 2 * c / a)^2 ≥
      9 * (a + b + c)^2 / (a * b + b * c + a * c) := by
  intro a b c ⟨ha, hb, hc⟩
  have hq : 0 < a * b + b * c + a * c := by positivity
  have hbound := lw_223_aux1 a b c ha hb hc
  have hs : 3 * (a * b + b * c + a * c) ≤ (a + b + c)^2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hthree : 3 ≤ a / b + b / c + c / a := by
    apply (le_of_mul_le_mul_left ?_ hq)
    nlinarith
  have hlinear : 9 * (a / b + b / c + c / a) ≤
      (1 + 2 * a / b)^2 + (1 + 2 * b / c)^2 + (1 + 2 * c / a)^2 := by
    have h1 := sq_nonneg (a / b - 1)
    have h2 := sq_nonneg (b / c - 1)
    have h3 := sq_nonneg (c / a - 1)
    simp only [mul_div_assoc] at *
    nlinarith
  have hratio : (a + b + c)^2 / (a * b + b * c + a * c) ≤
      a / b + b / c + c / a := (div_le_iff₀ hq).2 (by nlinarith [hbound])
  calc
    9 * (a + b + c)^2 / (a * b + b * c + a * c) =
        9 * ((a + b + c)^2 / (a * b + b * c + a * c)) := by ring
    _ ≤ 9 * (a / b + b / c + c / a) := by linarith
    _ ≤ _ := hlinear
end

-- forge:entry lw_19641 kind=proved origin=external
section
/- Easy. Let $a, b, c>0, a+b+c=1$ .Prove that \n $a^3+b^3+c^3\ge3(a^3c+b^3a+c^3b)$ -/
theorem lw_19641 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a + b + c = 1) :
    a ^ 3 + b ^ 3 + c ^ 3 ≥ 3 * (a ^ 3 * c + b ^ 3 * a + c ^ 3 * b) := by
  have hsum : (a + b + c) * (a ^ 3 + b ^ 3 + c ^ 3) =
      a ^ 3 + b ^ 3 + c ^ 3 := by rw [habc, one_mul]
  nlinarith only [hsum,
    sq_nonneg (a ^ 2 - b ^ 2 - a * c + a * b),
    sq_nonneg (b ^ 2 - c ^ 2 - a * b + b * c),
    sq_nonneg (c ^ 2 - a ^ 2 - b * c + c * a)]
end

-- forge:entry lw_28848 kind=disproved origin=external
section
/- If $25|a^5+b^5+c^5+d^5+e^5$ then $25|abcde$ -/
theorem lw_28848_disproof :
    ¬ (∀ {a b c d e : ℤ},
      25 ∣ a^5 + b^5 + c^5 + d^5 + e^5 → 25 ∣ a * b * c * d * e) := by
  intro h
  have hbad := h (a := 1) (b := -1) (c := 1) (d := -1) (e := 5) (by norm_num)
  norm_num at hbad
end

-- forge:entry lw_28269 kind=disproved origin=external
section
/- Let $a_n$ be a sequence such that $a_{n+2} = \frac{a_n +a_{n+1} }{1-a_n a_{n+1} } $ with $a_1=1 $ and $a_2=\frac{2}{\sqrt{3}} $ .\nThen find $|a_{2009}|$ . -/
open Real

theorem lw_28269_aux1 (θ : ℝ) (hθ : ∀ r : ℚ, θ ≠ (r : ℝ) * π)
    (p q : ℚ) (hp : p ≠ 0) :
    ∀ r : ℚ, (p : ℝ) * θ + (q : ℝ) * π ≠ (r : ℝ) * π := by
  intro r hr
  apply hθ ((r - q) / p)
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  push_cast
  field_simp
  nlinarith [hr]

theorem lw_28269_aux2 (x : ℝ) (hx : ∀ r : ℚ, x ≠ (r : ℝ) * π) :
    cos x ≠ 0 ∧ |tan x| ≠ 1 := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp h
    apply hx ((2 * (k : ℚ) + 1) / 2)
    push_cast
    linarith
  · intro h
    have hs : tan x ^ 2 = 1 := by nlinarith [sq_abs (tan x)]
    have ht : tan (2 * x) = 0 := by rw [Real.tan_two_mul, hs]; norm_num
    obtain ⟨k, hk⟩ := Real.tan_eq_zero_iff.mp ht
    apply hx ((k : ℚ) / 4)
    push_cast
    linarith

theorem lw_28269_aux3 (x : ℝ) :
    cos (2 * arctan x) = (1 - x ^ 2) / (1 + x ^ 2) := by
  rw [Real.cos_two_mul, Real.cos_arctan]
  have hs : (√(1 + x ^ 2)) ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (by positivity)
  rw [div_pow, one_pow, hs]
  field_simp
  ring

theorem lw_28269_disproof : ¬ (∀ (a : ℕ → ℝ) (a1 : a 0 = 1)
    (a2 : a 1 = 2 / Real.sqrt 3)
    (a_rec : ∀ n, a (n + 2) = (a n + a (n + 1)) / (1 - a n * a (n + 1))),
    |a 2009| = 1) := by
  intro H
  let θ : ℝ := arctan (2 / √3)
  have hs3 : (√(3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3ne : √(3 : ℝ) ≠ 0 := by positivity
  have ht : (2 / √(3 : ℝ)) ^ 2 = 4 / 3 := by
    rw [div_pow, hs3]
    norm_num
  have hc : cos (2 * θ) = -1 / 7 := by
    dsimp [θ]
    rw [lw_28269_aux3, ht]
    norm_num
  have hθ : ∀ r : ℚ, θ ≠ (r : ℝ) * π := by
    intro r hr
    have h := niven (θ := 2 * θ) ⟨2 * r, by push_cast; rw [hr]; ring⟩
      ⟨-1 / 7, by push_cast; nlinarith [hc]⟩
    rw [hc] at h
    norm_num at h
  let b : ℕ → ℝ := fun n => (Nat.fib n : ℝ) * θ +
    ((Nat.fib (n + 1) : ℝ) - (Nat.fib n : ℝ)) * (π / 4)
  have hb0 : b 0 = π / 4 := by simp [b]
  have hb1 : b 1 = θ := by simp [b]
  have hbirr (n : ℕ) (hn : n ≠ 0) : ∀ r : ℚ, b n ≠ (r : ℝ) * π := by
    have hf : (Nat.fib n : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.fib_pos.mpr (Nat.pos_of_ne_zero hn)))
    have h := lw_28269_aux1 θ hθ (Nat.fib n)
      (((Nat.fib (n + 1) : ℚ) - (Nat.fib n : ℚ)) / 4) hf
    convert h using 1 <;> dsimp [b] <;> push_cast <;> ring
  have hbcos (n : ℕ) : cos (b n) ≠ 0 := by
    by_cases hn : n = 0
    · subst n
      rw [hb0, Real.cos_pi_div_four]
      positivity
    · exact (lw_28269_aux2 (b n) (hbirr n hn)).1
  have hbrec (n : ℕ) : b (n + 2) = b n + b (n + 1) := by
    dsimp [b]
    rw [show n + 2 + 1 = (n + 1) + 2 by omega]
    simp only [Nat.fib_add_two, Nat.cast_add]
    ring
  have ha0 : tan (b 0) = 1 := by rw [hb0, Real.tan_pi_div_four]
  have ha1 : tan (b 1) = 2 / √3 := by rw [hb1]; exact Real.tan_arctan _
  have harec (n : ℕ) : tan (b (n + 2)) =
      (tan (b n) + tan (b (n + 1))) / (1 - tan (b n) * tan (b (n + 1))) := by
    rw [hbrec]
    exact Real.tan_add' ⟨Real.cos_ne_zero_iff.mp (hbcos n),
      Real.cos_ne_zero_iff.mp (hbcos (n + 1))⟩
  exact (lw_28269_aux2 (b 2009) (hbirr 2009 (by norm_num))).2
    (H (fun n => tan (b n)) ha0 ha1 harec)
end

end Mathlib2
