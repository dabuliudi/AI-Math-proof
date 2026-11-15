/- Mathlib2 分片 39（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0038
namespace Mathlib2

-- forge:entry lw_1820 kind=disproved origin=external
section
/- Let $a,\ b,\ c$ be positive real numbers. Prove that $\frac{a(b^3+c^3)}{c^2(a^2+bc)}+\frac{b(c^3+a^3)}{a^2(b^2+ca)}+\frac{c(a^3+b^3)}{b^2(c^2+ab)}\geq 3.$ Proposed by Kunihiko Chikaya -/
theorem lw_1820_disproof :
    ¬ (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c),
      (a * (b ^ 3 + c ^ 3) / c ^ 2 * (a ^ 2 + b * c) +
        b * (c ^ 3 + a ^ 3) / a ^ 2 * (b ^ 2 + c * a) +
        c * (a ^ 3 + b ^ 3) / b ^ 2 * (c ^ 2 + a * b)) ≥ 3) := by
  intro h
  have hhalf := h (1 / 2) (1 / 2) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at hhalf
end

-- forge:entry lw_10772 kind=proved origin=external
section
/- Let $a,b,c$ are positive. Prove that: \n\n $\frac{a}{b+c}+\frac{b}{a+c}+\frac{c}{a+b}+\frac{4abc}{(a+b)(b+c)(c+a)}\geq 2$ -/
theorem lw_10772 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a / (b + c) + b / (a + c) + c / (a + b) +
      4 * a * b * c / ((a + b) * (b + c) * (c + a))) ≥ 2 := by
  have hab : 0 < a + b := add_pos ha hb
  have hbc : 0 < b + c := add_pos hb hc
  have hac : 0 < a + c := add_pos ha hc
  have hca : 0 < c + a := add_pos hc ha
  have hd : 0 < (a + b) * (b + c) * (c + a) :=
    mul_pos (mul_pos hab hbc) hca
  have hs := Mathlib2.an_schur_deg_one a b c ha.le hb.le hc.le
  have hid :
      a / (b + c) + b / (a + c) + c / (a + b) +
        4 * a * b * c / ((a + b) * (b + c) * (c + a)) - 2 =
      (a * (a - b) * (a - c) + b * (b - a) * (b - c) +
        c * (c - a) * (c - b)) / ((a + b) * (b + c) * (c + a)) := by
    field_simp [hab.ne', hbc.ne', hac.ne', hca.ne']
    <;> ring
  apply sub_nonneg.mp
  rw [hid]
  exact div_nonneg hs hd.le
end

-- forge:entry lw_18499 kind=disproved origin=external
section
/- Find all triples of functions $f,g,h:\\mathbb{R}\\rightarrow\\mathbb{R}$ such that $f(h(g(x))+y)+g(z+f(y))=h(y)+g(y+f(z))+x$ for all $x,y,z\\in\\mathbb{R}$ . -/
theorem lw_18499_disproof :
    ¬ (∀ (f g h : ℝ → ℝ),
      (∀ x y z : ℝ,
        f (h (g x) + y) + g (z + f y) = h y + g (y + f z) + x) ↔
      ∃ c : ℝ, ∀ x : ℝ, f x = c * x ∧
        ∃ d : ℝ, ∀ y : ℝ, g y = d * y ∧
          ∃ e : ℝ, ∀ z : ℝ, h z = e * z ∧ c + d + e = 1) := by
  intro hall
  have heq := (hall (fun x => x) (fun _ => 0) (fun _ => 0)).mpr
    ⟨1, fun x => ⟨by simp, 0, fun y => ⟨by simp, 0, fun z =>
      ⟨by simp, by norm_num⟩⟩⟩⟩
  have hbad := heq 1 0 0
  norm_num at hbad
end

-- forge:entry lw_13549 kind=proved origin=external
section
/- For a,b,c real numbers prove that $3(a^4+b^4+c^4)^3 \geq (a^3+b^3+c^3)^4$ -/
theorem lw_13549 : ∀ a b c : ℝ,
    3 * (a ^ 4 + b ^ 4 + c ^ 4) ^ 3 ≥ (a ^ 3 + b ^ 3 + c ^ 3) ^ 4 := by
  intro a b c
  have h₁ : (a ^ 3 + b ^ 3 + c ^ 3) ^ 2 ≤
      (a ^ 4 + b ^ 4 + c ^ 4) * (a ^ 2 + b ^ 2 + c ^ 2) := by
    nlinarith only [sq_nonneg (a ^ 2 * b - b ^ 2 * a),
      sq_nonneg (a ^ 2 * c - c ^ 2 * a),
      sq_nonneg (b ^ 2 * c - c ^ 2 * b)]
  have h₂ : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≤
      3 * (a ^ 4 + b ^ 4 + c ^ 4) := by
    nlinarith only [sq_nonneg (a ^ 2 - b ^ 2),
      sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (b ^ 2 - c ^ 2)]
  calc
    (a ^ 3 + b ^ 3 + c ^ 3) ^ 4 =
        ((a ^ 3 + b ^ 3 + c ^ 3) ^ 2) ^ 2 := by ring
    _ ≤ ((a ^ 4 + b ^ 4 + c ^ 4) * (a ^ 2 + b ^ 2 + c ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) h₁ 2
    _ = (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 :=
      mul_pow _ _ _
    _ ≤ (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 * (3 * (a ^ 4 + b ^ 4 + c ^ 4)) :=
      mul_le_mul_of_nonneg_left h₂ (sq_nonneg _)
    _ = 3 * (a ^ 4 + b ^ 4 + c ^ 4) ^ 3 := by ring
end

-- forge:entry lw_19571 kind=disproved origin=external
section
/- $\frac{x^4 -{x^2} {y^2}}{x^3 +2y^3} \geq \frac{x^4}{x^3 +2y^3} - \frac{x}{3}$ -/
theorem lw_19571_disproof : ¬ (∀ (x y : ℝ),
    (x^4 - x^2 * y^2) / (x^3 + 2 * y^3) ≥
      x^4 / (x^3 + 2 * y^3) - x / 3) := by
  intro h
  have hbad := h (-1) 0
  norm_num at hbad
end

-- forge:entry lw_23000 kind=disproved origin=external
section
/- If $a,\,b,\,c>0$ , prove that: $3(x+y)^{2}(y+z)^{2}(z+x)^{2}(x+y+z)\ge 16(x^{2}+y^{2}+z^{2}+xy+yz+zx)^{2}xyz$ -/
theorem lw_23000_disproof : ¬ (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z),
    3 * (x + y) ^ 2 * (y + z) ^ 2 * (z + x) ^ 2 * (x + y + z) ≥
      16 * (x ^ 2 + y ^ 2 + z ^ 2 + x * y + y * z + z * x) ^ 2 * x * y * z) := by
  intro h
  have hbad := h 1 1 3 (by norm_num) (by norm_num) (by norm_num)
  norm_num at hbad
end

-- forge:entry lw_20194 kind=proved origin=external
section
/- Given the sequence $a_{n+2}=a_{n+1}+a_n$ with initial conditions $a_1=-1, a_2=1$, and $d$ is an integer. Prove that there exist infinitely many positive integers $n$ such that $d$ divides $a_n$. -/
theorem lw_20194 (d : ℤ) (a : ℕ → ℤ)
    (a0 : a 1 = -1 ∧ a 2 = 1)
    (a_rec : ∀ n, a (n + 2) = a (n + 1) + a n) :
    ∃ infinitely_many n : ℕ, d ∣ a n := by
  refine ⟨0, 3, ?_⟩
  have h3 : a 3 = 0 := by
    simpa [a0.1, a0.2] using a_rec 1
  rw [h3]
  exact dvd_zero d
end

-- forge:entry lw_12997 kind=proved origin=external
section
/- Let a,b,c be positive real numbers. Prove that: \n $\frac{a(a-2b+c)}{ab+1} + \frac{b(b-2c+a)}{bc+1} + \frac{c(c-2a+b)}{ac+1} \geq 0$ -/
lemma lw_12997_aux1 {K : Type*} [CommRing K] [LinearOrder K]
    [IsStrictOrderedRing K] (a b c : K) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hab : a ≤ b) (hac : a ≤ c) :
    0 ≤ a * (a - 2 * b + c) * (b * c + 1) * (c * a + 1) +
      b * (b - 2 * c + a) * (c * a + 1) * (a * b + 1) +
      c * (c - 2 * a + b) * (a * b + 1) * (b * c + 1) := by
  have hx : 0 ≤ b - a := sub_nonneg.mpr hab
  have hy : 0 ≤ c - a := sub_nonneg.mpr hac
  have hq : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a := by
    nlinarith only [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  calc
    0 ≤ (1 + 3 * a ^ 2) *
          (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) +
        a * ((b - a) ^ 3 + 3 * (b - a) * (c - a) ^ 2 + (c - a) ^ 3) +
        (b - a) * (c - a) ^ 2 * ((b - a) + (c - a)) +
        a * b * c * (a * (b - c) ^ 2 + b * (c - a) ^ 2 + c * (a - b) ^ 2) := by
      positivity
    _ = a * (a - 2 * b + c) * (b * c + 1) * (c * a + 1) +
        b * (b - 2 * c + a) * (c * a + 1) * (a * b + 1) +
        c * (c - 2 * a + b) * (a * b + 1) * (b * c + 1) := by
      ring

theorem lw_12997 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a * (a - 2 * b + c) / (a * b + 1) +
      b * (b - 2 * c + a) / (b * c + 1) +
      c * (c - 2 * a + b) / (c * a + 1)) ≥ 0 := by
  have hn : 0 ≤ a * (a - 2 * b + c) * (b * c + 1) * (c * a + 1) +
      b * (b - 2 * c + a) * (c * a + 1) * (a * b + 1) +
      c * (c - 2 * a + b) * (a * b + 1) * (b * c + 1) := by
    rcases le_total a b with hab | hba
    · rcases le_total a c with hac | hca
      · exact lw_12997_aux1 a b c ha.le hb.le hc.le hab hac
      · simpa only [add_comm, add_left_comm, add_assoc] using
          lw_12997_aux1 c a b hc.le ha.le hb.le hca (hca.trans hab)
    · rcases le_total b c with hbc | hcb
      · simpa only [add_comm, add_left_comm, add_assoc] using
          lw_12997_aux1 b c a hb.le hc.le ha.le hbc hba
      · simpa only [add_comm, add_left_comm, add_assoc] using
          lw_12997_aux1 c a b hc.le ha.le hb.le (hcb.trans hba) hcb
  have hab : 0 < a * b + 1 := by positivity
  have hbc : 0 < b * c + 1 := by positivity
  have hca : 0 < c * a + 1 := by positivity
  have heq : a * (a - 2 * b + c) / (a * b + 1) +
      b * (b - 2 * c + a) / (b * c + 1) +
      c * (c - 2 * a + b) / (c * a + 1) =
      (a * (a - 2 * b + c) * (b * c + 1) * (c * a + 1) +
        b * (b - 2 * c + a) * (c * a + 1) * (a * b + 1) +
        c * (c - 2 * a + b) * (a * b + 1) * (b * c + 1)) /
        ((a * b + 1) * (b * c + 1) * (c * a + 1)) := by
    field_simp [ne_of_gt hab, ne_of_gt hbc, ne_of_gt hca]
  rw [heq]
  exact div_nonneg hn (by positivity)
end

-- forge:entry lw_25490 kind=proved origin=external
section
/- Let be given $ a,b,c \in [1,2]$ . Prove that \n $ (a+b+c)(\frac1a+\frac1b+\frac1c) \leq 10$ -/
theorem lw_25490 (a b c : ℝ) (ha : 1 ≤ a ∧ a ≤ 2)
    (hb : 1 ≤ b ∧ b ≤ 2) (hc : 1 ≤ c ∧ c ≤ 2) :
    (a + b + c) * (1 / a + 1 / b + 1 / c) ≤ 10 := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha.1
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb.1
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc.1
  have ha1 : 0 ≤ a - 1 := sub_nonneg.mpr ha.1
  have hb1 : 0 ≤ b - 1 := sub_nonneg.mpr hb.1
  have hc1 : 0 ≤ c - 1 := sub_nonneg.mpr hc.1
  have ha2 : 0 ≤ 2 - a := sub_nonneg.mpr ha.2
  have hb2 : 0 ≤ 2 - b := sub_nonneg.mpr hb.2
  have hc2 : 0 ≤ 2 - c := sub_nonneg.mpr hc.2
  have hnonneg : 0 ≤
      (2 - a) * (2 - b) * (2 - c) +
      8 * (a - 1) * (b - 1) * (c - 1) +
      (b + c) * (a - 1) * (2 - a) +
      (a + c) * (b - 1) * (2 - b) +
      (a + b) * (c - 1) * (2 - c) := by
    positivity
  have hpoly : (a + b + c) * (a * b + a * c + b * c) ≤
      10 * (a * b * c) := by
    nlinarith only [hnonneg]
  have habc : 0 < a * b * c := by positivity
  have heq : (a + b + c) * (1 / a + 1 / b + 1 / c) =
      ((a + b + c) * (a * b + a * c + b * c)) / (a * b * c) := by
    field_simp
    <;> ring
  rw [heq]
  exact (div_le_iff₀ habc).2 hpoly
end

-- forge:entry lw_24088 kind=proved origin=external
section
/- Let $a, b > 1$ . Prove that $\frac{a}{\sqrt{a^2+1}}+\frac{b}{\sqrt{b^2+1}} \le \frac{2\sqrt{ab}}{\sqrt{ab+1}}$ -/
lemma lw_24088_aux1 (p t : ℝ) (hp : 1 ≤ p) (ht : p + 1 ≤ t) :
    (p + 1) * (t ^ 2 + p ^ 2 - 1 + 2 * p * t) ≤ 4 * p * t ^ 2 := by
  have h : 0 ≤ (t - (p + 1)) * ((3 * p - 1) * t + (p - 1) * (p + 1)) := by
    apply mul_nonneg (by linarith)
    have ht0 : 0 ≤ t := by linarith
    have h1 : 0 ≤ (3 * p - 1) * t := mul_nonneg (by linarith) ht0
    have h2 : 0 ≤ (p - 1) * (p + 1) := mul_nonneg (by linarith) (by linarith)
    linarith
  nlinarith only [h]

theorem lw_24088 (a b : ℝ) (ha : 1 < a) (hb : 1 < b) :
    (a / Real.sqrt (a ^ 2 + 1) + b / Real.sqrt (b ^ 2 + 1)) ≤
      (2 * Real.sqrt (a * b)) / Real.sqrt (a * b + 1) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hp : 1 ≤ a * b := by nlinarith
  have hu0 : 0 < Real.sqrt (a ^ 2 + 1) := Real.sqrt_pos.2 (by positivity)
  have hv0 : 0 < Real.sqrt (b ^ 2 + 1) := Real.sqrt_pos.2 (by positivity)
  have hw0 : 0 < Real.sqrt (a * b + 1) := Real.sqrt_pos.2 (by positivity)
  have hu2 := Real.sq_sqrt (show 0 ≤ a ^ 2 + 1 by positivity)
  have hv2 := Real.sq_sqrt (show 0 ≤ b ^ 2 + 1 by positivity)
  have hw2 := Real.sq_sqrt (show 0 ≤ a * b + 1 by positivity)
  have hr2 := Real.sq_sqrt (show 0 ≤ a * b by positivity)
  have ht : a * b + 1 ≤ Real.sqrt (a ^ 2 + 1) * Real.sqrt (b ^ 2 + 1) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).1
    rw [mul_pow, hu2, hv2]
    nlinarith [sq_nonneg (a - b)]
  have hpoly := lw_24088_aux1 (a * b)
    (Real.sqrt (a ^ 2 + 1) * Real.sqrt (b ^ 2 + 1)) hp ht
  have hsum : (a / Real.sqrt (a ^ 2 + 1) + b / Real.sqrt (b ^ 2 + 1)) ^ 2 =
      ((Real.sqrt (a ^ 2 + 1) * Real.sqrt (b ^ 2 + 1)) ^ 2 +
        (a * b) ^ 2 - 1 + 2 * (a * b) *
          (Real.sqrt (a ^ 2 + 1) * Real.sqrt (b ^ 2 + 1))) /
        (Real.sqrt (a ^ 2 + 1) * Real.sqrt (b ^ 2 + 1)) ^ 2 := by
    field_simp
    nlinarith [hu2, hv2]
  apply (sq_le_sq₀ (by positivity) (by positivity)).1
  rw [hsum, div_pow, mul_pow (2 : ℝ) (Real.sqrt (a * b)) 2, hr2, hw2]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith only [hpoly]
end

-- forge:entry lw_29119 kind=proved origin=external
section
/- The second part is equivalent to Schur inequality. \n $ a^4+b^4+c^4+abc(a+b+c) \ge a^3(b+c)+b^3(c+a)+c^3(a+b).$ -/
theorem lw_29119 {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0)
    (hab : a ≥ b) (hbc : b ≥ c) (hca : c ≥ a) :
    a^4 + b^4 + c^4 + a * b * c * (a + b + c) ≥
      a^3 * (b + c) + b^3 * (c + a) + c^3 * (a + b) := by
  have hab_eq : a = b := le_antisymm (le_trans hca hbc) hab
  have hbc_eq : b = c := le_antisymm (le_trans hab hca) hbc
  rw [hab_eq, hbc_eq]
  exact le_of_eq (by ring)
end

-- forge:entry lw_29257 kind=proved origin=external
section
/- For $a,\,b,\,c\ge 2$ , prove that: $\log_{b+c}a+\log_{c+a}b+\log_{a+b}c>1$ -/
lemma lw_29257_aux1 (x y z : ℝ) (hx : 1 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z) :
    Real.log x / (Real.log y + Real.log z) ≤ Real.logb (y + z) x := by
  have hy0 : 0 < y := by linarith
  have hz0 : 0 < z := by linarith
  have hmul : y + z ≤ y * z := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hz)]
  have hlog : Real.log (y + z) ≤ Real.log y + Real.log z := by
    calc
      Real.log (y + z) ≤ Real.log (y * z) :=
        Real.log_le_log (by linarith) hmul
      _ = Real.log y + Real.log z := Real.log_mul (ne_of_gt hy0) (ne_of_gt hz0)
  exact div_le_div_of_nonneg_left (Real.log_nonneg hx)
    (Real.log_pos (by linarith)) hlog

theorem lw_29257 (a b c : ℝ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    Real.logb (b + c) a + Real.logb (c + a) b + Real.logb (a + b) c > 1 := by
  have h := an_nesbitt (Real.log a) (Real.log b) (Real.log c)
    (Real.log_pos (by linarith)) (Real.log_pos (by linarith))
    (Real.log_pos (by linarith))
  have h₁ := lw_29257_aux1 a b c (by linarith) hb hc
  have h₂ := lw_29257_aux1 b c a (by linarith) hc ha
  have h₃ := lw_29257_aux1 c a b (by linarith) ha hb
  linarith
end

-- forge:entry lw_25563 kind=proved origin=external
section
/- For any $a_1,a_2,a_3,a_4\in \mathbb{Z}^+$ that $a_1a_2=a_3a_4$. Then there exist $b_1,b_2,b_3,b_4\in \mathbb{Z}^+$ that $a_1=b_1b_2,a_2=b_3b_4,a_3=b_2b_3,a_4=b_1b_4$. -/
theorem lw_25563 {a₁ a₂ a₃ a₄ : ℤ} (h : a₁ * a₂ = a₃ * a₄) :
    ∃ b₁ b₂ b₃ b₄ : ℤ,
      a₁ = b₁ * b₂ ∧ a₂ = b₃ * b₄ ∧ a₃ = b₂ * b₃ ∧ a₄ = b₁ * b₄ := by
  by_cases ha₁ : a₁ = 0
  · subst a₁
    have hz : a₃ = 0 ∨ a₄ = 0 := mul_eq_zero.mp (by simpa using h.symm)
    rcases hz with rfl | rfl
    · exact ⟨a₄, 0, a₂, 1, by simp⟩
    · exact ⟨0, a₃, 1, a₂, by simp⟩
  · obtain ⟨b₂, b₁, hb₂, hb₁, heq⟩ :=
      exists_dvd_and_dvd_of_dvd_mul (show a₁ ∣ a₃ * a₄ from ⟨a₂, h.symm⟩)
    obtain ⟨b₃, h₃⟩ := hb₂
    obtain ⟨b₄, h₄⟩ := hb₁
    refine ⟨b₁, b₂, b₃, b₄, ?_, ?_, h₃, h₄⟩
    · simpa [mul_comm] using heq
    · apply mul_left_cancel₀ ha₁
      calc
        a₁ * a₂ = a₃ * a₄ := h
        _ = a₁ * (b₃ * b₄) := by rw [h₃, h₄, heq]; ring
end

-- forge:entry lw_28216 kind=proved origin=external
section
/- If $a,b,c$ are positive real numbers such that $a+b+c = 1$ , prove that $ (1+a)(1+b)(1+c) \geq 8 (1-a)(1-b)(1-c) . $ -/
theorem lw_28216 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a + b + c = 1) :
    (1 + a) * (1 + b) * (1 + c) ≥ 8 * (1 - a) * (1 - b) * (1 - c) := by
  have hq : a * b + b * c + c * a ≤ (1 : ℝ) / 3 := by
    have hsq := congrArg (fun x : ℝ => x ^ 2) hab
    nlinarith only [hsq, sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hs := Mathlib2.an_schur_deg_one a b c ha.le hb.le hc.le
  have hs' : 0 ≤ (a + b + c) ^ 3 + 9 * a * b * c -
      4 * (a + b + c) * (a * b + b * c + c * a) := by
    nlinarith only [hs]
  rw [hab] at hs'
  nlinarith only [hs', hq, hab]
end

-- forge:entry lw_31127 kind=disproved origin=external
section
/- Let $ a,b,c\ge 0$ such that $ abc=1$ .Prove that $ (a+b+c)^3\ge \frac{8}{3}(a^2+b^2+c^2)^2+a+b+c -/
theorem lw_31127_disproof :
    ¬ (∀ (a b c : ℝ) (habc : a * b * c = 1),
      (a + b + c) ^ 3 ≥ (8 / 3) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 + a + b + c) := by
  intro h
  have hcounter := h 2 1 (1 / 2) (by norm_num)
  norm_num at hcounter
end

-- forge:entry lw_32551 kind=disproved origin=external
section
/- Finding the solutions to that quadratic, we get: $w=\boxed{\frac{-1\pm \sqrt{13}}{2}}$ -/
theorem lw_32551_disproof :
    ¬ (∀ (w : ℂ), w^2 + w + 3 = 0 ↔
      w = (-1 + Real.sqrt 13) / 2 ∨ w = (-1 - Real.sqrt 13) / 2) := by
  intro h
  have hw := (h ((-1 + (Real.sqrt 13 : ℂ)) / 2)).mpr (Or.inl rfl)
  have hr : (((-1 : ℝ) + Real.sqrt 13) / 2)^2 +
      ((-1 : ℝ) + Real.sqrt 13) / 2 + 3 = 0 := by
    exact_mod_cast hw
  have hs : (Real.sqrt 13)^2 = 13 := Real.sq_sqrt (by norm_num)
  nlinarith
end

-- forge:entry lw_31976 kind=proved origin=external
section
/- prove that: \n\n $x^2+y^2+z^2\geq \frac{1}{2}(y+x)(y+z)(z+x)$\n\n$x,y,z \in (0,\frac{3}{4}]$ -/
theorem lw_31976 (x y z : ℝ) (hx : x ∈ Set.Icc 0 (3/4))
    (hy : y ∈ Set.Icc 0 (3/4)) (hz : z ∈ Set.Icc 0 (3/4)) :
    x^2 + y^2 + z^2 ≥ (1/2) * (y + x) * (y + z) * (z + x) := by
  have hxy : 0 ≤ (x - y)^2 * (4*x + 4*y + z) :=
    mul_nonneg (sq_nonneg _) (by linarith [hx.1, hy.1, hz.1])
  have hyz : 0 ≤ (y - z)^2 * (4*y + 4*z + x) :=
    mul_nonneg (sq_nonneg _) (by linarith [hx.1, hy.1, hz.1])
  have hzx : 0 ≤ (z - x)^2 * (4*z + 4*x + y) :=
    mul_nonneg (sq_nonneg _) (by linarith [hx.1, hy.1, hz.1])
  have hxu : 0 ≤ x^2 * (3/4 - x) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hx.2)
  have hyu : 0 ≤ y^2 * (3/4 - y) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hy.2)
  have hzu : 0 ≤ z^2 * (3/4 - z) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hz.2)
  nlinarith only [hxy, hyz, hzx, hxu, hyu, hzu]
end

-- forge:entry lw_36839 kind=disproved origin=external
section
/- $ \frac{x^2}{y+z}+\frac{y^2}{x+z}+\frac{z^2}{x+y} \geq \frac{(x+y+z)^2}{2(x+y+z)}=\frac{x+y+z}{2}$ -/
theorem lw_36839_disproof :
    ¬ (∀ (x y z : ℝ),
      (x^2 / (y + z) + y^2 / (x + z) + z^2 / (x + y)) ≥
        (x + y + z) / 2) := by
  intro h
  have hbad := h (-1) (-1) (-2)
  norm_num at hbad
end

-- forge:entry lw_29567 kind=proved origin=external
section
/- Assume that $a,b,c,d>0$ ,prove that \n $\frac{a^2-bd}{b+d+2c}+\frac{b^2-ca}{c+a+2d}+\frac{c^2-db}{d+b+2a}+\frac{d^2-ac}{a+c+2b}\ge 0$ -/
theorem lw_29567_aux1 {K : Type*} [Field K] [CharZero K]
    (a b c d : K) (h₁ : b + d + 2 * c ≠ 0) (h₂ : d + b + 2 * a ≠ 0) :
    (a ^ 2 - b * d) / (b + d + 2 * c) +
      (c ^ 2 - d * b) / (d + b + 2 * a) =
    (a + c - b - d) / 2 +
      (4 * (a + c) * (a - c) ^ 2 + (a + b + c + d) * (b - d) ^ 2) /
        (2 * (b + d + 2 * c) * (d + b + 2 * a)) := by
  field_simp (discharger := solve
    | norm_num
    | (convert h₁ using 1 <;> ring)
    | (convert h₂ using 1 <;> ring)
    | (convert mul_ne_zero h₁ h₂ using 1 <;> ring))
  <;> ring

theorem lw_29567 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) :
    (a^2 - b * d)/(b + d + 2 * c) +
    (b^2 - c * a)/(c + a + 2 * d) +
    (c^2 - d * b)/(d + b + 2 * a) +
    (d^2 - a * c)/(a + c + 2 * b) ≥ 0 := by
  have h₁ : 0 < b + d + 2 * c := by positivity
  have h₂ : 0 < d + b + 2 * a := by positivity
  have h₃ : 0 < c + a + 2 * d := by positivity
  have h₄ : 0 < a + c + 2 * b := by positivity
  have hp : (a + c - b - d) / 2 ≤
      (a ^ 2 - b * d) / (b + d + 2 * c) +
        (c ^ 2 - d * b) / (d + b + 2 * a) := by
    rw [lw_29567_aux1 a b c d (ne_of_gt h₁) (ne_of_gt h₂)]
    have hr : 0 ≤
        (4 * (a + c) * (a - c) ^ 2 + (a + b + c + d) * (b - d) ^ 2) /
          (2 * (b + d + 2 * c) * (d + b + 2 * a)) := by positivity
    linarith
  have hq : (b + d - c - a) / 2 ≤
      (b ^ 2 - c * a) / (c + a + 2 * d) +
        (d ^ 2 - a * c) / (a + c + 2 * b) := by
    rw [lw_29567_aux1 b c d a (ne_of_gt h₃) (ne_of_gt h₄)]
    have hr : 0 ≤
        (4 * (b + d) * (b - d) ^ 2 + (b + c + d + a) * (c - a) ^ 2) /
          (2 * (c + a + 2 * d) * (a + c + 2 * b)) := by positivity
    linarith
  linarith
end

-- forge:entry lw_41940 kind=proved origin=external
section
/- Let $a,b,c$ be non-negative reals such that $ab+bc+ca=1$. Prove that $\frac{1}{a+b}+\frac{1}{b+c}+\frac{1}{c+a}+\frac{1}{a+b+c}\geq 3$. -/
theorem lw_41940 (a b c : ℝ) (hab : 0 ≤ a) (hbc : 0 ≤ b) (hca : 0 ≤ c) (habc : a * b + b * c + c * a = 1) : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) + 1 / (a + b + c) ≥ 3 := by
  have habpos : 0 < a + b := by
    by_contra h
    have ha : a = 0 := by linarith
    have hb : b = 0 := by linarith
    simp [ha, hb] at habc
  have hbcpos : 0 < b + c := by
    by_contra h
    have hb : b = 0 := by linarith
    have hc : c = 0 := by linarith
    simp [hb, hc] at habc
  have hcapos : 0 < c + a := by
    by_contra h
    have hc : c = 0 := by linarith
    have ha : a = 0 := by linarith
    simp [hc, ha] at habc
  let p := a + b + c
  let r := a * b * c
  have hp : 0 < p := by dsimp [p]; linarith
  have hr : 0 ≤ r := mul_nonneg (mul_nonneg hab hbc) hca
  have hpsq : 3 ≤ p ^ 2 := by
    dsimp [p]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hpone : 1 ≤ p := by
    by_contra h
    have hmul : 0 ≤ p * (1 - p) := mul_nonneg hp.le (by linarith)
    nlinarith
  have hschur : 4 * p ≤ p ^ 3 + 9 * r := by
    have hs := Mathlib2.an_schur_deg_one a b c hab hbc hca
    have hq : p * (a * b + b * c + c * a) = p := by rw [habc]; ring
    dsimp [p, r] at *
    nlinarith only [hs, hq]
  have hpoly : 0 ≤ p ^ 3 - 3 * p ^ 2 + 2 * p + (3 * p - 1) * r := by
    by_cases htwo : 2 ≤ p
    · have hmul : 0 ≤ p * (p - 1) * (p - 2) :=
        mul_nonneg (mul_nonneg hp.le (by linarith)) (by linarith)
      have hrmul : 0 ≤ (3 * p - 1) * r := mul_nonneg (by linarith) hr
      nlinarith only [hmul, hrmul]
    · have hsmul : 0 ≤ (3 * p - 1) * (p ^ 3 + 9 * r - 4 * p) :=
        mul_nonneg (by linarith) (by linarith)
      have hquad : 0 ≤ 3 * p ^ 2 - 4 * p + 7 := by
        nlinarith [sq_nonneg (p - 1)]
      have hmul : 0 ≤ p * (2 - p) * (3 * p ^ 2 - 4 * p + 7) :=
        mul_nonneg (mul_nonneg hp.le (by linarith)) hquad
      nlinarith only [hsmul, hmul]
  have hden : (a + b) * (b + c) * (c + a) = p - r := by
    calc
      (a + b) * (b + c) * (c + a) = p * (a * b + b * c + c * a) - r := by
        dsimp [p, r]
        ring
      _ = p - r := by rw [habc]; ring
  have hpr : 0 < p - r := by
    rw [← hden]
    exact mul_pos (mul_pos habpos hbcpos) hcapos
  have hpair : (b + c) * (c + a) + (c + a) * (a + b) + (a + b) * (b + c) = p ^ 2 + 1 := by
    dsimp [p]
    nlinarith only [habc]
  have hfrac : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) + 1 / (a + b + c) =
      (p * (p ^ 2 + 1) + (p - r)) / (p * (p - r)) := by
    calc
      _ = (p * ((b + c) * (c + a) + (c + a) * (a + b) + (a + b) * (b + c)) +
          (a + b) * (b + c) * (c + a)) / (p * ((a + b) * (b + c) * (c + a))) := by
        dsimp [p]
        field_simp [ne_of_gt habpos, ne_of_gt hbcpos, ne_of_gt hcapos,
          ne_of_gt (show 0 < a + b + c from hp)]
        <;> ring
      _ = _ := by rw [hden, hpair]
  rw [hfrac]
  apply (le_div_iff₀ (mul_pos hp hpr)).2
  nlinarith only [hpoly]
end

end Mathlib2
