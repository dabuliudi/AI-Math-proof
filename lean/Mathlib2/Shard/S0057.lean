/- Mathlib2 分片 57（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0056
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry x2611_14198_point_count kind=definition origin=definition
section
noncomputable def x2611_14198_point_count (d p r : ℕ) [Fact p.Prime] : ℕ :=
  Nat.card {xy : GaloisField p r × GaloisField p r //
    xy.2 ^ 2 = (Polynomial.Chebyshev.C (GaloisField p r) (d : ℤ)).eval xy.1} +
    if d % 2 = 0 then 2 else 1
end

-- forge:entry x2611_15008_subdividedLoop kind=definition origin=definition
section
noncomputable def x2611_15008_subdividedLoop {V E : Type*} (G : Graph V E) (e : E) : Prop :=
  ∃ v, (x2611_15008_contract G (x2611_15008_seriesClass G e \ {e})).IsLoopAt e v
end

-- forge:entry lw_42459 kind=proved origin=external
section
/- Let $a,b,c\geq 0$ and $a+b+c \leq 2$ . Prove that $\frac{a}{1+ a + b + c} \cdot \frac{b}{1+ b + c} \cdot\frac{c}{1 + c} \leq \frac{2}{3}+\sqrt[3]{3}-\sqrt[3]{9}$ -/
theorem lw_42459 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 2) :
    a / (1 + a + b + c) * b / (1 + b + c) * c / (1 + c) ≤
      2 / 3 + (3 : ℝ) ^ (1 / 3) - (9 : ℝ) ^ (1 / 3) := by
  have hd₁ : 0 < 1 + a + b + c := by linarith
  have hd₂ : 0 < 1 + b + c := by linarith
  have hd₃ : 0 < 1 + c := by linarith
  have h₁ : a / (1 + a + b + c) ≤ (2 : ℝ) / 3 := by
    apply (div_le_iff₀ hd₁).2
    nlinarith
  have h₂ : b / (1 + b + c) ≤ (1 : ℝ) := by
    apply (div_le_iff₀ hd₂).2
    linarith
  have h₃ : c / (1 + c) ≤ (1 : ℝ) := by
    apply (div_le_iff₀ hd₃).2
    linarith
  have h₄ : 0 ≤ b / (1 + b + c) := div_nonneg hb (le_of_lt hd₂)
  have h₅ : 0 ≤ c / (1 + c) := div_nonneg hc (le_of_lt hd₃)
  have h₆ : a / (1 + a + b + c) * (b / (1 + b + c)) * (c / (1 + c)) ≤
      (2 : ℝ) / 3 := by
    calc
      _ ≤ (2 / 3 : ℝ) * 1 * 1 :=
        mul_le_mul (mul_le_mul h₁ h₂ h₄ (by norm_num)) h₃ h₅ (by norm_num)
      _ = _ := by ring
  norm_num at ⊢
  convert h₆ using 1 <;> ring
end

-- forge:entry lw_43620 kind=proved origin=external
section
/- Prove that if positive integers $x,y$ satisfy $x+y= 3$ , $x,y \ge 1$ then $9(x- 1)(y- 1) + (y^2 + y+ 1)(x + 1) + (x^2-x+ 1)(y- 1) \ge 9$ -/
theorem lw_43620 (x y : ℕ) (h₁ : 1 ≤ x ∧ 1 ≤ y) (h₂ : x + y = 3) :
    9 * (x - 1) * (y - 1) + (y^2 + y + 1) * (x + 1) +
      (x^2 - x + 1) * (y - 1) ≥ 9 := by
  have hcases : (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
end

-- forge:entry x2611_12360_modMem kind=definition origin=definition
section
def x2611_12360_modMem (T : ℝ) (I : Set ℝ) (a : ℝ) : Prop :=
  ∃ x ∈ I, ∃ m : ℤ, a = x + (m : ℝ) * T
end

-- forge:entry x2611_15008_Tutte kind=definition origin=definition
section
noncomputable def x2611_15008_Tutte {V E : Type*} [Fintype E] (G : Graph V E) (x y : ℝ) : ℝ := by
  classical
  exact G.edgeSet.toFinset.powerset.sum (fun A =>
    (x - 1) ^ (x2611_15008_components (G.restrict (A : Set E)) - x2611_15008_components G) *
    (y - 1) ^ (A.card + x2611_15008_components (G.restrict (A : Set E)) - G.vertexSet.ncard))
end

-- forge:entry x2611_14198_maximal kind=definition origin=definition
section
def x2611_14198_maximal (d p r : ℕ) [Fact p.Prime] : Prop :=
  (x2611_14198_point_count d p r : ℝ) =
    (p : ℝ) ^ r + 1 + 2 * (((d - 1) / 2 : ℕ) : ℝ) * Real.sqrt ((p : ℝ) ^ r)
end

-- forge:entry x2611_12360_red kind=definition origin=definition
section
def x2611_12360_red (n p s : ℕ) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  0 ≤ (⌊‖x‖ ^ 2⌋ : ℤ) % (p : ℤ) ∧
    (⌊‖x‖ ^ 2⌋ : ℤ) % (p : ℤ) < (s : ℤ)
end

-- forge:entry x2611_14198_minimal kind=definition origin=definition
section
def x2611_14198_minimal (d p r : ℕ) [Fact p.Prime] : Prop :=
  (x2611_14198_point_count d p r : ℝ) =
    (p : ℝ) ^ r + 1 - 2 * (((d - 1) / 2 : ℕ) : ℝ) * Real.sqrt ((p : ℝ) ^ r)
end

-- forge:entry x2611_12360_gap kind=definition origin=definition
section
noncomputable def x2611_12360_gap (p : ℕ)
    (A : Set (AddCircle (p : ℝ))) : ℝ :=
  sSup {l : ℝ | 0 ≤ l ∧ l ≤ (p : ℝ) ∧
    ∃ a : ℝ, ∀ t : ℝ, a < t → t < a + l →
      (t : AddCircle (p : ℝ)) ∉ A}
end

-- forge:entry x2611_14160_subdividedStar kind=definition origin=definition
section
def x2611_14160_subdividedStar (a b : ℕ) : SimpleGraph (Fin (1 + a + b)) :=
  SimpleGraph.fromRel (fun u v =>
    (u.val = 0 ∧ 1 ≤ v.val ∧ v.val ≤ a) ∨
    (1 ≤ u.val ∧ u.val ≤ b ∧ v.val = a + u.val))
end

-- forge:entry x2611_14198_character_sum kind=definition origin=definition
section
noncomputable def x2611_14198_character_sum (d : ℕ) (χ : DirichletCharacter ℂ d) : ℂ :=
  ∑ a ∈ Finset.Icc 1 ((d - 1) / 2), (-1 : ℂ) ^ (a + 1) * χ (a : ZMod d)
end

-- forge:entry lw_43263 kind=disproved origin=external
section
/- Prove that $\frac{4^n}{2\sqrt{n}}<\binom{2n}{n}<\frac{4^n}{\sqrt{2n}}$ for all natural numbers n -/
theorem lw_43263_disproof : ¬ (∀ (n : ℕ) (hn : n > 0),
    (4^n / (2 * Real.sqrt n)) < (2 * n).choose n ∧
    ((2 * n).choose n) < (4^n / Real.sqrt (2 * n))) := by
  intro h
  have h1 := (h 1 (by norm_num)).1
  norm_num at h1
end

-- forge:entry x2611_12360_G kind=definition origin=definition
section
noncomputable def x2611_12360_G (p M : ℕ) (u : ℝ) : ℝ :=
  sSup (Set.range (fun β : ℝ =>
    x2611_12360_gap p (Set.range (fun k : Fin M =>
      ((-u * (k.val : ℝ) ^ 2 - β * (k.val : ℝ) : ℝ) : AddCircle (p : ℝ))))))
end

-- forge:entry x2611_14160_copyWeight kind=definition origin=definition
section
noncomputable def x2611_14160_copyWeight {V W Γ : Type*} [Fintype V]
    [AddCommMonoid Γ] (G : SimpleGraph V) (w : Sym2 W → Γ) (f : V ↪ W) : Γ := by
  classical
  exact ∑ e ∈ G.edgeFinset, w (Sym2.map f e)
end

-- forge:entry x2611_14198_twist kind=definition origin=definition
section
noncomputable def x2611_14198_twist (d : ℕ) (χ : DirichletCharacter ℂ d) : DirichletCharacter ℂ (4 * d) :=
  DirichletCharacter.changeLevel (Nat.dvd_mul_left d 4) χ *
    DirichletCharacter.changeLevel (Nat.dvd_mul_right 4 d)
      (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))
end

-- forge:entry x2611_14160_zeroSumForces kind=definition origin=definition
section
def x2611_14160_zeroSumForces {V : Type*} [Fintype V]
    (G : SimpleGraph V) (m N : ℕ) : Prop :=
  ∀ w : Sym2 (Fin N) → ZMod m, ∃ f : V ↪ Fin N,
    x2611_14160_copyWeight G w f = 0
end

-- forge:entry x2611_14160_zeroSumRamsey kind=definition origin=definition
section
noncomputable def x2611_14160_zeroSumRamsey {V : Type*} [Fintype V]
    (G : SimpleGraph V) (m : ℕ) : ℕ :=
  sInf {N : ℕ | x2611_14160_zeroSumForces G m N}
end

-- forge:entry x2611_14160_ramsey kind=definition origin=definition
section
noncomputable def x2611_14160_ramsey {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ w : Sym2 (Fin N) → Fin r,
    ∃ (f : V ↪ Fin N) (c : Fin r),
      ∀ e ∈ G.edgeSet, w (Sym2.map f e) = c}
end

-- forge:entry x2611_14160_disjointCopies kind=definition origin=definition
section
def x2611_14160_disjointCopies {V : Type*} (t : ℕ) (G : SimpleGraph V) :
    SimpleGraph (Fin t × V) :=
  SimpleGraph.fromRel (fun u v => u.1 = v.1 ∧ G.Adj u.2 v.2)
end

end Mathlib2
