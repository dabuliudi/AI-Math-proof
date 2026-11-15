/- Mathlib2 分片 53（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0052
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry x2611_10200_standard kind=definition origin=definition
section
def x2611_10200_standard (g k N : ℕ) (H : ℕ → ℤ) : Prop :=
  H 1 = 1 ∧
  (∀ n : ℕ, 2 ≤ n → n ≤ g + k + 1 →
    H n = 1 + (Finset.Icc 1 (min g (n - 1))).sum (fun j => H (n - j))) ∧
  (∀ n : ℕ, g + k + 2 ≤ n →
    H n = (Finset.Icc 1 g).sum (fun j => H (n - j)) +
      (N : ℤ) * H (n - (g + k + 1)))
end

-- forge:entry x2611_16338_vertexSum kind=definition origin=definition
section
def x2611_16338_vertexSum {V : Type*} (φ : V → ℕ) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun u v => φ u + φ v, fun u v => Nat.add_comm (φ u) (φ v)⟩
end

-- forge:entry x2611_15210_rho_prime kind=definition origin=definition
section
noncomputable def x2611_15210_rho_prime (m : ℕ) : ℝ :=
  ((7 : ℝ) ^ (2 * m) / (7 + 21 * ((2 * m).choose m : ℝ))) ^
    (1 / (5 * (2 * (m : ℝ) - 1)))
end

-- forge:entry x2611_15379_hongQianPeriod kind=definition origin=definition
section
def x2611_15379_hongQianPeriod (k a : ℕ) : ℕ :=
  Nat.lcmUpto k /
    (max 1 (((Finset.range (k + 1)).filter (fun p =>
      Nat.Prime p ∧ ¬ p ∣ a ∧
        (Nat.lcmUpto k).factorization p ≤ (k + 1).factorization p)).sup
          (fun p => p ^ (Nat.lcmUpto k).factorization p)) *
      ∏ q ∈ (Nat.gcd a (Nat.lcmUpto k)).primeFactors,
        q ^ (Nat.lcmUpto k).factorization q)
end

-- forge:entry x2611_16899_atom_family kind=definition origin=definition
section
def x2611_16899_atom_family (n : ℕ) (τ : RatFunc ℚ)
    (A : (Fin n → ℕ) → MvPolynomial (Fin n) (RatFunc ℚ)) : Prop :=
  (∀ b, Antitone b → A b = Finset.univ.prod (fun i => MvPolynomial.X i ^ b i)) ∧
  ∀ (b : Fin n → ℕ) (i j : Fin n), j.val = i.val + 1 → b i < b j →
    (MvPolynomial.X i - MvPolynomial.X j) * A b =
      MvPolynomial.C (1 - τ) * MvPolynomial.X j *
        (A (b ∘ Equiv.swap i j) - MvPolynomial.rename (Equiv.swap i j) (A (b ∘ Equiv.swap i j))) +
      MvPolynomial.C τ * (MvPolynomial.X i - MvPolynomial.X j) *
        MvPolynomial.rename (Equiv.swap i j) (A (b ∘ Equiv.swap i j))
end

-- forge:entry x2611_10200_complete kind=definition origin=definition
section
def x2611_10200_complete (H : ℕ → ℤ) : Prop :=
  ∀ t : ℤ, 1 ≤ t → ∃ S : Finset ℕ,
    (∀ i ∈ S, 1 ≤ i) ∧ t = S.sum H
end

-- forge:entry x2611_15210_Q kind=definition origin=definition
section
noncomputable def x2611_15210_Q (n m K : ℕ) (p : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (K + 1), (n.choose (j * m) : ℝ) * p ^ (j * m) * (1 - p) ^ (n - j * m)
end

-- forge:entry x2611_16899_expansion kind=definition origin=definition
section
def x2611_16899_expansion (n d : ℕ)
    (P : MvPolynomial (Fin n) (RatFunc ℚ))
    (A : (Fin n → ℕ) → MvPolynomial (Fin n) (RatFunc ℚ))
    (c : (Fin n → ℕ) → RatFunc ℚ) : Prop :=
  P = Finset.univ.sum (fun γ : Fin n → Fin (d + 1) =>
    if Finset.univ.sum (fun i : Fin n => (γ i).val) = d then
      MvPolynomial.C (c (fun i => (γ i).val)) * A (fun i => (γ i).val) else 0)
end

-- forge:entry x2611_10200_B kind=definition origin=definition
section
def x2611_10200_B (H : ℕ → ℤ) (n : ℕ) : ℤ :=
  1 + (Finset.Icc 1 (n - 1)).sum H - H n
end

-- forge:entry x2611_16458_zeroFree kind=definition origin=definition
section
noncomputable def x2611_16458_zeroFree {V : Type*} [Finite V]
    (P N : SimpleGraph V) : Polynomial ℤ := by
  classical
  letI := Fintype.ofFinite V
  exact Finset.sum (P.edgeFinset.disjSum N.edgeFinset).powerset (fun F =>
    let P' : SimpleGraph V := SimpleGraph.fromEdgeSet {e | Sum.inl e ∈ F}
    let N' : SimpleGraph V := SimpleGraph.fromEdgeSet {e | Sum.inr e ∈ F}
    if x2611_16458_balanced P' N' then
      Polynomial.C ((-1 : ℤ) ^ F.card) *
        Polynomial.X ^ Nat.card (P' ⊔ N').ConnectedComponent
    else 0)
end

-- forge:entry x2611_15210_P kind=definition origin=definition
section
def x2611_15210_P : Fin 9 → Fin 5 → ℕ :=
  ![![0, 0, 0, 0, 0], ![0, 0, 1, 1, 0], ![0, 0, 1, 1, 1],
    ![0, 1, 0, 1, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 1, 1],
    ![1, 0, 0, 1, 1], ![1, 0, 1, 0, 0], ![1, 0, 1, 1, 0]]
end

-- forge:entry x2611_16338_totalLabeling kind=definition origin=definition
section
def x2611_16338_totalLabeling {V : Type*} (G : SimpleGraph V) (s : ℕ)
    (φ : V → ℕ) (ψ : Sym2 V → ℕ) : Prop :=
  (∀ v, 1 ≤ φ v ∧ φ v ≤ s) ∧
  (∀ e ∈ G.edgeSet, 1 ≤ ψ e ∧ ψ e ≤ s) ∧
  Set.InjOn (fun e => x2611_16338_vertexSum φ e + ψ e) G.edgeSet
end

-- forge:entry x2611_16899_counterexample_polynomial kind=definition origin=definition
section
noncomputable def x2611_16899_counterexample_polynomial : Polynomial ℚ :=
  Polynomial.X^5 + Polynomial.X^6 + 2*Polynomial.X^7 - Polynomial.X^10 +
  5*Polynomial.X^11 + 10*Polynomial.X^12 + 26*Polynomial.X^13 + 42*Polynomial.X^14 +
  58*Polynomial.X^15 + 66*Polynomial.X^16 + 59*Polynomial.X^17 + 42*Polynomial.X^18 +
  22*Polynomial.X^19 + 7*Polynomial.X^20 + Polynomial.X^21
end

-- forge:entry x2611_16458_numerator kind=definition origin=definition
section
noncomputable def x2611_16458_numerator (n : ℕ) (p : Polynomial ℤ) : Polynomial ℤ :=
  Finset.sum (Finset.range (n + 2)) (fun i =>
    Polynomial.C (Finset.sum (Finset.range i) (fun j =>
      (-1 : ℤ) ^ j * ((n + 1).choose j : ℤ) *
        p.eval ((i - j - 1 : ℕ) : ℤ))) * Polynomial.X ^ i)
end

-- forge:entry x2611_15210_binary_witness kind=definition origin=definition
section
def x2611_15210_binary_witness (m r L : ℕ) (B : ℝ) : Prop :=
  ∃ (N : ℕ) (a : Fin N → Fin r → ZMod m),
    B ≤ (N : ℝ) ∧ (∀ i j, a i j = 0 ∨ a i j = 1) ∧
    ∀ I : Finset (Fin N), I.card = L → ∑ i ∈ I, a i ≠ 0
end

-- forge:entry lw_46560 kind=disproved origin=external
section
/- Solve the inequality: \\(\\frac{a+b+c+d}{4} \\ge \\sqrt{\\sqrt{abcd}}\\) -/
theorem lw_46560_disproof :
    ¬ (∀ (a b c d : ℝ),
      (a + b + c + d) / 4 ≥ Real.sqrt (Real.sqrt (a * b * c * d))) := by
  intro h
  have hcounter := h (-4) 0 0 0
  norm_num at hcounter
end

-- forge:entry lw_47241 kind=proved origin=external
section
/- And for this, we have $2a^2+2b^2+c^2 \ge \frac{\sqrt{10}}{5}(2a+4b)c.$ -/
theorem lw_47241 (a b c : ℝ) :
    2 * a ^ 2 + 2 * b ^ 2 + c ^ 2 ≥
      (Real.sqrt 10 / 5) * (2 * a + 4 * b) * c := by
  have hs : (Real.sqrt (10 : ℝ)) ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have h₁ := sq_nonneg (Real.sqrt 10 * a - c)
  have h₂ := sq_nonneg (Real.sqrt 10 * b - 2 * c)
  ring_nf at h₁ h₂
  rw [hs] at h₁ h₂
  nlinarith
end

-- forge:entry lw_49560 kind=proved origin=external
section
/- Let $x;y;z>0$ and $x+y+z=3$ . Prove that: $\sum \frac{4+\sqrt{x}}{4-x}\geq 5$ -/
lemma lw_49560_aux1 (s : ℝ) (hs : 0 ≤ s) (h : s ^ 2 < 4) :
    (13 * s ^ 2 + 17) / 18 ≤ (4 + s) / (4 - s ^ 2) := by
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 18) (by linarith)).2
  have hp : 0 ≤ (s - 1) ^ 2 * (13 * s ^ 2 + 26 * s + 4) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  nlinarith [hp]

theorem lw_49560 (x y z : ℝ) (hx : 0 < x ∧ 0 < y ∧ 0 < z)
    (h : x + y + z = 3) :
    (4 + Real.sqrt x) / (4 - x) + (4 + Real.sqrt y) / (4 - y) +
      (4 + Real.sqrt z) / (4 - z) ≥ 5 := by
  obtain ⟨hx, hy, hz⟩ := hx
  have hsx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (le_of_lt hx)
  have hsy : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt (le_of_lt hy)
  have hsz : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt (le_of_lt hz)
  have hbx := lw_49560_aux1 (Real.sqrt x) (Real.sqrt_nonneg x) (by rw [hsx]; linarith)
  have hby := lw_49560_aux1 (Real.sqrt y) (Real.sqrt_nonneg y) (by rw [hsy]; linarith)
  have hbz := lw_49560_aux1 (Real.sqrt z) (Real.sqrt_nonneg z) (by rw [hsz]; linarith)
  rw [hsx] at hbx
  rw [hsy] at hby
  rw [hsz] at hbz
  linarith
end

-- forge:entry x2611_16899_prefix_height kind=definition origin=definition
section
def x2611_16899_prefix_height {n : ℕ} (b : Fin n → ℕ) (k : ℕ) : ℤ :=
  (k : ℤ) - Finset.univ.sum (fun i : Fin n => if i.val < k then (b i : ℤ) else 0)
end

-- forge:entry x2611_16338_edgeClass kind=definition origin=definition
section
def x2611_16338_edgeClass {V : Type*} (G : SimpleGraph V)
    (φ : V → ℕ) (r : ℕ) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ x2611_16338_vertexSum φ e = r}
end

end Mathlib2
