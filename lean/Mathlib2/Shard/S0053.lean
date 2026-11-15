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

end Mathlib2
