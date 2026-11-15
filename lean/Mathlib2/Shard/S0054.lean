/- Mathlib2 分片 54（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0053
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry x2611_15723_descents kind=definition origin=definition
section
def x2611_15723_descents {n : ℕ} (π : Equiv.Perm (Fin n)) : Finset ℕ :=
  (Finset.univ.filter (fun i : Fin n =>
    ∃ j : Fin n, j.val = i.val + 1 ∧ π j < π i)).image (fun i => i.val + 1)
end

-- forge:entry x2611_15512_set_polynomial kind=definition origin=definition
section
noncomputable def x2611_15512_set_polynomial {α : Type*} [Fintype α]
    (P : Set α → Prop) : MvPolynomial α ℝ := by
  classical
  exact ∑ A ∈ Finset.univ.powerset.filter (fun A : Finset α => P (↑A : Set α)),
    ∏ a ∈ A, MvPolynomial.X a
end

-- forge:entry x2611_16458_isBlock kind=definition origin=definition
section
def x2611_16458_isBlock {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  (∃ v ∈ S, ∃ w ∈ S, G.Adj v w) ∧
  (G.induce S).Connected ∧
  (∀ v ∈ S, (G.induce (S \ {v})).Connected) ∧
  ∀ T : Set V, S ⊆ T →
    (∃ v ∈ T, ∃ w ∈ T, G.Adj v w) →
    (G.induce T).Connected →
    (∀ v ∈ T, (G.induce (T \ {v})).Connected) → T = S
end

-- forge:entry x2611_16899_flagged_llt kind=definition origin=definition
section
noncomputable def x2611_16899_flagged_llt (n : ℕ) : MvPolynomial (Fin n) (RatFunc ℚ) :=
  Finset.univ.sum (fun w : Fin n → Fin n =>
    if ∀ j : Fin n, (w j).val < n - j.val then
      MvPolynomial.C (RatFunc.X ^
        ((Finset.univ : Finset (Fin n × Fin n)).filter
          (fun ij => ij.1 < ij.2 ∧ w ij.2 < w ij.1)).card) *
      Finset.univ.prod (fun j : Fin n => MvPolynomial.X (w j)) else 0)
end

-- forge:entry x2611_16338_tes kind=definition origin=definition
section
noncomputable def x2611_16338_tes {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {s : ℕ | 0 < s ∧ ∃ (φ : V → ℕ) (ψ : Sym2 V → ℕ),
    x2611_16338_totalLabeling G s φ ψ}
end

-- forge:entry x2611_15723_des kind=definition origin=definition
section
def x2611_15723_des {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ :=
  (x2611_15723_descents π).card
end

-- forge:entry x2611_15512_rayleigh_difference kind=definition origin=definition
section
noncomputable def x2611_15512_rayleigh_difference {α R : Type*} [CommRing R]
    (F : MvPolynomial α R) (e f : α) : MvPolynomial α R :=
  MvPolynomial.pderiv e F * MvPolynomial.pderiv f F -
    F * MvPolynomial.pderiv e (MvPolynomial.pderiv f F)
end

-- forge:entry x2611_16458_hasBalancedBlock kind=definition origin=definition
section
def x2611_16458_hasBalancedBlock {V : Type*} (P N : SimpleGraph V) : Prop :=
  ∃ S : Set V, x2611_16458_isBlock (P ⊔ N) S ∧
    x2611_16458_balanced (P.induce S) (N.induce S)
end

-- forge:entry x2611_15723_maj kind=definition origin=definition
section
def x2611_15723_maj {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ :=
  (x2611_15723_descents π).sum id
end

-- forge:entry x2611_15512_tutte kind=definition origin=definition
section
noncomputable def x2611_15512_tutte {α : Type*} [Fintype α]
    (M : Matroid α) (q : ℝ) : MvPolynomial α ℝ := by
  classical
  exact ∑ A ∈ M.E.toFinset.powerset,
    MvPolynomial.C ((q ^ (M.eRk (↑A : Set α)).toNat)⁻¹) *
      ∏ a ∈ A, MvPolynomial.X a
end

-- forge:entry x2611_16458_split kind=definition origin=definition
section
def x2611_16458_split {V : Type*} (P N : SimpleGraph V) (u : V) :
    SimpleGraph (Bool ⊕ {v : V // v ≠ u}) :=
  SimpleGraph.fromRel (fun a b => match a, b with
    | Sum.inl s, Sum.inl t => s ≠ t
    | Sum.inl s, Sum.inr w => if s then P.Adj u w.val else N.Adj u w.val
    | Sum.inr v, Sum.inr w => P.Adj v.val w.val
    | _, _ => False)
end

-- forge:entry x2611_15505_word_multiplicities kind=definition origin=definition
section
def x2611_15505_word_multiplicities (n : ℕ) (w : List ℕ) : Prop :=
  w.length = n * (n + 1) / 2 ∧ (∀ j ∈ w, j < n) ∧
  ∀ j : ℕ, j < n → w.count j = n - j
end

-- forge:entry lw_49950 kind=disproved origin=external
section
/- Show that $x \ln x$ is convex on the positive real numbers -/
theorem lw_49950_disproof :
    ¬ (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (a b : ℝ) (hab : a + b = 1),
      x * Real.log x + y * Real.log y ≤
        a * Real.log (a * x) + b * Real.log (b * y)) := by
  intro h
  have hbad := h 2 1 (by norm_num) (by norm_num) 1 0 (by norm_num)
  norm_num at hbad
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  linarith
end

-- forge:entry lw_50342 kind=disproved origin=external
section
/- Let $x,y,z>0$ ,prove \n${\frac { \left( {x}^{2}+{y}^{2}+{z}^{2} \right) ^{3}}{{x}^{3}+{y}^{3}+{z}^{3}}}\geq {\frac {729}{512}}\,{\frac { \left( y+z \right) ^{3} \left( z+x \right) ^{3} \left( x+y \right) ^{3}}{ \left( x+y+z \right) ^{2} \left( xy+xz+yz \right) ^{2}}}$ -/
theorem lw_50342_disproof : ¬ (∀ (x y z : ℝ),
    (x^2 + y^2 + z^2)^3 / (x^3 + y^3 + z^3) ≥
      729/512 * (y + z)^3 * (z + x)^3 * (x + y)^3 /
        (x + y + z)^2 * (x*y + x*z + y*z)^2) := by
  intro h
  have h1 := h 1 1 1
  norm_num at h1
end

-- forge:entry x2611_15358_D kind=definition origin=definition
section
noncomputable def x2611_15358_D (G : SimpleGraph (Fin 14)) : ℕ :=
  (Finset.univ.powersetCard 7).sum (fun U : Finset (Fin 14) =>
    Nat.card (G.induce (↑U : Set (Fin 14))).ConnectedComponent - 1)
end

-- forge:entry x2611_15723_cycleShuffle kind=definition origin=definition
section
noncomputable def x2611_15723_cycleShuffle {k l : ℕ}
    (σ : Equiv.Perm (Fin k)) (τ : Equiv.Perm (Fin l)) :
    Finset (Equiv.Perm (Fin (k + l))) := by
  classical
  exact Finset.univ.filter (fun π =>
    ∃ (e : Fin k ↪o Fin (k + l)) (f : Fin l ↪o Fin (k + l)),
      Disjoint (Set.range e) (Set.range f) ∧
      Set.range e ∪ Set.range f = Set.univ ∧
      (∀ i, π (e i) = e (σ i)) ∧ (∀ j, π (f j) = f (τ j)))
end

-- forge:entry x2611_15512_z_rayleigh kind=definition origin=definition
section
def x2611_15512_z_rayleigh {α : Type*} [Fintype α]
    (M : Matroid α) : Prop :=
  ∀ (q : ℝ), 0 < q → q ≤ 1 →
    ∀ (e f : α), e ∈ M.E → f ∈ M.E → e ≠ f →
      ∀ (x : α → ℝ), (∀ a ∈ M.E, 0 < x a) →
        0 ≤ MvPolynomial.eval x
          (x2611_15512_rayleigh_difference (x2611_15512_tutte M q) e f)
end

-- forge:entry x2611_16458_twoConnected kind=definition origin=definition
section
def x2611_16458_twoConnected {V : Type*} [Finite V] (G : SimpleGraph V) : Prop :=
  3 ≤ Nat.card V ∧ G.Connected ∧
    ∀ v : V, (G.induce {w : V | w ≠ v}).Connected
end

-- forge:entry x2611_15008_components kind=definition origin=definition
section
noncomputable def x2611_15008_components {V E : Type*} (G : Graph V E) : ℕ :=
  Nat.card G.toSimpleGraph.ConnectedComponent
end

-- forge:entry x2611_15723_shuffle kind=definition origin=definition
section
noncomputable def x2611_15723_shuffle {k l : ℕ}
    (σ : Equiv.Perm (Fin k)) (τ : Equiv.Perm (Fin l)) :
    Finset (Equiv.Perm (Fin (k + l))) := by
  classical
  exact Finset.univ.filter (fun π =>
    (List.ofFn (fun i : Fin k => (σ i).val)).Sublist
      (List.ofFn (fun i : Fin (k + l) => (π i).val)) ∧
    (List.ofFn (fun j : Fin l => k + (τ j).val)).Sublist
      (List.ofFn (fun i : Fin (k + l) => (π i).val)))
end

end Mathlib2
