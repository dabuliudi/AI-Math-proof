/- Mathlib2 分片 55（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0053
import Mathlib2.Shard.S0054
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry x2611_15512_simple kind=definition origin=definition
section
def x2611_15512_simple {α : Type*} (M : Matroid α) : Prop :=
  ∀ (A : Set α), A ⊆ M.E → A.encard ≤ 2 → M.Indep A
end

-- forge:entry x2611_15358_N kind=definition origin=definition
section
noncomputable def x2611_15358_N (G : SimpleGraph (Fin 14)) (k : ℕ) : ℕ :=
  (Finset.univ.powersetCard 7).sum (fun U : Finset (Fin 14) =>
    Nat.card {C : (G.induce (↑U : Set (Fin 14))).ConnectedComponent //
      Nat.card C.supp = k})
end

-- forge:entry x2611_16458_beta kind=definition origin=definition
section
noncomputable def x2611_16458_beta {V : Type*} [Finite V] (G : SimpleGraph V) : ℤ :=
  (-1 : ℤ) ^ Nat.card V * (x2611_16458_zeroFree G ⊥).derivative.eval 1
end

-- forge:entry lw_49727 kind=proved origin=external
section
/- If $x, y$ and $z$ are positive real number and $k > 1$ such that $(x+y+z)\left ( \frac{1}{x}+\frac{1}{y}+\frac{1}{z} \right )=9+\frac{8}{k^2-1},$ then $\frac{2(k+1)^3+(k-1)^3}{(k-1)(k+1)^2} \leqslant \frac{x^3+y^3+z^3}{xyz} \leqslant \frac{2(k-1)^3+(k+1)^3}{(k+1)(k-1)^2}.$ -/
lemma lw_49727_aux1 (x y z : ℝ) :
    0 ≤ (x + y + z) ^ 2 * (x * y + y * z + z * x) ^ 2 -
      4 * (x * y + y * z + z * x) ^ 3 - 4 * (x + y + z) ^ 3 * (x * y * z) +
      18 * (x + y + z) * (x * y + y * z + z * x) * (x * y * z) -
      27 * (x * y * z) ^ 2 := by
  calc
    0 ≤ (x - y) ^ 2 * (y - z) ^ 2 * (z - x) ^ 2 := by positivity
    _ = _ := by ring

lemma lw_49727_aux2 (p q r a t : ℝ) (hr : 0 < r) (hp : 0 ≤ p)
    (ha : a * r = p ^ 3) (ht : t * r = p * q)
    (hd : 0 ≤ p ^ 2 * q ^ 2 - 4 * q ^ 3 - 4 * p ^ 3 * r +
      18 * p * q * r - 27 * r ^ 2) :
    4 * a ^ 2 - (t ^ 2 + 18 * t - 27) * a + 4 * t ^ 3 ≤ 0 := by
  have he : (4 * a ^ 2 - (t ^ 2 + 18 * t - 27) * a + 4 * t ^ 3) * r ^ 3 =
      -p ^ 3 * (p ^ 2 * q ^ 2 - 4 * q ^ 3 - 4 * p ^ 3 * r +
        18 * p * q * r - 27 * r ^ 2) := by
    calc
      _ = (a * r) * (4 * (a * r) * r - (t * r) ^ 2 -
          18 * (t * r) * r + 27 * r ^ 2) + 4 * (t * r) ^ 3 := by ring
      _ = _ := by rw [ha, ht]; ring
  have hm : (4 * a ^ 2 - (t ^ 2 + 18 * t - 27) * a + 4 * t ^ 3) * r ^ 3 ≤ 0 := by
    rw [he]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (pow_nonneg hp 3)) hd
  exact nonpos_of_mul_nonpos_left hm (pow_pos hr 3)

lemma lw_49727_aux3 (a l u : ℝ) (hlu : l ≤ u)
    (h : (a - l) * (a - u) ≤ 0) : l ≤ a ∧ a ≤ u := by
  rcases mul_nonpos_iff.mp h with h | h <;> constructor <;> linarith [h.1, h.2]

theorem lw_49727 (x y z k : ℝ) (hx : 0 < x ∧ 0 < y ∧ 0 < z) (hy : k > 1) :
    (x + y + z) * (1 / x + 1 / y + 1 / z) = 9 + 8 / (k ^ 2 - 1) →
      (2 * (k + 1) ^ 3 + (k - 1) ^ 3) / ((k - 1) * (k + 1) ^ 2) ≤
        (x ^ 3 + y ^ 3 + z ^ 3) / (x * y * z) ∧
      (x ^ 3 + y ^ 3 + z ^ 3) / (x * y * z) ≤
        (2 * (k - 1) ^ 3 + (k + 1) ^ 3) / ((k + 1) * (k - 1) ^ 2) := by
  intro h
  rcases hx with ⟨hx, hy', hz⟩
  have hx0 := ne_of_gt hx
  have hy0 := ne_of_gt hy'
  have hz0 := ne_of_gt hz
  have hm : 0 < k - 1 := by linarith
  have hp : 0 < k + 1 := by linarith
  have hd : 0 < k ^ 2 - 1 := by nlinarith
  have hm0 := ne_of_gt hm
  have hp0 := ne_of_gt hp
  have hd0 := ne_of_gt hd
  let p := x + y + z
  let q := x * y + y * z + z * x
  let r := x * y * z
  let t := 9 + 8 / (k ^ 2 - 1)
  let a := p ^ 3 / r
  let l := (3 * k + 1) ^ 3 / ((k - 1) * (k + 1) ^ 2)
  let u := (3 * k - 1) ^ 3 / ((k + 1) * (k - 1) ^ 2)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr0 := ne_of_gt hr
  have ha : a * r = p ^ 3 := by dsimp [a]; exact div_mul_cancel₀ _ hr0
  have ht : t * r = p * q := by
    dsimp [t]
    rw [← h]
    dsimp [r, p, q]
    field_simp
    <;> ring
  have hquad := lw_49727_aux2 p q r a t hr (by dsimp [p]; positivity)
    ha ht (lw_49727_aux1 x y z)
  have hsum : 4 * (l + u) = t ^ 2 + 18 * t - 27 := by
    dsimp [l, u, t]
    field_simp
    <;> ring
  have hprod : l * u = t ^ 3 := by
    dsimp [l, u, t]
    field_simp
    <;> ring
  have hdiff : u - l = 16 * k / (k ^ 2 - 1) ^ 2 := by
    dsimp [l, u]
    field_simp
    <;> ring
  have hlu : l ≤ u := by
    have hk : 0 ≤ k := by linarith
    have : 0 ≤ u - l := by rw [hdiff]; positivity
    linarith
  have hpoly : (a - l) * (a - u) ≤ 0 := by
    calc
      _ = (4 * a ^ 2 - (t ^ 2 + 18 * t - 27) * a + 4 * t ^ 3) / 4 := by
        rw [← hsum, ← hprod]
        ring
      _ ≤ 0 := by linarith [hquad]
  obtain ⟨hal, hau⟩ := lw_49727_aux3 a l u hlu hpoly
  have hval : (x ^ 3 + y ^ 3 + z ^ 3) / (x * y * z) = a - 3 * t + 3 := by
    have ht' : t = p * q / r := (eq_div_iff hr0).mpr ht
    rw [ht']
    dsimp [a, p, q, r]
    field_simp
    <;> ring
  have hl : (2 * (k + 1) ^ 3 + (k - 1) ^ 3) / ((k - 1) * (k + 1) ^ 2) =
      l - 3 * t + 3 := by
    dsimp [l, t]
    field_simp
    <;> ring
  have hu : (2 * (k - 1) ^ 3 + (k + 1) ^ 3) / ((k + 1) * (k - 1) ^ 2) =
      u - 3 * t + 3 := by
    dsimp [u, t]
    field_simp
    <;> ring
  rw [hval, hl, hu]
  constructor <;> linarith
end

-- forge:entry lw_50616 kind=proved origin=external
section
/- Given $ x, y, z \geq\ 0$ and $ x+y+z=1.$ \n Prove that: $ \sqrt{\frac{xy}{xy+z}} \leq\ \frac{3}{2}$ -/
theorem lw_50616 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0)
    (h : x + y + z = 1) : √((x * y) / (x * y + z)) ≤ 3 / 2 := by
  have hfrac : (x * y) / (x * y + z) ≤ 1 :=
    div_le_one_of_le₀ (le_add_of_nonneg_right hz) (add_nonneg (mul_nonneg hx hy) hz)
  calc
    √((x * y) / (x * y + z)) ≤ 1 := Real.sqrt_le_one.mpr hfrac
    _ ≤ 3 / 2 := by norm_num
end

-- forge:entry x2611_15505_formal_word kind=definition origin=definition
section
def x2611_15505_formal_word (n : ℕ) (w : List ℕ) : Prop :=
  x2611_15505_word_multiplicities n w ∧
  ∀ j : ℕ, j + 1 < n →
    w.filter (fun k => k = j ∨ k = j + 1) =
      (List.replicate (n - j - 1) [j, j + 1]).flatten ++ [j]
end

-- forge:entry x2611_15723_noOrderIso kind=definition origin=definition
section
def x2611_15723_noOrderIso {k l : ℕ}
    (σ : Equiv.Perm (Fin k)) (τ : Equiv.Perm (Fin l)) : Prop :=
  ∀ (a : Fin k) (b : Fin l),
    ¬ ∃ e : {x : Fin k // σ.SameCycle a x} ≃o
        {y : Fin l // τ.SameCycle b y},
      ∀ x y : {z : Fin k // σ.SameCycle a z},
        σ x.val = y.val → τ (e x).val = (e y).val
end

-- forge:entry x2611_15512_normalized_tutte kind=definition origin=definition
section
noncomputable def x2611_15512_normalized_tutte {α : Type*} [Fintype α]
    (M : Matroid α) : MvPolynomial α (Polynomial ℝ) := by
  classical
  exact ∑ A ∈ M.E.toFinset.powerset,
    MvPolynomial.C ((Polynomial.X : Polynomial ℝ) ^ (3 - (M.eRk (↑A : Set α)).toNat)) *
      ∏ a ∈ A, MvPolynomial.X a
end

-- forge:entry x2611_16458_blockBetaProduct kind=definition origin=definition
section
noncomputable def x2611_16458_blockBetaProduct {V : Type*} [Finite V]
    (P N : SimpleGraph V) (u : V) : ℤ := by
  classical
  letI := Fintype.ofFinite V
  exact Finset.prod (Finset.univ.filter (fun S : Set V => x2611_16458_isBlock (P ⊔ N) S))
    (fun S => if hu : u ∈ S then
      x2611_16458_beta (x2611_16458_split (P.induce S) (N.induce S) ⟨u, hu⟩)
    else 1)
end

-- forge:entry x2611_15358_t kind=definition origin=definition
section
noncomputable def x2611_15358_t (G : SimpleGraph (Fin 14))
    (S : Finset (Fin 14)) : ℕ :=
  Nat.card {v : Fin 14 // ∀ x ∈ S, (Gᶜ).Adj x v}
end

-- forge:entry lw_50515 kind=disproved origin=external
section
/- Let $a,b,c$ be real numbers such that $a^2+b^2+c^2=2(ab+bc+ca) $ . Prove that\n$$abc\leq \frac{2}{25}(b+c)(c+a)(a+b) $$ -/
theorem lw_50515_disproof :
    ¬ (∀ (a b c : ℝ),
      a ^ 2 + b ^ 2 + c ^ 2 = 2 * (a * b + b * c + c * a) →
      a * b * c ≤ (2 / 25) * (b + c) * (c + a) * (a + b)) := by
  intro h
  have hfalse := h (-1) (-1) 0 (by norm_num)
  norm_num at hfalse
end

-- forge:entry x2611_15505_realizes kind=definition origin=definition
section
def x2611_15505_realizes (n : ℕ) (p : Polynomial ℝ) (w : List ℕ) : Prop :=
  p ≠ 0 ∧ p.natDegree = n ∧ x2611_15505_word_multiplicities n w ∧
  ∃ x : Fin w.length → ℝ, StrictMono x ∧
    ∀ j : ℕ, j < n →
      ((Polynomial.derivative : Polynomial ℝ → Polynomial ℝ)^[j] p).roots =
        (Finset.univ.filter (fun i : Fin w.length => w.get i = j)).val.map x
end

-- forge:entry x2611_15008_contract kind=definition origin=definition
section
def x2611_15008_contract {V E : Type*} (G : Graph V E) (S : Set E) :
    Graph (Quotient (Relation.EqvGen.setoid (fun u v : V => ∃ e ∈ S, G.IsLink e u v))) E :=
  (G.map (Quotient.mk (Relation.EqvGen.setoid (fun u v : V => ∃ e ∈ S, G.IsLink e u v)))).deleteEdges S
end

-- forge:entry x2611_15723_qchoose kind=definition origin=definition
section
def x2611_15723_qchoose (q : ℚ) (n k : ℕ) : ℚ :=
  ∑ S ∈ (Finset.range n).powersetCard k,
    q ^ ((∑ i ∈ S, i) - k * (k - 1) / 2)
end

-- forge:entry x2611_14754_direction kind=definition origin=definition
section
def x2611_14754_direction (d : ℕ) (v : Fin d → ℤ) : Prop :=
  v ≠ 0 ∧ ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1
end

-- forge:entry x2611_15512_graph_star kind=definition origin=definition
section
noncomputable def x2611_15512_graph_star {α β : Type*} [Fintype β]
    (E : Finset α) (p : α → β) : MvPolynomial α ℝ := by
  classical
  exact ∑ v : β,
    ((∏ a ∈ E.filter (fun a => p a = v), (1 + MvPolynomial.X a)) - 1)
end

-- forge:entry x2611_16458_edges kind=definition origin=definition
section
def x2611_16458_edges (n : ℕ) (E : List (ℕ × ℕ)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun v w => (v.val + 1, w.val + 1) ∈ E)
end

-- forge:entry x2611_15505_ordered_roots kind=definition origin=definition
section
def x2611_15505_ordered_roots (p : Polynomial ℝ) (m : ℕ) (x : Fin m → ℝ) : Prop :=
  p ≠ 0 ∧ p.natDegree = m ∧ StrictMono x ∧
  p.roots = Finset.univ.val.map x
end

-- forge:entry x2611_15008_bridge kind=definition origin=definition
section
noncomputable def x2611_15008_bridge {V E : Type*} (G : Graph V E) (e : E) : Prop :=
  e ∈ G.edgeSet ∧ x2611_15008_components G < x2611_15008_components (G.deleteEdges {e})
end

-- forge:entry x2611_15723_zchoose kind=definition origin=definition
section
def x2611_15723_zchoose (n k : ℤ) : ℕ :=
  if 0 ≤ n ∧ 0 ≤ k then Nat.choose n.toNat k.toNat else 0
end

end Mathlib2
