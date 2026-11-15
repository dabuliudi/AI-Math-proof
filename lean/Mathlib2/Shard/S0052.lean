/- Mathlib2 分片 52（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0051
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry x2611_11972_sharp kind=definition origin=definition
section
noncomputable def x2611_11972_sharp (k : List ℤ) : ℝ := by
  classical
  exact ∑' n : Fin k.length → ℕ, if Monotone n then
    (2 : ℝ) ^ (Finset.univ.image n).card *
      ∏ j : Fin k.length,
        (if k.get j < 0 then (-1 : ℝ) ^ (n j + 1) else 1) /
          ((n j + 1 : ℕ) : ℝ) ^ (k.get j).natAbs
    else 0
end

-- forge:entry x2611_16923_entries kind=definition origin=definition
section
noncomputable def x2611_16923_entries {r : ℕ} (k : Fin r → ℕ) : List (ℕ × (Fin r →₀ ℕ)) :=
  List.ofFn (fun i => (k i, Finsupp.single i 1))
end

-- forge:entry x2611_10200_a kind=definition origin=definition
section
noncomputable def x2611_10200_a (g : ℕ) (m : ℤ) : ℤ :=
  if m < 0 then 0 else
    PowerSeries.coeff m.toNat (PowerSeries.invOfUnit
      (((1 - PowerSeries.X) ^ 2 : PowerSeries ℤ) * x2611_10200_Q g) 1)
end

-- forge:entry x2611_15379_periodFormula kind=definition origin=definition
section
noncomputable def x2611_15379_periodFormula (k a b c : ℕ) (f : ℕ → ℂ) : ℕ := by
  classical
  let d := Nat.gcd a b
  let A := a / d
  let L := Nat.lcmUpto k
  let R : ℕ → ℕ → ℂ := fun p j =>
    f (p ^ (d.factorization p + c.factorization p + j)) /
      f (p ^ (d.factorization p + c.factorization p + j - 1))
  let M : ℕ → ℕ := fun p =>
    ((Finset.Icc 1 (L.factorization p)).filter
      (fun j => (k + 1).factorization p < j ∧ R p j ≠ 1)).sup id
  let K : ℕ → ℂ := fun p =>
    f (p ^ (d.factorization p + c.factorization p)) ^ k *
      ∏ j ∈ Finset.Icc 1 (min (L.factorization p) ((k + 1).factorization p)),
        R p j ^ ((k + 1) / p ^ j - 1)
  let e : ℕ → ℕ := fun p =>
    if 0 < M p then c.factorization p + M p
    else ((Finset.range (c.factorization p)).filter
      (fun j => f (p ^ (d.factorization p + j)) ^ k ≠ K p)).sup (fun j => j + 1)
  exact ∏ p ∈ ((c * L).primeFactors.filter (fun p => ¬ p ∣ A)), p ^ e p
end

-- forge:entry x2611_11287_centralizer_count kind=definition origin=definition
section
noncomputable def x2611_11287_centralizer_count {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (H : ℤ) : ℕ :=
  x2611_11287_lattice_count (Subalgebra.centralizer ℤ ({A} : Set (Matrix (Fin n) (Fin n) ℤ))).toSubmodule H
end

-- forge:entry x2611_15210_A kind=definition origin=definition
section
noncomputable def x2611_15210_A (L : ℕ) (G : Type*) [AddCommMonoid G] : ℕ :=
  x2611_15210_s L G - 1
end

-- forge:entry lw_46331 kind=proved origin=external
section
/- Let $x,y,z\geq 0,xy+yz+zx=1$ ,prove that: $y^5z+z^5x+x^5y\geq \frac{1}{27}(x+y+z)^5xyz$ -/
lemma lw_46331_aux1 (x y z : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) :
    (x + y + z) ^ 5 * x * y * z ≤
      27 * (x * y + y * z + z * x) * (x ^ 5 * y + y ^ 5 * z + z ^ 5 * x) := by
  obtain ⟨a, ha, rfl⟩ := exists_nonneg_add_of_le hxy
  obtain ⟨b, hb, rfl⟩ := exists_nonneg_add_of_le hyz
  apply sub_nonneg.mp
  calc
    0 ≤ x ^ 6 * (459 * a ^ 2 + 459 * a * b + 459 * b ^ 2) +
        x ^ 5 * (1764 * a ^ 3 + 2241 * a ^ 2 * b + 2457 * a * b ^ 2 + 990 * b ^ 3) +
        x ^ 4 * (2775 * a ^ 4 + 4200 * a ^ 3 * b + 4905 * a ^ 2 * b ^ 2 +
          3480 * a * b ^ 3 + 840 * b ^ 4) +
        x ^ 3 * (2305 * a ^ 5 + 3940 * a ^ 4 * b + 4660 * a ^ 3 * b ^ 2 +
          4400 * a ^ 2 * b ^ 3 + 2045 * a * b ^ 4 + 335 * b ^ 5) +
        x ^ 2 * (1073 * a ^ 6 + 1977 * a ^ 5 * b + 2160 * a ^ 4 * b ^ 2 +
          2330 * a ^ 3 * b ^ 3 + 1560 * a ^ 2 * b ^ 4 + 486 * a * b ^ 5 + 53 * b ^ 6) +
        x * (265 * a ^ 7 + 509 * a ^ 6 * b + 434 * a ^ 5 * b ^ 2 +
          420 * a ^ 4 * b ^ 3 + 355 * a ^ 3 * b ^ 4 + 151 * a ^ 2 * b ^ 5 + 26 * a * b ^ 6) +
        27 * a ^ 6 * (a + b) ^ 2 := by positivity
    _ = 27 * (x * (x + a) + (x + a) * (x + a + b) + (x + a + b) * x) *
        (x ^ 5 * (x + a) + (x + a) ^ 5 * (x + a + b) + (x + a + b) ^ 5 * x) -
        (x + (x + a) + (x + a + b)) ^ 5 * x * (x + a) * (x + a + b) := by ring

lemma lw_46331_aux2 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (x + y + z) ^ 5 * x * y * z ≤
      27 * (x * y + y * z + z * x) * (x ^ 5 * y + y ^ 5 * z + z ^ 5 * x) := by
  have hreverse (a b c : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
      (a + b + c) ^ 5 * a * b * c ≤
        27 * (a * b + b * c + c * a) * (a ^ 5 * c + c ^ 5 * b + b ^ 5 * a) := by
    have hb : 0 ≤ b := ha.trans hab
    have hc : 0 ≤ c := hb.trans hbc
    have hba : 0 ≤ b - a := sub_nonneg.mpr hab
    have hcb : 0 ≤ c - b := sub_nonneg.mpr hbc
    have hca : 0 ≤ c - a := sub_nonneg.mpr (hab.trans hbc)
    have hd : 0 ≤ (b - a) * (c - b) * (c - a) *
        (a ^ 3 + b ^ 3 + c ^ 3 + a ^ 2 * b + a ^ 2 * c + a * b ^ 2 +
          b ^ 2 * c + a * c ^ 2 + b * c ^ 2 + a * b * c) := by positivity
    have hcmp : a ^ 5 * b + b ^ 5 * c + c ^ 5 * a ≤
        a ^ 5 * c + c ^ 5 * b + b ^ 5 * a := by
      nlinarith only [hd]
    exact (lw_46331_aux1 a b c ha hab hbc).trans
      (mul_le_mul_of_nonneg_left hcmp (by positivity))
  rcases le_total x y with hxy | hyx
  · rcases le_total y z with hyz | hzy
    · exact lw_46331_aux1 x y z hx hxy hyz
    · rcases le_total x z with hxz | hzx
      · convert hreverse x z y hx hxz hzy using 1 <;> ring
      · convert lw_46331_aux1 z x y hz hzx hxy using 1 <;> ring
  · rcases le_total x z with hxz | hzx
    · convert hreverse y x z hy hyx hxz using 1 <;> ring
    · rcases le_total y z with hyz | hzy
      · convert lw_46331_aux1 y z x hy hyz hzx using 1 <;> ring
      · convert hreverse z y x hz hzy hyx using 1 <;> ring

theorem lw_46331 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0)
    (h : x * y + y * z + z * x = 1) :
    y ^ 5 * z + z ^ 5 * x + x ^ 5 * y ≥ (1 / 27) * (x + y + z) ^ 5 * x * y * z := by
  have hmain := lw_46331_aux2 x y z hx hy hz
  rw [h] at hmain
  nlinarith only [hmain]
end

-- forge:entry x2611_16923_blocks kind=definition origin=definition
section
noncomputable def x2611_16923_blocks {r : ℕ} (k : Fin r → ℕ)
    (c : Composition r) : List (ℕ × (Fin r →₀ ℕ)) :=
  List.ofFn (fun h : Fin c.length =>
    ((∑ j : Fin (c.blocksFun h), k (c.embedding h j)),
      ∑ j : Fin (c.blocksFun h), Finsupp.single (c.embedding h j) 1))
end

-- forge:entry x2611_15210_rho kind=definition origin=definition
section
noncomputable def x2611_15210_rho (m : ℕ) : ℝ :=
  ((9 : ℝ) ^ (2 * m) / (9 + 36 * ((2 * m).choose m : ℝ))) ^
    (1 / (5 * (2 * (m : ℝ) - 1)))
end

-- forge:entry x2611_10200_M kind=definition origin=definition
section
noncomputable def x2611_10200_M (g k : ℕ) : ℝ :=
  ((x2611_10200_a g ((g + k : ℕ) : ℤ) : ℝ) + 1) / (2 : ℝ) ^ g
end

-- forge:entry x2611_10667_p kind=definition origin=definition
section
noncomputable def x2611_10667_p (B C : ℕ) (t : ℚ) : Polynomial ℚ :=
  (-Polynomial.X) ^ B * Finset.sum (Finset.range (C + 2)) (fun i =>
    Polynomial.C ((1 - t) ^ ((C : ℤ) - (i : ℤ)) *
      (-t) ^ ((i : ℤ) - 1) *
      ((if i = 0 then 0 else (Nat.choose C (i - 1) : ℚ)) -
        t * (Nat.choose (C + 1) i : ℚ))) * Polynomial.X ^ i)
end

-- forge:entry x2611_15379_monotonicPeriod kind=definition origin=definition
section
def x2611_15379_monotonicPeriod (k a b c : ℕ) : ℕ :=
  (∏ p ∈ (c.primeFactors.filter (fun p => ¬ p ∣ a / Nat.gcd a b)),
    p ^ c.factorization p) *
  ∏ p ∈ ((Nat.lcmUpto k).primeFactors.filter (fun p =>
    ¬ p ∣ a / Nat.gcd a b ∧
      (k + 1).factorization p < (Nat.lcmUpto k).factorization p)),
    p ^ (Nat.lcmUpto k).factorization p
end

-- forge:entry x2611_11287_exceptional_count kind=definition origin=definition
section
noncomputable def x2611_11287_exceptional_count (n : ℕ) (H : ℤ) : ℕ :=
  Set.ncard {A : Matrix (Fin n) (Fin n) ℤ |
    (∀ i j, |A i j| ≤ H) ∧ n < x2611_11287_centralizer_dim (A.map (Int.castRingHom ℚ))}
end

-- forge:entry x2611_16899_alpha kind=definition origin=definition
section
def x2611_16899_alpha : Fin 14 → ℕ := ![0,0,1,2,0,1,2,0,1,2,0,1,2,2]
end

-- forge:entry x2611_10200_f kind=definition origin=definition
section
noncomputable def x2611_10200_f (g k N : ℕ) (m : ℤ) : ℤ :=
  if m < 0 then 0 else
    PowerSeries.coeff m.toNat
      ((1 - PowerSeries.C ((N : ℤ) - 1) * PowerSeries.X ^ k +
          PowerSeries.C ((N : ℤ) - 2) * PowerSeries.X ^ (k + 1)) *
        PowerSeries.invOfUnit
          (((1 - PowerSeries.X) ^ 2 : PowerSeries ℤ) *
            (x2611_10200_Q g - PowerSeries.C (N : ℤ) *
              PowerSeries.X ^ (g + k + 1))) 1)
end

-- forge:entry x2611_15210_alpha kind=definition origin=definition
section
noncomputable def x2611_15210_alpha (β : ℝ) : ℝ :=
  sInf {a : ℝ | 0 < a ∧ a ^ 5 = 12 * a + 8 * β}
end

-- forge:entry x2611_15379_N kind=definition origin=definition
section
noncomputable def x2611_15379_N (p j k : ℕ) (u z : ℤ) : ℕ :=
  ((Finset.Icc (0 : ℤ) (k : ℤ)).filter
    (fun i => (p : ℤ) ^ j ∣ z + u * i)).card
end

-- forge:entry x2611_11287_rank_count kind=definition origin=definition
section
noncomputable def x2611_11287_rank_count (n k : ℕ) (H : ℤ) : ℕ :=
  Set.ncard {A : Matrix (Fin n) (Fin n) ℤ |
    (∀ i j, |A i j| ≤ H) ∧ (A.map (Int.castRingHom ℚ)).rank = k}
end

-- forge:entry x2611_16899_key_family kind=definition origin=definition
section
def x2611_16899_key_family (n : ℕ)
    (K : (Fin n → ℕ) → MvPolynomial (Fin n) (RatFunc ℚ)) : Prop :=
  (∀ b, Antitone b → K b = Finset.univ.prod (fun i => MvPolynomial.X i ^ b i)) ∧
  ∀ (b : Fin n → ℕ) (i j : Fin n), j.val = i.val + 1 → b i < b j →
    (MvPolynomial.X i - MvPolynomial.X j) * K b =
      MvPolynomial.X i * K (b ∘ Equiv.swap i j) -
      MvPolynomial.X j * MvPolynomial.rename (Equiv.swap i j) (K (b ∘ Equiv.swap i j))
end

-- forge:entry x2611_16458_balanced kind=definition origin=definition
section
def x2611_16458_balanced {V : Type*} (P N : SimpleGraph V) : Prop :=
  ∃ ε : V → Bool,
    (∀ v w, P.Adj v w → ε v = ε w) ∧
    (∀ v w, N.Adj v w → ε v ≠ ε w)
end

end Mathlib2
