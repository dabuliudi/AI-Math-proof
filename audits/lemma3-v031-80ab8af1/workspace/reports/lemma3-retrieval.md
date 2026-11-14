# Lemma 3 Mathlib 检索报告

本地固定版本源码；used 表示是否在新证明中显式调用。因子分解路线作为备选，最终采用单位性质路线。

## Polynomial.isUnit_iff_degree_eq_zero

来源：lean\.lake\packages\mathlib\Mathlib\Algebra\Polynomial\FieldDivision.lean:286；Mathlib 定理复用。

```lean
theorem isUnit_iff_degree_eq_zero : IsUnit p ↔ degree p = 0 :=
  ⟨degree_eq_zero_of_isUnit, fun h =>
    have : degree p ≤ 0 := by simp [*, le_refl]
```

## Polynomial.degree_eq_natDegree

来源：lean\.lake\packages\mathlib\Mathlib\Algebra\Polynomial\Degree\Definitions.lean:93；Mathlib 定理复用。

```lean
theorem degree_eq_natDegree (hp : p ≠ 0) : degree p = (natDegree p : WithBot ℕ) := by
  let ⟨n, hn⟩ := not_forall.1 (mt Option.eq_none_iff_forall_not_mem.2 (mt degree_eq_bot.1 hp))
  have hn : degree p = some n := Classical.not_not.1 hn
```

## UniqueFactorizationMonoid.radical_radical

来源：lean\.lake\packages\mathlib\Mathlib\RingTheory\Radical.lean:268；Mathlib 定理复用。

```lean
lemma radical_radical : radical (radical a) = radical a :=
  radical_eq_of_primeFactors_eq primeFactors_radical

```

## UniqueFactorizationMonoid.radical_of_isUnit

来源：lean\.lake\packages\mathlib\Mathlib\RingTheory\Radical.lean:180；Mathlib 定理复用。

```lean
theorem radical_of_isUnit (h : IsUnit a) : radical a = 1 :=
  (radical_eq_of_associated (associated_one_iff_isUnit.mpr h)).trans radical_one

```

## UniqueFactorizationMonoid.radical_eq_one_iff

来源：lean\.lake\packages\mathlib\Mathlib\RingTheory\Radical.lean:259；Mathlib 定理复用。

```lean
theorem radical_eq_one_iff : radical a = 1 ↔ a = 0 ∨ IsUnit a := by
  refine ⟨?_, (Or.elim · (by simp +contextual) radical_of_isUnit)⟩
  intro h
```

## UniqueFactorizationMonoid.radical_ne_zero

来源：lean\.lake\packages\mathlib\Mathlib\RingTheory\Radical.lean:212；Mathlib 定理复用。

```lean
@[simp] theorem radical_ne_zero [Nontrivial M] : radical a ≠ 0 := by
  rw [radical, ← Finset.prod_val]
  apply Multiset.prod_ne_zero
```

## Polynomial.natDegree_eq_zero_of_isUnit

来源：lean\.lake\packages\mathlib\Mathlib\Algebra\Polynomial\Degree\Units.lean:27；Mathlib 定理复用。

```lean
lemma natDegree_eq_zero_of_isUnit (h : IsUnit p) : natDegree p = 0 := by
  nontriviality R
  obtain ⟨q, hq⟩ := h.exists_right_inv
```

## Polynomial.natDegree_pos_iff_degree_pos

来源：lean\.lake\packages\mathlib\Mathlib\Algebra\Polynomial\Degree\Definitions.lean:511；Mathlib 定理复用。

```lean
theorem natDegree_pos_iff_degree_pos : 0 < natDegree p ↔ 0 < degree p :=
  lt_iff_lt_of_le_iff_le natDegree_le_iff_degree_le

```

## WithBot.coe_le_coe

来源：lean\.lake\packages\mathlib\Mathlib\Order\WithBot.lean:245；Mathlib 定理复用。

```lean
@[simp, norm_cast] lemma coe_le_coe : (a : WithBot α) ≤ b ↔ a ≤ b := by simp [le_def]

lemma not_coe_le_bot (a : α) : ¬(a : WithBot α) ≤ ⊥ := by simp [le_def]
```

## degree_radical_le

来源：lean\.lake\packages\mathlib\Mathlib\RingTheory\Polynomial\Radical.lean:22；检索参考（未直接用于证明）。

```lean
theorem degree_radical_le {a : k[X]} (h : a ≠ 0) : (radical a).degree ≤ a.degree :=
  degree_le_of_dvd radical_dvd_self h

```

## natDegree_radical_le

来源：lean\.lake\packages\mathlib\Mathlib\RingTheory\Polynomial\Radical.lean:25；检索参考（未直接用于证明）。

```lean
theorem natDegree_radical_le {a : k[X]} :
    (radical a).natDegree ≤ a.natDegree := by
  by_cases ha : a = 0
```

## UniqueFactorizationMonoid.dvd_radical_iff_of_irreducible

来源：lean\.lake\packages\mathlib\Mathlib\RingTheory\Radical.lean:223；检索参考（未直接用于证明）。

```lean
lemma dvd_radical_iff_of_irreducible (ha : Irreducible a) (hb : b ≠ 0) :
    a ∣ radical b ↔ a ∣ b := by
  constructor
```

## UniqueFactorizationMonoid.primeFactors

来源：lean\.lake\packages\mathlib\Mathlib\RingTheory\Radical.lean:67；检索参考（未直接用于证明）。

```lean
def primeFactors (a : M) : Finset M :=
  (normalizedFactors a).toFinset

```

## UniqueFactorizationMonoid.radical

来源：lean\.lake\packages\mathlib\Mathlib\RingTheory\Radical.lean:155；检索参考（未直接用于证明）。

```lean
def radical (a : M) : M :=
  (primeFactors a).prod id

```

## UniqueFactorizationMonoid.primeFactors_val_eq_normalizedFactors

来源：lean\.lake\packages\mathlib\Mathlib\RingTheory\Radical.lean:121；检索参考（未直接用于证明）。

```lean
lemma primeFactors_val_eq_normalizedFactors (ha : IsRadical a) :
    (primeFactors a).val = normalizedFactors a := by
  classical
```

## Polynomial.natDegree_multiset_prod

来源：lean\.lake\packages\mathlib\Mathlib\Algebra\Polynomial\BigOperators.lean:319；检索参考（未直接用于证明）。

```lean
theorem natDegree_multiset_prod (h : (0 : R[X]) ∉ t) :
    natDegree t.prod = (t.map natDegree).sum := by
  nontriviality R
```
