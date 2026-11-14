# Mathlib 检索独立验收：PASS（扩充原检索范围）

以下类型来自本轮真实Lean环境的ConstantInfo.type，由ppExpr完整打印；含全部隐式参数和实例假设，宇宙变量为多态参数。不是取源码连续三行猜测声明。只列本地五个声明直接使用的库定理/命题性实例；库内传递依赖不逐层展开。

总计18个直接Mathlib定理（含命题性实例）；原报告9项仅为显式数学主干，另有lt_of_lt_of_le及实例依赖。核心Lean基础定理详见all-direct-declarations.json。

## AddCancelMonoid.toIsCancelAdd — PASS

来源：D:\mathproof\lean\.lake\packages\mathlib\Mathlib\Algebra\Group\Defs.lean:758
方式：Lean实例推导中的命题性实例。用途：提供域上多项式非平凡、整环、唯一分解等实例；完整前提及使用者见type和used_by。
使用者：mathlib2_unit_of_radical_unit, mathlib2_radical_natDegree_ne_zero, mathlib2_mason_lemma3_nat, mathlib2_mason_lemma3

```lean
AddCancelMonoid.toIsCancelAdd :
∀ (M : Type u) [inst : AddCancelMonoid M], IsCancelAdd M
```

## EuclideanDomain.toNontrivial — PASS

来源：D:\mathproof\lean\.lake\packages\mathlib\Mathlib\Algebra\EuclideanDomain\Defs.lean:69
方式：Lean实例推导中的命题性实例。用途：提供域上多项式非平凡、整环、唯一分解等实例；完整前提及使用者见type和used_by。
使用者：mathlib2_radical_natDegree_ne_zero, mathlib2_mason_lemma3

```lean
EuclideanDomain.toNontrivial :
∀ {R : Type u} [self : EuclideanDomain R], Nontrivial R
```

## EuclideanDomain.to_principal_ideal_domain — PASS

来源：D:\mathproof\lean\.lake\packages\mathlib\Mathlib\RingTheory\PrincipalIdealDomain.lean:262
方式：Lean实例推导中的命题性实例。用途：提供域上多项式非平凡、整环、唯一分解等实例；完整前提及使用者见type和used_by。
使用者：mathlib2_unit_of_radical_unit, mathlib2_radical_natDegree_ne_zero, mathlib2_mason_lemma3_nat, mathlib2_mason_lemma3

```lean
EuclideanDomain.to_principal_ideal_domain :
∀ {R : Type u} [inst : EuclideanDomain R], IsPrincipalIdealRing R
```

## IsDomain.to_noZeroDivisors — PASS

来源：D:\mathproof\lean\.lake\packages\mathlib\Mathlib\Algebra\Ring\Basic.lean:222
方式：Lean实例推导中的命题性实例。用途：提供域上多项式非平凡、整环、唯一分解等实例；完整前提及使用者见type和used_by。
使用者：mathlib2_radical_natDegree_ne_zero

```lean
IsDomain.to_noZeroDivisors :
∀ (α : Type u_3) [inst : Semiring α] [IsDomain α], NoZeroDivisors α
```

## Polynomial.degree_eq_natDegree — PASS

来源：D:\mathproof\lean\.lake\packages\mathlib\Mathlib\Algebra\Polynomial\Degree\Definitions.lean:93
方式：显式数学主干复用。用途：非零多项式的degree/natDegree转换。
使用者：mathlib2_unit_of_natDegree_zero, mathlib2_mason_lemma3

```lean
Polynomial.degree_eq_natDegree :
∀ {R : Type u} [inst : Semiring R] {p : R[X]}, p ≠ 0 → p.degree = ↑p.natDegree
```

## Polynomial.instIsDomainOfIsCancelAdd — PASS

来源：D:\mathproof\lean\.lake\packages\mathlib\Mathlib\Algebra\Polynomial\Basic.lean:1163
方式：Lean实例推导中的命题性实例。用途：提供域上多项式非平凡、整环、唯一分解等实例；完整前提及使用者见type和used_by。
使用者：mathlib2_unit_of_radical_unit, mathlib2_radical_natDegree_ne_zero, mathlib2_mason_lemma3_nat, mathlib2_mason_lemma3

```lean
Polynomial.instIsDomainOfIsCancelAdd :
∀ {R : Type u} [inst : Semiring R] [IsCancelAdd R] [IsDomain R], IsDomain R[X]
```

## Polynomial.isUnit_iff_degree_eq_zero — PASS

来源：D:\mathproof\lean\.lake\packages\mathlib\Mathlib\Algebra\Polynomial\FieldDivision.lean:286
方式：显式数学主干复用。用途：次数零推出单位。
使用者：mathlib2_unit_of_natDegree_zero

```lean
Polynomial.isUnit_iff_degree_eq_zero :
∀ {R : Type u} [inst : Field R] {p : R[X]}, IsUnit p ↔ p.degree = 0
```

## Polynomial.natDegree_eq_zero_of_isUnit — PASS

来源：D:\mathproof\lean\.lake\packages\mathlib\Mathlib\Algebra\Polynomial\Degree\Units.lean:27
方式：显式数学主干复用。用途：原多项式为单位导致natDegree为零，形成矛盾。
使用者：mathlib2_radical_natDegree_ne_zero

```lean
Polynomial.natDegree_eq_zero_of_isUnit :
∀ {R : Type u} [inst : Semiring R] [NoZeroDivisors R] {p : R[X]}, IsUnit p → p.natDegree = 0
```

## Polynomial.natDegree_pos_iff_degree_pos — PASS

来源：D:\mathproof\lean\.lake\packages\mathlib\Mathlib\Algebra\Polynomial\Degree\Definitions.lean:511
方式：显式数学主干复用。用途：最终目标的degree正前提转为natDegree正。
使用者：mathlib2_mason_lemma3

```lean
Polynomial.natDegree_pos_iff_degree_pos :
∀ {R : Type u} [inst : Semiring R] {p : R[X]}, 0 < p.natDegree ↔ 0 < p.degree
```

## Polynomial.nontrivial — PASS

来源：D:\mathproof\lean\.lake\packages\mathlib\Mathlib\Algebra\Polynomial\Basic.lean:1142
方式：Lean实例推导中的命题性实例。用途：提供域上多项式非平凡、整环、唯一分解等实例；完整前提及使用者见type和used_by。
使用者：mathlib2_radical_natDegree_ne_zero, mathlib2_mason_lemma3

```lean
Polynomial.nontrivial :
∀ {R : Type u} [inst : Semiring R] [Nontrivial R], Nontrivial R[X]
```

## PrincipalIdealRing.to_uniqueFactorizationMonoid — PASS

来源：D:\mathproof\lean\.lake\packages\mathlib\Mathlib\RingTheory\PrincipalIdealDomain.lean:341
方式：Lean实例推导中的命题性实例。用途：提供域上多项式非平凡、整环、唯一分解等实例；完整前提及使用者见type和used_by。
使用者：mathlib2_unit_of_radical_unit, mathlib2_radical_natDegree_ne_zero, mathlib2_mason_lemma3_nat, mathlib2_mason_lemma3

```lean
PrincipalIdealRing.to_uniqueFactorizationMonoid :
∀ {R : Type u} [inst : CommRing R] [inst_1 : IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
```

## UniqueFactorizationMonoid.radical_eq_one_iff — PASS

来源：D:\mathproof\lean\.lake\packages\mathlib\Mathlib\RingTheory\Radical.lean:259
方式：显式数学主干复用。用途：从radical等于1及非零推出单位。
使用者：mathlib2_unit_of_radical_unit

```lean
UniqueFactorizationMonoid.radical_eq_one_iff :
∀ {M : Type u_1} [inst : CancelCommMonoidWithZero M] [inst_1 : NormalizationMonoid M]
  [inst_2 : UniqueFactorizationMonoid M] {a : M}, UniqueFactorizationMonoid.radical a = 1 ↔ a = 0 ∨ IsUnit a
```

## UniqueFactorizationMonoid.radical_ne_zero — PASS

来源：D:\mathproof\lean\.lake\packages\mathlib\Mathlib\RingTheory\Radical.lean:212
方式：显式数学主干复用。用途：排除radical为零，允许次数转换。
使用者：mathlib2_radical_natDegree_ne_zero, mathlib2_mason_lemma3

```lean
UniqueFactorizationMonoid.radical_ne_zero :
∀ {M : Type u_1} [inst : CancelCommMonoidWithZero M] [inst_1 : NormalizationMonoid M]
  [inst_2 : UniqueFactorizationMonoid M] {a : M} [Nontrivial M], UniqueFactorizationMonoid.radical a ≠ 0
```

## UniqueFactorizationMonoid.radical_of_isUnit — PASS

来源：D:\mathproof\lean\.lake\packages\mathlib\Mathlib\RingTheory\Radical.lean:180
方式：显式数学主干复用。用途：单位的radical等于1。
使用者：mathlib2_unit_of_radical_unit

```lean
UniqueFactorizationMonoid.radical_of_isUnit :
∀ {M : Type u_1} [inst : CancelCommMonoidWithZero M] [inst_1 : NormalizationMonoid M]
  [inst_2 : UniqueFactorizationMonoid M] {a : M}, IsUnit a → UniqueFactorizationMonoid.radical a = 1
```

## UniqueFactorizationMonoid.radical_radical — PASS

来源：D:\mathproof\lean\.lake\packages\mathlib\Mathlib\RingTheory\Radical.lean:268
方式：显式数学主干复用。用途：radical幂等性。
使用者：mathlib2_unit_of_radical_unit

```lean
UniqueFactorizationMonoid.radical_radical :
∀ {M : Type u_1} [inst : CancelCommMonoidWithZero M] [inst_1 : NormalizationMonoid M]
  [inst_2 : UniqueFactorizationMonoid M] {a : M},
  UniqueFactorizationMonoid.radical (UniqueFactorizationMonoid.radical a) = UniqueFactorizationMonoid.radical a
```

## WithBot.coe_le_coe — PASS

来源：D:\mathproof\lean\.lake\packages\mathlib\Mathlib\Order\WithBot.lean:245
方式：显式数学主干复用。用途：将自然数次数下界提升到WithBot次数下界。
使用者：mathlib2_mason_lemma3

```lean
WithBot.coe_le_coe :
∀ {α : Type u_1} {a b : α} [inst : LE α], ↑a ≤ ↑b ↔ a ≤ b
```

## instIsDomain — PASS

来源：D:\mathproof\lean\.lake\packages\mathlib\Mathlib\Algebra\Field\IsField.lean:59
方式：Lean实例推导中的命题性实例。用途：提供域上多项式非平凡、整环、唯一分解等实例；完整前提及使用者见type和used_by。
使用者：mathlib2_unit_of_radical_unit, mathlib2_radical_natDegree_ne_zero, mathlib2_mason_lemma3_nat, mathlib2_mason_lemma3

```lean
instIsDomain :
∀ {R : Type u} [inst : Semifield R], IsDomain R
```

## lt_of_lt_of_le — PASS

来源：D:\mathproof\lean\.lake\packages\mathlib\Mathlib\Order\Defs\PartialOrder.lean:95
方式：显式基础顺序定理。用途：由0<1和1≤degree推出0<degree。
使用者：mathlib2_mason_lemma3

```lean
lt_of_lt_of_le :
∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b ≤ c → a < c
```
