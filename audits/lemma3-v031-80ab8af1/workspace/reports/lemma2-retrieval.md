# Lemma 2 Mathlib 检索报告

检索对象是当前固定版本本地源码，非模型生成的定理名称。精确文件哈希见同名JSON。

|声明|源码位置|本次使用|
|---|---|---|
|divRadical_dvd_derivative|lean\.lake\packages\mathlib\Mathlib\RingTheory\Polynomial\Radical.lean:31|是|
|divRadical_dvd_wronskian_left|lean\.lake\packages\mathlib\Mathlib\RingTheory\Polynomial\Radical.lean:58|否：可选复用路径|
|divRadical_dvd_wronskian_right|lean\.lake\packages\mathlib\Mathlib\RingTheory\Polynomial\Radical.lean:66|否：可选复用路径|
|EuclideanDomain.divRadical_dvd_self|lean\.lake\packages\mathlib\Mathlib\RingTheory\Radical.lean:426|是|
|EuclideanDomain.divRadical|lean\.lake\packages\mathlib\Mathlib\RingTheory\Radical.lean:399|是|
|Polynomial.wronskian|lean\.lake\packages\mathlib\Mathlib\RingTheory\Polynomial\Wronskian.lean:39|是|
|mul_sub|lean\.lake\packages\mathlib\Mathlib\Algebra\Ring\Defs.lean:322|是|
|mul_assoc|lean\.lake\packages\mathlib\Mathlib\Algebra\Group\Defs.lean:200|是|

直接Theorem Reuse可用：divRadical_dvd_wronskian_left。它比纸面Lemma2更强，允许a=0。本次选择新编写的见证组合脚本，以显式复用已验证Lemma1。右侧版本以b/rad(b)为除数，不直接对应本任务。

### 原始声明摘录

**divRadical_dvd_derivative**
```lean
theorem divRadical_dvd_derivative (a : k[X]) : divRadical a ∣ derivative a := by
  induction a using induction_on_coprime
  · case h0 =>
```

**divRadical_dvd_wronskian_left**
```lean
theorem divRadical_dvd_wronskian_left (a b : k[X]) : divRadical a ∣ wronskian a b := by
  rw [wronskian]
  apply dvd_sub
```

**divRadical_dvd_wronskian_right**
```lean
theorem divRadical_dvd_wronskian_right (a b : k[X]) : divRadical b ∣ wronskian a b := by
  rw [← wronskian_neg_eq, dvd_neg]
  exact divRadical_dvd_wronskian_left _ _
```

**EuclideanDomain.divRadical_dvd_self**
```lean
theorem divRadical_dvd_self (a : E) : divRadical a ∣ a :=
  ⟨radical a, divRadical_mul_radical.symm⟩

```

**EuclideanDomain.divRadical**
```lean
def divRadical (a : E) : E := a / radical a

theorem radical_mul_divRadical : radical a * divRadical a = a := by
```

**Polynomial.wronskian**
```lean
def wronskian (a b : R[X]) : R[X] :=
  a * (derivative b) - (derivative a) * b

```

**mul_sub**
```lean
alias mul_sub := mul_sub_left_distrib

theorem mul_sub_right_distrib (a b c : α) : (a - b) * c = a * c - b * c := by
```

**mul_assoc**
```lean
theorem mul_assoc : ∀ a b c : G, a * b * c = a * (b * c) :=
  Semigroup.mul_assoc

```
