# Mathlib2 目录

共 684 条内核验证的定理：673 条证明，11 条证伪；682 条需要 agent 才证出，2 条被自动化直接关掉。

排序分数只是启发：需要 agent 才能证出、被后续证明引用、证伪了一个猜想、前人失败过，都加分。“复核”一栏是独立 agent 对“Lean 命题是否忠实于原文”的判断，不是内核保证的内容。

## `Mathlib2.lib_fib_period_iff`

Fibonacci period criterion: m is a period of the Fibonacci sequence modulo N iff F_m ≡ 0 and F_(m+1) ≡ 1 (mod N). Promoted from Mathlib2.p3_aux_period_aux2 / p3_aux_period_aux3 (the same two-term induction is re-done in p3_cor1_aux3/aux4).

```lean
∀ (N m : ℕ), (∀ (i : ℕ), Nat.fib (i + m) ≡ Nat.fib i [MOD N]) ↔ Nat.fib m ≡ 0 [MOD N] ∧ Nat.fib (m + 1) ≡ 1 [MOD N]
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.p3_aux_period_aux2）
- 完成者：curator_1
- 尝试次数：1
- 被引用：11 次
- 分数：25
- 依赖：`p3_aux_period_aux2`

## `Mathlib2.lib_pisano_dvd_iff_period`

The positive periods of the Fibonacci sequence mod m are exactly the positive multiples of the Pisano period p3_pisano m (the least period divides every period, and every multiple of it is a period). Promoted from Mathlib2.bld2_pisano_fib_dvd_four_mul_aux1 and bld2_pisano_fib_odd_eq_aux1 (same argument also inline in p3_prop2).

```lean
∀ (m N : ℕ), 0 < N → (Mathlib2.p3_pisano m ∣ N ↔ ∀ (i : ℕ), Nat.fib (i + N) ≡ Nat.fib i [MOD m])
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.bld2_pisano_fib_dvd_four_mul_aux1）
- 完成者：curator_1
- 尝试次数：1
- 被引用：11 次
- 分数：25
- 依赖：`bld2_pisano_fib_dvd_four_mul_aux1`、`p3_pisano`

## `Mathlib2.p5_psi_ge_succ`

Equation (8): psi(n) >= n+1 for n >= 2.

```lean
∀ (n : ℕ), 2 ≤ n → n + 1 ≤ Mathlib2.p5_dedekind_psi n
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2404.19332v1 equation (8)）
- 完成者：paper_5
- 尝试次数：1
- 被引用：10 次
- 分数：23
- 依赖：`p5_dedekind_psi`、`p5_psi_mul_coprime`、`p5_psi_prime_mul_of_dvd`、`p5_psi_prime_pow`
- 复核（reviewer_5）：faithful — Eq (8) prints psi(n) >= n+1 with no range, but it is used for n with Omega(n)=m>=2, so n>=2 is implicit; Lean adds 2<=n, which is needed (false at n=1). Numerically true 2..100000.

## `Mathlib2.bld3_pisano_dvd_of_period`

Uses Mathlib2.bld2_pisano_fib_odd_eq: if k = 0 trivial; otherwise by the auxiliary lemma bld2_pisano_fib_odd_eq_aux1 the Pisano period P is a positive period, and k % P is again a period smaller than P, so by minimality (Nat.sInf_le) k % P = 0.

```lean
∀ (m k : ℕ), (∀ (i : ℕ), Nat.fib (i + k) ≡ Nat.fib i [MOD m]) → Mathlib2.p3_pisano m ∣ k
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_pisano_fib_odd_eq）
- 完成者：r8_prover_2
- 尝试次数：1
- 被引用：9 次
- 分数：21
- 依赖：`lib_pisano_dvd_iff_period`、`p3_pisano`

## `Mathlib2.an_cassini_int`

Cassini's identity: F_{n+2} F_n - F_{n+1}^2 = (-1)^{n+1} over the integers.

```lean
∀ (n : ℕ), ↑(Nat.fib (n + 2)) * ↑(Nat.fib n) - ↑(Nat.fib (n + 1)) ^ 2 = (-1) ^ (n + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_3
- 尝试次数：1
- 被引用：8 次
- 分数：19

## `Mathlib2.p3_aux_period`

auxiliary: for even n, 2n is a period of Fibonacci mod F_n

```lean
∀ (n k i : ℕ), 2 ∣ n → Nat.fib (i + 2 * n * k) ≡ Nat.fib i [MOD Nat.fib n]
```
- 结论：证明
- 层级：agent
- 来源：conjecture（arXiv:2504.09938 auxiliary to Proposition 2 / Theorem 2）
- 完成者：paper_3
- 尝试次数：1
- 被引用：8 次
- 分数：19
- 复核（reviewer_3）：unsure — Not a claim of the paper: auxiliary lemma (2n is a period of Fibonacci mod F_n for even n), the content of the paper's proof of Proposition 2. Consistent with my check that pi(F_n) | 2n for even n<60.

## `Mathlib2.p5_lemma1`

Lemma 1 (Atanassov): phi(n)+psi(n) >= 2n for n >= 2.

```lean
∀ (n : ℕ), 2 ≤ n → 2 * n ≤ n.totient + Mathlib2.p5_dedekind_psi n
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2404.19332v1 Lemma 1）
- 完成者：paper_5
- 尝试次数：1
- 被引用：8 次
- 分数：19
- 依赖：`p5_dedekind_psi`、`p5_psi_ge_succ`、`p5_psi_ge_succ_aux1`、`p5_psi_ge_succ_aux2`、`p5_psi_prime_mul_of_dvd`
- 复核（reviewer_5）：faithful — Verbatim Lemma 1: phi(n)+psi(n) >= 2n for n>=2 (cited from [1]); Lean identical. Numerically true to 100000 (equality at primes and prime powers; also true at n=1).

## `Mathlib2.p5_lemma2`

Lemma 2 (Sandor-Atanassov): phi(n)+sigma(n) >= 2n for n >= 2.

```lean
∀ (n : ℕ), 2 ≤ n → 2 * n ≤ n.totient + (ArithmeticFunction.sigma 1) n
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2404.19332v1 Lemma 2）
- 完成者：paper_5
- 尝试次数：1
- 被引用：8 次
- 分数：19
- 依赖：`p5_dedekind_psi`、`p5_lemma1`、`p5_psi_ge_succ_aux1`、`p5_psi_ge_succ_aux2`、`p5_psi_prime_mul_of_dvd`、`p5_sigma_prime_mul_of_dvd`
- 复核（reviewer_5）：faithful — Verbatim Lemma 2: phi(n)+sigma(n) >= 2n for n>=2 (cited from [7]); Lean identical. Numerically true to 100000, equality at primes (and n=1).

## `Mathlib2.bld_center_card_of_card_prime_cube`

Uses Mathlib2.alg_center_index_not_prime: the centre of a p-group is non-trivial, so |Z| ∈ {p, p^2, p^3}; p^3 is excluded by non-commutativity and p^2 would give prime index p, contradicting the library theorem.

```lean
∀ (p : ℕ), Nat.Prime p → ∀ (G : Type u_1) [inst : Group G], Nat.card G = p ^ 3 → (∃ a b, a * b ≠ b * a) → Nat.card ↥(Subgroup.center G) = p
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.alg_center_index_not_prime）
- 完成者：r6_prover_2
- 尝试次数：1
- 被引用：7 次
- 分数：17
- 依赖：`alg_center_index_not_prime`

## `Mathlib2.p5_sigma_ge_succ`

Equation (8): sigma(n) >= n+1 for n >= 2.

```lean
∀ (n : ℕ), 2 ≤ n → n + 1 ≤ (ArithmeticFunction.sigma 1) n
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2404.19332v1 equation (8)）
- 完成者：paper_5
- 尝试次数：1
- 被引用：7 次
- 分数：17
- 复核（reviewer_5）：faithful — Eq (8) prints sigma(n) >= n+1 with no range, used for n with Omega(n)>=2; Lean adds 2<=n, necessary since it fails at n=1. Numerically true 2..100000.

## `Mathlib2.ana_sqrt_two_rec_closed_form`

Viète-type closed form: the nested radical sequence equals 2cos(π/2^(n+1)) — induction using the half-angle identity 2 + 2cos(2t) = 4cos^2 t and positivity of cos on (0, π/2].

```lean
∀ (a : ℕ → ℝ), a 0 = 0 → (∀ (n : ℕ), a (n + 1) = √(2 + a n)) → ∀ (n : ℕ), a n = 2 * Real.cos (Real.pi / 2 ^ (n + 1))
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_8
- 尝试次数：1
- 被引用：6 次
- 分数：15

## `Mathlib2.bld2_lucas_sq_sub_five_fib_sq`

Uses Mathlib2.an_cassini_int (with the definition Mathlib2.p3_lucas): the cast of p3_lucas n is 2 F(n+1) - F(n) (no truncation since F(n) ≤ 2 F(n+1)); expand (2F(n+1) - F(n))^2 - 5F(n)^2 = 4(F(n+1)^2 - F(n+1)F(n) - F(n)^2) and rewrite with Cassini F(n+2)F(n) - F(n+1)^2 = (-1)^(n+1), F(n+2) = F(n+1) + F(n).

```lean
∀ (n : ℕ), ↑(Mathlib2.p3_lucas n) ^ 2 - 5 * ↑(Nat.fib n) ^ 2 = 4 * (-1) ^ n
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.an_cassini_int, Mathlib2.p3_lucas）
- 完成者：r7_prover_2
- 尝试次数：1
- 被引用：6 次
- 分数：15
- 依赖：`an_cassini_int`、`p3_lucas`

## `Mathlib2.ana_sqrt_two_rec_lt_two`

The nested radical sequence a_0 = 0, a_{n+1} = sqrt(2 + a_n) stays in [0,2) — induction: if 0 ≤ a_n < 2 then 2 + a_n < 4 so sqrt(2 + a_n) < 2.

```lean
∀ (a : ℕ → ℝ), a 0 = 0 → (∀ (n : ℕ), a (n + 1) = √(2 + a n)) → ∀ (n : ℕ), 0 ≤ a n ∧ a n < 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_8
- 尝试次数：1
- 被引用：5 次
- 分数：13

## `Mathlib2.bld2_rank_pow_convex`

Uses Mathlib2.bld_frobenius_rank_inequality: apply Frobenius to the triple (A, A^k, A): rank (A * A^k) + rank (A^k * A) ≤ rank (A^k) + rank (A * A^k * A).

```lean
∀ (K : Type u_1) [inst : Field K] (ι : Type u_2) [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (A : Matrix ι ι K) (k : ℕ), 2 * (A ^ (k + 1)).rank ≤ (A ^ k).rank + (A ^ (k + 2)).rank
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_frobenius_rank_inequality）
- 完成者：r7_prover_1
- 尝试次数：1
- 被引用：5 次
- 分数：13
- 依赖：`bld_frobenius_rank_inequality`

## `Mathlib2.bld3_pisano_pos_and_period`

Uses Mathlib2.bld2_pisano_fib_odd_eq: by its auxiliary lemma bld2_pisano_fib_odd_eq_aux1 it suffices to exhibit one positive period N; pigeonhole on the pairs (fib i, fib (i+1)) mod m gives i < j with equal pairs, and the recurrence run backwards (fib (i) = fib (i+2) - fib (i+1)) shows N = j - i is a period.

```lean
∀ (m : ℕ), 0 < m → 0 < Mathlib2.p3_pisano m ∧ ∀ (i : ℕ), Nat.fib (i + Mathlib2.p3_pisano m) ≡ Nat.fib i [MOD m]
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_pisano_fib_odd_eq）
- 完成者：r8_prover_2
- 尝试次数：1
- 被引用：5 次
- 分数：13
- 依赖：`bld2_pisano_fib_odd_eq_aux1`、`lib_fib_period_iff`、`p3_pisano`

## `Mathlib2.calc_tsum_inv_three_consecutive`

∑_{n≥1} 1/(n(n+1)(n+2)) = 1/4 — telescoping: term = (1/2)(1/((n+1)(n+2)) − 1/((n+2)(n+3))); HasSum via tendsto of partial sums 1/4 − 1/(2(N+1)(N+2)).

```lean
∑' (n : ℕ), 1 / ((↑n + 1) * (↑n + 2) * (↑n + 3)) = 1 / 4
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：5 次
- 分数：13

## `Mathlib2.gen_an_amgm_finset_ordered_ring`

Generalizes Mathlib2.an2_amgm_range_pow: ℝ → any linearly ordered commutative ring via a division-free form card^card · ∏ a ≤ (∑ a)^card, range (n+1) → arbitrary Finset. Also implies an_amgm_three_cube. Proof idea: no n-th roots available, so induct on the finset (e.g. Cauchy forward–backward induction, or the smoothing step replacing min and max by mean-preserving pair).

```lean
∀ (R : Type u_1) [inst : CommRing R] [inst_1 : LinearOrder R] [IsStrictOrderedRing R] (ι : Type u_2) (s : Finset ι) (a : ι → R), (∀ i ∈ s, 0 ≤ a i) → ↑s.card ^ s.card * ∏ i ∈ s, a i ≤ (∑ i ∈ s, a i) ^ s.card
```
- 结论：证明
- 层级：agent
- 来源：conjecture（generalization of Mathlib2.an2_amgm_range_pow）
- 完成者：gen_prover_1
- 尝试次数：1
- 被引用：5 次
- 分数：13

## `Mathlib2.lib_matrix_rank_eq_zero_iff`

A matrix over a field has rank zero iff it is the zero matrix (Matrix.rank A = 0 ↔ A = 0). Promoted from inline derivations (Submodule.finrank_eq_zero + LinearMap.range_eq_bot) inside two bld2 rank proofs in shard S0017.

```lean
∀ (K : Type u_1) [inst : Field K] (m : Type u_2) (n : Type u_3) [Fintype m] [inst_2 : Fintype n] (A : Matrix m n K), A.rank = 0 ↔ A = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.bld2_involution_iff_rank_add_rank (inline)）
- 完成者：curator_1
- 尝试次数：1
- 被引用：5 次
- 分数：13

## `Mathlib2.p3_aux_fib_prime`

auxiliary (used in proofs of Thm 1 and Thm 2): L_p = 1 and F_p = 5^((p-1)/2) mod p for odd primes p

```lean
∀ (p : ℕ), Nat.Prime p → p ≠ 2 → 2 * ↑(Nat.fib (p + 1)) - ↑(Nat.fib p) ≡ 1 [ZMOD ↑p] ∧ ↑(Nat.fib p) ≡ 5 ^ (p / 2) [ZMOD ↑p]
```
- 结论：证明
- 层级：agent
- 来源：conjecture（arXiv:2504.09938 auxiliary to Theorems 1, 2）
- 完成者：paper_3
- 尝试次数：1
- 被引用：5 次
- 分数：13
- 复核（reviewer_3）：unsure — Not a claim of the paper: auxiliary lemma (L_p = 1 and F_p = 5^((p-1)/2) mod p for odd primes) used by the auditor. Standard facts, consistent with my numerics (F_p = +-1 mod p).

## `Mathlib2.p3_prop1`

S_n = F_{n+2} - 1

```lean
∀ (n : ℕ), Mathlib2.p3_fibsum n = Nat.fib (n + 2) - 1
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2504.09938 Proposition 1）
- 完成者：paper_3
- 尝试次数：1
- 被引用：5 次
- 分数：13
- 依赖：`p3_fibsum`
- 复核（reviewer_3）：faithful — Paper Prop 1: 'Let n in N. Then S_n = F_{n+2} - 1.' Lean identical; natural subtraction harmless since fib(n+2)>=1; n=0 also holds (0=0). Checked numerically.

## `Mathlib2.p4_x_block`

Auditor's helper lemma (not a statement of the paper): if 2^(s-1) < n <= 2^s and t^2 <= 2n < (t+1)^2 then r(n)=s, m(n)=t and x(n) = floor((2n-1)/3) - (s+1)t.

```lean
∀ (n s t : ℕ), n ≤ 2 ^ s → 2 ^ s < 2 * n → t * t ≤ 2 * n → 2 * n < (t + 1) * (t + 1) → Mathlib2.p4_x n = (2 * ↑n - 1) / 3 - (↑s + 1) * ↑t
```
- 结论：证明
- 层级：agent
- 来源：conjecture（arXiv:2503.03469v1 (helper, combines definitions (a)-(d))）
- 完成者：paper_4
- 尝试次数：1
- 被引用：5 次
- 分数：13
- 依赖：`p4_m`、`p4_r`、`p4_x`、`p4_z`
- 复核（reviewer_4）：unsure — Not a claim of the paper: auditor's helper giving x(n) on a block with r(n)=s, m(n)=t. Consistent with definitions (a)-(d).
- 复核（reviewer_4）：unsure — Not a claim of the paper: auditor's helper giving x(n) on a block with r(n)=s, m(n)=t. Consistent with definitions (a)-(d).

## `Mathlib2.bld2_hardy_inequality_tsum`

Uses Mathlib2.r3_hardy_inequality_finite: the partial sums of the nonnegative left series are bounded by 4 * ∑_{k<n} a k^2 ≤ 4 * ∑' a k^2, so the series is summable (summable_of_sum_range_le) and its tsum obeys the same bound.

```lean
∀ (a : ℕ → ℝ), (Summable fun k => a k ^ 2) → (Summable fun k => ((∑ i ∈ Finset.range (k + 1), a i) / (↑k + 1)) ^ 2) ∧ ∑' (k : ℕ), ((∑ i ∈ Finset.range (k + 1), a i) / (↑k + 1)) ^ 2 ≤ 4 * ∑' (k : ℕ), a k ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.r3_hardy_inequality_finite）
- 完成者：r7_prover_2
- 尝试次数：1
- 被引用：4 次
- 分数：11
- 依赖：`r3_hardy_inequality_finite`

## `Mathlib2.bld2_pisano_fib_dvd_four_mul`

Uses Mathlib2.p3_aux_period (and the argument of Mathlib2.p3_prop2): p3_aux_period with index 2n gives fib (i + 4n) ≡ fib i mod fib (2n), and fib n ∣ fib (2n), so 4n is a period modulo fib n; the least period divides every period (division with remainder), as in p3_prop2.

```lean
∀ (n : ℕ), 0 < n → Mathlib2.p3_pisano (Nat.fib n) ∣ 4 * n
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.p3_aux_period, Mathlib2.p3_prop2）
- 完成者：r7_prover_1
- 尝试次数：1
- 被引用：4 次
- 分数：11
- 依赖：`p3_aux_period`、`p3_pisano`

## `Mathlib2.bld2_sqrt_two_rec_defect_summable`

Uses Mathlib2.bld_sqrt_two_rec_rate and Mathlib2.ana_sqrt_two_rec_lt_two: 0 ≤ 2 - a n ≤ π^2 / 4^(n+1), and the geometric series on the right is summable, so comparison applies.

```lean
∀ (a : ℕ → ℝ), a 0 = 0 → (∀ (n : ℕ), a (n + 1) = √(2 + a n)) → Summable fun n => 2 - a n
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_sqrt_two_rec_rate, Mathlib2.ana_sqrt_two_rec_lt_two）
- 完成者：r7_prover_3
- 尝试次数：1
- 被引用：4 次
- 分数：11
- 依赖：`ana_sqrt_two_rec_lt_two`、`bld_sqrt_two_rec_rate`

## `Mathlib2.bld3_pisano_dvd_pisano_of_dvd`

Uses Mathlib2.bld2_pisano_fib_odd_eq: if p3_pisano n = 0 trivial; otherwise it is a period mod n (aux1 of bld2_pisano_fib_odd_eq), hence a period mod m, and the least period mod m divides every period (remainder argument with minimality).

```lean
∀ (m n : ℕ), m ∣ n → Mathlib2.p3_pisano m ∣ Mathlib2.p3_pisano n
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_pisano_fib_odd_eq）
- 完成者：r8_prover_1
- 尝试次数：1
- 被引用：4 次
- 分数：11
- 依赖：`lib_pisano_dvd_iff_period`、`p3_pisano`

## `Mathlib2.bld4_pisano_lucas_dvd_four_mul`

Uses Mathlib2.an_cassini_int, Mathlib2.lib_fib_period_iff and Mathlib2.bld3_pisano_dvd_of_period: modulo L_n = F_{n+1} + F_{n−1} one has F_{2n} = F_n L_n ≡ 0 and F_{2n+1} = F_{n+1}^2 + F_n^2 ≡ F_n^2 − F_{n+1}F_{n−1} = ±1 by an_cassini_int. Hence F_{4n} ≡ 0 and F_{4n+1} ≡ F_{2n+1}^2 ≡ 1, so lib_fib_period_iff makes 4n a period mod L_n and bld3_pisano_dvd_of_period concludes (n = 0 trivial).

```lean
∀ (n : ℕ), Mathlib2.p3_pisano (Mathlib2.p3_lucas n) ∣ 4 * n
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.an_cassini_int, Mathlib2.lib_fib_period_iff, Mathlib2.bld3_pisano_dvd_of_period）
- 完成者：r9_prover_1
- 尝试次数：1
- 被引用：4 次
- 分数：11
- 依赖：`bld3_pisano_dvd_of_period`、`lib_fib_cassini_cast`、`lib_fib_period_iff`、`lib_p3_lucas_cast`、`p3_lucas`、`p3_pisano`

## `Mathlib2.bld_idempotent_sum_rank`

Uses Mathlib2.gen_lin_idempotent_trace_eq_rank_field three times: rank(A+B) = tr(A+B) = tr A + tr B = rank A + rank B in K, then Nat.cast injectivity in characteristic zero.

```lean
∀ (K : Type u_1) [inst : Field K] [CharZero K] (ι : Type u_2) [inst_2 : Fintype ι] [DecidableEq ι] (A B : Matrix ι ι K), A * A = A → B * B = B → (A + B) * (A + B) = A + B → (A + B).rank = A.rank + B.rank
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.gen_lin_idempotent_trace_eq_rank_field）
- 完成者：r6_prover_2
- 尝试次数：1
- 被引用：4 次
- 分数：11
- 依赖：`gen_lin_idempotent_trace_eq_rank_field`

## `Mathlib2.bld_sqrt_two_rec_viete_prod`

Uses Mathlib2.ana_sqrt_two_rec_closed_form: a (i+1)/2 = cos(π/2^(i+2)); induct on n with sin(2θ) = 2 sin θ cos θ (finite Viète product).

```lean
∀ (a : ℕ → ℝ), a 0 = 0 → (∀ (n : ℕ), a (n + 1) = √(2 + a n)) → ∀ (n : ℕ), (∏ i ∈ Finset.range n, a (i + 1) / 2) * (2 ^ n * Real.sin (Real.pi / 2 ^ (n + 1))) = 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.ana_sqrt_two_rec_closed_form）
- 完成者：r6_prover_1
- 尝试次数：1
- 被引用：4 次
- 分数：11
- 依赖：`ana_sqrt_two_rec_closed_form`

## `Mathlib2.bld_surjective_nonexpanding_compact_isometry`

Uses Mathlib2.top_expanding_compact_isometry and Mathlib2.top_isometry_compact_surjective: a right inverse g of f is expanding, hence an isometry by the first theorem and surjective by the second; so g is a bijective isometry and f = g⁻¹ is an isometry.

```lean
∀ {X : Type u_1} [inst : MetricSpace X] [CompactSpace X] (f : X → X), Function.Surjective f → (∀ (x y : X), dist (f x) (f y) ≤ dist x y) → Isometry f
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.top_expanding_compact_isometry, Mathlib2.top_isometry_compact_surjective）
- 完成者：r6_prover_3
- 尝试次数：1
- 被引用：4 次
- 分数：11
- 依赖：`top_expanding_compact_isometry`、`top_isometry_compact_surjective`

## `Mathlib2.calc_integral_beta_nat`

Beta integral at naturals: ∫₀¹ xᵐ(1−x)ⁿ dx = m! n!/(m+n+1)! — induction on n with integration by parts B(m,n+1) = (n+1)/(m+1)·B(m+1,n); base ∫ xᵐ = 1/(m+1).

```lean
∀ (m n : ℕ), ∫ (x : ℝ) in 0..1, x ^ m * (1 - x) ^ n = ↑m.factorial * ↑n.factorial / ↑(m + n + 1).factorial
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：4 次
- 分数：11

## `Mathlib2.fld_prime_one_mod_three_eq_sq_add_three_sq`

Every prime p ≡ 1 (mod 3) is of the form a^2 + 3b^2 — -3 is a square mod p (cube roots of unity in F_p), so p | x^2 + 3 for some x; Thue's lemma / pigeonhole gives 0 < a^2 + 3b^2 ≡ 0 mod p with a, b < √p, hence a^2 + 3b^2 ∈ {p, 2p, 3p}; 2p is impossible mod 4 (or mod 3) and 3p reduces to p by a = 3a'.

```lean
∀ (p : ℕ), Nat.Prime p → p % 3 = 1 → ∃ a b, p = a ^ 2 + 3 * b ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_6x
- 尝试次数：1
- 被引用：4 次
- 分数：11

## `Mathlib2.gen_lin_idempotent_trace_eq_rank_field`

Generalizes Mathlib2.lin_idempotent_trace_eq_rank: ℚ → arbitrary field K (any characteristic; the rank is cast into K), Fin n → arbitrary Fintype. Also subsumes lin_idempotent_rank_complement_aux1 (the ℝ copy). Proof idea: the original proof is field-agnostic: toLin' A is idempotent, LinearMap.IsIdempotentElem.isProj_range + LinearMap.IsProj.trace + Matrix.trace_toLin'_eq.

```lean
∀ (K : Type u_1) [inst : Field K] (ι : Type u_2) [inst_1 : Fintype ι] [DecidableEq ι] (A : Matrix ι ι K), A * A = A → A.trace = ↑A.rank
```
- 结论：证明
- 层级：agent
- 来源：conjecture（generalization of Mathlib2.lin_idempotent_trace_eq_rank）
- 完成者：gen_prover_1
- 尝试次数：1
- 被引用：4 次
- 分数：11

## `Mathlib2.lib_p3_lucas_cast`

Cast formula for the Lucas numbers L_n = 2 F_(n+1) - F_n (Mathlib2.p3_lucas) in an arbitrary ring: the truncated subtraction in the definition is exact. Promoted and generalised from Mathlib2.p3_remark3_aux1 (the case R = ℤ; re-derived in bld2_lucas_sq_sub_five_fib_sq, bld2_pell_five_solutions_lucas, bld3_pell_five_neg_four_solutions_lucas).

```lean
∀ (R : Type u_1) [inst : Ring R] (n : ℕ), ↑(Mathlib2.p3_lucas n) = 2 * ↑(Nat.fib (n + 1)) - ↑(Nat.fib n)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.p3_remark3_aux1）
- 完成者：curator_2
- 尝试次数：1
- 被引用：4 次
- 分数：11
- 依赖：`p3_lucas`

## `Mathlib2.nt2_prime_three_mod_four_dvd_sq_add_sq`

Generalization of Mathlib2.nt_seven_dvd_sq_add_sq from 7 to every prime p ≡ 3 (mod 4): if p divides a^2+b^2 then p divides both a and b (-1 is not a square mod p).

```lean
∀ (p : ℕ), Nat.Prime p → p % 4 = 3 → ∀ (a b : ℤ), ↑p ∣ a ^ 2 + b ^ 2 → ↑p ∣ a ∧ ↑p ∣ b
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_c
- 尝试次数：1
- 被引用：4 次
- 分数：11

## `Mathlib2.p4_rem1_large`

Remark 1 conclusion: x(n) > 0 for every n > 2^12 = 4096.

```lean
∀ (n : ℕ), 4096 < n → 0 < Mathlib2.p4_x n
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Remark 1）
- 完成者：paper_4
- 尝试次数：1
- 被引用：4 次
- 分数：11
- 依赖：`p4_rem1_bound_even`、`p4_rem1_bound_odd`、`p4_x`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). Paper: 'x(n)>0 for every n>2^12=4096'. Identical. Checked numerically to n=300000.

## `Mathlib2.p4_small_classify`

Auditor's helper lemma (not a numbered statement of the paper): the finite verification for 1 <= n <= 4096 underlying Theorem 1, done block by block on the maximal intervals where r and m are constant (the paper's Lemma 2 / table).

```lean
∀ (n : ℕ), 0 < n → n ≤ 4096 → (Mathlib2.p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546) ∧ (Mathlib2.p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ 513 ≤ n ∧ n ≤ 528) ∧ (n ≠ 129 → -58 ≤ Mathlib2.p4_x n)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（arXiv:2503.03469v1 proof of Theorem 1 (finite check)）
- 完成者：paper_4
- 尝试次数：1
- 被引用：4 次
- 分数：11
- 依赖：`p4_x`、`p4_x_block`
- 复核（reviewer_4）：unsure — Not a claim of the paper: auditor's finite-check helper for n<=4096 combining Theorem 1(i),(ii),(vi). Consistent with my computation.

## `Mathlib2.p5_psi_prime_mul_of_dvd`

Equation (7), psi part: if p | n then psi(np) = p psi(n).

```lean
∀ (p n : ℕ), Nat.Prime p → p ∣ n → n ≠ 0 → Mathlib2.p5_dedekind_psi (p * n) = p * Mathlib2.p5_dedekind_psi n
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2404.19332v1 equation (7)）
- 完成者：paper_5
- 尝试次数：1
- 被引用：4 次
- 分数：11
- 依赖：`p5_dedekind_psi`、`p5_psi_mul_coprime`、`p5_psi_prime_pow`
- 复核（reviewer_5）：faithful — Eq (7) verbatim: for p | n, psi(np)=p psi(n); Lean matches, with the harmless extra hypothesis n != 0 (paper's n is a positive integer). The phi part of (7) is not a separate task (Mathlib fact).

## `Mathlib2.ab_abundant_def`

Paper's definition of abundant (all divisors sum to more than 2n) agrees with Mathlib's Nat.Abundant (proper divisors sum > n).

```lean
∀ (n : ℕ), n.Abundant ↔ 2 * n < ∑ d ∈ n.divisors, d
```
- 结论：证明
- 层级：agent
- 来源：paper（s40753-021-00140-1 p.28 Appendix 2 Task 3 definition）
- 完成者：paper_2
- 尝试次数：1
- 被引用：3 次
- 分数：9
- 复核（reviewer_2）：faithful — Compared Appendix 2 Task 3 definition (divisors add up to more than 2n) with Mathlib Nat.Abundant (n < sum of properDivisors). The Lean iff bridges them for all n in N; at n=0 both sides are false (Nat.divisors 0 = empty), so no edge-case gap. Differences: paper says 'integer n' (negatives/0 not mea

## `Mathlib2.alg_rat_pow_ne_two`

X^n - 2 has no rational root for n ≥ 2 — rational root theorem / compare 2-adic valuations: n * v_2(q) = 1 is impossible.

```lean
∀ (n : ℕ), 2 ≤ n → ∀ (q : ℚ), q ^ n ≠ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_1
- 尝试次数：1
- 被引用：3 次
- 分数：9

## `Mathlib2.bld2_pisano_fib_odd_eq`

Uses Mathlib2.p3_aux_period and Mathlib2.an_cassini_int: 4n is a period (p3_aux_period at index 2n, fib n ∣ fib (2n)), so the period k divides 4n and n ∣ k, k ∈ {n, 2n, 4n}; k = n fails since fib (n+1) ≡ fib (n-1) ≢ 1; k = 2n fails since fib (2n+1) = fib(n)^2 + fib(n+1)^2 ≡ fib(n-1)^2 ≡ (-1)^n = -1 mod fib n by Cassini, and fib n > 2.

```lean
∀ (n : ℕ), 5 ≤ n → Odd n → Mathlib2.p3_pisano (Nat.fib n) = 4 * n
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.p3_aux_period, Mathlib2.an_cassini_int）
- 完成者：r7_prover_4
- 尝试次数：1
- 被引用：3 次
- 分数：9
- 依赖：`an_cassini_int`、`bld2_pisano_fib_dvd_four_mul`、`p3_aux_period`、`p3_pisano`

## `Mathlib2.bld2_rank_add_rank_one_sub`

Uses Mathlib2.gen_lin_sylvester_rank_rect: the inequality ≤ is Sylvester applied to A and 1 - A (A * (1 - A) = A - A*A); for ≥ show range A ⊓ range (1 - A) = range (A * (1 - A)) and range A ⊔ range (1 - A) = ⊤, then use the dimension formula.

```lean
∀ (K : Type u_1) [inst : Field K] (ι : Type u_2) [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (A : Matrix ι ι K), A.rank + (1 - A).rank = Fintype.card ι + (A - A * A).rank
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.gen_lin_sylvester_rank_rect）
- 完成者：r7_prover_1
- 尝试次数：1
- 被引用：3 次
- 分数：9
- 依赖：`gen_lin_sylvester_rank_rect`

## `Mathlib2.bld3_pell_five_neg_four_solutions_lucas`

Uses Mathlib2.bld2_fib_odd_index_iff_five_sq_sub_four and Mathlib2.bld2_lucas_sq_sub_five_fib_sq: the odd-index characterisation gives y = fib (2n+1) (choose n with the right value; fib 1 = fib 2 only matters for y = 1 where n = 0 works), and L^2 = 5 F^2 - 4 at odd index forces x = p3_lucas (2n+1) by injectivity of squaring on ℕ.

```lean
∀ (x y : ℕ), x ^ 2 + 4 = 5 * y ^ 2 → ∃ n, y = Nat.fib (2 * n + 1) ∧ x = Mathlib2.p3_lucas (2 * n + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_fib_odd_index_iff_five_sq_sub_four, Mathlib2.bld2_lucas_sq_sub_five_fib_sq）
- 完成者：r8_prover_2
- 尝试次数：1
- 被引用：3 次
- 分数：9
- 依赖：`bld2_fib_odd_index_iff_five_sq_sub_four`、`bld2_lucas_sq_sub_five_fib_sq`、`p3_lucas`

## `Mathlib2.bld3_rank_pow_card_stabilizes`

Uses Mathlib2.bld2_rank_pow_convex: Fitting-type stabilisation: the drops d_k = rank A^k - rank A^(k+1) are non-negative and, by convexity, non-increasing; if d_n > 0 with n = card ι then d_0,...,d_n ≥ 1 and rank A^0 = n ≥ n + 1, contradiction.

```lean
∀ (K : Type u_1) [inst : Field K] (ι : Type u_2) [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (A : Matrix ι ι K), (A ^ (Fintype.card ι + 1)).rank = (A ^ Fintype.card ι).rank
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_rank_pow_convex）
- 完成者：r8_prover_1
- 尝试次数：1
- 被引用：3 次
- 分数：9
- 依赖：`bld2_rank_pow_convex`

## `Mathlib2.bld4_isometry_compact_uniform_recurrence`

Uses Mathlib2.lib_compactSpace_exists_lt_and_dist_lt: take a finite ε/3-net t of X and apply the lemma in the compact space Y = (t → X) (sup metric) to u k = fun i => f^[k] i, getting m < n' with dist (f^[m] i) (f^[n'] i) < ε/3 for all i ∈ t. With n = n' − m, the isometry property gives dist i (f^[n] i) < ε/3 on the net, and the triangle inequality (f^[n] is an isometry) gives dist (f^[n] x) x < ε for all x.

```lean
∀ {X : Type u_1} [inst : MetricSpace X] [CompactSpace X] (f : X → X), Isometry f → ∀ (ε : ℝ), 0 < ε → ∃ n, 0 < n ∧ ∀ (x : X), dist (f^[n] x) x < ε
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.lib_compactSpace_exists_lt_and_dist_lt）
- 完成者：r9_prover_1
- 尝试次数：1
- 被引用：3 次
- 分数：9
- 依赖：`lib_compactSpace_exists_lt_and_dist_lt`

## `Mathlib2.bld5_nilpotent_pow_rank_succ_eq_zero`

Uses Mathlib2.bld2_rank_pow_convex, Mathlib2.gen_lin_nilpotent_pow_card_reduced, Mathlib2.bld4_rank_pow_eq_of_card_le and Mathlib2.lib_matrix_rank_eq_zero_iff (nilpotency index ≤ rank + 1): let r_k = rank(A^k). If r_{k+1} = r_k for some k then by bld2_rank_pow_convex (non-increasing non-negative drops) r_j = r_k for all j ≥ k, and by gen_lin_nilpotent_pow_card_reduced / bld4_rank_pow_eq_of_card_le r_j = 0 for large j, so r_k = 0. Hence r_k strictly decreases until it reaches 0, so r_{k+1} ≤ r_1 − k while positive; thus r_{r_1 + 1} = 0 and lib_matrix_rank_eq_zero_iff gives A^(rank A + 1) = 0.

```lean
∀ (K : Type u_1) [inst : Field K] (ι : Type u_2) [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (A : Matrix ι ι K), IsNilpotent A → A ^ (A.rank + 1) = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_rank_pow_convex, Mathlib2.gen_lin_nilpotent_pow_card_reduced, Mathlib2.bld4_rank_pow_eq_of_card_le, Mathlib2.lib_matrix_rank_eq_zero_iff）
- 完成者：prover_bb
- 尝试次数：1
- 被引用：3 次
- 分数：9
- 依赖：`bld2_rank_pow_convex`、`gen_lin_nilpotent_pow_card_reduced`、`lib_matrix_rank_eq_zero_iff`

## `Mathlib2.bld5_pisano_lucas_odd_eq`

Uses Mathlib2.lib_fib_period_iff, Mathlib2.bld3_pisano_dvd_of_period, Mathlib2.lib_pisano_dvd_iff_period, Mathlib2.lib_fib_cassini_cast and Mathlib2.lib_p3_lucas_cast: F_{2n} = F_n·L_n ≡ 0 (Nat.fib_two_mul) and F_{2n+1} = F_{n+1}·L_n − (−1)^n ≡ 1 mod L_n for odd n (lib_p3_lucas_cast, Nat.fib_two_mul_add_one, lib_fib_cassini_cast); so lib_fib_period_iff + bld3_pisano_dvd_of_period give π ∣ 2n (improving bld4_pisano_lucas_dvd_four_mul). Conversely lib_pisano_dvd_iff_period (i = 0) gives L_n ∣ F_π, hence by Nat.fib_gcd L_n ∣ F_{gcd(π,2n)}; F_{n+1} < L_n forces gcd(π, 2n) ≥ n + 2, and the only divisor of 2n above n is 2n, so 2n ∣ π.

```lean
∀ (n : ℕ), 3 ≤ n → Odd n → Mathlib2.p3_pisano (Mathlib2.p3_lucas n) = 2 * n
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.lib_fib_period_iff, Mathlib2.bld3_pisano_dvd_of_period, Mathlib2.lib_pisano_dvd_iff_period, Mathlib2.lib_fib_cassini_cast, Mathlib2.lib_p3_lucas_cast）
- 完成者：prover_ba
- 尝试次数：1
- 被引用：3 次
- 分数：9
- 依赖：`bld3_pisano_dvd_of_period`、`bld3_pisano_pos_and_period`、`lib_fib_cassini_cast`、`lib_fib_period_iff`、`lib_p3_lucas_cast`、`p3_lucas`、`p3_pisano`

## `Mathlib2.bld5_pisano_mul_dvd_mul`

Uses Mathlib2.bld3_pisano_pos_and_period, Mathlib2.lib_fib_period_iff and Mathlib2.bld3_pisano_dvd_of_period: (m = 0 is trivial.) Let N = pisano m; bld3_pisano_pos_and_period + lib_fib_period_iff give F_N ≡ 0, F_{N+1} ≡ 1 mod m, i.e. Q^N = 1 + m•M for the Fibonacci matrix Q = !![1,1;1,0] over ℤ (Matrix.fib-style identity Q^n = [[F_{n+1},F_n],[F_n,F_{n-1}]]). Binomial expansion (Commute.add_pow) of (1 + m•M)^d: the j = 1 term is d·m·M and for j ≥ 2 m^j is divisible by m·d since d ∣ m; so Q^{dN} ≡ 1 mod d·m, i.e. F_{dN} ≡ 0, F_{dN+1} ≡ 1 mod d·m. lib_fib_period_iff turns this into dN being a period and bld3_pisano_dvd_of_period concludes. Special case: π(p^(k+1)) ∣ p·π(p^k).

```lean
∀ (d m : ℕ), d ∣ m → Mathlib2.p3_pisano (d * m) ∣ d * Mathlib2.p3_pisano m
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld3_pisano_pos_and_period, Mathlib2.lib_fib_period_iff, Mathlib2.bld3_pisano_dvd_of_period）
- 完成者：prover_ba
- 尝试次数：1
- 被引用：3 次
- 分数：9
- 依赖：`bld3_pisano_dvd_of_period`、`bld3_pisano_pos_and_period`、`lib_fib_period_iff`、`p3_pisano`

## `Mathlib2.bld_edelstein_iterates_tendsto`

Uses Mathlib2.top_tendsto_of_subseq_limits_unique (and complements Mathlib2.top_edelstein_unique_fixed_point): dist (f^[n] x) p is antitone with limit c; any subsequential limit b satisfies dist b p = c = dist (f b) p by continuity, forcing b = p by strict contraction; conclude by the subsequence criterion on the compact space.

```lean
∀ {X : Type u_1} [inst : MetricSpace X] [CompactSpace X] (f : X → X), (∀ (x y : X), x ≠ y → dist (f x) (f y) < dist x y) → ∀ (p : X), f p = p → ∀ (x : X), Filter.Tendsto (fun n => f^[n] x) Filter.atTop (nhds p)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.top_tendsto_of_subseq_limits_unique, Mathlib2.top_edelstein_unique_fixed_point）
- 完成者：r6_prover_3
- 尝试次数：1
- 被引用：3 次
- 分数：9
- 依赖：`top_tendsto_of_subseq_limits_unique`

## `Mathlib2.bld_frobenius_rank_inequality`

Uses Mathlib2.gen_lin_sylvester_rank_rect: take a rank factorisation B = M * N with M : n × Fin r, N : Fin r × p, r = rank B; apply the rectangular Sylvester inequality to (A*M) and (N*C) to get rank(AM) + rank(NC) ≤ r + rank(ABC), then rank(AB) ≤ rank(AM) and rank(BC) ≤ rank(NC).

```lean
∀ (K : Type u_1) [inst : Field K] (m : Type u_2) (n : Type u_3) (p : Type u_4) (q : Type u_5) [Fintype m] [inst_2 : Fintype n] [inst_3 : Fintype p] [inst_4 : Fintype q] (A : Matrix m n K) (B : Matrix n p K) (C : Matrix p q K), (A * B).rank + (B * C).rank ≤ B.rank + (A * B * C).rank
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.gen_lin_sylvester_rank_rect）
- 完成者：r6_prover_2
- 尝试次数：1
- 被引用：3 次
- 分数：9
- 依赖：`gen_lin_sylvester_rank_rect`

## `Mathlib2.bld_involution_rank_add_rank`

Uses Mathlib2.gen_lin_idempotent_rank_complement_field: P = (1/2) • (1 + A) is idempotent with 1 - P = (1/2) • (1 - A); rank is invariant under scaling by the unit 1/2.

```lean
∀ (K : Type u_1) [inst : Field K] [CharZero K] (ι : Type u_2) [inst_2 : Fintype ι] [inst_3 : DecidableEq ι] (A : Matrix ι ι K), A * A = 1 → (1 + A).rank + (1 - A).rank = Fintype.card ι
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.gen_lin_idempotent_rank_complement_field）
- 完成者：r6_prover_2
- 尝试次数：1
- 被引用：3 次
- 分数：9
- 依赖：`bld_involution_trace_rank_aux1`、`bld_involution_trace_rank_aux2`、`gen_lin_idempotent_rank_complement_field`

## `Mathlib2.bld_involution_trace_rank`

Uses Mathlib2.gen_lin_idempotent_trace_eq_rank_field: P = (1/2) • (1 + A) is idempotent, so tr P = rank P = rank (1 + A) (scaling by a unit preserves rank), and tr P = (n + tr A)/2.

```lean
∀ (K : Type u_1) [inst : Field K] [CharZero K] (ι : Type u_2) [inst_2 : Fintype ι] [inst_3 : DecidableEq ι] (A : Matrix ι ι K), A * A = 1 → A.trace + ↑(Fintype.card ι) = 2 * ↑(1 + A).rank
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.gen_lin_idempotent_trace_eq_rank_field）
- 完成者：r6_prover_2
- 尝试次数：1
- 被引用：3 次
- 分数：9
- 依赖：`gen_lin_idempotent_trace_eq_rank_field`

## `Mathlib2.bld_sqrt_two_rec_rate`

Uses Mathlib2.ana_sqrt_two_rec_closed_form: a n = 2 cos(π/2^(n+1)), so 2 - a n = 4 sin^2(π/2^(n+2)) ≤ 4 (π/2^(n+2))^2 = π^2/4^(n+1). Quantitative rate for Mathlib2.ana_sqrt_two_rec_tendsto.

```lean
∀ (a : ℕ → ℝ), a 0 = 0 → (∀ (n : ℕ), a (n + 1) = √(2 + a n)) → ∀ (n : ℕ), 2 - a n ≤ Real.pi ^ 2 / 4 ^ (n + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.ana_sqrt_two_rec_closed_form）
- 完成者：r6_prover_1
- 尝试次数：1
- 被引用：3 次
- 分数：9
- 依赖：`ana_sqrt_two_rec_closed_form`

## `Mathlib2.calc_tsum_inv_odd_sq`

∑ 1/(2n+1)² = π²/8 — split Basel sum hasSum_zeta_two into even and odd indices (tsum_even_add_odd); even part is (1/4)·π²/6.

```lean
∑' (n : ℕ), 1 / (2 * ↑n + 1) ^ 2 = Real.pi ^ 2 / 8
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：3 次
- 分数：9

## `Mathlib2.comb_degree_add_degree_le_of_triangle_free`

In a triangle-free graph adjacent vertices u, v satisfy deg u + deg v ≤ n (the key step of Mantel's theorem) — the neighbour sets of u and v are disjoint, since a common neighbour w gives the 3-clique {u,v,w}.

```lean
∀ (V : Type) [inst : Fintype V] [DecidableEq V] (G : SimpleGraph V) [inst_2 : DecidableRel G.Adj], G.CliqueFree 3 → ∀ (u v : V), G.Adj u v → G.degree u + G.degree v ≤ Fintype.card V
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_7
- 尝试次数：1
- 被引用：3 次
- 分数：9

## `Mathlib2.gen_lin_sylvester_rank_rect`

Generalizes Mathlib2.lin_sylvester_rank: ℝ → arbitrary field K, square Fin n matrices → rectangular matrices A : m×n, B : n×p over arbitrary Fintypes. Proof idea: the original proof (rank-nullity for A.mulVecLin and for its restriction to range B.mulVecLin) never uses ℝ or squareness.

```lean
∀ (K : Type u_1) [inst : Field K] (m : Type u_2) (n : Type u_3) (p : Type u_4) [Fintype m] [inst_2 : Fintype n] [inst_3 : Fintype p] (A : Matrix m n K) (B : Matrix n p K), A.rank + B.rank ≤ Fintype.card n + (A * B).rank
```
- 结论：证明
- 层级：agent
- 来源：conjecture（generalization of Mathlib2.lin_sylvester_rank）
- 完成者：gen_prover_1
- 尝试次数：1
- 被引用：3 次
- 分数：9

## `Mathlib2.lib_fib_cassini_cast`

Cassini's identity F_(n+2) F_n - F_(n+1)^2 = (-1)^(n+1) in an arbitrary commutative ring (e.g. ZMod p). Promoted and generalised from Mathlib2.p3_aux_period_aux1 (same identity over ℤ as Mathlib2.an_cassini_int, r3_fib_iff_five_sq_pm_four_is_square_s1h1, p3_cor1_aux1).

```lean
∀ (R : Type u_1) [inst : CommRing R] (n : ℕ), ↑(Nat.fib (n + 2)) * ↑(Nat.fib n) - ↑(Nat.fib (n + 1)) ^ 2 = (-1) ^ (n + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.p3_aux_period_aux1）
- 完成者：curator_2
- 尝试次数：1
- 被引用：3 次
- 分数：9
- 依赖：`an_cassini_int`

## `Mathlib2.lib_matrix_rank_smul`

Scaling a (rectangular) matrix over a field by a nonzero scalar does not change its rank: rank (c • M) = rank M. Promoted from Mathlib2.bld_involution_trace_rank_aux1 (also re-proved as bld2_tripotent_rank_split_aux1 and bld2_involution_iff_rank_add_rank_aux1); generalised from square to rectangular matrices.

```lean
∀ (K : Type u_1) [inst : Field K] (m : Type u_2) (n : Type u_3) [Fintype m] [inst_2 : Fintype n] (c : K), c ≠ 0 → ∀ (M : Matrix m n K), (c • M).rank = M.rank
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.bld_involution_trace_rank_aux1）
- 完成者：curator_1
- 尝试次数：1
- 被引用：3 次
- 分数：9

## `Mathlib2.p4_ex1_mono`

The sequences z, m, r are non-decreasing.

```lean
∀ (a b : ℕ), a ≤ b → Mathlib2.p4_z a ≤ Mathlib2.p4_z b ∧ Mathlib2.p4_m a ≤ Mathlib2.p4_m b ∧ Mathlib2.p4_r a ≤ Mathlib2.p4_r b
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Exercise 1 (observations)）
- 完成者：paper_4
- 尝试次数：1
- 被引用：3 次
- 分数：9
- 依赖：`p4_m`、`p4_r`、`p4_z`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). Paper: 'the sequences z(n), m(n), r(n) are non-decreasing'. Same statement; Lean also allows a=0 which is harmless.

## `Mathlib2.p4_lem1_i`

Lemma 1(i): for positive integers a <= n <= b, z(a)-(r(b)+1)m(b) <= x(n) <= z(b)-(r(a)+1)m(a).

```lean
∀ (a b n : ℕ), 0 < a → a ≤ n → n ≤ b → Mathlib2.p4_z a - (↑(Mathlib2.p4_r b) + 1) * ↑(Mathlib2.p4_m b) ≤ Mathlib2.p4_x n ∧ Mathlib2.p4_x n ≤ Mathlib2.p4_z b - (↑(Mathlib2.p4_r a) + 1) * ↑(Mathlib2.p4_m a)
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Lemma 1(i)）
- 完成者：paper_4
- 尝试次数：1
- 被引用：3 次
- 分数：9
- 依赖：`p4_ex1_mono`、`p4_m`、`p4_r`、`p4_x`、`p4_z`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). Paper: positive integers a<=n<=b, z(a)-(r(b)+1)m(b) <= x(n) <= z(b)-(r(a)+1)m(a). Lean identical (0<a gives positivity of all three).

## `Mathlib2.p4_rem1_even`

Remark 1, s=2k: 2^k <= m(2^s) < 2^(k+1) and z(2^s)=p where 2^(2k+1)=3p+2.

```lean
∀ (k : ℕ), 2 ^ k ≤ Mathlib2.p4_m (2 ^ (2 * k)) ∧ Mathlib2.p4_m (2 ^ (2 * k)) < 2 ^ (k + 1) ∧ 2 ^ (2 * k + 1) = 3 * Mathlib2.p4_z (2 ^ (2 * k)) + 2
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Remark 1）
- 完成者：paper_4
- 尝试次数：1
- 被引用：3 次
- 分数：9
- 依赖：`p4_m`、`p4_z`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). Paper (s=2k): 2^k<=m(2^s)<2^(k+1), 2^(2k+1)=3p+2, z(2^s)=p. Lean matches. The printed text has typos here ('(2k+1)^2' for (2^(k+1))^2 and '2^(2k+1)=2*2^k' for 2*2^(2k)) which the Lean statement silently corrects; they do not affe

## `Mathlib2.p5_psi_prime_pow`

Spec for the Dedekind psi definition: psi(p^(k+1)) = p^k (p+1).

```lean
∀ (p k : ℕ), Nat.Prime p → Mathlib2.p5_dedekind_psi (p ^ (k + 1)) = p ^ k * (p + 1)
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2404.19332v1 Section 1 (definition of psi)）
- 完成者：paper_5
- 尝试次数：1
- 被引用：3 次
- 分数：9
- 依赖：`p5_dedekind_psi`
- 复核（reviewer_5）：faithful — Spec lemma for the definition, not a numbered paper statement: psi(p^(k+1))=p^k(p+1) is exactly the paper's formula on a prime power.

## `Mathlib2.poly_abc_radical_bound_of_coprime`

ABC for polynomials in two-variable form: coprime a, b in char 0 with a non-constant satisfy max(deg a, deg b) + 1 ≤ deg rad(ab(a+b)) — b ≠ 0 and a+b ≠ 0 follow from coprimality and deg a > 0; Uses Mathlib2.ms_mason_stothers_v2 with c = -(a+b) (derivative a ≠ 0 in char 0 kills the first alternative), and radical(a*b*(-(a+b))) = radical(a*b*(a+b)) by associatedness.

```lean
∀ {k : Type u_1} [inst : Field k] [inst_1 : DecidableEq k] [CharZero k] (a b : Polynomial k), IsCoprime a b → 0 < a.natDegree → max a.natDegree b.natDegree + 1 ≤ (UniqueFactorizationMonoid.radical (a * b * (a + b))).natDegree
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pa
- 尝试次数：1
- 被引用：3 次
- 分数：9
- 依赖：`ms_mason_stothers_v2`

## `Mathlib2.poly_chebyshev_T_card_distinct_real_roots`

T_n has exactly n distinct real roots — the n points cos((2k+1)π/(2n)), k < n, are distinct (cos is injective on [0,π]) roots since T_n(cos θ) = cos(nθ); and T_n has degree n so at most n roots.

```lean
∀ (n : ℕ), (Polynomial.Chebyshev.T ℝ ↑n).roots.toFinset.card = n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pa
- 尝试次数：1
- 被引用：3 次
- 分数：9

## `Mathlib2.r3_fib_iff_five_sq_pm_four_is_square`

Gessel's criterion: y is a Fibonacci number iff 5y^2+4 or 5y^2-4 is a perfect square. Builds on Cassini's identity Mathlib2.an_cassini_int (the forward direction is L_n^2 - 5F_n^2 = 4(-1)^n with L_n = F_{n-1}+F_{n+1}, a rewriting of Cassini). Proof idea for the converse: descent on the Pell-type equation x^2 - 5y^2 = ±4: x ≡ y mod 2, and for y ≥ 2 the map (x,y) ↦ ((3y - x)/2 ... ) i.e. (y, (x-y)/2) ↦ ((x-y)/2, (3y-x)/2) steps down to a smaller solution of the opposite sign, mirroring (F_{n+1},F_n) ↦ (F_n,F_{n-1}); strong induction with base cases y ≤ 1.

```lean
∀ (y : ℕ), (∃ n, y = Nat.fib n) ↔ ∃ x, x ^ 2 = 5 * y ^ 2 + 4 ∨ x ^ 2 + 4 = 5 * y ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r3_prover_4
- 尝试次数：1
- 被引用：3 次
- 分数：9
- 依赖：`r3_fib_iff_five_sq_pm_four_is_square_s1h1`、`r3_fib_iff_five_sq_pm_four_is_square_s1h2`、`r3_fib_iff_five_sq_pm_four_is_square_s1h3`

## `Mathlib2.top_edelstein_unique_fixed_point`

Edelstein: a strictly distance-decreasing self-map of a nonempty compact metric space has exactly one fixed point — f is 1-Lipschitz hence continuous, x ↦ dist x (f x) attains its minimum at some p; if f p ≠ p then dist (f p) (f (f p)) < dist p (f p) contradicts minimality; uniqueness is immediate from strictness.

```lean
∀ {X : Type u_1} [inst : MetricSpace X] [CompactSpace X] [Nonempty X] (f : X → X), (∀ (x y : X), x ≠ y → dist (f x) (f y) < dist x y) → ∃! p, f p = p
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_4
- 尝试次数：1
- 被引用：3 次
- 分数：9

## `Mathlib2.top_expanding_compact_isometry`

A distance non-decreasing self-map of a compact metric space is an isometry — for x, y use compactness of X × X to find iterates n with (f^[n] x, f^[n] y) arbitrarily close to (x, y) (recurrence of the orbit of the expanding map f × f); then dist (f x) (f y) ≤ dist (f^[n] x) (f^[n] y) ≤ dist x y + 2ε.

```lean
∀ {X : Type u_1} [inst : MetricSpace X] [CompactSpace X] (f : X → X), (∀ (x y : X), dist x y ≤ dist (f x) (f y)) → Isometry f
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_2
- 尝试次数：1
- 被引用：3 次
- 分数：9

## `Mathlib2.ab_perfect_mul_abundant`

Corrected task: a proper multiple (k > 1) of a perfect number is abundant.

```lean
∀ (n k : ℕ), n.Perfect → 1 < k → (k * n).Abundant
```
- 结论：证明
- 层级：agent
- 来源：paper（s40753-021-00140-1 p.9 Data Collection; 11 Table 2）
- 完成者：paper_2
- 尝试次数：2
- 被引用：2 次
- 分数：8
- 依赖：`ab_t2_sum_divisors_ge`
- 复核（reviewer_2）：faithful — Compared with p.9 ('prompted to provide a proof for k > 1') and Table 2 (n a positive perfect integer, k > 1, conclusion kn abundant). Lean: Nat.Perfect n (includes 0 < n), 1 < k, Nat.Abundant (k*n); via the bridge lemmas this is the paper's all-divisor formulation. No differences found beyond restr

## `Mathlib2.ab_t2_mul_mem_divisors`

Table 2 step 5: if d divides n then k d is a divisor of k n.

```lean
∀ (n k d : ℕ), 0 < k → d ∈ n.divisors → k * d ∈ (k * n).divisors
```
- 结论：证明
- 层级：agent
- 来源：paper（s40753-021-00140-1 p.11 Table 2 step [5]）
- 完成者：paper_2
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 复核（reviewer_2）：faithful — Table 2 step [5]: k d_i are among the divisors of kn. Lean: for 0 < k and d in Nat.divisors n (which forces n != 0), k*d in Nat.divisors (k*n). More general than the paper's context (k > 1, n perfect) but implies the step; harmless generalization. Transcription: PDF has 'kdi, kd2, ... kdr' (paper ty

## `Mathlib2.alg_center_index_not_prime`

The index of the center of a group is never a prime — if [G : Z(G)] = p then G/Z(G) is cyclic, so G is abelian and the index is 1.

```lean
∀ (G : Type u_1) [inst : Group G], ¬Nat.Prime (Subgroup.center G).index
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_1
- 尝试次数：1
- 被引用：2 次
- 分数：7

## `Mathlib2.an2_amgm_range_pow`

AM-GM for n+1 nonnegative reals in power form (no rpow): prod a_i ≤ (mean)^(n+1). Generalizes Mathlib2.an_amgm_three_cube (n = 2).

```lean
∀ (n : ℕ) (a : ℕ → ℝ), (∀ (i : ℕ), 0 ≤ a i) → ∏ i ∈ Finset.range (n + 1), a i ≤ ((∑ i ∈ Finset.range (n + 1), a i) / (↑n + 1)) ^ (n + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_a
- 尝试次数：1
- 被引用：2 次
- 分数：7

## `Mathlib2.an2_succ_pow_lt_three_mul_pow`

(1 + 1/n)^n < 3 for n ≥ 1, stated in naturals as (n+1)^n < 3 n^n.

```lean
∀ (n : ℕ), 0 < n → (n + 1) ^ n < 3 * n ^ n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_c
- 尝试次数：1
- 被引用：2 次
- 分数：7

## `Mathlib2.ana_sin_ge_cubic_of_nonneg`

sin x ≥ x - x^3/6 for every x ≥ 0 (Mathlib only has it for x ≤ 1) — differentiate twice: the derivative cos x - 1 + x^2/2 is nonnegative by Real.one_sub_sq_div_two_le_cos, so the difference is monotone from value 0 at 0.

```lean
∀ (x : ℝ), 0 ≤ x → x - x ^ 3 / 6 ≤ Real.sin x
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_2
- 尝试次数：1
- 被引用：2 次
- 分数：7

## `Mathlib2.arith_abundant_mul`

Every positive multiple of an abundant number is abundant — Uses Mathlib2.ab_abundant_def at the first and last step to pass to full divisor sums, and Mathlib2.ab_t2_mul_mem_divisors to inject d ↦ k·d from divisors of n into divisors of k·n, so σ(kn) ≥ kσ(n) > 2kn.

```lean
∀ (n k : ℕ), n.Abundant → 0 < k → (k * n).Abundant
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_aa
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`ab_abundant_def`、`ab_t2_mul_mem_divisors`

## `Mathlib2.arith_card_divisors_odd_iff_isSquare`

τ(n) is odd iff n is a perfect square — the involution d ↦ n/d on divisors has a fixed point iff n is a square.

```lean
∀ (n : ℕ), 0 < n → (Odd n.divisors.card ↔ IsSquare n)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_aa
- 尝试次数：1
- 被引用：2 次
- 分数：7

## `Mathlib2.arith_sigma_odd_iff`

σ(n) is odd iff n is a square or twice a square — σ multiplicative; σ(2^a) is always odd, σ(p^a) for odd p is odd iff a is even.

```lean
∀ (n : ℕ), 0 < n → (Odd ((ArithmeticFunction.sigma 1) n) ↔ IsSquare n ∨ ∃ m, n = 2 * m ^ 2)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_aa
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`arith_card_divisors_odd_iff_isSquare`、`arith_card_divisors_odd_iff_isSquare_aux1`

## `Mathlib2.bld2_commutator_eq_center_of_card_prime_cube`

Uses Mathlib2.bld_center_card_of_card_prime_cube: the centre has order p, so G / Z(G) has order p^2 and is abelian, giving commutator G ≤ Z(G); the commutator subgroup is nontrivial (G non-abelian) and Z(G) has prime order, so the inclusion is an equality.

```lean
∀ (p : ℕ), Nat.Prime p → ∀ (G : Type u_1) [inst : Group G], Nat.card G = p ^ 3 → (∃ a b, a * b ≠ b * a) → commutator G = Subgroup.center G
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_center_card_of_card_prime_cube）
- 完成者：r7_prover_4
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`bld_center_card_of_card_prime_cube`

## `Mathlib2.bld2_fib_odd_index_iff_five_sq_sub_four`

Uses Mathlib2.r3_fib_iff_five_sq_pm_four_is_square and Mathlib2.bld_fib_even_index_iff_five_sq_add_four: y is Fibonacci iff one of the two Pell conditions holds, and the +4 condition characterises even indices; the two conditions hold simultaneously only for y = 1 = fib 1 = fib 2 (x'^2 - x^2 = 8), which settles the overlap, using strict monotonicity of fib from index 2.

```lean
∀ (y : ℕ), (∃ n, y = Nat.fib (2 * n + 1)) ↔ ∃ x, x ^ 2 + 4 = 5 * y ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.r3_fib_iff_five_sq_pm_four_is_square, Mathlib2.bld_fib_even_index_iff_five_sq_add_four）
- 完成者：r7_prover_2
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`bld2_lucas_sq_sub_five_fib_sq`、`bld_fib_even_index_iff_five_sq_add_four`、`p3_lucas`、`r3_fib_iff_five_sq_pm_four_is_square`

## `Mathlib2.bld2_idempotent_iff_rank_add_rank`

Uses Mathlib2.gen_lin_idempotent_rank_complement_field (and Mathlib2.gen_lin_sylvester_rank_rect): forward direction is the rank-complement theorem; conversely the rank equality forces range A and range (1 - A) to be complementary, and A(1-A)x lies in both, so A - A*A = 0.

```lean
∀ (K : Type u_1) [inst : Field K] (ι : Type u_2) [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (A : Matrix ι ι K), A * A = A ↔ A.rank + (1 - A).rank = Fintype.card ι
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.gen_lin_idempotent_rank_complement_field, Mathlib2.gen_lin_sylvester_rank_rect）
- 完成者：r7_prover_1
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`bld2_rank_add_rank_one_sub`、`gen_lin_idempotent_rank_complement_field`

## `Mathlib2.bld2_mantel_equality_regular`

Uses Mathlib2.comb_degree_add_degree_le_of_triangle_free (equality case of Mathlib2.bld_mantel_triangle_free): summing deg u + deg v ≤ n over edges gives ∑ deg^2 ≤ n * e; with Cauchy-Schwarz (2e)^2 ≤ n ∑ deg^2 and 4e = n^2 both are equalities, so ∑ (2 deg v - n)^2 = 0 and every degree equals n/2.

```lean
∀ (V : Type) [inst : Fintype V] [DecidableEq V] (G : SimpleGraph V) [inst_2 : DecidableRel G.Adj], G.CliqueFree 3 → 4 * G.edgeFinset.card = Fintype.card V ^ 2 → ∀ (v : V), 2 * G.degree v = Fintype.card V
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.comb_degree_add_degree_le_of_triangle_free, Mathlib2.bld_mantel_triangle_free）
- 完成者：r7_prover_2
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`comb_degree_add_degree_le_of_triangle_free`

## `Mathlib2.bld2_pell_five_solutions_lucas`

Uses Mathlib2.bld_fib_even_index_iff_five_sq_add_four and Mathlib2.an_cassini_int: the characterisation gives y = fib (2n); the Lucas identity L(2n)^2 = 5 fib(2n)^2 + 4 (from Cassini, with L = Mathlib2.p3_lucas) gives x^2 = L(2n)^2, hence x = L(2n) in ℕ.

```lean
∀ (x y : ℕ), x ^ 2 = 5 * y ^ 2 + 4 → ∃ n, y = Nat.fib (2 * n) ∧ x = Mathlib2.p3_lucas (2 * n)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_fib_even_index_iff_five_sq_add_four, Mathlib2.an_cassini_int, Mathlib2.p3_lucas）
- 完成者：r7_prover_2
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`bld2_lucas_sq_sub_five_fib_sq`、`bld_fib_even_index_iff_five_sq_add_four`、`p3_lucas`

## `Mathlib2.bld2_rat_sq_add_sq_ne_prime_mul_coprime`

Uses Mathlib2.nt2_prime_three_mod_four_dvd_sq_add_sq (generalising Mathlib2.bld_rat_sq_add_sq_ne_prime_three_mod_four): clear denominators to a^2 + b^2 = p * m * d^2 in ℤ with d ≠ 0; by strong induction on |d| (or on the p-adic valuation), p ∣ a and p ∣ b, so p^2 ∣ p * m * d^2, so p ∣ d (as p ∤ m), and dividing a, b, d by p gives a smaller solution.

```lean
∀ (p m : ℕ), Nat.Prime p → p % 4 = 3 → ¬p ∣ m → ∀ (x y : ℚ), x ^ 2 + y ^ 2 ≠ ↑p * ↑m
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.nt2_prime_three_mod_four_dvd_sq_add_sq, Mathlib2.bld_rat_sq_add_sq_ne_prime_three_mod_four）
- 完成者：r7_prover_3
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`nt2_prime_three_mod_four_dvd_sq_add_sq`

## `Mathlib2.bld3_card_sylow_of_card_prime_mul_prime`

Uses Mathlib2.bld_center_eq_bot_of_card_prime_mul_prime: the number of Sylow p-subgroups divides q, so is 1 or q; if 1 the Sylow p-subgroup P is normal of order p, G acts on it by conjugation through Aut(P) of order p - 1 coprime to pq, so P is central, contradicting the trivial centre.

```lean
∀ (p q : ℕ) [Fact (Nat.Prime p)], Nat.Prime q → p < q → ∀ (G : Type u_1) [inst : Group G], Nat.card G = p * q → (∃ a b, a * b ≠ b * a) → Nat.card (Sylow p G) = q
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_center_eq_bot_of_card_prime_mul_prime）
- 完成者：r8_prover_4
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`bld_center_eq_bot_of_card_prime_mul_prime`

## `Mathlib2.bld3_edelstein_iterates_tendsto_uniformly`

Uses Mathlib2.bld_edelstein_iterates_tendsto: the continuous functions x ↦ dist (f^[n] x) p decrease in n and tend to 0 pointwise by the library theorem; Dini's argument (the open sets {x | dist (f^[n] x) p < ε} increase and cover the compact X) gives uniformity.

```lean
∀ {X : Type u_1} [inst : MetricSpace X] [CompactSpace X] (f : X → X), (∀ (x y : X), x ≠ y → dist (f x) (f y) < dist x y) → ∀ (p : X), f p = p → ∀ (ε : ℝ), 0 < ε → ∃ N, ∀ (n : ℕ), N ≤ n → ∀ (x : X), dist (f^[n] x) p < ε
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_edelstein_iterates_tendsto）
- 完成者：r8_prover_1
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`bld_edelstein_iterates_tendsto`

## `Mathlib2.bld3_mantel_equality_same_neighbors`

Uses Mathlib2.bld2_mantel_equality_regular and Mathlib2.comb_degree_add_degree_le_of_triangle_free: all degrees are n/2; for an edge u v the neighbourhoods are disjoint of total size n so they partition V; if z ~ x then y lies in N(x) or N(z), the former is excluded, so y ~ z (the extremal graph is complete bipartite).

```lean
∀ (V : Type) [inst : Fintype V] [DecidableEq V] (G : SimpleGraph V) [inst_2 : DecidableRel G.Adj], G.CliqueFree 3 → 4 * G.edgeFinset.card = Fintype.card V ^ 2 → ∀ (x y : V), ¬G.Adj x y → ∀ (z : V), G.Adj x z ↔ G.Adj y z
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_mantel_equality_regular, Mathlib2.comb_degree_add_degree_le_of_triangle_free）
- 完成者：r8_prover_2
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`bld2_mantel_equality_regular`

## `Mathlib2.bld3_mul_pow_prime_of_card_prime_cube`

Uses Mathlib2.bld2_commutator_eq_center_of_card_prime_cube and Mathlib2.bld_center_card_of_card_prime_cube: commutators are central of order dividing p, so by induction (a b)^k = a^k b^k c^(k(k-1)/2) with c the central commutator of b and a; for odd p, p ∣ p(p-1)/2 and c^p = 1 (false for p = 2, e.g. the dihedral group of order 8).

```lean
∀ (p : ℕ), Nat.Prime p → ∀ (G : Type u_1) [inst : Group G], Nat.card G = p ^ 3 → (∃ a b, a * b ≠ b * a) → p ≠ 2 → ∀ (a b : G), (a * b) ^ p = a ^ p * b ^ p
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_commutator_eq_center_of_card_prime_cube, Mathlib2.bld_center_card_of_card_prime_cube）
- 完成者：r8_prover_3
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`bld2_commutator_eq_center_of_card_prime_cube`、`bld_center_card_of_card_prime_cube`

## `Mathlib2.bld3_rat_sq_add_sq_ne_of_odd_padicValNat`

Uses Mathlib2.bld2_rat_sq_add_sq_ne_prime_mul_coprime: write n = p^(2k+1) m with p ∤ m; if x^2 + y^2 = n then (x/p^k)^2 + (y/p^k)^2 = p m, contradicting the library theorem (rational form of the two-squares obstruction).

```lean
∀ (p n : ℕ), Nat.Prime p → p % 4 = 3 → Odd (padicValNat p n) → ∀ (x y : ℚ), x ^ 2 + y ^ 2 ≠ ↑n
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_rat_sq_add_sq_ne_prime_mul_coprime）
- 完成者：r8_prover_3
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`bld2_rat_sq_add_sq_ne_prime_mul_coprime`

## `Mathlib2.bld3_sqrt_two_rec_defect_tsum_bounds`

Uses Mathlib2.bld_sqrt_two_rec_rate and Mathlib2.bld2_sqrt_two_rec_defect_summable: upper bound: compare termwise with the geometric series ∑ π^2/4^(n+1) = π^2/3 using the rate; lower bound: 2 - a (n+1) = (2 - a n)/(2 + a (n+1)) ≥ (2 - a n)/4 gives 2 - a n ≥ 2/4^n, whose sum is 8/3; summability from the library.

```lean
∀ (a : ℕ → ℝ), a 0 = 0 → (∀ (n : ℕ), a (n + 1) = √(2 + a n)) → 8 / 3 ≤ ∑' (n : ℕ), (2 - a n) ∧ ∑' (n : ℕ), (2 - a n) ≤ Real.pi ^ 2 / 3
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_sqrt_two_rec_rate, Mathlib2.bld2_sqrt_two_rec_defect_summable）
- 完成者：r8_prover_3
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`ana_sqrt_two_rec_lt_two`、`bld2_sqrt_two_rec_defect_summable`、`bld_sqrt_two_rec_rate`

## `Mathlib2.bld4_fitting_range_inter_ker_pow_card`

Uses Mathlib2.bld3_rank_pow_card_stabilizes and Mathlib2.bld2_rank_pow_convex: with N = A^n, stabilisation (base case from rank_pow_card_stabilizes, propagated to exponent 2n by rank_pow_convex) gives rank(N * N) = rank N. By rank–nullity ker N ≤ ker (N * N) have equal finrank, hence are equal, which is the claim (Fitting: range N ∩ ker N = 0).

```lean
∀ (K : Type u_1) [inst : Field K] (ι : Type u_2) [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (A : Matrix ι ι K) (v : ι → K), (A ^ Fintype.card ι).mulVec ((A ^ Fintype.card ι).mulVec v) = 0 → (A ^ Fintype.card ι).mulVec v = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld3_rank_pow_card_stabilizes, Mathlib2.bld2_rank_pow_convex）
- 完成者：r9_prover_2
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`bld2_rank_pow_convex`、`bld3_rank_pow_card_stabilizes`

## `Mathlib2.bld4_pisano_mul_of_coprime`

Uses Mathlib2.bld3_pisano_dvd_pisano_of_dvd, Mathlib2.bld3_pisano_pos_and_period and Mathlib2.bld3_pisano_dvd_of_period: pisano_dvd_pisano_of_dvd (m ∣ mn, n ∣ mn) gives lcm ∣ π(mn). Conversely pos_and_period makes L = lcm(π m, π n) a period mod m and mod n (iterate the period), hence mod mn by Nat.modEq_and_modEq_iff_modEq_mul for coprime m n, and dvd_of_period gives π(mn) ∣ L. Case m = 0 forces n = 1 (both sides 0).

```lean
∀ (m n : ℕ), m.Coprime n → Mathlib2.p3_pisano (m * n) = (Mathlib2.p3_pisano m).lcm (Mathlib2.p3_pisano n)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld3_pisano_dvd_pisano_of_dvd, Mathlib2.bld3_pisano_pos_and_period, Mathlib2.bld3_pisano_dvd_of_period）
- 完成者：r9_prover_1
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`bld3_pisano_dvd_of_period`、`bld3_pisano_dvd_pisano_of_dvd`、`bld3_pisano_pos_and_period`、`lib_pisano_dvd_iff_period`、`p3_pisano`

## `Mathlib2.bld4_pisano_prime_dvd_two_mul_succ_of_not_isSquare_five`

Uses Mathlib2.p3_aux_fib_prime, Mathlib2.lib_fib_period_iff and Mathlib2.bld3_pisano_dvd_of_period: p ≠ 2, 5 since 5 is a square there; Euler's criterion gives 5^(p/2) = −1, so p3_aux_fib_prime yields F_p ≡ −1, F_{p+1} ≡ 0, hence F_{p+2} ≡ −1 mod p. By Nat.fib_add, F_{2p+2} ≡ 0 and F_{2p+3} ≡ F_{p+2}^2 ≡ 1, so lib_fib_period_iff makes 2(p+1) a period and bld3_pisano_dvd_of_period concludes.

```lean
∀ (p : ℕ) [inst : Fact (Nat.Prime p)], ¬IsSquare 5 → Mathlib2.p3_pisano p ∣ 2 * (p + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.p3_aux_fib_prime, Mathlib2.lib_fib_period_iff, Mathlib2.bld3_pisano_dvd_of_period）
- 完成者：r9_prover_1
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`bld3_pisano_dvd_of_period`、`lib_fib_period_iff`、`p3_aux_fib_prime`、`p3_pisano`

## `Mathlib2.bld4_pow_prime_monoidHom_center_of_card_prime_cube`

Uses Mathlib2.bld3_pow_prime_mem_center_of_card_prime_cube and Mathlib2.bld3_mul_pow_prime_of_card_prime_cube: define φ g = ⟨g^p, _⟩ using pow_prime_mem_center for membership; map_mul is exactly (ab)^p = a^p b^p from mul_pow_prime (p odd), map_one is one_pow.

```lean
∀ (p : ℕ), Nat.Prime p → ∀ (G : Type u_1) [inst : Group G], Nat.card G = p ^ 3 → (∃ a b, a * b ≠ b * a) → p ≠ 2 → ∃ φ, ∀ (g : G), ↑(φ g) = g ^ p
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld3_pow_prime_mem_center_of_card_prime_cube, Mathlib2.bld3_mul_pow_prime_of_card_prime_cube）
- 完成者：r9_prover_3
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`bld3_mul_pow_prime_of_card_prime_cube`、`bld3_pow_prime_mem_center_of_card_prime_cube`

## `Mathlib2.bld5_pisano_five_pow`

Uses Mathlib2.lib_fib_period_iff, Mathlib2.bld3_pisano_dvd_of_period, Mathlib2.bld3_pisano_dvd_pisano_of_dvd and Mathlib2.lib_pisano_dvd_iff_period: key identity F_{5n} = 25F_n^5 + 25(-1)^n F_n^3 + 5F_n (over ℤ), whence by induction 5^j ∣ F_{5^j} but 5^(j+1) ∤ F_{5^j}. Upper bound: induct with the matrix/binomial argument (Q^{4·5^k} = 1 + 5^k•M ⇒ Q^{4·5^(k+1)} ≡ 1 mod 5^(k+1)), base F_20 = 6765, F_21 = 10946; then lib_fib_period_iff + bld3_pisano_dvd_of_period give pisano ∣ 4·5^(k+1). Lower bound by induction: bld3_pisano_dvd_pisano_of_dvd gives 4·5^k ∣ pisano(5^(k+1)) ∣ 4·5^(k+1), so the quotient is 1 or 5; if pisano = 4·5^k then (lib_pisano_dvd_iff_period, i = 0) 5^(k+1) ∣ F_{4·5^k}, and with 5^(k+1) ∣ F_{5^(k+1)} and Nat.fib_gcd this gives 5^(k+1) ∣ F_{5^k}, contradiction. Base pisano 5 = 20 by direct check of the divisors of 20.

```lean
∀ (k : ℕ), Mathlib2.p3_pisano (5 ^ (k + 1)) = 4 * 5 ^ (k + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.lib_fib_period_iff, Mathlib2.bld3_pisano_dvd_of_period, Mathlib2.bld3_pisano_dvd_pisano_of_dvd, Mathlib2.lib_pisano_dvd_iff_period）
- 完成者：prover_bb
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`bld3_pisano_dvd_of_period`、`bld3_pisano_dvd_pisano_of_dvd`、`bld5_pisano_mul_dvd_mul`、`lib_fib_period_iff`、`lib_pisano_dvd_iff_period`、`p3_pisano`

## `Mathlib2.bld5_pisano_two_pow`

Uses Mathlib2.lib_fib_period_iff, Mathlib2.bld3_pisano_dvd_of_period, Mathlib2.bld3_pisano_dvd_pisano_of_dvd and Mathlib2.lib_pisano_dvd_iff_period: prove by induction on j ≥ 1, using Nat.fib_two_mul and Nat.fib_two_mul_add_one, that F_{3·2^j} ≡ 2^(j+2) mod 2^(j+3) and F_{3·2^j+1} ≡ 1 + 2^(j+1) mod 2^(j+2) (base F_6 = 8, F_7 = 13). Upper bound: F_{3·2^k} ≡ 0, F_{3·2^k+1} ≡ 1 mod 2^(k+1), so lib_fib_period_iff + bld3_pisano_dvd_of_period give pisano ∣ 3·2^k. Lower bound by induction on k: bld3_pisano_dvd_pisano_of_dvd gives 3·2^(k-1) = pisano(2^k) ∣ pisano(2^(k+1)), so the value is 3·2^(k-1) or 3·2^k; the former is not a period (lib_pisano_dvd_iff_period at i = 1, or i = 0 when k = 1) because F_{3·2^(k-1)+1} ≡ 1 + 2^k ≢ 1 mod 2^(k+1). Base: pisano 2 = 3 by direct check.

```lean
∀ (k : ℕ), Mathlib2.p3_pisano (2 ^ (k + 1)) = 3 * 2 ^ k
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.lib_fib_period_iff, Mathlib2.bld3_pisano_dvd_of_period, Mathlib2.bld3_pisano_dvd_pisano_of_dvd, Mathlib2.lib_pisano_dvd_iff_period）
- 完成者：prover_bb
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`bld3_pisano_dvd_of_period`、`bld3_pisano_dvd_pisano_of_dvd`、`bld4_pisano_lucas_dvd_four_mul_aux1`、`lib_fib_period_iff`、`lib_pisano_dvd_iff_period`、`p3_pisano`

## `Mathlib2.bld_center_eq_bot_of_card_prime_mul_prime`

Uses Mathlib2.alg_center_index_not_prime: |Z| divides p*q; |Z| = p or q gives prime index, contradicting the library theorem, and |Z| = p*q contradicts non-commutativity, so |Z| = 1.

```lean
∀ (p q : ℕ), Nat.Prime p → Nat.Prime q → ∀ (G : Type u_1) [inst : Group G], Nat.card G = p * q → (∃ a b, a * b ≠ b * a) → Subgroup.center G = ⊥
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.alg_center_index_not_prime）
- 完成者：r6_prover_2
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`alg_center_index_not_prime`

## `Mathlib2.bld_fib_even_index_iff_five_sq_add_four`

Uses Mathlib2.r3_fib_iff_five_sq_pm_four_is_square and Mathlib2.an_cassini_int: solutions of the Pell-type equation x^2 - 5y^2 = 4 are exactly even-indexed Fibonacci numbers. (⇐) the library iff gives y = fib m; if m is odd then Cassini gives 5y^2-4 a square as well, and two squares differing by 8 force y = 1 = fib 2. (⇒) L_{2n}^2 = 5 F_{2n}^2 + 4 from Cassini.

```lean
∀ (y : ℕ), (∃ n, y = Nat.fib (2 * n)) ↔ ∃ x, x ^ 2 = 5 * y ^ 2 + 4
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.r3_fib_iff_five_sq_pm_four_is_square, Mathlib2.an_cassini_int）
- 完成者：r6_prover_3
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`an_cassini_int`、`r3_fib_iff_five_sq_pm_four_is_square`

## `Mathlib2.calc_integral_dalzell`

Dalzell's integral ∫₀¹ x⁴(1−x)⁴/(1+x²) dx = 22/7 − π — polynomial division: integrand = x⁶ − 4x⁵ + 5x⁴ − 4x² + 4 − 4/(1+x²); integrate termwise, integral_inv_one_add_sq / arctan 1 = π/4.

```lean
∫ (x : ℝ) in 0..1, x ^ 4 * (1 - x) ^ 4 / (1 + x ^ 2) = 22 / 7 - Real.pi
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：2 次
- 分数：7

## `Mathlib2.calc_one_add_inv_pow_lt_exp`

(1+1/n)ⁿ < e — from 1 + t < exp t for t ≠ 0 (Real.add_one_lt_exp) at t = 1/n, raise to n-th power, exp(1/n)^n = e.

```lean
∀ (n : ℕ), 0 < n → (1 + 1 / ↑n) ^ n < Real.exp 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：2 次
- 分数：7

## `Mathlib2.calc_sum_card_fixed_points_perm`

Total number of fixed points over all permutations of Fin n (n ≥ 1) is n! (expected number of fixed points is 1) — double count pairs (σ,i) with σ i = i: each i has (n−1)! stabiliser elements (MulAction.card stabilizer / Equiv.Perm.decomposeFin), so total n·(n−1)!.

```lean
∀ (n : ℕ), 0 < n → ∑ σ, {i | σ i = i}.card = n.factorial
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_cb
- 尝试次数：1
- 被引用：2 次
- 分数：7

## `Mathlib2.gen_lin_idempotent_rank_complement_field`

Generalizes Mathlib2.lin_idempotent_rank_complement: ℝ → arbitrary field K, Fin n → arbitrary Fintype. Proof idea: avoid the trace argument (fails to conclude in positive characteristic); instead range(1-A) = ker A for idempotent A and rank-nullity, or Sylvester (A(1-A)=0 gives ≤) plus rank subadditivity for A + (1-A) = 1 (gives ≥).

```lean
∀ (K : Type u_1) [inst : Field K] (ι : Type u_2) [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (A : Matrix ι ι K), A * A = A → A.rank + (1 - A).rank = Fintype.card ι
```
- 结论：证明
- 层级：agent
- 来源：conjecture（generalization of Mathlib2.lin_idempotent_rank_complement）
- 完成者：gen_prover_1
- 尝试次数：1
- 被引用：2 次
- 分数：7

## `Mathlib2.gen_lin_nilpotent_det_one_add_reduced`

Generalizes Mathlib2.lin_nilpotent_det_one_add: ℝ → any reduced commutative ring (false in non-reduced rings: det(1+[ε]) = 1+ε), Fin n → Fintype. Proof idea: charpoly(−A) = X^card as for nilpotent matrices over a reduced ring; evaluate at 1: det(1·1 − (−A)) = 1.

```lean
∀ (R : Type u_1) [inst : CommRing R] [IsReduced R] (ι : Type u_2) [inst_2 : Fintype ι] [inst_3 : DecidableEq ι] (A : Matrix ι ι R), IsNilpotent A → (1 + A).det = 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture（generalization of Mathlib2.lin_nilpotent_det_one_add）
- 完成者：gen_prover_1
- 尝试次数：1
- 被引用：2 次
- 分数：7

## `Mathlib2.gen_lin_nilpotent_pow_card_reduced`

Generalizes Mathlib2.lin_nilpotent_pow_card: ℝ → any reduced commutative ring (false for non-reduced rings: the 1×1 matrix [ε], ε²=0), Fin n → Fintype. Proof idea: Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent gives charpoly − X^card nilpotent in R[X], which is reduced, so charpoly = X^card; then Cayley–Hamilton (Matrix.aeval_self_charpoly).

```lean
∀ (R : Type u_1) [inst : CommRing R] [IsReduced R] (ι : Type u_2) [inst_2 : Fintype ι] [inst_3 : DecidableEq ι] (A : Matrix ι ι R), IsNilpotent A → A ^ Fintype.card ι = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture（generalization of Mathlib2.lin_nilpotent_pow_card）
- 完成者：gen_prover_1
- 尝试次数：1
- 被引用：2 次
- 分数：7

## `Mathlib2.lib_chebyshev_T_natDegree_le`

promoted from Mathlib2.poly_chebyshev_T_card_distinct_real_roots_aux1 (generalised from natural to integer index): the Chebyshev polynomial T_n has degree at most |n| over any commutative ring.

```lean
∀ (R : Type u_1) [inst : CommRing R] (n : ℤ), (Polynomial.Chebyshev.T R n).natDegree ≤ n.natAbs
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：curator_3
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`poly_chebyshev_T_card_distinct_real_roots_aux1`

## `Mathlib2.lin_cayley_hamilton_two`

Cayley–Hamilton for 2×2 matrices over a commutative ring: A² − (tr A)A + (det A)I = 0 — entrywise check after expanding mul, trace and det on Fin 2, then ring.

```lean
∀ (R : Type) [inst : CommRing R] (A : Matrix (Fin 2) (Fin 2) R), A * A - A.trace • A + A.det • 1 = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_3
- 尝试次数：1
- 被引用：2 次
- 分数：7

## `Mathlib2.ms_fermat_catalan`

Fermat–Catalan for polynomials: u a^p + v b^q + w c^r = 0 with 1/p+1/q+1/r ≤ 1, exponents prime to char, forces coprime nonzero a,b,c to be constant.

```lean
∀ {k : Type u_1} [inst : Field k] (p q r : ℕ), 1 ≤ p → 1 ≤ q → 1 ≤ r → ¬ringChar k ∣ p → ¬ringChar k ∣ q → ¬ringChar k ∣ r → 1 / ↑p + 1 / ↑q + 1 / ↑r ≤ 1 → ∀ (u v w : k), u ≠ 0 → v ≠ 0 → w ≠ 0 → ∀ (a b c : Polynomial k), a ≠ 0 → b ≠ 0 → c ≠ 0 → IsCoprime a b → IsCoprime b c → IsCoprime c a → Polynomial.C u * a ^ p + Polynomial.C v * b ^ q + Polynomial.C w * c ^ r = 0 → a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2408.15180v2 Theorem 2, p.3）
- 完成者：paper_1
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 复核（reviewer_1）：faithful — Compared PDF p.3 Theorem 2; transcription matches. All hypotheses present, none added: p,q,r>=1 in N, not ringChar | p,q,r (in char 0 this is p,q,r != 0, vacuous, as the prose intends), 1/p+1/q+1/r<=1 cast to Q so no N-division pitfall, u,v,w nonzero embedded via Polynomial.C. 'Constants' is rendere

## `Mathlib2.nt2_fib_odd_index_no_prime_factor_three_mod_four`

No prime p ≡ 3 (mod 4) divides an odd-indexed Fibonacci number: F_{2n+1} = F_n^2 + F_{n+1}^2 is a sum of two coprime squares.

```lean
∀ (n p : ℕ), Nat.Prime p → p % 4 = 3 → ¬p ∣ Nat.fib (2 * n + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_a
- 尝试次数：1
- 被引用：2 次
- 分数：7

## `Mathlib2.nt2_prod_divisors_sq`

The square of the product of the divisors of n equals n^{d(n)}.

```lean
∀ (n : ℕ), (∏ d ∈ n.divisors, d) ^ 2 = n ^ n.divisors.card
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_d
- 尝试次数：1
- 被引用：2 次
- 分数：7

## `Mathlib2.nt2_two_mul_sum_coprime_eq_mul_totient`

For n > 1 the sum of the integers in [0,n) coprime to n is n φ(n)/2 (pair k with n-k).

```lean
∀ (n : ℕ), 1 < n → 2 * ∑ k ∈ Finset.range n with k.Coprime n, k = n * n.totient
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_e
- 尝试次数：1
- 被引用：2 次
- 分数：7

## `Mathlib2.p3_thm1_corrected`

CORRECTED Theorem 1 (auditor's correction, not the paper's wording): S_p = 1 mod p if p = 1,4 mod 5 and S_p = -2 mod p if p = 2,3 mod 5

```lean
∀ (p : ℕ), Nat.Prime p → 5 < p → (p % 5 = 1 ∨ p % 5 = 4 → ↑(Mathlib2.p3_fibsum p) ≡ 1 [ZMOD ↑p]) ∧ (p % 5 = 2 ∨ p % 5 = 3 → ↑(Mathlib2.p3_fibsum p) ≡ -2 [ZMOD ↑p])
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2504.09938 Theorem 1 (corrected by auditor)）
- 完成者：paper_3
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`p3_aux_fib_prime`、`p3_fibsum`、`p3_prop1_aux1`
- 复核（reviewer_3）：unsure — Not a claim of the paper: auditor's corrected residues (1 if p=+-1 mod 5, -2 if p=+-2 mod 5). Verified independently in Python for all primes 5<p<200 and by redoing the paper's Binet computation (k=0 term is C(p+2,1)*5^0=p+2, giving 4F_{p+2}=2+6(5/p)). Informal and source fields do say 'auditor's co

## `Mathlib2.p4_ex1_levels`

Level sets: z(n)=k iff 3k < 2n <= 3k+3; m(n)=k iff k^2 <= 2n < (k+1)^2; for k>=1, r(n)=k iff 2^(k-1) < n <= 2^k.

```lean
∀ (n k : ℕ), 0 < n → (Mathlib2.p4_z n = ↑k ↔ 3 * k < 2 * n ∧ 2 * n ≤ 3 * k + 3) ∧ (Mathlib2.p4_m n = k ↔ k ^ 2 ≤ 2 * n ∧ 2 * n < (k + 1) ^ 2) ∧ (1 ≤ k → (Mathlib2.p4_r n = k ↔ 2 ^ (k - 1) < n ∧ n ≤ 2 ^ k))
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Exercise 1 (observations)）
- 完成者：paper_4
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`p4_m`、`p4_r`、`p4_z`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). The three iff characterisations match (k non-negative; r-case for k>=1; paper's extra 'n>=2' is implied). Difference: the paper's parenthetical counts (one/two n for z; k or k+1 n for m; 2^(k-1) n for r) are NOT formalised; I che

## `Mathlib2.p4_r_spec`

The Lean definition p4_r agrees with the paper's: r(n) is the least non-negative integer with n <= 2^r(n).

```lean
∀ (n : ℕ), n ≤ 2 ^ Mathlib2.p4_r n ∧ ∀ (k : ℕ), n ≤ 2 ^ k → Mathlib2.p4_r n ≤ k
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Introduction, definition (c)）
- 完成者：paper_4
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`p4_r`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). States definition (c): n<=2^r(n) and minimality over naturals k. Matches 'least non-negative integer'.

## `Mathlib2.p4_rem1_lower`

Remark 1: for 2^s < n <= 2^(s+1), r(n)=s+1 and x(n) >= z(2^s)-(s+2)m(2^(s+1)).

```lean
∀ (s n : ℕ), 2 ^ s < n → n ≤ 2 ^ (s + 1) → Mathlib2.p4_r n = s + 1 ∧ Mathlib2.p4_z (2 ^ s) - (↑s + 2) * ↑(Mathlib2.p4_m (2 ^ (s + 1))) ≤ Mathlib2.p4_x n
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Remark 1）
- 完成者：paper_4
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`p4_ex1_levels`、`p4_lem1_i`、`p4_m`、`p4_r`、`p4_x`、`p4_z`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). Paper: for 2^s<n<=2^(s+1), r(n)=s+1 and x(n)>=z(2^s)-(s+2)m(2^(s+1)). Lean identical.

## `Mathlib2.p4_rem1_odd`

Remark 1, s=2k+1: m(2^s)=2^(k+1) and z(2^s)=q where 2^(2k+2)=3q+1.

```lean
∀ (k : ℕ), Mathlib2.p4_m (2 ^ (2 * k + 1)) = 2 ^ (k + 1) ∧ 2 ^ (2 * k + 2) = 3 * Mathlib2.p4_z (2 ^ (2 * k + 1)) + 1
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Remark 1）
- 完成者：paper_4
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`p4_m`、`p4_z`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). Paper (s=2k+1): m(2^s)=2^(k+1), 2^(2k+2)=3q+1, z(2^s)=q. Lean matches.

## `Mathlib2.p5_psi_mul_coprime`

Spec: Dedekind psi is multiplicative on coprime arguments.

```lean
∀ (m n : ℕ), m.Coprime n → Mathlib2.p5_dedekind_psi (m * n) = Mathlib2.p5_dedekind_psi m * Mathlib2.p5_dedekind_psi n
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2404.19332v1 Section 1 (definition of psi)）
- 完成者：paper_5
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`p5_dedekind_psi`
- 复核（reviewer_5）：faithful — Spec lemma, not stated in the paper but immediate from its product formula: psi multiplicative on coprime arguments (degenerate 0 cases are consistent with psi(0)=1). Source field correctly points to the definition rather than a theorem.

## `Mathlib2.p5_sigma_prime_mul_of_dvd`

Equation (7), sigma part: if p | n then sigma(np) > p sigma(n).

```lean
∀ (p n : ℕ), Nat.Prime p → p ∣ n → n ≠ 0 → p * (ArithmeticFunction.sigma 1) n < (ArithmeticFunction.sigma 1) (p * n)
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2404.19332v1 equation (7)）
- 完成者：paper_5
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 复核（reviewer_5）：faithful — Eq (7) verbatim: for p | n, sigma(np) > p sigma(n) (strict); Lean has strict < with p prime, p | n, n != 0. Matches.

## `Mathlib2.poly_cyclotomic_two_mul_odd_comp_neg`

For odd n > 1, Φ_{2n}(X) = Φ_n(-X) — Polynomial.cyclotomic_mul_prime_of_not_dvd-type identity Φ_{2n}(X)·Φ_n(X) = Φ_n(X^2) (expand by the prime 2 ∤ n), together with Φ_n(X^2) = Φ_n(X)·Φ_n(-X) up to sign, proved via strong induction on n using X^n - 1 = ∏_{d ∣ n} Φ_d and (-X)^n - 1 = -(X^n + 1) for odd n; φ(n) even for n > 1 fixes the sign.

```lean
∀ (n : ℕ), Odd n → 1 < n → Polynomial.cyclotomic (2 * n) ℤ = (Polynomial.cyclotomic n ℤ).comp (-Polynomial.X)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pb
- 尝试次数：1
- 被引用：2 次
- 分数：7

## `Mathlib2.r3_fib_iff_five_sq_pm_four_is_square_s1h1`

r3_fib_iff_five_sq_pm_four_is_square 的证明骨架中第 1 个空洞

```lean
∀ (n : ℕ), ↑(Nat.fib (n + 1)) ^ 2 - ↑(Nat.fib (n + 1)) * ↑(Nat.fib n) - ↑(Nat.fib n) ^ 2 = (-1) ^ n
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_fib_iff_five_sq_pm_four_is_square）
- 完成者：r3_prover_4
- 尝试次数：1
- 被引用：2 次
- 分数：7

## `Mathlib2.r3_hardy_inequality_finite`

Hardy's inequality for finite sums with the sharp constant 4 (p = 2): the sum of squares of the running averages is at most 4 times the sum of squares. Proof idea: with α_k the k-th average, a_k = kα_k - (k-1)α_{k-1}, show α_k^2 - 2α_k a_k ≤ (k-1)α_{k-1}^2 - kα_k^2 (AM-GM on the cross term), telescope to get Σα_k^2 ≤ 2Σα_k a_k, then Cauchy–Schwarz and cancel sqrt(Σα_k^2).

```lean
∀ (a : ℕ → ℝ) (n : ℕ), ∑ k ∈ Finset.range n, ((∑ i ∈ Finset.range (k + 1), a i) / (↑k + 1)) ^ 2 ≤ 4 * ∑ k ∈ Finset.range n, a k ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r3_prover_3
- 尝试次数：1
- 被引用：2 次
- 分数：7
- 依赖：`r3_hardy_inequality_finite_s1h1`、`r3_hardy_inequality_finite_s1h2`、`r3_hardy_inequality_finite_s2h1`

## `Mathlib2.top_isometry_compact_surjective`

An isometry of a compact metric space into itself is surjective — if y is not in the (closed) range, pick ε > 0 with ball y ε disjoint from range f; the orbit f^[n] y then satisfies dist (f^[m] y) (f^[n] y) = dist y (f^[n-m] y) ≥ ε, so it has no convergent subsequence, contradicting sequential compactness.

```lean
∀ {X : Type u_1} [inst : MetricSpace X] [CompactSpace X] (f : X → X), Isometry f → Function.Surjective f
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_4
- 尝试次数：1
- 被引用：2 次
- 分数：7

## `Mathlib2.ab_perfect_six`

6 is perfect.

```lean
Nat.Perfect 6
```
- 结论：证明
- 层级：agent
- 来源：paper（s40753-021-00140-1 p.17）
- 完成者：paper_2
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 复核（reviewer_2）：faithful — p.17: '6 (the smallest perfect number)' implies 6 is perfect; Lean Nat.Perfect 6 is exactly that under the equivalent proper-divisor definition. Transcription matches PDF page 17 (index 16), sentence spans the page break from p.16.

## `Mathlib2.ab_prime_mul_prime_not_abundant`

Auditor's correction of Task 3(b) (not stated in paper): a product of two primes is never abundant.

```lean
∀ (p q : ℕ), Nat.Prime p → Nat.Prime q → ¬(p * q).Abundant
```
- 结论：证明
- 层级：agent
- 来源：paper（s40753-021-00140-1 p.28 Appendix 2 Task 3(b) (auditor's corrected form; the paper gives none)）
- 完成者：paper_2
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 复核（reviewer_2）：unsure — Not a claim of the paper: this is the formalizer's own corrected form of Task 3(b); the paper gives no correction and does not discuss the truth of 3(b). The 'original' field quotes the opposite statement from the paper. Mathematically it is the true negation-for-all-primes (p*q has proper divisors 

## `Mathlib2.ab_t2_sum_divisors_ge`

Table 2 step 9: sum of divisors of kn is at least 2kn + 1 (the k d_i together with 1).

```lean
∀ (n k : ℕ), n.Perfect → 1 < k → 2 * (k * n) + 1 ≤ ∑ d ∈ (k * n).divisors, d
```
- 结论：证明
- 层级：agent
- 来源：paper（s40753-021-00140-1 p.11 Table 2 step [9]）
- 完成者：paper_2
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 复核（reviewer_2）：faithful — Table 2 step [9]. The PDF line reads 'sum of divisors of kn >= sum k d_i = 2kn+1 > sum k d_i = 2kn', which is garbled as printed (a '+1' after the first sum is evidently missing, since step [8] says sum k d_i = 2kn). Lean states the evident intent: 2kn + 1 <= sum of Nat.divisors (k*n) for perfect n,

## `Mathlib2.alg_artin_schreier_irreducible_zmod_s1h1`

alg_artin_schreier_irreducible_zmod 的证明骨架中第 1 个空洞

```lean
∀ (p : ℕ) [Fact (Nat.Prime p)] (K : Type) [inst : CommRing K] [CharP K p] (α : K), α ^ p = α + 1 → ∀ (k : ℕ), α ^ p ^ k = α + ↑k
```
- 结论：证明
- 层级：agent
- 来源：decomposition（alg_artin_schreier_irreducible_zmod）
- 完成者：r4_prover_10
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.alg_artin_schreier_irreducible_zmod_s1h2`

alg_artin_schreier_irreducible_zmod 的证明骨架中第 2 个空洞

```lean
∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (g : Polynomial (ZMod p)), Irreducible g → AdjoinRoot.root g ^ p ^ g.natDegree = AdjoinRoot.root g
```
- 结论：证明
- 层级：agent
- 来源：decomposition（alg_artin_schreier_irreducible_zmod）
- 完成者：r4_prover_10
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.alg_artin_schreier_irreducible_zmod_s1h3`

alg_artin_schreier_irreducible_zmod 的证明骨架中第 3 个空洞

```lean
∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (g : Polynomial (ZMod p)), Irreducible g → CharP (AdjoinRoot g) p
```
- 结论：证明
- 层级：agent
- 来源：decomposition（alg_artin_schreier_irreducible_zmod）
- 完成者：r4_prover_10
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.alg_artin_schreier_irreducible_zmod_s1h4`

alg_artin_schreier_irreducible_zmod 的证明骨架中第 4 个空洞

```lean
∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (f : Polynomial (ZMod p)), f = Polynomial.X ^ p - Polynomial.X - 1 → f.natDegree = p
```
- 结论：证明
- 层级：agent
- 来源：decomposition（alg_artin_schreier_irreducible_zmod）
- 完成者：r4_prover_10
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.alg_card_range_sq_zmod_prime`

For an odd prime p there are exactly (p+1)/2 squares in ZMod p — the squaring map is 2-to-1 on nonzero elements (x² = y² iff x = ±y and x ≠ -x), plus 0.

```lean
∀ (p : ℕ) [inst : Fact (Nat.Prime p)], p ≠ 2 → Nat.card ↑(Set.range fun x => x ^ 2) = (p + 1) / 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_6
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.alg_isCyclic_of_card_eq_prime_mul_prime`

A group of order pq with primes p < q and p ∤ q - 1 is cyclic — by Sylow's theorems both the Sylow p- and Sylow q-subgroup are unique hence normal, so G is their internal direct product C_p × C_q, which is cyclic since p, q are coprime.

```lean
∀ (p q : ℕ), Nat.Prime p → Nat.Prime q → p < q → ¬p ∣ q - 1 → ∀ (G : Type u_1) [inst : Group G], Nat.card G = p * q → IsCyclic G
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_6
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.alg_perm_eq_mul_two_involutions_s1h1`

alg_perm_eq_mul_two_involutions 的证明骨架中第 1 个空洞

```lean
∀ (n : ℕ) (τ : Equiv.Perm (Fin n)), τ.IsCycle → ∃ a, a * a = 1 ∧ a * τ * a = τ⁻¹ ∧ ∀ (x : Fin n), τ x = x → a x = x
```
- 结论：证明
- 层级：agent
- 来源：decomposition（alg_perm_eq_mul_two_involutions）
- 完成者：r4_prover_10
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.alg_perm_eq_mul_two_involutions_s2h2`

alg_perm_eq_mul_two_involutions 的证明骨架中第 2 个空洞

```lean
∀ (n : ℕ) (τ ρ : Equiv.Perm (Fin n)), τ.Disjoint ρ → (∃ a, a * a = 1 ∧ a * τ * a = τ⁻¹ ∧ ∀ (x : Fin n), τ x = x → a x = x) → (∃ a, a * a = 1 ∧ a * ρ * a = ρ⁻¹ ∧ ∀ (x : Fin n), ρ x = x → a x = x) → ∃ a, a * a = 1 ∧ a * (τ * ρ) * a = (τ * ρ)⁻¹ ∧ ∀ (x : Fin n), τ (ρ x) = x → a x = x
```
- 结论：证明
- 层级：agent
- 来源：decomposition（alg_perm_eq_mul_two_involutions）
- 完成者：r4_prover_10
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.alg_x_pow_four_add_one_not_irreducible_zmod`

X^4 + 1 is reducible modulo every prime — for p = 2 it is (X+1)^4; for odd p one of -1, 2, -2 is a square mod p (Legendre symbol multiplicativity), giving (X²+a)(X²-a), (X²+bX+1)(X²-bX+1) or (X²+cX-1)(X²-cX-1).

```lean
∀ (p : ℕ) [inst : Fact (Nat.Prime p)], ¬Irreducible (Polynomial.X ^ 4 + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_6
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.an2_one_add_inv_pow_strict_mono`

The sequence (1 + 1/m)^m is strictly increasing for m ≥ 1.

```lean
∀ (n : ℕ), (1 + 1 / (↑n + 1)) ^ (n + 1) < (1 + 1 / (↑n + 2)) ^ (n + 2)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_b
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.an2_sum_inv_sqrt_bounds`

2(sqrt(n+1) - 1) ≤ sum_{k=1}^n 1/sqrt k ≤ 2 sqrt n.

```lean
∀ (n : ℕ), 2 * (√(↑n + 1) - 1) ≤ ∑ i ∈ Finset.range n, 1 / √(↑i + 1) ∧ ∑ i ∈ Finset.range n, 1 / √(↑i + 1) ≤ 2 * √↑n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_c
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.ana_convex_bddAbove_const`

A convex function on ℝ that is bounded above is constant — if f x < f y, write y as a convex combination of x and the far point z_t = x + t(y - x), t > 1: f y ≤ (1 - 1/t) f x + (1/t) f z_t gives f z_t ≥ f x + t (f y - f x) → ∞, contradicting the bound; symmetric for f y < f x.

```lean
∀ (f : ℝ → ℝ), ConvexOn ℝ Set.univ f → ∀ (M : ℝ), (∀ (x : ℝ), f x ≤ M) → ∀ (x y : ℝ), f x = f y
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_9
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.arith_centralBinom_dvd_lcm`

C(2n,n) divides lcm(1,…,2n) — for each prime p, v_p(C(2n,n)) ≤ log_p(2n) (Nat.factorization_choose_le_log) and p^⌊log_p 2n⌋ ≤ 2n lies in the range, so it divides the lcm; assemble via factorization.

```lean
∀ (n : ℕ), n.centralBinom ∣ (Finset.Icc 1 (2 * n)).lcm id
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ab
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.arith_even_perfect_last_digit`

Every even perfect number ends in 6 or 8 — by Euclid–Euler (Mathlib) n = 2^k(2^(k+1)-1) with 2^(k+1)-1 prime; k+1 = 2 or odd; reduce 2^k mod 10 by k mod 4.

```lean
∀ (n : ℕ), Even n → n.Perfect → n % 10 = 6 ∨ n % 10 = 8
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_aa
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.arith_odd_perfect_euler_form`

Euler's theorem on odd perfect numbers: n = p^a m² with p ≡ a ≡ 1 (mod 4), p ∤ m — σ(n) = 2n ≡ 2 (mod 4), so exactly one factor σ(q^e) is even and it is ≡ 2 mod 4; σ(q^e) for odd q is odd iff e even, and ≡ 2 mod 4 forces q ≡ e ≡ 1 mod 4.

```lean
∀ (n : ℕ), Odd n → n.Perfect → ∃ p a m, Nat.Prime p ∧ p % 4 = 1 ∧ a % 4 = 1 ∧ ¬p ∣ m ∧ n = p ^ a * m ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_aa
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`arith_card_divisors_odd_iff_isSquare`、`arith_card_divisors_odd_iff_isSquare_aux1`、`arith_perfect_not_isSquare`、`arith_sigma_odd_iff_aux1`、`arith_sigma_odd_iff_aux2`

## `Mathlib2.arith_perfect_not_isSquare`

No perfect number is a square — σ(m²) is odd (each σ(p^(2a)) is a sum of an odd number of odd terms, or p = 2) but σ(n) = 2n is even.

```lean
∀ (n : ℕ), n.Perfect → ¬IsSquare n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_aa
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`arith_sigma_odd_iff`

## `Mathlib2.arith_sigma_mul_totient_lt_sq`

σ(n)φ(n) < n² for n ≥ 2 — both sides multiplicative; on a prime power σ(p^a)φ(p^a) = p^(a-1)(p^(a+1)-1) < p^(2a); multiply over the factorization (strong induction splitting off ordCompl).

```lean
∀ (n : ℕ), 2 ≤ n → (ArithmeticFunction.sigma 1) n * n.totient < n ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ab
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.bld2_card_conjClasses_of_card_prime_cube`

Uses Mathlib2.bld_center_card_of_card_prime_cube: |Z(G)| = p gives p singleton classes; a non-central x has centralizer containing Z(G) and x, proper in G, hence of order p^2, so its class has p elements; the p^3 - p non-central elements form p^2 - 1 classes (class equation).

```lean
∀ (p : ℕ), Nat.Prime p → ∀ (G : Type u_1) [inst : Group G], Nat.card G = p ^ 3 → (∃ a b, a * b ≠ b * a) → Nat.card (ConjClasses G) = p ^ 2 + p - 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_center_card_of_card_prime_cube）
- 完成者：r7_prover_4
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`bld_center_card_of_card_prime_cube`

## `Mathlib2.bld2_commuting_idempotents_rank_join`

Uses Mathlib2.bld_idempotent_sum_rank twice: A and B - A*B are idempotents with idempotent sum A + B - A*B, so rank (A + B - A*B) = rank A + rank (B - A*B); A*B and B - A*B are idempotents with sum B, so rank B = rank (A*B) + rank (B - A*B).

```lean
∀ (K : Type u_1) [inst : Field K] [CharZero K] (ι : Type u_2) [inst_2 : Fintype ι] [DecidableEq ι] (A B : Matrix ι ι K), A * A = A → B * B = B → A * B = B * A → (A + B - A * B).rank + (A * B).rank = A.rank + B.rank
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_idempotent_sum_rank）
- 完成者：r7_prover_1
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`bld_idempotent_sum_rank`

## `Mathlib2.bld2_expanding_compact_isometryEquiv`

Uses Mathlib2.top_expanding_compact_isometry and Mathlib2.top_isometry_compact_surjective: an expanding self-map of a compact metric space is an isometry, hence surjective; with injectivity of isometries this gives a bijective isometry, packaged as an IsometryEquiv.

```lean
∀ {X : Type u_1} [inst : MetricSpace X] [CompactSpace X] (f : X → X), (∀ (x y : X), dist x y ≤ dist (f x) (f y)) → ∃ e, ∀ (x : X), e x = f x
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.top_expanding_compact_isometry, Mathlib2.top_isometry_compact_surjective）
- 完成者：r7_prover_1
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`top_expanding_compact_isometry`、`top_isometry_compact_surjective`

## `Mathlib2.bld2_sqrt_two_rec_defect_asymptotic`

Uses Mathlib2.ana_sqrt_two_rec_closed_form (sharpening Mathlib2.bld_sqrt_two_rec_rate): 2 - a n = 2 - 2 cos (π/2^(n+1)) = 4 sin^2 (π/2^(n+2)), so 4^n * (2 - a n) = (2^(n+1) * sin (π/2^(n+2)))^2, which tends to (π/2)^2 since sin x / x → 1.

```lean
∀ (a : ℕ → ℝ), a 0 = 0 → (∀ (n : ℕ), a (n + 1) = √(2 + a n)) → Filter.Tendsto (fun n => 4 ^ n * (2 - a n)) Filter.atTop (nhds (Real.pi ^ 2 / 4))
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.ana_sqrt_two_rec_closed_form, Mathlib2.bld_sqrt_two_rec_rate）
- 完成者：r7_prover_3
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`ana_sqrt_two_rec_closed_form`、`bld_sqrt_two_rec_viete_prod`、`bld_sqrt_two_rec_viete_tendsto`

## `Mathlib2.bld2_tripotent_rank_split`

Uses Mathlib2.bld_idempotent_sum_rank: P = (1/2)(A*A + A) and Q = (1/2)(A*A - A) are idempotents whose sum A*A is idempotent, so rank (A*A) = rank P + rank Q; scalars 1/2 do not change rank and rank (A*A) = rank A since A = A*(A*A).

```lean
∀ (K : Type u_1) [inst : Field K] [CharZero K] (ι : Type u_2) [inst_2 : Fintype ι] [DecidableEq ι] (A : Matrix ι ι K), A * A * A = A → A.rank = (A * A + A).rank + (A * A - A).rank
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_idempotent_sum_rank）
- 完成者：r7_prover_3
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`bld_idempotent_sum_rank`

## `Mathlib2.bld3_card_conjClasses_of_card_prime_mul_prime`

Uses Mathlib2.bld_center_eq_bot_of_card_prime_mul_prime and Mathlib2.alg_isCyclic_of_card_eq_prime_mul_prime: the centre is trivial, so every non-identity class has size p or q; the normal Sylow q-subgroup contributes (q-1)/p classes of size p (centralizer of order q), the remaining q(p-1) elements of order p have centralizer of order p and form p - 1 classes of size q; total 1 + (q-1)/p + (p-1).

```lean
∀ (p q : ℕ), Nat.Prime p → Nat.Prime q → p < q → ∀ (G : Type u_1) [inst : Group G], Nat.card G = p * q → (∃ a b, a * b ≠ b * a) → Nat.card (ConjClasses G) = p + (q - 1) / p
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_center_eq_bot_of_card_prime_mul_prime, Mathlib2.alg_isCyclic_of_card_eq_prime_mul_prime）
- 完成者：r8_prover_4
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`alg_isCyclic_of_card_eq_prime_mul_prime`、`alg_isCyclic_of_card_eq_prime_mul_prime_aux1`、`bld_center_eq_bot_of_card_prime_mul_prime`

## `Mathlib2.bld3_commuting_idempotents_rank_sub`

Uses Mathlib2.bld_idempotent_sum_rank and Mathlib2.bld2_commuting_idempotents_rank_join: P = A - AB and Q = B - AB are orthogonal idempotents with A = AB + P, B = AB + Q, so rank P = rank A - rank AB and rank Q = rank B - rank AB; (P - Q)^2 = P + Q is idempotent of rank rank P + rank Q, which squeezes rank (A - B) = rank (P - Q) between rank (P + Q) and rank P + rank Q.

```lean
∀ (K : Type u_1) [inst : Field K] [CharZero K] (ι : Type u_2) [inst_2 : Fintype ι] [DecidableEq ι] (A B : Matrix ι ι K), A * A = A → B * B = B → A * B = B * A → (A - B).rank + 2 * (A * B).rank = A.rank + B.rank
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_idempotent_sum_rank, Mathlib2.bld2_commuting_idempotents_rank_join）
- 完成者：r8_prover_1
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`bld_idempotent_sum_rank`

## `Mathlib2.bld3_compact_mutual_expanding_isometry`

Uses Mathlib2.bld2_expanding_compact_isometryEquiv and Mathlib2.top_expanding_compact_isometry: g ∘ f is expanding on compact X hence an isometry, which squeezes dist x x' ≤ dist (f x) (f x') ≤ dist (g (f x)) (g (f x')) = dist x x'; f ∘ g is expanding on Y hence a bijective isometry, so f is surjective (Cantor–Bernstein for compact metric spaces).

```lean
∀ {X : Type u_1} [inst : MetricSpace X] [CompactSpace X] {Y : Type u_2} [inst_2 : MetricSpace Y] [CompactSpace Y] (f : X → Y) (g : Y → X), (∀ (x x' : X), dist x x' ≤ dist (f x) (f x')) → (∀ (y y' : Y), dist y y' ≤ dist (g y) (g y')) → Isometry f ∧ Function.Surjective f
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_expanding_compact_isometryEquiv, Mathlib2.top_expanding_compact_isometry）
- 完成者：r8_prover_1
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`bld2_expanding_compact_isometryEquiv`、`top_expanding_compact_isometry`

## `Mathlib2.bld3_nilpotent_rank_pow_le`

Uses Mathlib2.bld2_rank_pow_convex and Mathlib2.bld_nilpotent_rank_bound: by convexity the drops d_k are non-increasing, so once d_k = 0 the rank is constant forever; nilpotency forces that constant to be 0, hence the rank drops by at least 1 at each step until it reaches 0, giving rank A^k ≤ n - k (truncated subtraction).

```lean
∀ (K : Type u_1) [inst : Field K] (ι : Type u_2) [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (A : Matrix ι ι K), IsNilpotent A → ∀ (k : ℕ), (A ^ k).rank ≤ Fintype.card ι - k
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_rank_pow_convex, Mathlib2.bld_nilpotent_rank_bound）
- 完成者：r8_prover_1
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`bld2_rank_pow_convex`、`bld3_rank_pow_card_stabilizes_aux1`、`bld3_rank_pow_card_stabilizes_aux2`

## `Mathlib2.bld3_pell_five_one_solutions`

Uses Mathlib2.bld2_pell_five_solutions_lucas: (2x)^2 = 5 (2y)^2 + 4, so 2y = fib (2m) and 2x = p3_lucas (2m); fib (2m) is even iff 3 ∣ 2m iff 3 ∣ m (fib mod 2 has period 3), so 2m = 6n.

```lean
∀ (x y : ℕ), x ^ 2 = 5 * y ^ 2 + 1 → ∃ n, 2 * y = Nat.fib (6 * n) ∧ 2 * x = Mathlib2.p3_lucas (6 * n)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_pell_five_solutions_lucas）
- 完成者：r8_prover_2
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`bld2_pell_five_solutions_lucas`、`p3_lucas`

## `Mathlib2.bld3_pow_prime_mem_center_of_card_prime_cube`

Uses Mathlib2.bld_center_card_of_card_prime_cube and Mathlib2.bld2_commutator_eq_center_of_card_prime_cube: the centre has order p so G/Z has order p^2 and is not cyclic (else G abelian), hence every element of G/Z has order dividing p, i.e. g^p ∈ Z.

```lean
∀ (p : ℕ), Nat.Prime p → ∀ (G : Type u_1) [inst : Group G], Nat.card G = p ^ 3 → (∃ a b, a * b ≠ b * a) → ∀ (g : G), g ^ p ∈ Subgroup.center G
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_center_card_of_card_prime_cube, Mathlib2.bld2_commutator_eq_center_of_card_prime_cube）
- 完成者：r8_prover_3
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`bld_center_card_of_card_prime_cube`

## `Mathlib2.bld3_rank_tripotent_defect`

Uses Mathlib2.bld_frobenius_rank_inequality and Mathlib2.bld2_tripotent_rank_split: generalises the tripotent rank split (the case A^3 = A); ≤ is Frobenius for the triple (A + 1, A, A - 1); ≥ by block elimination on diag(A^2 + A, A^2 - A) using 2A = (A^2 + A) - (A^2 - A) and invertibility of 2.

```lean
∀ (K : Type u_1) [inst : Field K] [CharZero K] (ι : Type u_2) [inst_2 : Fintype ι] [DecidableEq ι] (A : Matrix ι ι K), (A * A + A).rank + (A * A - A).rank = A.rank + (A * A * A - A).rank
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_frobenius_rank_inequality, Mathlib2.bld2_tripotent_rank_split）
- 完成者：r8_prover_1
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`bld_frobenius_rank_inequality`

## `Mathlib2.bld4_card_orderOf_eq_prime_of_card_prime_mul_prime`

Uses Mathlib2.bld3_card_sylow_of_card_prime_mul_prime: there are exactly q Sylow p-subgroups, each of order p; two distinct ones meet trivially, and every element of order p generates one. So the elements of order p are the disjoint union over the q Sylow p-subgroups of their p − 1 non-identity elements.

```lean
∀ (p q : ℕ) [Fact (Nat.Prime p)], Nat.Prime q → p < q → ∀ (G : Type u_1) [inst : Group G], Nat.card G = p * q → (∃ a b, a * b ≠ b * a) → Nat.card { g // orderOf g = p } = q * (p - 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld3_card_sylow_of_card_prime_mul_prime）
- 完成者：r9_prover_1
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`bld3_card_sylow_of_card_prime_mul_prime`、`bld3_card_sylow_of_card_prime_mul_prime_aux1`

## `Mathlib2.bld4_carleman_finite_three`

Uses Mathlib2.an2_amgm_range_pow and Mathlib2.an2_succ_pow_lt_three_mul_pow (Carleman's inequality with constant 3 > e): with weights c_i = (i+2)^(i+1)/(i+1)^i (0-indexed) one has ∏_{i≤k} c_i = (k+2)^(k+1), so by an2_amgm_range_pow applied to a_i c_i, (∏_{i≤k} a_i)^(1/(k+1)) ≤ (∑_{i≤k} a_i c_i)/((k+1)(k+2)). Summing over k < n, swapping sums and telescoping ∑_{k≥i} 1/((k+1)(k+2)) ≤ 1/(i+1) gives ≤ ∑ a_i c_i/(i+1) = ∑ a_i ((i+2)/(i+1))^(i+1) ≤ 3 ∑ a_i by an2_succ_pow_lt_three_mul_pow.

```lean
∀ (a : ℕ → ℝ), (∀ (i : ℕ), 0 ≤ a i) → ∀ (n : ℕ), ∑ k ∈ Finset.range n, (∏ i ∈ Finset.range (k + 1), a i) ^ (1 / (↑k + 1)) ≤ 3 * ∑ k ∈ Finset.range n, a k
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.an2_amgm_range_pow, Mathlib2.an2_succ_pow_lt_three_mul_pow）
- 完成者：r9_prover_2
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`an2_amgm_range_pow`、`an2_succ_pow_lt_three_mul_pow`

## `Mathlib2.bld4_mantel_equality_complete_bipartite`

Uses Mathlib2.bld2_mantel_equality_regular and Mathlib2.bld3_mantel_equality_same_neighbors: if V is empty take s = ∅; otherwise fix v and let s = G.neighborFinset v, of size n/2 by bld2_mantel_equality_regular. Two vertices of s are non-adjacent (triangle-free); a vertex y ∉ s is non-adjacent to v so by bld3_mantel_equality_same_neighbors it has the same neighbours as v, i.e. it is adjacent exactly to the vertices of s; this gives Adj x y ↔ (x ∈ s ↔ y ∉ s) in all four cases.

```lean
∀ (V : Type) [inst : Fintype V] [DecidableEq V] (G : SimpleGraph V) [inst_2 : DecidableRel G.Adj], G.CliqueFree 3 → 4 * G.edgeFinset.card = Fintype.card V ^ 2 → ∃ s, 2 * s.card = Fintype.card V ∧ ∀ (x y : V), G.Adj x y ↔ (x ∈ s ↔ y ∉ s)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_mantel_equality_regular, Mathlib2.bld3_mantel_equality_same_neighbors）
- 完成者：r9_prover_3
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`bld2_mantel_equality_regular`、`bld3_mantel_equality_same_neighbors`

## `Mathlib2.bld4_nilpotent_corank_one_rank_pow`

Uses Mathlib2.bld3_nilpotent_rank_pow_le and Mathlib2.lib_matrix_mul_rank_le_add_rank_pow: the upper bound rank A^k ≤ n − k is bld3_nilpotent_rank_pow_le. For the lower bound, lib_matrix_mul_rank_le_add_rank_pow gives k(n − 1) ≤ (k − 1)n + rank A^k, i.e. rank A^k ≥ n − k (k = 0 separately: rank 1 = n). This is the single-Jordan-block case.

```lean
∀ (K : Type u_1) [inst : Field K] (ι : Type u_2) [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (A : Matrix ι ι K), IsNilpotent A → A.rank + 1 = Fintype.card ι → ∀ k ≤ Fintype.card ι, (A ^ k).rank = Fintype.card ι - k
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld3_nilpotent_rank_pow_le, Mathlib2.lib_matrix_mul_rank_le_add_rank_pow）
- 完成者：r9_prover_2
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`bld3_nilpotent_rank_pow_le`、`lib_matrix_mul_rank_le_add_rank_pow`

## `Mathlib2.bld4_permMatrix_involution_rank_fixed_points`

Uses Mathlib2.bld_involution_trace_rank: the permutation matrix P of an involution satisfies P * P = 1 (Matrix.permMatrix_mul), so bld_involution_trace_rank gives tr P + n = 2 rank(1 + P) in K; tr P is the number of fixed points of σ (diagonal entries are 1 or 0), and Nat.cast injectivity in characteristic 0 gives the identity in ℕ.

```lean
∀ (K : Type u_1) [inst : Field K] [CharZero K] (ι : Type u_2) [inst_2 : Fintype ι] [inst_3 : DecidableEq ι] (σ : Equiv.Perm ι), σ * σ = 1 → 2 * (1 + Equiv.Perm.permMatrix K σ).rank = Fintype.card ι + {i | σ i = i}.card
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_involution_trace_rank）
- 完成者：r9_prover_2
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`bld_involution_trace_rank`

## `Mathlib2.bld4_pisano_prime_dvd_pred_of_isSquare_five`

Uses Mathlib2.p3_aux_fib_prime, Mathlib2.lib_fib_period_iff and Mathlib2.bld3_pisano_dvd_of_period: by Euler's criterion (ZMod.euler_criterion) 5^(p/2) = 1 in ZMod p, so p3_aux_fib_prime gives F_p ≡ 1 and 2F_{p+1} − F_p ≡ 1, hence F_{p+1} ≡ 1 and F_{p−1} = F_{p+1} − F_p ≡ 0 mod p. lib_fib_period_iff (with m = p − 1) turns this into p − 1 being a period, and bld3_pisano_dvd_of_period concludes.

```lean
∀ (p : ℕ) [inst : Fact (Nat.Prime p)], p ≠ 2 → p ≠ 5 → IsSquare 5 → Mathlib2.p3_pisano p ∣ p - 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.p3_aux_fib_prime, Mathlib2.lib_fib_period_iff, Mathlib2.bld3_pisano_dvd_of_period）
- 完成者：r9_prover_1
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`bld3_pisano_dvd_of_period`、`lib_fib_period_iff`、`p3_aux_fib_prime`、`p3_pisano`

## `Mathlib2.bld4_prime_dvd_fib_pred_mul_fib_mul_fib_succ`

Uses Mathlib2.p3_aux_fib_prime and Mathlib2.an_cassini_int: p = 2 and p = 5 by computation (F_3 = 2, F_5 = 5). Otherwise p3_aux_fib_prime gives F_p ≡ 5^(p/2), so F_p^2 ≡ 5^(p−1) ≡ 1 mod p by Fermat; an_cassini_int at n = p − 1 gives F_{p+1} F_{p−1} = F_p^2 + (−1)^p = F_p^2 − 1 ≡ 0 mod p.

```lean
∀ (p : ℕ), Nat.Prime p → p ∣ Nat.fib (p - 1) * Nat.fib p * Nat.fib (p + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.p3_aux_fib_prime, Mathlib2.an_cassini_int）
- 完成者：r9_prover_1
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`an_cassini_int`、`p3_aux_fib_prime`

## `Mathlib2.bld4_sqrt_two_rec_defect_tsum_lower`

Uses Mathlib2.bld2_sqrt_two_rec_defect_summable, Mathlib2.ana_sqrt_two_rec_closed_form and Mathlib2.ana_sin_ge_cubic_of_nonneg: termwise 2 − a_n ≥ π^2/4^(n+1) − π^4/(192·16^n) (closed form + cubic sine bound, as in the pointwise estimate). The right side is a difference of geometric series with sum π^2/3 − π^4/180; bld2_sqrt_two_rec_defect_summable supplies summability of the left side so tsum comparison (hasSum_le / tsum_le_tsum) applies. Improves the bound 8/3 of bld3_sqrt_two_rec_defect_tsum_bounds.

```lean
∀ (a : ℕ → ℝ), a 0 = 0 → (∀ (n : ℕ), a (n + 1) = √(2 + a n)) → Real.pi ^ 2 / 3 - Real.pi ^ 4 / 180 ≤ ∑' (n : ℕ), (2 - a n)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_sqrt_two_rec_defect_summable, Mathlib2.ana_sqrt_two_rec_closed_form, Mathlib2.ana_sin_ge_cubic_of_nonneg）
- 完成者：r9_prover_3
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`ana_sin_ge_cubic_of_nonneg`、`ana_sqrt_two_rec_closed_form`、`bld2_sqrt_two_rec_defect_summable`

## `Mathlib2.bld4_tripotent_trace_eq_rank_sub_rank`

Uses Mathlib2.gen_lin_idempotent_trace_eq_rank_field and Mathlib2.lib_matrix_rank_smul: P = (1/2)(A^2 + A) and Q = (1/2)(A^2 − A) are idempotent when A^3 = A, and A = P − Q. So tr A = tr P − tr Q = rank P − rank Q by gen_lin_idempotent_trace_eq_rank_field, and lib_matrix_rank_smul removes the scalar 1/2 from the ranks.

```lean
∀ (K : Type u_1) [inst : Field K] [CharZero K] (ι : Type u_2) [inst_2 : Fintype ι] [DecidableEq ι] (A : Matrix ι ι K), A * A * A = A → A.trace = ↑(A * A + A).rank - ↑(A * A - A).rank
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.gen_lin_idempotent_trace_eq_rank_field, Mathlib2.lib_matrix_rank_smul）
- 完成者：r9_prover_3
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`gen_lin_idempotent_trace_eq_rank_field`、`lib_matrix_rank_smul`

## `Mathlib2.bld5_nilpotent_max_index_rank`

Uses Mathlib2.bld2_rank_pow_convex, Mathlib2.gen_lin_nilpotent_pow_card_reduced and Mathlib2.lib_matrix_rank_eq_zero_iff (converse of bld4_nilpotent_corank_one_rank_pow): let r_k = rank(A^k), n = card ι, d_k = r_k − r_{k+1} ≥ 0 (Matrix.rank_mul_le_left). gen_lin_nilpotent_pow_card_reduced gives r_n = 0, and lib_matrix_rank_eq_zero_iff with the hypothesis gives r_{n−1} ≥ 1, so d_{n−1} ≥ 1. bld2_rank_pow_convex says d_k is non-increasing, so d_k ≥ 1 for all k ≤ n−1. Since d_0 + … + d_{n−1} = r_0 − r_n = n, every d_k = 1; in particular rank A = r_1 = n − 1.

```lean
∀ (K : Type u_1) [inst : Field K] (ι : Type u_2) [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (A : Matrix ι ι K), IsNilpotent A → A ^ (Fintype.card ι - 1) ≠ 0 → A.rank + 1 = Fintype.card ι
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_rank_pow_convex, Mathlib2.gen_lin_nilpotent_pow_card_reduced, Mathlib2.lib_matrix_rank_eq_zero_iff）
- 完成者：prover_bb
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`bld5_nilpotent_pow_rank_succ_eq_zero_aux2`、`gen_lin_nilpotent_pow_card_reduced`、`lib_matrix_rank_eq_zero_iff`

## `Mathlib2.bld5_prime_dvd_fib_succ_of_not_isSquare_five`

Uses Mathlib2.bld4_prime_dvd_fib_pred_mul_fib_mul_fib_succ, Mathlib2.bld4_pisano_prime_dvd_two_mul_succ_of_not_isSquare_five and Mathlib2.lib_pisano_dvd_iff_period: p is odd (5 = 1 is a square in ZMod 2). The second bld4 theorem with lib_pisano_dvd_iff_period (i = 0) gives p ∣ F_{2(p+1)}. By the first, p divides F_{p-1}, F_p or F_{p+1}. If p ∣ F_p then Nat.fib_gcd gives p ∣ F_{gcd(p, 2p+2)} = F_1 = 1; if p ∣ F_{p-1} then p ∣ F_{gcd(p-1, 2p+2)} with gcd(p-1, 2p+2) ∣ 4, so p ∣ F_4 = 3, p = 3, but then F_{p-1} = F_2 = 1. Both impossible, so p ∣ F_{p+1}.

```lean
∀ (p : ℕ) [inst : Fact (Nat.Prime p)], ¬IsSquare 5 → p ∣ Nat.fib (p + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld4_prime_dvd_fib_pred_mul_fib_mul_fib_succ, Mathlib2.bld4_pisano_prime_dvd_two_mul_succ_of_not_isSquare_five, Mathlib2.lib_pisano_dvd_iff_period）
- 完成者：prover_ba
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`bld4_pisano_prime_dvd_two_mul_succ_of_not_isSquare_five`、`bld4_prime_dvd_fib_pred_mul_fib_mul_fib_succ`、`lib_pisano_dvd_iff_period`、`p3_pisano`

## `Mathlib2.bld5_prime_dvd_lucas_four_mul_mod_eight`

Uses Mathlib2.bld2_lucas_sq_sub_five_fib_sq and Mathlib2.lib_p3_lucas_cast: first the duplication formula L_{2m} = L_m² − 2(−1)^m in ℤ (from lib_p3_lucas_cast, Nat.fib_two_mul, Nat.fib_two_mul_add_one, giving 2L_{2m} = L_m² + 5F_m², then the bld2 identity L_m² − 5F_m² = 4(−1)^m). With m = 2n: L_{4n} = L_{2n}² − 2, so p ∣ L_{4n} makes 2 a square in ZMod p, and ZMod.exists_sq_eq_two_iff (p ≠ 2) gives p ≡ ±1 mod 8.

```lean
∀ (p n : ℕ), Nat.Prime p → p ≠ 2 → p ∣ Mathlib2.p3_lucas (4 * n) → p % 8 = 1 ∨ p % 8 = 7
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_lucas_sq_sub_five_fib_sq, Mathlib2.lib_p3_lucas_cast）
- 完成者：prover_ba
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`lib_fib_cassini_cast`、`lib_p3_lucas_cast`、`p3_lucas`

## `Mathlib2.bld_nilpotent_rank_bound`

Uses Mathlib2.gen_lin_sylvester_rank_rect: by induction on j, j * rank A ≤ (j-1) * n + rank (A^j) (Sylvester applied to A^j and A); at j = k the last term vanishes. Special case k = 2: A^2 = 0 implies 2 rank A ≤ n.

```lean
∀ (K : Type u_1) [inst : Field K] (ι : Type u_2) [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (A : Matrix ι ι K) (k : ℕ), A ^ k = 0 → k * A.rank ≤ (k - 1) * Fintype.card ι
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.gen_lin_sylvester_rank_rect）
- 完成者：r6_prover_2
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`gen_lin_sylvester_rank_rect`

## `Mathlib2.bld_sqrt_two_rec_viete_tendsto`

Uses Mathlib2.ana_sqrt_two_rec_closed_form (and the finite product identity derived from it): the partial products equal 1/(2^n sin(π/2^(n+1))), and 2^n sin(π/2^(n+1)) → π/2 since sin t / t → 1. This is Viète's formula 2/π = (√2/2)(√(2+√2)/2)⋯.

```lean
∀ (a : ℕ → ℝ), a 0 = 0 → (∀ (n : ℕ), a (n + 1) = √(2 + a n)) → Filter.Tendsto (fun n => ∏ i ∈ Finset.range n, a (i + 1) / 2) Filter.atTop (nhds (2 / Real.pi))
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.ana_sqrt_two_rec_closed_form）
- 完成者：r6_prover_1
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`bld_sqrt_two_rec_viete_prod`

## `Mathlib2.calc_card_involutions_rec`

Involution numbers satisfy I(n+2) = I(n+1) + (n+1)·I(n) — split involutions of Fin (n+2) by whether the last point is fixed (I(n+1)) or swapped with one of n+1 others (remaining n points carry an involution).

```lean
∀ (n : ℕ), {σ | σ * σ = 1}.card = {σ | σ * σ = 1}.card + (n + 1) * {σ | σ * σ = 1}.card
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_cb
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`comb_card_involutions_rec`

## `Mathlib2.calc_card_no_adjacent_subsets`

Subsets of {0,…,n−1} with no two consecutive elements number F_{n+2} — two-step induction: split by whether the last element is in the set, giving a(n+2) = a(n+1) + a(n); bijections via Fin.castSucc / Finset.map.

```lean
∀ (n : ℕ), {s | ∀ (i j : Fin n), i ∈ s → j ∈ s → ↑i + 1 ≠ ↑j}.card = Nat.fib (n + 2)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_cb
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.calc_card_surjective_fin_three`

Number of surjections from an n-set (n ≥ 1) onto a 3-set is 3ⁿ − 3·2ⁿ + 3 — inclusion–exclusion over the missed values; count functions avoiding a given value (2ⁿ) and avoiding two values (1).

```lean
∀ (n : ℕ), 0 < n → ↑{f | Function.Surjective f}.card = 3 ^ n - 3 * 2 ^ n + 3
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_cb
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.calc_exp_lt_one_add_inv_pow_succ`

e < (1+1/n)^(n+1) — equivalent to 1/(n+1) < log(1+1/n), i.e. exp(−1/(n+1)) > 1 − 1/(n+1) = n/(n+1) (Real.add_one_lt_exp at t = −1/(n+1)); invert and raise to power n+1.

```lean
∀ (n : ℕ), 0 < n → Real.exp 1 < (1 + 1 / ↑n) ^ (n + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.calc_rpow_lt_rpow_swap_of_exp_le`

For e ≤ x < y, yˣ < xʸ — log t / t is strictly decreasing on [e, ∞) (derivative (1 − log t)/t² < 0 for t > e), so log y / y < log x / x; exponentiate.

```lean
∀ (x y : ℝ), Real.exp 1 ≤ x → x < y → y ^ x < x ^ y
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.calc_sum_sq_card_fixed_points_perm`

Second moment of fixed-point count: ∑_σ fix(σ)² = 2·n! for n ≥ 2 (variance 1) — count triples (σ,i,j) with both fixed: n·(n−1)! diagonal plus n(n−1)·(n−2)! off-diagonal; equivalently Burnside for the action on ordered pairs (2 orbits).

```lean
∀ (n : ℕ), 2 ≤ n → ∑ σ, {i | σ i = i}.card ^ 2 = 2 * n.factorial
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_cb
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`calc_sum_card_fixed_points_perm_aux1`

## `Mathlib2.calc_tsum_fib_div_two_pow`

∑ Fₙ/2ⁿ = 2 — summability by Fₙ ≤ φⁿ-type bound (fib n ≤ (7/4)^n or 2^n·(geometric)), then S = 1/2 + S/2 + S/4 from the recurrence; or closed partial sums 2 − F_{N+3}/2^N… 

```lean
∑' (n : ℕ), ↑(Nat.fib n) / 2 ^ n = 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`calc_tsum_inv_three_consecutive_aux1`

## `Mathlib2.calc_tsum_inv_odd_consecutive`

∑ 1/((2n+1)(2n+3)) = 1/2 — telescoping, partial sums (1/2)(1 − 1/(2N+1)).

```lean
∑' (n : ℕ), 1 / ((2 * ↑n + 1) * (2 * ↑n + 3)) = 1 / 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`calc_tsum_inv_three_consecutive_aux1`

## `Mathlib2.comb_card_involutions_rec`

The number a(n) of involutions (σ² = 1) in S_n satisfies a(n+2) = a(n+1) + (n+1)·a(n) — split on whether σ fixes the last point (restrict to Fin (n+1)) or swaps it with one of the n+1 others (remove both points, leaving an involution of an n-set).

```lean
∀ (n : ℕ), Fintype.card { σ // σ * σ = 1 } = Fintype.card { σ // σ * σ = 1 } + (n + 1) * Fintype.card { σ // σ * σ = 1 }
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_4
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.comb_exists_cut_half_edges`

Every finite graph has a cut containing at least half of its edges — take s maximising the cut size: every vertex then has at least half of its neighbours on the other side (else moving it increases the cut); sum over vertices. Or average over all 2^n subsets.

```lean
∀ (V : Type) [inst : Fintype V] [inst_1 : DecidableEq V] (G : SimpleGraph V) [inst_2 : DecidableRel G.Adj], ∃ s, G.edgeFinset.card ≤ 2 * {p ∈ s ×ˢ sᶜ | G.Adj p.1 p.2}.card
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_9
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.fld_card_hyperbola_zmod`

For odd p and a ≠ 0 the equation x^2 - y^2 = a has exactly p-1 solutions in F_p — the change of variables u = x+y, v = x-y is a bijection of F_p^2 (2 invertible) turning it into uv = a, whose solutions are (u, a/u) for the p-1 units u.

```lean
∀ (p : ℕ) [inst : Fact (Nat.Prime p)], p ≠ 2 → ∀ (a : ZMod p), a ≠ 0 → {v | v.1 ^ 2 - v.2 ^ 2 = a}.card = p - 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_6x
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.fld_card_image_sq_finite_field`

A finite field of odd characteristic with q elements has exactly (q+1)/2 squares. Generalizes Mathlib2.alg_card_range_sq_zmod_prime from ZMod p to all finite fields — squaring is 2-to-1 on nonzero elements (x^2 = y^2 iff x = ±y, and x ≠ -x as char ≠ 2), plus 0; q is odd.

```lean
∀ (K : Type) [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K], ringChar K ≠ 2 → (Finset.image (fun x => x ^ 2) Finset.univ).card = (Fintype.card K + 1) / 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_fa
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.fld_gaussianInt_prime_of_norm_prime`

A Gaussian integer whose norm is a rational prime is a Gaussian prime — if z = xy then N(x)N(y) = p so one of x, y has norm 1 and is a unit (Zsqrtd.norm_eq_one_iff), so z is irreducible; ℤ[i] is a PID so irreducible elements are prime.

```lean
∀ (z : GaussianInt), Nat.Prime (Zsqrtd.norm z).natAbs → Prime z
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_fa
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.fld_isSquare_neg_three_zmod_iff`

-3 is a quadratic residue mod a prime p > 3 iff p ≡ 1 (mod 3) — either via legendreSym multiplicativity, (-1/p) and quadratic reciprocity for 3, or directly: -3 = (2ω+1)^2 where ω is a primitive cube root of unity, which exists in F_p iff 3 | p-1.

```lean
∀ (p : ℕ) [inst : Fact (Nat.Prime p)], 3 < p → (IsSquare (-3) ↔ p % 3 = 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_6x
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`fld_prime_one_mod_three_eq_sq_add_three_sq_aux3`

## `Mathlib2.fld_minpoly_sqrt_two_add_sqrt_three`

The minimal polynomial of √2 + √3 over ℚ is X^4 - 10X^2 + 1 — the polynomial is monic and vanishes at √2+√3 ((√2+√3)^2 = 5 + 2√6); Uses Mathlib2.poly_x4_sub_10x2_add_1_irreducible_int for irreducibility over ℤ, transferred to ℚ by Gauss's lemma (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map), then minpoly.eq_of_irreducible_of_monic.

```lean
minpoly ℚ (√2 + √3) = Polynomial.X ^ 4 - 10 * Polynomial.X ^ 2 + 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_fa
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`poly_x4_sub_10x2_add_1_irreducible_int`

## `Mathlib2.fld_sum_quadraticChar_sq_add`

Quadratic character sum Σ_x χ(x^2 + a) = -1 for a ≠ 0 in F_p, p odd — count solutions of y^2 = x^2 + a two ways: it equals Σ_x (1 + χ(x^2 + a)) by quadraticChar_card_sqrts and equals p - 1 by the hyperbola count (y-x)(y+x) = a.

```lean
∀ (p : ℕ) [inst : Fact (Nat.Prime p)], p ≠ 2 → ∀ (a : ZMod p), a ≠ 0 → ∑ x, (quadraticChar (ZMod p)) (x ^ 2 + a) = -1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_6x
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`fld_card_hyperbola_zmod`

## `Mathlib2.gen_nt_sq_add_sq_eq_prime_mul_sq`

Generalizes Mathlib2.nt2_sq_add_sq_eq_seven_mul_sq: 7 → every prime p ≡ 3 (mod 4). Proof idea: infinite descent on |z| (or on x²+y²) using Mathlib2.nt2_prime_three_mod_four_dvd_sq_add_sq: p ∣ x, p ∣ y, hence p ∣ z², p ∣ z, and (x/p, y/p, z/p) is a smaller solution.

```lean
∀ (p : ℕ), Nat.Prime p → p % 4 = 3 → ∀ (x y z : ℤ), x ^ 2 + y ^ 2 = ↑p * z ^ 2 → x = 0 ∧ y = 0 ∧ z = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture（generalization of Mathlib2.nt2_sq_add_sq_eq_seven_mul_sq）
- 完成者：gen_prover_2
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`nt2_prime_three_mod_four_dvd_sq_add_sq`

## `Mathlib2.geo_prod_sin_pi_mul_div`

∏_{k=1}^{m−1} sin(kπ/m) = m / 2^{m−1} (with m = n+1) — from ∏_{k=1}^{m−1}(1 − ζ^k) = m for ζ = exp(2πi/m) (IsPrimitiveRoot.prod_one_sub_pow_eq_order), take norms and use |1 − e^{2iθ}| = 2 sin θ for θ ∈ [0, π].

```lean
∀ (n : ℕ), ∏ k ∈ Finset.range n, Real.sin ((↑k + 1) * Real.pi / (↑n + 1)) = (↑n + 1) / 2 ^ n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_2
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.lib_compactSpace_exists_lt_and_dist_lt`

Pigeonhole principle in a compact pseudometric space: every sequence has two terms u m, u n with m < n at distance < ε (take a convergent subsequence). Promoted from Mathlib2.top_expanding_compact_isometry_aux2 (the same argument is used in top_isometry_compact_surjective); generalised from metric to pseudometric spaces.

```lean
∀ {Y : Type u_1} [inst : PseudoMetricSpace Y] [CompactSpace Y] (u : ℕ → Y) (ε : ℝ), 0 < ε → ∃ m n, m < n ∧ dist (u m) (u n) < ε
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.top_expanding_compact_isometry_aux2）
- 完成者：curator_1
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.lib_matrix_mul_rank_le_add_rank_pow`

Iterated Sylvester rank inequality for powers of a square matrix over a field: j * rank A ≤ (j - 1) * n + rank (A^j) (so A^j = 0 forces rank A ≤ (j-1)n/j). Promoted from Mathlib2.bld_nilpotent_rank_bound_aux1 (stated there with j+1).

```lean
∀ (K : Type u_1) [inst : Field K] (ι : Type u_2) [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (A : Matrix ι ι K) (j : ℕ), j * A.rank ≤ (j - 1) * Fintype.card ι + (A ^ j).rank
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.bld_nilpotent_rank_bound_aux1）
- 完成者：curator_1
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`bld_nilpotent_rank_bound_aux1`

## `Mathlib2.lib_matrix_rank_pow_succ_lt_of_isNilpotent_of_ne_zero`

promoted from Mathlib2.bld5_nilpotent_pow_rank_succ_eq_zero_aux2 (hypothesis restated as A^k ≠ 0 instead of rank ≠ 0): for a nilpotent matrix the ranks of the powers strictly decrease as long as the power is nonzero.

```lean
∀ (K : Type u_1) [inst : Field K] (ι : Type u_2) [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (A : Matrix ι ι K), IsNilpotent A → ∀ (k : ℕ), A ^ k ≠ 0 → (A ^ (k + 1)).rank < (A ^ k).rank
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：curator_3
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`bld5_nilpotent_pow_rank_succ_eq_zero_aux2`、`lib_matrix_rank_eq_zero_iff`

## `Mathlib2.ms_abc_noncoprime_char0_v2`

Non-coprime Mason–Stothers in char 0: nonzero a+b+c=0 are all constant or max degree < deg rad(a) + deg rad(b) + deg(c).

```lean
∀ {k : Type u_1} [inst : Field k] [inst_1 : DecidableEq k] [CharZero k] (a b c : Polynomial k), a ≠ 0 → b ≠ 0 → c ≠ 0 → a + b + c = 0 → a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 ∨ max (max a.natDegree b.natDegree) c.natDegree < (UniqueFactorizationMonoid.radical a).natDegree + (UniqueFactorizationMonoid.radical b).natDegree + c.natDegree
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2408.15180v2 Theorem 5, p.11）
- 完成者：paper_1
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`ms_radical_degree_pos_v2`
- 复核（reviewer_1）：faithful — Compared PDF p.11 Theorem 5; transcription matches. Characteristic zero is [CharZero k], a,b,c nonzero with a+b+c=0 and no coprimality, 'a,b,c in k' is all three natDegree = 0, and the bound is the same asymmetric deg rad(a) + deg rad(b) + deg(c) (c without radical, exactly as printed). Differences 

## `Mathlib2.ms_davenport`

Davenport: in characteristic zero, non-constant f,g with f^3 ≠ g^2 satisfy deg(f^3 - g^2) ≥ deg(f)/2 + 1.

```lean
∀ {k : Type u_1} [inst : Field k] [CharZero k] (f g : Polynomial k), 0 < f.natDegree → 0 < g.natDegree → f ^ 3 ≠ g ^ 2 → f.natDegree + 2 ≤ 2 * (f ^ 3 - g ^ 2).natDegree
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2408.15180v2 Theorem 4, p.4）
- 完成者：paper_1
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`ms_abc_noncoprime_char0_v2`
- 复核（reviewer_1）：faithful — Compared PDF p.4 Theorem 4; transcription matches. deg(f^3-g^2) >= deg(f)/2 + 1 is multiplied by 2 to f.natDegree + 2 <= 2*(f^3-g^2).natDegree, an exact equivalence in N with no truncation. Non-constant is 0 < natDegree for both f and g; f^3 != g^2 makes the difference nonzero so natDegree = degree;

## `Mathlib2.ms_divrad_dvd_derivative_v2`

For nonzero a in k[t], a/rad(a) divides the derivative a'.

```lean
∀ {k : Type u_1} [inst : Field k] [inst_1 : DecidableEq k] (a : Polynomial k), a ≠ 0 → a / UniqueFactorizationMonoid.radical a ∣ Polynomial.derivative a
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2408.15180v2 Lemma 1, p.4）
- 完成者：paper_1
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 复核（reviewer_1）：faithful — Compared PDF p.4 Lemma 1; transcription matches. '/' is Polynomial Euclidean division, which is the exact quotient here because radical a divides a, so a / radical a is the prose a/rad(a) (same as the paper's divRadical). Only difference is the extra [DecidableEq k] instance; the field k is implicit

## `Mathlib2.ms_flt_poly`

Fermat's Last Theorem for polynomials: for n ≥ 3 prime to char k, nonzero pairwise coprime solutions of a^n+b^n=c^n in k[t] are constants.

```lean
∀ {k : Type u_1} [inst : Field k] (n : ℕ), 3 ≤ n → ¬ringChar k ∣ n → ∀ (a b c : Polynomial k), a ≠ 0 → b ≠ 0 → c ≠ 0 → IsCoprime a b → IsCoprime b c → IsCoprime c a → a ^ n + b ^ n = c ^ n → a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2408.15180v2 Corollary 1, p.3）
- 完成者：paper_1
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 复核（reviewer_1）：faithful — Compared PDF p.3 Corollary 1; transcription matches. n>=3, not ringChar k | n, nonzero, pairwise coprime, a^n+b^n=c^n all present with no extra hypotheses; conclusion natDegree = 0 for each is 'constant'. No differences beyond n being a natural number rather than an integer (n>=3 anyway).

## `Mathlib2.ms_mason_stothers_v2`

Mason–Stothers: nonzero pairwise coprime a+b+c=0 in k[t] have all derivatives zero or max degree < deg rad(abc).

```lean
∀ {k : Type u_1} [inst : Field k] [inst_1 : DecidableEq k] (a b c : Polynomial k), a ≠ 0 → b ≠ 0 → c ≠ 0 → IsCoprime a b → IsCoprime b c → IsCoprime c a → a + b + c = 0 → Polynomial.derivative a = 0 ∧ Polynomial.derivative b = 0 ∧ Polynomial.derivative c = 0 ∨ max (max a.natDegree b.natDegree) c.natDegree < (UniqueFactorizationMonoid.radical (a * b * c)).natDegree
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2408.15180v2 Theorem 1, p.2）
- 完成者：paper_1
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 复核（reviewer_1）：faithful — Compared PDF p.2 Theorem 1 with the Lean statement; the 'original' transcription matches the PDF. Hypotheses (nonzero, three pairwise IsCoprime, a+b+c=0, arbitrary field) and the disjunctive conclusion match. Differences are packaging only: extra [DecidableEq k] instance, natDegree instead of degree

## `Mathlib2.ms_radical_degree_pos_v2`

A polynomial over a field of degree ≥ 1 has radical of degree ≥ 1.

```lean
∀ {k : Type u_1} [inst : Field k] [inst_1 : DecidableEq k] (a : Polynomial k), 1 ≤ a.natDegree → 1 ≤ (UniqueFactorizationMonoid.radical a).natDegree
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2408.15180v2 Lemma 3, p.7）
- 完成者：paper_1
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 复核（reviewer_1）：faithful — Compared PDF p.7 Lemma 3; transcription matches. 'degree >= 1' is 1 <= natDegree, which already forces a != 0, so natDegree and degree agree and the zero-polynomial convention (Mathlib radical 0 = 1) never comes into play. Conclusion 1 <= (radical a).natDegree is the same claim; only extra is [Decid

## `Mathlib2.nt2_dvd_two_pow_sub_one_eq_one`

If n ≥ 1 divides 2^n - 1 then n = 1 (take the least prime factor p of n; the order of 2 mod p divides gcd(n, p-1) = 1).

```lean
∀ (n : ℕ), 0 < n → n ∣ 2 ^ n - 1 → n = 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_a
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.nt2_fermat_number_prime_factor_form`

Every prime factor p of the Fermat number 2^(2^n)+1 has the form m·2^(n+1) + 1: the order of 2 mod p is exactly 2^(n+1), which divides p - 1.

```lean
∀ (n p : ℕ), Nat.Prime p → (∃ k, p * k = 2 ^ 2 ^ n + 1) → ∃ m, p = m * 2 ^ (n + 1) + 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_d
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.nt2_lte_three_two_pow_three_pow_add_one`

Lifting the exponent: the exact power of 3 dividing 2^(3^n) + 1 is 3^(n+1).

```lean
∀ (n : ℕ), ∃ k, 2 ^ 3 ^ n + 1 = 3 ^ (n + 1) * k ∧ ¬3 ∣ k
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_e
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.nt2_pow_four_add_four_mul_pow_four_not_prime`

Generalization of Mathlib2.nt_pow4_add_four_not_prime (the case k = 1): n^4 + 4k^4 = ((n-k)^2 + k^2)((n+k)^2 + k^2) is composite for n > 1, k ≥ 1.

```lean
∀ (n k : ℕ), 1 < n → 0 < k → ¬Nat.Prime (n ^ 4 + 4 * k ^ 4)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_d
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.nt_seven_dvd_sq_add_sq`

If 7 divides a^2 + b^2 then 7 divides both a and b.

```lean
∀ (a b : ℤ), 7 ∣ a ^ 2 + b ^ 2 → 7 ∣ a ∧ 7 ∣ b
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_2
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.p3_prop2`

for even n > 1 the Pisano period of F_n divides 2n

```lean
∀ (n : ℕ), 1 < n → 2 ∣ n → Mathlib2.p3_pisano (Nat.fib n) ∣ 2 * n
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2504.09938 Proposition 2）
- 完成者：paper_3
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`p3_aux_period`、`p3_pisano`
- 复核（reviewer_3）：faithful — Paper: n>1, 2|n implies pi(F_n) | 2n. Lean identical using p3_pisano (least positive period). Checked numerically for even n<60 (pi(F_n)=2n for n>=4, pi(F_2)=1).

## `Mathlib2.p3_remark2`

k is self-summable iff F_k divides F_{F_k+2} - 1

```lean
∀ (k : ℕ), Mathlib2.p3_self_summable k ↔ Nat.fib k ∣ Nat.fib (Nat.fib k + 2) - 1
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2504.09938 Remark 2）
- 完成者：paper_3
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`p3_fibsum`、`p3_prop1`、`p3_self_summable`
- 复核（reviewer_3）：faithful — Paper: self-summable k are those with F_k | (F_{F_k+2} - 1). Lean iff is the same; natural subtraction safe since fib(m+2)>=1. The lists of first terms in the remark are not formalized (not checked by Lean).

## `Mathlib2.p3_thm2`

for n = 2p or 4p with p an odd prime, p = 2 mod 3, p = ±2 mod 5: F_n is odd and F_n divides F_{F_n+2} - 1

```lean
∀ (p n : ℕ), Nat.Prime p → Odd p → p % 3 = 2 → p % 5 = 2 ∨ p % 5 = 3 → n = 2 * p ∨ n = 4 * p → Nat.fib n ≡ 1 [MOD 2] ∧ ↑(Nat.fib (Nat.fib n + 2)) - 1 ≡ 0 [ZMOD ↑(Nat.fib n)]
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2504.09938 Theorem 2）
- 完成者：paper_3
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`p3_aux_period`、`p3_aux_period_aux3`、`p3_thm1_corrected_aux1`
- 复核（reviewer_3）：faithful — Paper: n=2p or 4p, p odd prime, p=2 mod 3, p=+-2 mod 5; then F_n odd and F_{F_n+2}-1 = 0 mod F_n. Lean hypotheses and both conclusions match exactly (p%5=2 or 3 is +-2 mod 5). Checked numerically for p=17,23,47,53, both n. Note on the proof only: for n=4p, F_n = -3 mod 2n (not -1 or 0), so the paper

## `Mathlib2.p4_rem1_bound_even`

Remark 1: for s=2k, k>=6 and 2^s<n<=2^(s+1): 3x(n) >= 2^(k+1)(2^k-6k-6)-2 >= 2^(k+1)-2 > 0.

```lean
∀ (k n : ℕ), 6 ≤ k → 2 ^ (2 * k) < n → n ≤ 2 ^ (2 * k + 1) → 2 ^ (k + 1) - 2 ≤ 3 * Mathlib2.p4_x n ∧ 0 < Mathlib2.p4_x n
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Remark 1）
- 完成者：paper_4
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`p4_m`、`p4_r`、`p4_rem1_even`、`p4_rem1_lower`、`p4_rem1_odd`、`p4_x`、`p4_z`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). Paper: s=2k, k>=6, 2^s<n<=2^(s+1) gives 3x(n)>=...>=2^(k+1)-2>0. Lean keeps the final bound and positivity but omits the intermediate expression 2^(k+1)(2^k-6k-6)-2. Numerically the final bound actually holds from k=5 and fails f

## `Mathlib2.p4_rem1_bound_odd`

Remark 1: for s=2k+1, k>=6 and 2^s<n<=2^(s+1): 3x(n) > 2^(k+2)(2^k-6k-9)-1 >= 2^(k+2)-1 > 0.

```lean
∀ (k n : ℕ), 6 ≤ k → 2 ^ (2 * k + 1) < n → n ≤ 2 ^ (2 * k + 2) → 2 ^ (k + 2) - 1 < 3 * Mathlib2.p4_x n ∧ 0 < Mathlib2.p4_x n
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Remark 1）
- 完成者：paper_4
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`p4_m`、`p4_r`、`p4_rem1_even`、`p4_rem1_lower`、`p4_rem1_odd`、`p4_x`、`p4_z`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). Paper: k>=6, s=2k+1, 2^s<n<=2^(s+1) gives 3x(n)>...>=2^(k+2)-1>0. Lean keeps the final strict bound and positivity, omitting the intermediate expression. This is the bound the proof of Theorem 1(v) relies on, and it carries the h

## `Mathlib2.p4_thm1_i`

Theorem 1(i): x(n)=0 iff n is one of 436, 451, 529, 545, 546.

```lean
∀ (n : ℕ), 0 < n → (Mathlib2.p4_x n = 0 ↔ n = 436 ∨ n = 451 ∨ n = 529 ∨ n = 545 ∨ n = 546)
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Theorem 1(i)）
- 完成者：paper_4
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`p4_rem1_large`、`p4_small_classify`、`p4_x`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). x(n)=0 iff n in {436,451,529,545,546}, n positive. Identical; confirmed by computation to n=300000.

## `Mathlib2.p4_thm1_iii`

Theorem 1(iii): x(n)>0 iff 437 <= n <= 512 with n not 450, 451, or n >= 530 with n not 545, 546.

```lean
∀ (n : ℕ), 0 < n → (0 < Mathlib2.p4_x n ↔ 437 ≤ n ∧ n ≤ 512 ∧ n ≠ 450 ∧ n ≠ 451 ∨ 530 ≤ n ∧ n ≠ 545 ∧ n ≠ 546)
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Theorem 1(iii)）
- 完成者：paper_4
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`p4_rem1_large`、`p4_small_classify`、`p4_x`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). x(n)>0 iff (437<=n<=512, n not 450,451) or (n>=530, n not 545,546). Identical; confirmed numerically to 300000.

## `Mathlib2.p4_thm1_iv`

Theorem 1(iv): x(n) > 0 for every n >= 547.

```lean
∀ (n : ℕ), 547 ≤ n → 0 < Mathlib2.p4_x n
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Theorem 1(iv)）
- 完成者：paper_4
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`p4_thm1_iii`、`p4_x`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). x(n)>0 for every n>=547. Identical.

## `Mathlib2.p4_thm1_v_step_fixed`

Auditor's correction, not the paper's wording: the claim in the proof of Theorem 1(v) holds once k >= 4: if 2^(k+2) > 3B+1 and k >= 4 then x(2^(2k+2)) > B.

```lean
∀ (B k : ℕ), 4 ≤ k → 3 * B + 1 < 2 ^ (k + 2) → ↑B < Mathlib2.p4_x (2 ^ (2 * k + 2))
```
- 结论：证明
- 层级：agent
- 来源：conjecture（arXiv:2503.03469v1 proof of Theorem 1(v) (corrected)）
- 完成者：paper_4
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`p4_m`、`p4_r`、`p4_rem1_even`、`p4_x`、`p4_z`
- 复核（reviewer_4）：unsure — Not a claim of the paper: auditor's repaired version with k>=4 added. My computation agrees it holds for k=4..12 (k=4: x(1024)=187>20); the paper's own implicit range via Remark 1 would be k>=6.

## `Mathlib2.p4_z_spec`

The Lean definition p4_z agrees with the paper's: z(n) is the largest integer with 3 z(n) < 2n.

```lean
∀ (n : ℕ), 3 * Mathlib2.p4_z n < 2 * ↑n ∧ ∀ (k : ℤ), 3 * k < 2 * ↑n → k ≤ Mathlib2.p4_z n
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Introduction, definition (a)）
- 完成者：paper_4
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`p4_z`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). States exactly definition (a) (largest integer k with 3k<2n, k ranging over Int); this is the bridge from the closed form to the paper's wording. Holds for n=0 too, harmless.

## `Mathlib2.poly_abc_distinct_roots_complex`

Stothers' form over ℂ: for coprime a, b with a non-constant, the product ab(a+b) has at least deg a + 1 distinct complex roots — Uses Mathlib2.ms_mason_stothers_v2 (c = -(a+b)) to get deg a < deg rad(ab(a+b)), then show over an algebraically closed field that natDegree (radical p) equals the number of distinct roots of p (radical is the product of the distinct monic linear factors).

```lean
∀ (a b : Polynomial ℂ), IsCoprime a b → 0 < a.natDegree → a.natDegree + 1 ≤ (a * b * (a + b)).roots.toFinset.card
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pa
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`poly_abc_radical_bound_of_coprime`

## `Mathlib2.poly_cyclotomic_reverse_eq_self`

Cyclotomic polynomials Φ_n (n ≥ 2) are palindromic — strong induction: X^n - 1 = ∏_{d ∣ n} Φ_d, reverse is multiplicative, reverse(X^n - 1) = -(X^n - 1), reverse(Φ_1) = -Φ_1, and cancel the product over proper divisors d ≥ 2 by the induction hypothesis.

```lean
∀ (n : ℕ), 2 ≤ n → (Polynomial.cyclotomic n ℤ).reverse = Polynomial.cyclotomic n ℤ
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pb
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.poly_flt_noncoprime_proportional`

FLT for polynomials without coprimality: in char 0, any nonzero solution of a^n + b^n = c^n (n ≥ 3) is a common polynomial d times a constant solution — take d = gcd(a,b); d^n ∣ c^n gives d ∣ c; the quotients are pairwise coprime and satisfy the same equation, so Uses Mathlib2.ms_flt_poly to make them constants.

```lean
∀ {k : Type u_1} [inst : Field k] [DecidableEq k] [CharZero k] (n : ℕ), 3 ≤ n → ∀ (a b c : Polynomial k), a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ n + b ^ n = c ^ n → ∃ d α β γ, a = Polynomial.C α * d ∧ b = Polynomial.C β * d ∧ c = Polynomial.C γ * d
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pa
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`ms_flt_poly`

## `Mathlib2.poly_no_consecutive_powerful`

In char 0 there are no non-constant 'consecutive powerful polynomials': if every irreducible factor of f and of f+1 occurs at least squared then f is constant — a powerful polynomial g satisfies 2·deg rad g ≤ deg g; Uses Mathlib2.ms_mason_stothers_v2 with (f, 1, -(f+1)): deg f < deg rad(f(f+1)) = deg rad f + deg rad(f+1) ≤ deg f/2 + deg f/2, contradiction.

```lean
∀ {k : Type u_1} [inst : Field k] [DecidableEq k] [CharZero k] (f : Polynomial k), (∀ (p : Polynomial k), Irreducible p → p ∣ f → p ^ 2 ∣ f) → (∀ (p : Polynomial k), Irreducible p → p ∣ f + 1 → p ^ 2 ∣ f + 1) → f.natDegree = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pa
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`poly_abc_radical_bound_of_coprime`

## `Mathlib2.poly_ratfunc_fermat_curve_const`

The Fermat curve x^n + y^n = 1 (n ≥ 3) has no non-constant rational parametrisation in char 0 — write f = a/c, g = b/c with common denominator, cancel gcd(a,b,c) to get pairwise coprime a^n + b^n = c^n, then Uses Mathlib2.ms_flt_poly to conclude a, b, c constant; the cases a = 0 or b = 0 (g^n = 1 forces g constant) are separate.

```lean
∀ {k : Type u_1} [inst : Field k] [DecidableEq k] [CharZero k] (n : ℕ), 3 ≤ n → ∀ (f g : RatFunc k), f ^ n + g ^ n = 1 → (∃ c, f = RatFunc.C c) ∧ ∃ d, g = RatFunc.C d
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pa
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`poly_flt_noncoprime_proportional`

## `Mathlib2.poly_real_nonneg_eq_sum_two_squares`

A real polynomial that is nonnegative on ℝ is a sum of two squares of real polynomials — strong induction on degree: real roots have even multiplicity (factor out (X-r)^2), irreducible quadratic factors are (X-u)^2 + v^2, and sums of two squares are closed under multiplication (Brahmagupta identity).

```lean
∀ (p : Polynomial ℝ), (∀ (x : ℝ), 0 ≤ Polynomial.eval x p) → ∃ f g, p = f ^ 2 + g ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pa
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.poly_x2_x_1_dvd_trinomial`

X^2+X+1 divides X^(3k+2) + X^(3m+1) + 1 over ℤ — X^3 ≡ 1 mod X^2+X+1 (since X^3 - 1 = (X-1)(X^2+X+1)), so the trinomial is ≡ X^2 + X + 1 ≡ 0.

```lean
∀ (k m : ℕ), Polynomial.X ^ 2 + Polynomial.X + 1 ∣ Polynomial.X ^ (3 * k + 2) + Polynomial.X ^ (3 * m + 1) + 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pb
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.poly_x4_sub_10x2_add_1_irreducible_int`

The minimal polynomial X^4 - 10X^2 + 1 of √2+√3 is irreducible over ℤ — no integer roots (±1 fail); a factorisation into monic quadratics (X^2+aX+b)(X^2-aX+d) with bd = 1 forces a(d-b) = 0 and b+d-a^2 = -10, i.e. a^2 = 12 or a^2 = 8 or (a = 0, b + d = -10 with bd = 1), all impossible.

```lean
Irreducible (Polynomial.X ^ 4 - 10 * Polynomial.X ^ 2 + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pb
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_erdos_szekeres`

Erdős–Szekeres: any sequence of rs+1 distinct reals has an increasing subsequence of length r+1 or a decreasing one of length s+1. Proof idea: label each index i with (length of longest increasing subsequence ending at i, longest decreasing ending at i); labels are pairwise distinct (for i<j one of the two coordinates strictly grows); if all labels lay in [1,r]×[1,s] pigeonhole would be violated.

```lean
∀ (r s : ℕ) (f : Fin (r * s + 1) → ℝ), Function.Injective f → (∃ t, r < t.card ∧ StrictMonoOn f ↑t) ∨ ∃ t, s < t.card ∧ StrictAntiOn f ↑t
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r3_prover_4
- 尝试次数：1
- 被引用：1 次
- 分数：5
- 依赖：`r3_erdos_szekeres_s1h1`、`r3_erdos_szekeres_s1h2`

## `Mathlib2.r3_erdos_szekeres_s1h1`

r3_erdos_szekeres 的证明骨架中第 1 个空洞

```lean
∀ (n : ℕ) (g : Fin n → ℝ), ∃ a, (∀ (i : Fin n), 1 ≤ a i ∧ ∃ t, t.card = a i ∧ StrictMonoOn g ↑t) ∧ ∀ (i j : Fin n), i < j → g i < g j → a i < a j
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_erdos_szekeres）
- 完成者：r3_prover_4
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_erdos_szekeres_s1h2`

r3_erdos_szekeres 的证明骨架中第 2 个空洞

```lean
∀ (r s : ℕ) (a b : Fin (r * s + 1) → ℕ), (∀ (i : Fin (r * s + 1)), 1 ≤ a i ∧ a i ≤ r) → (∀ (i : Fin (r * s + 1)), 1 ≤ b i ∧ b i ≤ s) → ∃ i j, i < j ∧ a i = a j ∧ b i = b j
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_erdos_szekeres）
- 完成者：r3_prover_4
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_exists_dvd_pair_of_card_gt_s1h1`

r3_exists_dvd_pair_of_card_gt 的证明骨架中第 1 个空洞

```lean
∀ (n m : ℕ), m ∈ Finset.Icc 1 (2 * n) → m / 2 ^ m.factorization 2 ∈ Finset.image (fun i => 2 * i + 1) (Finset.range n)
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_exists_dvd_pair_of_card_gt）
- 完成者：r3_prover_3
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_exists_dvd_pair_of_card_gt_s1h2`

r3_exists_dvd_pair_of_card_gt 的证明骨架中第 2 个空洞

```lean
∀ (a b : ℕ), 0 < a → 0 < b → a / 2 ^ a.factorization 2 = b / 2 ^ b.factorization 2 → a ∣ b ∨ b ∣ a
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_exists_dvd_pair_of_card_gt）
- 完成者：r3_prover_3
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_fermat_fourth_pow_sub_ne_sq_s1h1v1`

r3_fermat_fourth_pow_sub_ne_sq 的证明骨架中第 1 个空洞

```lean
(∀ (x y z : ℤ), x.gcd y = 1 → y ≠ 0 → z ≠ 0 → x ^ 4 - y ^ 4 ≠ z ^ 2) → ∀ (x y z : ℤ), y ≠ 0 → z ≠ 0 → x ^ 4 - y ^ 4 ≠ z ^ 2
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_fermat_fourth_pow_sub_ne_sq）
- 完成者：r3_prover_1
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_fermat_fourth_pow_sub_ne_sq_s1h2`

r3_fermat_fourth_pow_sub_ne_sq 的证明骨架中第 2 个空洞

```lean
∀ (x y z : ℤ), x.gcd y = 1 → y % 2 = 1 → z ≠ 0 → x ^ 4 - y ^ 4 = z ^ 2 → ∃ m n w, |m| < |x| ∧ m.gcd n = 1 ∧ n ≠ 0 ∧ w ≠ 0 ∧ m ^ 4 - n ^ 4 = w ^ 2
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_fermat_fourth_pow_sub_ne_sq）
- 完成者：r3_prover_1
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_fermat_fourth_pow_sub_ne_sq_s1h3`

r3_fermat_fourth_pow_sub_ne_sq 的证明骨架中第 3 个空洞

```lean
∀ (x y z : ℤ), x.gcd y = 1 → y % 2 = 0 → y ≠ 0 → x ^ 4 - y ^ 4 = z ^ 2 → ∃ a b, x ^ 2 = (2 * a ^ 2) ^ 2 + (b ^ 2) ^ 2 ∧ a ≠ 0 ∧ (2 * a ^ 2).gcd (b ^ 2) = 1
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_fermat_fourth_pow_sub_ne_sq）
- 完成者：r3_prover_1
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_fermat_fourth_pow_sub_ne_sq_s1h4`

r3_fermat_fourth_pow_sub_ne_sq 的证明骨架中第 4 个空洞

```lean
∀ (x a b : ℤ), a ≠ 0 → (2 * a ^ 2).gcd (b ^ 2) = 1 → x ^ 2 = (2 * a ^ 2) ^ 2 + (b ^ 2) ^ 2 → ∃ c d w, |c| < |x| ∧ c.gcd d = 1 ∧ d ≠ 0 ∧ w ≠ 0 ∧ c ^ 4 - d ^ 4 = w ^ 2
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_fermat_fourth_pow_sub_ne_sq）
- 完成者：r3_prover_1
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_fib_iff_five_sq_pm_four_is_square_s1h2`

r3_fib_iff_five_sq_pm_four_is_square 的证明骨架中第 2 个空洞

```lean
∀ (v u : ℕ), u ≤ v → ↑v ^ 2 - ↑v * ↑u - ↑u ^ 2 = 1 ∨ ↑v ^ 2 - ↑v * ↑u - ↑u ^ 2 = -1 → ∃ n, u = Nat.fib n ∧ v = Nat.fib (n + 1)
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_fib_iff_five_sq_pm_four_is_square）
- 完成者：r3_prover_4
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_fib_iff_five_sq_pm_four_is_square_s1h3`

r3_fib_iff_five_sq_pm_four_is_square 的证明骨架中第 3 个空洞

```lean
∀ (x u : ℕ), x ^ 2 = 5 * u ^ 2 + 4 ∨ x ^ 2 + 4 = 5 * u ^ 2 → ∃ v, x + u = 2 * v ∧ u ≤ v
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_fib_iff_five_sq_pm_four_is_square）
- 完成者：r3_prover_4
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_hardy_inequality_finite_s1h1`

r3_hardy_inequality_finite 的证明骨架中第 1 个空洞

```lean
∀ (a : ℕ → ℝ) (k : ℕ), ((∑ i ∈ Finset.range (k + 1), a i) / (↑k + 1)) ^ 2 - 2 * ((∑ i ∈ Finset.range (k + 1), a i) / (↑k + 1)) * a k ≤ (∑ i ∈ Finset.range k, a i) ^ 2 / ↑k - (∑ i ∈ Finset.range (k + 1), a i) ^ 2 / (↑k + 1)
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_hardy_inequality_finite）
- 完成者：r3_prover_3
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_hardy_inequality_finite_s1h2`

r3_hardy_inequality_finite 的证明骨架中第 2 个空洞

```lean
∀ (a : ℕ → ℝ) (n : ℕ), (∀ (k : ℕ), ((∑ i ∈ Finset.range (k + 1), a i) / (↑k + 1)) ^ 2 - 2 * ((∑ i ∈ Finset.range (k + 1), a i) / (↑k + 1)) * a k ≤ (∑ i ∈ Finset.range k, a i) ^ 2 / ↑k - (∑ i ∈ Finset.range (k + 1), a i) ^ 2 / (↑k + 1)) → ∑ k ∈ Finset.range n, ((∑ i ∈ Finset.range (k + 1), a i) / (↑k + 1)) ^ 2 ≤ 2 * ∑ k ∈ Finset.range n, (∑ i ∈ Finset.range (k + 1), a i) / (↑k + 1) * a k
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_hardy_inequality_finite）
- 完成者：r3_prover_3
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_hardy_inequality_finite_s2h1`

r3_hardy_inequality_finite 的证明骨架中第 1 个空洞

```lean
∀ (T B Q : ℝ), 0 ≤ T → 0 ≤ B → T ≤ 2 * Q → Q ^ 2 ≤ T * B → T ≤ 4 * B
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_hardy_inequality_finite）
- 完成者：r3_prover_3
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_imo1988_vieta_jumping_s1h1`

r3_imo1988_vieta_jumping 的证明骨架中第 1 个空洞

```lean
∀ (q a b : ℕ), 0 < b → a ^ 2 + b ^ 2 = q * (a * b + 1) → a ≤ q * b
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_imo1988_vieta_jumping）
- 完成者：r3_prover_1
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_imo1988_vieta_jumping_s1h2`

r3_imo1988_vieta_jumping 的证明骨架中第 2 个空洞

```lean
(∀ (q a b : ℕ), 0 < b → a ^ 2 + b ^ 2 = q * (a * b + 1) → a ≤ q * b) → ∀ (q a b : ℕ), a ≤ q * b → a ^ 2 + b ^ 2 = q * (a * b + 1) → (q * b - a) ^ 2 + b ^ 2 = q * ((q * b - a) * b + 1)
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_imo1988_vieta_jumping）
- 完成者：r3_prover_1
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_imo1988_vieta_jumping_s1h3`

r3_imo1988_vieta_jumping 的证明骨架中第 3 个空洞

```lean
(∀ (q a b : ℕ), 0 < b → a ^ 2 + b ^ 2 = q * (a * b + 1) → a ≤ q * b) → (∀ (q a b : ℕ), a ≤ q * b → a ^ 2 + b ^ 2 = q * (a * b + 1) → (q * b - a) ^ 2 + b ^ 2 = q * ((q * b - a) * b + 1)) → ∀ (q a b : ℕ), 0 < b → b ≤ a → a ^ 2 + b ^ 2 = q * (a * b + 1) → q * b - a < a
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_imo1988_vieta_jumping）
- 完成者：r3_prover_1
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_imo1990_sq_dvd_two_pow_add_one_s2h1`

r3_imo1990_sq_dvd_two_pow_add_one 的证明骨架中第 1 个空洞

```lean
∀ (c m q : ℕ), m ≠ 0 → Nat.Prime q → q ∣ m → (∀ (r : ℕ), Nat.Prime r → r ∣ m → q ≤ r) → q ∣ 2 ^ (c * m) + 1 → q ∣ 2 ^ (2 * c) - 1
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_imo1990_sq_dvd_two_pow_add_one）
- 完成者：r3_prover_1
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_imo1990_sq_dvd_two_pow_add_one_s2h2`

r3_imo1990_sq_dvd_two_pow_add_one 的证明骨架中第 2 个空洞

```lean
(∀ (c m q : ℕ), m ≠ 0 → Nat.Prime q → q ∣ m → (∀ (r : ℕ), Nat.Prime r → r ∣ m → q ≤ r) → q ∣ 2 ^ (c * m) + 1 → q ∣ 2 ^ (2 * c) - 1) → ∀ (n : ℕ), n ^ 2 ∣ 2 ^ n + 1 → ¬9 ∣ n
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_imo1990_sq_dvd_two_pow_add_one）
- 完成者：r3_prover_1
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_imo1990_sq_dvd_two_pow_add_one_s2h3`

r3_imo1990_sq_dvd_two_pow_add_one 的证明骨架中第 3 个空洞

```lean
(∀ (c m q : ℕ), m ≠ 0 → Nat.Prime q → q ∣ m → (∀ (r : ℕ), Nat.Prime r → r ∣ m → q ≤ r) → q ∣ 2 ^ (c * m) + 1 → q ∣ 2 ^ (2 * c) - 1) → (∀ (n : ℕ), n ^ 2 ∣ 2 ^ n + 1 → ¬9 ∣ n) → ∀ (n : ℕ), ¬7 ∣ 2 ^ n + 1
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_imo1990_sq_dvd_two_pow_add_one）
- 完成者：r3_prover_1
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_imo2000_q2_s1h1`

r3_imo2000_q2 的证明骨架中第 1 个空洞

```lean
∀ (a b c : ℝ), 0 < a → 0 < b → 0 < c → a * b * c = 1 → ∀ (x y z : ℝ), 0 < x → 0 < y → 0 < z → x * y * z = 1 → (x - 1 + 1 / y) * (y - 1 + 1 / z) ≤ x ^ 2 * y
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_imo2000_q2）
- 完成者：r3_prover_2
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_imo2000_q2_s1h2`

r3_imo2000_q2 的证明骨架中第 2 个空洞

```lean
∀ (a b c : ℝ), 0 < a → 0 < b → 0 < c → a * b * c = 1 → (∀ (x y z : ℝ), 0 < x → 0 < y → 0 < z → x * y * z = 1 → (x - 1 + 1 / y) * (y - 1 + 1 / z) ≤ x ^ 2 * y) → ∀ (x y z : ℝ), 0 < x → 0 < y → 0 < z → x * y * z = 1 → 0 ≤ x - 1 + 1 / y ∨ 0 ≤ y - 1 + 1 / z
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_imo2000_q2）
- 完成者：r3_prover_2
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_imo2000_q2_s1h3`

r3_imo2000_q2 的证明骨架中第 3 个空洞

```lean
∀ (a b c : ℝ), 0 < a → 0 < b → 0 < c → a * b * c = 1 → (∀ (x y z : ℝ), 0 < x → 0 < y → 0 < z → x * y * z = 1 → (x - 1 + 1 / y) * (y - 1 + 1 / z) ≤ x ^ 2 * y) → (∀ (x y z : ℝ), 0 < x → 0 < y → 0 < z → x * y * z = 1 → 0 ≤ x - 1 + 1 / y ∨ 0 ≤ y - 1 + 1 / z) → ∀ (u v w p q r : ℝ), 0 ≤ u → 0 ≤ v → 0 ≤ w → u * v ≤ p → v * w ≤ q → w * u ≤ r → p * q * r = 1 → u * v * w ≤ 1
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_imo2000_q2）
- 完成者：r3_prover_2
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_imo2000_q2_s1h4`

r3_imo2000_q2 的证明骨架中第 4 个空洞

```lean
∀ (a b c : ℝ), 0 < a → 0 < b → 0 < c → a * b * c = 1 → (∀ (x y z : ℝ), 0 < x → 0 < y → 0 < z → x * y * z = 1 → (x - 1 + 1 / y) * (y - 1 + 1 / z) ≤ x ^ 2 * y) → (∀ (x y z : ℝ), 0 < x → 0 < y → 0 < z → x * y * z = 1 → 0 ≤ x - 1 + 1 / y ∨ 0 ≤ y - 1 + 1 / z) → (∀ (u v w p q r : ℝ), 0 ≤ u → 0 ≤ v → 0 ≤ w → u * v ≤ p → v * w ≤ q → w * u ≤ r → p * q * r = 1 → u * v * w ≤ 1) → ∀ (u v w : ℝ), 0 ≤ u ∨ 0 ≤ v → 0 ≤ v ∨ 0 ≤ w → 0 ≤ w ∨ 0 ≤ u → 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ w ∨ u * v * w ≤ 0
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_imo2000_q2）
- 完成者：r3_prover_2
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_mordell_y_sq_eq_x_cube_add_seven_s1h1`

r3_mordell_y_sq_eq_x_cube_add_seven 的证明骨架中第 1 个空洞

```lean
∀ (N : ℕ), N % 4 = 3 → ∃ p, Nat.Prime p ∧ p % 4 = 3 ∧ p ∣ N
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_mordell_y_sq_eq_x_cube_add_seven）
- 完成者：r3_prover_3
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_mordell_y_sq_eq_x_cube_add_seven_s1h2`

r3_mordell_y_sq_eq_x_cube_add_seven 的证明骨架中第 2 个空洞

```lean
∀ (a b : ℤ), b ^ 2 = a ^ 3 + 7 → a % 2 = 1
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_mordell_y_sq_eq_x_cube_add_seven）
- 完成者：r3_prover_3
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_mordell_y_sq_eq_x_cube_add_seven_s1h3`

r3_mordell_y_sq_eq_x_cube_add_seven 的证明骨架中第 3 个空洞

```lean
∀ (a : ℤ), a % 2 = 1 → (a ^ 2 - 2 * a + 4).natAbs % 4 = 3
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_mordell_y_sq_eq_x_cube_add_seven）
- 完成者：r3_prover_3
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_ramsey_three_three_pigeonhole`

Pigeonhole step of R(3,3)<=6 (hole 2 of the r3_ramsey_three_three skeleton; proposed by hand because sketch left an orphan child that blocks re-sketching): in a graph on >= 6 vertices some vertex v has three distinct neighbours or three distinct non-neighbours.

```lean
∀ (V : Type) [inst : Fintype V], 6 ≤ Fintype.card V → ∀ (G : SimpleGraph V), ∃ v x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ (G.Adj v x ∧ G.Adj v y ∧ G.Adj v z ∨ Gᶜ.Adj v x ∧ Gᶜ.Adj v y ∧ Gᶜ.Adj v z)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r3_prover_2
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_ramsey_three_three_s1h1`

r3_ramsey_three_three 的证明骨架中第 1 个空洞

```lean
∀ (V : Type) [inst : Fintype V], 6 ≤ Fintype.card V → ∀ (G H : SimpleGraph V) (x y z : V), H.Adj x y → H.Adj x z → H.Adj y z → ¬H.CliqueFree 3
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_ramsey_three_three）
- 完成者：r3_prover_2
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_sylvester_nonrepresentable_count_v2_s1h1`

r3_sylvester_nonrepresentable_count_v2 的证明骨架中第 1 个空洞

```lean
∀ (a b : ℕ), 0 < a → 0 < b → a.Coprime b → ∀ n < (a - 1) * (b - 1), (∃ x y, a * x + b * y = n) → ¬∃ x y, a * x + b * y = (a - 1) * (b - 1) - 1 - n
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_sylvester_nonrepresentable_count_v2）
- 完成者：r3_prover_5
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_sylvester_nonrepresentable_count_v2_s1h2`

r3_sylvester_nonrepresentable_count_v2 的证明骨架中第 2 个空洞

```lean
∀ (a b : ℕ), 0 < a → 0 < b → a.Coprime b → ∀ n < (a - 1) * (b - 1), (¬∃ x y, a * x + b * y = n) → ∃ x y, a * x + b * y = (a - 1) * (b - 1) - 1 - n
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_sylvester_nonrepresentable_count_v2）
- 完成者：r3_prover_5
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_sylvester_nonrepresentable_count_v2_s1h3`

r3_sylvester_nonrepresentable_count_v2 的证明骨架中第 3 个空洞

```lean
∀ (a b : ℕ), 0 < a → 0 < b → a.Coprime b → ∀ (M : ℕ) (P : ℕ → Prop) [inst : DecidablePred fun n => ¬P n], (∀ n < M, P n ↔ ¬P (M - 1 - n)) → 2 * {n ∈ Finset.range M | ¬P n}.card = M
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_sylvester_nonrepresentable_count_v2）
- 完成者：r3_prover_5
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_wolstenholme_harmonic_s1h1`

r3_wolstenholme_harmonic 的证明骨架中第 1 个空洞

```lean
∀ (p : ℕ), Nat.Prime p → 5 ≤ p → ∀ k ∈ Finset.Icc 1 (p - 1), (p - 1).factorial / k + (p - 1).factorial / (p - k) = p * ((p - 1).factorial / (k * (p - k)))
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_wolstenholme_harmonic）
- 完成者：r3_prover_5
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_wolstenholme_harmonic_s1h2`

r3_wolstenholme_harmonic 的证明骨架中第 2 个空洞

```lean
∀ (p : ℕ), Nat.Prime p → 5 ≤ p → ∑ k ∈ Finset.Icc 1 (p - 1), (p - 1).factorial / (p - k) = ∑ k ∈ Finset.Icc 1 (p - 1), (p - 1).factorial / k
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_wolstenholme_harmonic）
- 完成者：r3_prover_5
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_wolstenholme_harmonic_s1h3`

r3_wolstenholme_harmonic 的证明骨架中第 3 个空洞

```lean
∀ (p : ℕ), Nat.Prime p → 5 ≤ p → ∀ k ∈ Finset.Icc 1 (p - 1), ↑((p - 1).factorial / (k * (p - k))) = (↑k)⁻¹ ^ 2
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_wolstenholme_harmonic）
- 完成者：r3_prover_5
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.r3_wolstenholme_harmonic_s1h4`

r3_wolstenholme_harmonic 的证明骨架中第 4 个空洞

```lean
∀ (p : ℕ), Nat.Prime p → 5 ≤ p → ∑ k ∈ Finset.Icc 1 (p - 1), (↑k)⁻¹ ^ 2 = 0
```
- 结论：证明
- 层级：agent
- 来源：decomposition（r3_wolstenholme_harmonic）
- 完成者：r3_prover_5
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.top_tendsto_of_subseq_limits_unique`

In a compact metric space a sequence all of whose convergent subsequences have limit a converges to a — otherwise infinitely many terms stay ε-far from a; extract a subsequence of those, then a convergent sub-subsequence by sequential compactness, whose limit is ≠ a.

```lean
∀ {X : Type u_1} [inst : MetricSpace X] [CompactSpace X] (u : ℕ → X) (a : X), (∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (b : X), Filter.Tendsto (u ∘ φ) Filter.atTop (nhds b) → b = a) → Filter.Tendsto u Filter.atTop (nhds a)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_3
- 尝试次数：1
- 被引用：1 次
- 分数：5

## `Mathlib2.ab_perfect_mul_abundant_any_disproof`

Task 3(a) literally, k any natural number (including 0). FALSE (k = 1, k = 0).

```lean
¬∀ (n k : ℕ), n.Perfect → (k * n).Abundant
```
- 结论：证伪
- 层级：agent
- 来源：paper（s40753-021-00140-1 p.28 Appendix 2 Task 3(a) / Fig. 4）
- 完成者：paper_2
- 尝试次数：1
- 被引用：0 次
- 分数：4
- 复核（reviewer_2）：unsure — Same Task 3(a) text but with k ranging over Lean's N including 0. The paper's handling (k = 1 as the limit case, fix k > 1) indicates N starts at 1, so allowing k = 0 makes this a slightly stronger statement than the paper's; it is literal only under the 0-in-N convention. The statement is false eit

## `Mathlib2.ab_perfect_mul_abundant_pos_disproof`

Task 3(a) literally with N = positive integers. FALSE at k = 1, as the paper notes.

```lean
¬∀ (n k : ℕ), n.Perfect → 0 < k → (k * n).Abundant
```
- 结论：证伪
- 层级：agent
- 来源：paper（s40753-021-00140-1 p.28 Appendix 2 Task 3(a) / Fig. 4）
- 完成者：paper_2
- 尝试次数：1
- 被引用：0 次
- 分数：4
- 复核（reviewer_2）：faithful — Task 3(a) 'If n is perfect, then kn is abundant for any k in N' with N = positive integers, which is the reading the paper itself uses (k = 1 is called the 'limit case', correction is k > 1). Nat.Perfect/Nat.Abundant agree with the paper's all-divisor definitions for n > 0. Disproof (k = 1) is exact

## `Mathlib2.ab_prime_mul_prime_abundant_disproof`

Task 3(b) literally: product of two primes is abundant. FALSE (2*3 = 6 is perfect).

```lean
¬∀ (p q : ℕ), Nat.Prime p → Nat.Prime q → (p * q).Abundant
```
- 结论：证伪
- 层级：agent
- 来源：paper（s40753-021-00140-1 p.28 Appendix 2 Task 3(b)）
- 完成者：paper_2
- 尝试次数：1
- 被引用：0 次
- 分数：4
- 复核（reviewer_2）：faithful — Task 3(b) verbatim: 'If p1 and p2 are primes, then p1p2 is abundant'. Lean allows p = q, as the paper's wording does (no distinctness stated); the statement is false in every case so the reading does not matter. Important caveat: Appendix 2 lists this under 'Tasks' as a statement for students to ass

## `Mathlib2.an_div_add_div_ge_two_ne_disproof`

[suspected false] a/b + b/a ≥ 2 assuming only a, b nonzero (fails for opposite signs).

```lean
¬∀ (a b : ℝ), a ≠ 0 → b ≠ 0 → 2 ≤ a / b + b / a
```
- 结论：证伪
- 层级：agent
- 来源：conjecture
- 完成者：prover_4
- 尝试次数：1
- 被引用：0 次
- 分数：4

## `Mathlib2.an_sum_sq_range_closed_disproof`

[suspected false] off-by-one closed form for the sum of squares below n.

```lean
¬∀ (n : ℕ), ∑ i ∈ Finset.range n, i ^ 2 = n * (n + 1) * (2 * n + 1) / 6
```
- 结论：证伪
- 层级：agent
- 来源：conjecture
- 完成者：prover_5
- 尝试次数：1
- 被引用：0 次
- 分数：4

## `Mathlib2.nt_euler_poly_prime_disproof`

[suspected false] Euler's polynomial n^2+n+41 is always prime (fails at n = 40).

```lean
¬∀ (n : ℕ), Nat.Prime (n ^ 2 + n + 41)
```
- 结论：证伪
- 层级：agent
- 来源：conjecture
- 完成者：prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：4

## `Mathlib2.nt_gcd_factorial_succ_add_one_disproof`

[suspected false] n!+1 and (n+1)!+1 are always coprime (fails at n = 0, where both are 2).

```lean
¬∀ (n : ℕ), (n.factorial + 1).gcd ((n + 1).factorial + 1) = 1
```
- 结论：证伪
- 层级：agent
- 来源：conjecture
- 完成者：prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：4

## `Mathlib2.p3_thm1_disproof`

Theorem 1 as literally written: S_p = 3 mod p if p = 1,4 mod 5 and S_p = 1 mod p if p = 2,3 mod 5

```lean
¬∀ (p : ℕ), Nat.Prime p → 5 < p → (p % 5 = 1 ∨ p % 5 = 4 → ↑(Mathlib2.p3_fibsum p) ≡ 3 [ZMOD ↑p]) ∧ (p % 5 = 2 ∨ p % 5 = 3 → ↑(Mathlib2.p3_fibsum p) ≡ 1 [ZMOD ↑p])
```
- 结论：证伪
- 层级：agent
- 来源：paper（arXiv:2504.09938 Theorem 1）
- 完成者：paper_3
- 尝试次数：1
- 被引用：0 次
- 分数：4
- 依赖：`p3_fibsum`
- 复核（reviewer_3）：faithful — Read v3 HTML myself (and v1, v2: same residues in all three versions). Printed: p>5 prime, S_p = 3 mod p if p=1,4 mod 5; 1 mod p if p=2,3 mod 5, with S_n=F_1+...+F_n, F_1=F_2=1. Lean is the literal statement, not a straw man. Independent Python for all 43 primes 5<p<200: literal reading holds for NO

## `Mathlib2.p4_thm1_v_step_disproof`

Claim made inside the proof of Theorem 1(v), formalized literally: if B is a positive integer and 2^(k+2) > 3B+1 then x(2^(2k+2)) > B. (Numerically false: k=1, B=2 gives x(16) = -15.)

```lean
¬∀ (B k : ℕ), 0 < B → 3 * B + 1 < 2 ^ (k + 2) → ↑B < Mathlib2.p4_x (2 ^ (2 * k + 2))
```
- 结论：证伪
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 proof of Theorem 1(v)）
- 完成者：paper_4
- 尝试次数：1
- 被引用：0 次
- 分数：4
- 依赖：`p4_x`、`p4_x_block`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). The printed sentence is: 'Indeed, taking into account Remark 1, if B is an arbitrary positive integer and k is such that 2^(k+2)>3B+1 then x(2^(2k+2))>B.' The Lean statement is a literal transcription and is false exactly for k=1

## `Mathlib2.r3_hardy_inequality_finite_s1h3_disproof`

r3_hardy_inequality_finite 的证明骨架中第 3 个空洞

```lean
¬∀ (T B Q : ℝ), 0 ≤ T → T ≤ 2 * Q → Q ^ 2 ≤ T * B → T ≤ 4 * B
```
- 结论：证伪
- 层级：agent
- 来源：decomposition（r3_hardy_inequality_finite）
- 完成者：r3_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：4

## `Mathlib2.r3_imo1990_sq_dvd_two_pow_add_one_s1h1_disproof`

r3_imo1990_sq_dvd_two_pow_add_one 的证明骨架中第 1 个空洞

```lean
¬∀ (c m q : ℕ), Nat.Prime q → q ∣ m → (∀ (r : ℕ), Nat.Prime r → r ∣ m → q ≤ r) → q ∣ 2 ^ (c * m) + 1 → q ∣ 2 ^ (2 * c) - 1
```
- 结论：证伪
- 层级：agent
- 来源：decomposition（r3_imo1990_sq_dvd_two_pow_add_one）
- 完成者：r3_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：4

## `Mathlib2.ab_eight_not_perfect`

8 is not perfect.

```lean
¬Nat.Perfect 8
```
- 结论：证明
- 层级：agent
- 来源：paper（s40753-021-00140-1 p.19）
- 完成者：paper_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 复核（reviewer_2）：faithful — p.19: a student 'found that 8 was not a perfect number'. Lean: not Nat.Perfect 8 (divisors sum 15, not 16). Exact match; it is a reported student finding rather than a theorem of the paper.

## `Mathlib2.ab_fine_shift`

Shift of a fine function by a natural number is fine.

```lean
∀ (f : ℝ → ℝ) (k : ℕ), (∀ (n : ℤ), f ↑n = 0) → ∀ (n : ℤ), (fun x => f (x - ↑k)) ↑n = 0
```
- 结论：证明
- 层级：agent
- 来源：paper（s40753-021-00140-1 p.28 Appendix 2 Task 2(b)）
- 完成者：paper_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 复核（reviewer_2）：faithful — Appendix 2 Task 2(b): g(x) = f(x - k) for some k in N, f fine, prove g fine. Lean quantifies universally over k : N (correct reading of 'for some k' in a definition) and inlines fine and g. k = 0 is included in Lean, harmless whichever N convention the paper uses. No other differences.

## `Mathlib2.ab_perfect_one_mul_not_abundant`

The task statement fails at k = 1 for every perfect n.

```lean
∀ (n : ℕ), n.Perfect → ¬(1 * n).Abundant
```
- 结论：证明
- 层级：agent
- 来源：paper（s40753-021-00140-1 p.9; 11 Table 2 step [1]）
- 完成者：paper_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 复核（reviewer_2）：faithful — Table 2 step [1] 'False for k = 1'. Lean proves the universal form: for every perfect n, 1*n is not abundant, which is the reason the paper's statement fails at k = 1 (slightly more than the bare existence of a counterexample; non-vacuous given ab_perfect_six). Harmless strengthening; transcription 

## `Mathlib2.ab_perfect_twenty_eight`

28 is perfect.

```lean
Nat.Perfect 28
```
- 结论：证明
- 层级：agent
- 来源：paper（s40753-021-00140-1 p.17）
- 完成者：paper_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 复核（reviewer_2）：faithful — p.17 names 28 as a perfect number chosen by students, checked by 'sum of their divisors was double the original numbers'. Nat.Perfect 28 is that claim. The 'original' uses an ellipsis joining two adjacent sentences but does not change meaning.

## `Mathlib2.ab_preserved_mul`

If A is closed under multiplication and f, g are preserved in A then f × g is preserved in A.

```lean
∀ (f g : ℝ → ℝ) (A : Set ℝ), (∀ x ∈ A, ∀ y ∈ A, x * y ∈ A) → f '' A ⊆ A → g '' A ⊆ A → (fun x => f x * g x) '' A ⊆ A
```
- 结论：证明
- 层级：agent
- 来源：paper（s40753-021-00140-1 p.28 Appendix 2 Task 4(b)）
- 完成者：paper_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 复核（reviewer_2）：faithful — Appendix 2 Task 4(b). Lean encodes 'preserved in A' as f '' A ⊆ A, reading the paper's 'f(A) ⊂ A' as non-strict inclusion (standard, but a strict reading would give a different statement), and closure of A under multiplication and pointwise product exactly as stated. The paper defines 'preserved' fo

## `Mathlib2.ab_six_le_of_perfect`

6 is the smallest perfect number.

```lean
∀ (n : ℕ), n.Perfect → 6 ≤ n
```
- 结论：证明
- 层级：agent
- 来源：paper（s40753-021-00140-1 p.17）
- 完成者：paper_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 复核（reviewer_2）：faithful — p.17 parenthetical '6 (the smallest perfect number)'. Lean: every perfect n satisfies 6 <= n, which together with ab_perfect_six is exactly minimality; Nat.Perfect excludes 0 so the bound is not broken by n = 0. No differences.

## `Mathlib2.ab_sqrt_three_add_sqrt_five`

sqrt 3 + sqrt 5 < 4.

```lean
√3 + √5 < 4
```
- 结论：证明
- 层级：agent
- 来源：paper（s40753-021-00140-1 p.28 Appendix 2 Task 1）
- 完成者：paper_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 复核（reviewer_2）：faithful — Appendix 2 Task 1 'Prove that sqrt 3 + sqrt 5 < 4' vs Real.sqrt 3 + Real.sqrt 5 < 4. Exact match, no differences.
- 复核（reviewer_2）：faithful — Appendix 2 Task 1 'Prove that sqrt 3 + sqrt 5 < 4' vs Real.sqrt 3 + Real.sqrt 5 < 4. Exact match, no differences.

## `Mathlib2.ab_t2_one_mem_divisors`

Table 2 step 7: 1 is a divisor of kn.

```lean
∀ (n k : ℕ), n.Perfect → 1 < k → 1 ∈ (k * n).divisors
```
- 结论：证明
- 层级：agent
- 来源：paper（s40753-021-00140-1 p.11 Table 2 step [7]）
- 完成者：paper_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 复核（reviewer_2）：faithful — Table 2 step [7]: 1 is a divisor of kn. Lean: n perfect, 1 < k implies 1 in Nat.divisors (k*n); the hypotheses are just the proof's context and guarantee kn != 0 (needed because Nat.divisors 0 is empty). No differences.

## `Mathlib2.ab_t2_sum_mul_divisors`

Table 2 step 8: sum of k d_i over divisors d_i of perfect n equals 2kn.

```lean
∀ (n k : ℕ), n.Perfect → ∑ d ∈ n.divisors, k * d = 2 * (k * n)
```
- 结论：证明
- 层级：agent
- 来源：paper（s40753-021-00140-1 p.11 Table 2 steps [4],[8]）
- 完成者：r3_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 复核（reviewer_2）：faithful — Table 2 steps [4],[8]: sum of d_i = 2n hence sum of k d_i = 2kn, the d_i being all divisors of perfect n. Lean: for perfect n and any k, sum over Nat.divisors n of k*d = 2*(k*n). Holds for all k rather than only k > 1; harmless. Transcription matches.

## `Mathlib2.alg_artin_schreier_irreducible_zmod`

The Artin–Schreier polynomial X^p - X - 1 is irreducible over ZMod p — if α is a root in an extension then the roots are α + i (i ∈ F_p), so all irreducible factors have the same degree d with d ∣ p; d = 1 is impossible since a^p - a - 1 = -1 ≠ 0 for a ∈ F_p.

```lean
∀ (p : ℕ) [inst : Fact (Nat.Prime p)], Irreducible (Polynomial.X ^ p - Polynomial.X - 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_10
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`alg_artin_schreier_irreducible_zmod_s1h1`、`alg_artin_schreier_irreducible_zmod_s1h2`、`alg_artin_schreier_irreducible_zmod_s1h3`、`alg_artin_schreier_irreducible_zmod_s1h4`

## `Mathlib2.alg_card_eq_two_of_two_conj_classes`

A finite group with exactly two conjugacy classes has order 2 — the classes are {1} and G \ {1}, whose size |G| - 1 divides |G| by orbit-stabilizer, forcing |G| = 2.

```lean
∀ (G : Type u_1) [inst : Group G] [Finite G], Nat.card (ConjClasses G) = 2 → Nat.card G = 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.alg_card_le_two_of_mulAut_trivial`

A finite group with trivial automorphism group has at most 2 elements — inner automorphisms trivial gives G abelian; inversion trivial gives exponent 2; so G is an F_2-vector space, and if its dimension is ≥ 2 swapping two basis vectors is a nontrivial automorphism.

```lean
∀ (G : Type u_1) [inst : Group G] [Finite G], (∀ (f : MulAut G), f = 1) → Nat.card G ≤ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_6
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.alg_card_prime_of_subgroups_trivial`

A group whose only subgroups are ⊥ and ⊤ is trivial or (finite) of prime order — any g ≠ 1 generates G so G is cyclic; ℤ has proper subgroups so G is finite, and a cyclic group of composite order has a proper subgroup.

```lean
∀ (G : Type u_1) [inst : Group G], (∀ (H : Subgroup G), H = ⊥ ∨ H = ⊤) → Nat.card G = 1 ∨ Nat.Prime (Nat.card G)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.alg_card_sq_eq_one_zmod_two_pow`

For k ≥ 3 the congruence x² = 1 mod 2^k has exactly four solutions (±1 and 2^(k-1) ± 1) — 2^k | (x-1)(x+1) with gcd(x-1, x+1) = 2 forces 2^(k-1) | x - 1 or 2^(k-1) | x + 1.

```lean
∀ (k : ℕ), 3 ≤ k → Nat.card { x // x ^ 2 = 1 } = 4
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_6
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.alg_card_two_pow_of_mul_self_eq_one`

A finite group in which every element squares to 1 has order a power of 2 — it is a 2-group (IsPGroup 2), then use IsPGroup.iff_card; or Cauchy's theorem for an odd prime divisor.

```lean
∀ (G : Type u_1) [inst : Group G] [Finite G], (∀ (g : G), g * g = 1) → ∃ k, Nat.card G = 2 ^ k
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.alg_isunit_one_sub_mul_comm`

In any ring, if 1 - ab is a unit then so is 1 - ba — if c is the inverse of 1 - ab then 1 + b*c*a is a two-sided inverse of 1 - ba.

```lean
∀ (R : Type u_1) [inst : Ring R] (a b : R), IsUnit (1 - a * b) → IsUnit (1 - b * a)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_6
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.alg_odd_card_order_two_of_even_card`

In a finite group of even order the number of elements of order exactly 2 is odd — pair g with g⁻¹: the elements with g ≠ g⁻¹ come in pairs, so |{g : g² = 1}| is even, and removing the identity leaves an odd number.

```lean
∀ (G : Type u_1) [inst : Group G] [Finite G], Even (Nat.card G) → Odd (Nat.card { g // orderOf g = 2 })
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.alg_perm_eq_mul_two_involutions`

Every permutation of a finite set is a product of two involutions — on each cycle (x, σx, …, σ^{m-1}x) define a as the reflection σ^i x ↦ σ^{-i} x; then a is an involution and a σ a = σ⁻¹, so b = a σ satisfies b² = 1 and σ = a b.

```lean
∀ (n : ℕ) (σ : Equiv.Perm (Fin n)), ∃ a b, a * a = 1 ∧ b * b = 1 ∧ σ = a * b
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_10
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`alg_perm_eq_mul_two_involutions_s1h1`、`alg_perm_eq_mul_two_involutions_s2h2`

## `Mathlib2.alg_perm_fin_center_eq_bot`

The center of the symmetric group S_n is trivial for n ≥ 3 — if σ i = j ≠ i pick k ∉ {i, j}; then σ does not commute with the transposition swap j k.

```lean
∀ (n : ℕ), 3 ≤ n → Subgroup.center (Equiv.Perm (Fin n)) = ⊥
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_6
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.alg_ring_comm_of_pow_three_eq_self`

A ring in which x³ = x for all x is commutative — show 6 = 0 and 3(x² + x) = 0, squares are central (via idempotents e = x² and (e y - e y e)² = 0 implies nilpotents vanish), then x = x³ - ... combine 3x(x+1) and 2-torsion parts to get commutativity.

```lean
∀ (R : Type u_1) [inst : Ring R], (∀ (x : R), x ^ 3 = x) → ∀ (x y : R), x * y = y * x
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_6
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.alg_three_consecutive_pow_mul_comm`

If (ab)^i = a^i b^i for three consecutive exponents i then the group is abelian (Herstein) — from n and n+1 get a^n b = b a^n, from n+1 and n+2 get a^(n+1) b = b a^(n+1), then cancel.

```lean
∀ (G : Type u_1) [inst : Group G] (n : ℕ), (∀ (a b : G), (a * b) ^ n = a ^ n * b ^ n) → (∀ (a b : G), (a * b) ^ (n + 1) = a ^ (n + 1) * b ^ (n + 1)) → (∀ (a b : G), (a * b) ^ (n + 2) = a ^ (n + 2) * b ^ (n + 2)) → ∀ (a b : G), a * b = b * a
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.alg_unique_right_inverse_is_left_inverse`

In a ring, if a has a unique right inverse b then b is also a left inverse — apply uniqueness to c = b + (1 - b*a), which satisfies a*c = 1.

```lean
∀ (R : Type u_1) [inst : Ring R] (a b : R), a * b = 1 → (∀ (c : R), a * c = 1 → c = b) → b * a = 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.an2_alt_sum_choose_mul_pow_eq_zero`

The n-th finite difference of a monomial of degree m < n vanishes: sum_k (-1)^k C(n,k) k^m = 0.

```lean
∀ (n m : ℕ), m < n → ∑ k ∈ Finset.range (n + 1), (-1) ^ k * ↑(n.choose k) * ↑k ^ m = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_b
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.an2_card_no_consecutive_fib_v3`

The number of subsets of {0,...,n-1} containing no two consecutive integers is the Fibonacci number F_{n+2}.

```lean
∀ (n : ℕ), {s ∈ (Finset.range n).powerset | ∀ i ∈ s, i + 1 ∉ s}.card = Nat.fib (n + 2)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_e
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.an2_chebyshev_index_weighted`

Chebyshev sum inequality against the index sequence: for a monotone real sequence a, (n-1) * sum_{i<n} a_i ≤ 2 * sum_{i<n} i * a_i.

```lean
∀ (a : ℕ → ℝ), Monotone a → ∀ (n : ℕ), (↑n - 1) * ∑ i ∈ Finset.range n, a i ≤ 2 * ∑ i ∈ Finset.range n, ↑i * a i
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_a
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.an2_cyclic_div_ge_card`

Cyclic ratio inequality for n+1 positive reals: x_0/x_1 + x_1/x_2 + ... + x_{n-1}/x_n + x_n/x_0 ≥ n+1. Generalizes Mathlib2.an_cyclic_div_ge_three (n = 2).

```lean
∀ (n : ℕ) (x : ℕ → ℝ), (∀ (i : ℕ), 0 < x i) → ↑n + 1 ≤ ∑ i ∈ Finset.range n, x i / x (i + 1) + x n / x 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_c
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.an2_harmonic_two_pow_ge_v3`

Oresme's bound: the harmonic number H_{2^n} is at least 1 + n/2.

```lean
∀ (n : ℕ), 1 + ↑n / 2 ≤ ∑ i ∈ Finset.range (2 ^ n), 1 / (↑i + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_e
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.an2_nesbitt_general`

Nesbitt's inequality for N = n+2 positive reals with sum S: sum a_i/(S - a_i) ≥ N/(N-1). Generalizes Mathlib2.an_nesbitt (n = 1).

```lean
∀ (n : ℕ) (a : ℕ → ℝ), (∀ (i : ℕ), 0 < a i) → (↑n + 2) / (↑n + 1) ≤ ∑ i ∈ Finset.range (n + 2), a i / (∑ j ∈ Finset.range (n + 2), a j - a i)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_b
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.an2_num_derangements_bounds_v3`

For N ≥ 2 the derangement number satisfies N!/3 ≤ D_N ≤ N!/2.

```lean
∀ (n : ℕ), (n + 2).factorial ≤ 3 * numDerangements (n + 2) ∧ 2 * numDerangements (n + 2) ≤ (n + 2).factorial
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_d
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.an2_pow_self_le_three_pow_mul_factorial`

n! ≥ (n/3)^n, stated as n^n ≤ 3^n * n!. Induction using (n+1)^n ≤ 3 n^n.

```lean
∀ (n : ℕ), n ^ n ≤ 3 ^ n * n.factorial
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_c
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`an2_succ_pow_lt_three_mul_pow`

## `Mathlib2.an2_sum_sqrt_le_sqrt_card_mul_sum`

n-term QM-AM in sqrt form: sum of sqrt(a_i) ≤ sqrt(n * sum a_i). Generalizes Mathlib2.an_sqrt_add_le_sqrt_two_mul (the case n = 2).

```lean
∀ (n : ℕ) (a : ℕ → ℝ), (∀ (i : ℕ), 0 ≤ a i) → ∑ i ∈ Finset.range n, √(a i) ≤ √(↑n * ∑ i ∈ Finset.range n, a i)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_b
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.an_amgm_three_cube`

AM-GM for three nonnegative reals in cubed form.

```lean
∀ (a b c : ℝ), 0 ≤ a → 0 ≤ b → 0 ≤ c → a * b * c ≤ ((a + b + c) / 3) ^ 3
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_5
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.an_card_lt_pairs`

The number of pairs (i,j) with i<j<n is n(n-1)/2.

```lean
∀ (n : ℕ), {p ∈ Finset.range n ×ˢ Finset.range n | p.1 < p.2}.card = n * (n - 1) / 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_5
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.an_cyclic_div_ge_three`

For positive reals a, b, c: a/b + b/c + c/a ≥ 3.

```lean
∀ (a b c : ℝ), 0 < a → 0 < b → 0 < c → 3 ≤ a / b + b / c + c / a
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.an_nesbitt`

Nesbitt's inequality for positive reals.

```lean
∀ (a b c : ℝ), 0 < a → 0 < b → 0 < c → 3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.an_schur_deg_one`

Schur's inequality (t = 1) for nonnegative reals.

```lean
∀ (a b c : ℝ), 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_4
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.an_sqrt_add_le_sqrt_two_mul`

For nonnegative a, b: sqrt a + sqrt b ≤ sqrt(2(a+b)).

```lean
∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → √a + √b ≤ √(2 * (a + b))
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.an_sum_cubes_eq_sq_sum`

Nicomachus: the sum of the first n cubes equals the square of the sum of the first n integers.

```lean
∀ (n : ℕ), ∑ i ∈ Finset.range (n + 1), i ^ 3 = (∑ i ∈ Finset.range (n + 1), i) ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.an_sum_fib_odd`

Sum of the first n odd-indexed Fibonacci numbers is F_{2n}.

```lean
∀ (n : ℕ), ∑ i ∈ Finset.range n, Nat.fib (2 * i + 1) = Nat.fib (2 * n)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.an_sum_fib_sq`

Sum of squares of Fibonacci numbers F_0..F_n equals F_n * F_{n+1}.

```lean
∀ (n : ℕ), ∑ i ∈ Finset.range (n + 1), Nat.fib i ^ 2 = Nat.fib n * Nat.fib (n + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.an_sum_mul_choose`

Sum over k ≤ m of k*C(m,k) equals m*2^(m-1), stated with m = n+1.

```lean
∀ (n : ℕ), ∑ k ∈ Finset.range (n + 2), k * (n + 1).choose k = (n + 1) * 2 ^ n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.an_sum_mul_two_pow`

sum_{i≤n} i*2^i = (n-1)*2^(n+1) + 2, rearranged to avoid natural subtraction.

```lean
∀ (n : ℕ), ∑ i ∈ Finset.range (n + 1), i * 2 ^ i + 2 ^ (n + 1) = n * 2 ^ (n + 1) + 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_5
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.an_telescoping_inv_mul`

Telescoping sum: sum_{i<n} 1/((i+1)(i+2)) = n/(n+1).

```lean
∀ (n : ℕ), ∑ i ∈ Finset.range n, 1 / ((↑i + 1) * (↑i + 2)) = ↑n / (↑n + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.ana_continuous_additive_linear`

Cauchy's functional equation: a continuous additive function on ℝ is linear — additivity gives f(q) = q f(1) for rational q, and both sides are continuous so they agree on the closure of ℚ (or package f as a continuous AddMonoidHom and use map_real_smul).

```lean
∀ (f : ℝ → ℝ), Continuous f → (∀ (x y : ℝ), f (x + y) = f x + f y) → ∀ (x : ℝ), f x = f 1 * x
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_8
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.ana_exp_ge_cubic_taylor`

The cubic Taylor polynomial of exp is a lower bound on all of ℝ (odd degree) — g = exp - T3 has g' = exp - T2 ≥ ... ; iterate: exp - (1+x) ≥ 0 everywhere, so exp - T2 is increasing with zero at 0, so exp - T3 has a minimum 0 at 0.

```lean
∀ (x : ℝ), 1 + x + x ^ 2 / 2 + x ^ 3 / 6 ≤ Real.exp x
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.ana_fenchel_young_exp`

Fenchel–Young inequality for the conjugate pair exp and b log b - b — apply 1 + t ≤ exp t with t = a - log b and multiply by b = exp(log b).

```lean
∀ (a b : ℝ), 0 < b → a * b ≤ Real.exp a + b * Real.log b - b
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_8
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.ana_hasSum_inv_mul_succ`

The telescoping series sum 1/((n+1)(n+2)) equals 1 — partial sums are 1 - 1/(N+1) by induction; conclude with hasSum_iff_tendsto_nat_of_nonneg.

```lean
HasSum (fun n => 1 / ((↑n + 1) * (↑n + 2))) 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.ana_integral_x_mul_exp`

The integral of x e^x over [0,1] is 1 — the antiderivative is (x-1)e^x; apply the fundamental theorem of calculus (integral_eq_sub_of_hasDerivAt).

```lean
∫ (x : ℝ) in 0..1, x * Real.exp x = 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.ana_integral_x_mul_sin`

The integral of x sin x over [0,π] is π — the antiderivative is sin x - x cos x; apply the fundamental theorem of calculus.

```lean
∫ (x : ℝ) in 0..Real.pi, x * Real.sin x = Real.pi
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.ana_log_one_add_ge_quadratic`

log(1+x) ≥ x - x^2/2 for x ≥ 0 — the difference vanishes at 0 and has derivative 1/(1+x) - 1 + x = x^2/(1+x) ≥ 0, so it is monotone on [0,∞).

```lean
∀ (x : ℝ), 0 ≤ x → x - x ^ 2 / 2 ≤ Real.log (1 + x)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.ana_monotone_additive_linear`

A monotone additive function on ℝ is linear — f(q) = q f(1) on rationals; for real x squeeze between rationals p < x < q: p f(1) ≤ f(x) ≤ q f(1) (f(1) ≥ 0 by monotonicity), and let p, q → x.

```lean
∀ (f : ℝ → ℝ), Monotone f → (∀ (x y : ℝ), f (x + y) = f x + f y) → ∀ (x : ℝ), f x = f 1 * x
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_9
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.ana_one_add_inv_pow_mono`

The sequence (1 + 1/n)^n is nondecreasing — AM-GM on n copies of (1 + 1/n) and one copy of 1, or equivalently Bernoulli's inequality applied to (1 - 1/(n+1)^2)^(n+1) ≥ 1 - 1/(n+1); n = 0 is trivial.

```lean
∀ (n : ℕ), (1 + 1 / ↑n) ^ n ≤ (1 + 1 / (↑n + 1)) ^ (n + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_8
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`an2_one_add_inv_pow_strict_mono`

## `Mathlib2.ana_sin_le_parabola`

On [0,π] the sine lies below the parabola through (0,0), (π/2,1), (π,0) — by symmetry reduce to [0,π/2]; there h = parabola - sin has h(0)=h(π/2)=0, h'(π/2)=0 and h'' = sin x - 8/π^2 changes sign once, so h' is decreasing then increasing to 0, forcing h to rise then fall, hence h ≥ 0.

```lean
∀ (x : ℝ), 0 ≤ x → x ≤ Real.pi → Real.sin x ≤ 4 * x * (Real.pi - x) / Real.pi ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.ana_sqrt_sub_sqrt_le_sqrt_abs`

The square root is 1/2-Hölder with constant 1 — WLOG y ≤ x; then (sqrt x - sqrt y)^2 ≤ (sqrt x - sqrt y)(sqrt x + sqrt y) = x - y, and take square roots.

```lean
∀ (x y : ℝ), 0 ≤ x → 0 ≤ y → |√x - √y| ≤ √|x - y|
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_8
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.ana_sqrt_two_rec_tendsto`

The nested radical sequence sqrt(2 + sqrt(2 + ...)) converges to 2 — show 0 ≤ a_n < 2 and the contraction 2 - a_{n+1} = (2 - a_n)/(2 + a_{n+1}) ≤ (2 - a_n)/2, so 0 ≤ 2 - a_n ≤ 2/2^n and squeeze.

```lean
∀ (a : ℕ → ℝ), a 0 = 0 → (∀ (n : ℕ), a (n + 1) = √(2 + a n)) → Filter.Tendsto a Filter.atTop (nhds 2)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_8
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`ana_sqrt_two_rec_closed_form`

## `Mathlib2.ana_tendsto_quadratic_ratio`

(n^2+1)/(2n^2+3) tends to 1/2 — divide numerator and denominator by n^2 and use 1/n^2 → 0, or bound |difference| = 1/(2(2n^2+3)) and squeeze.

```lean
Filter.Tendsto (fun n => (↑n ^ 2 + 1) / (2 * ↑n ^ 2 + 3)) Filter.atTop (nhds (1 / 2))
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.ana_tsum_inv_cube_le`

zeta(3) ≤ 5/4 — for n ≥ 3, 1/n^3 ≤ 1/((n-1)n(n+1)) = (1/2)(1/((n-1)n) - 1/(n(n+1))), which telescopes to 1/12; so every partial sum is ≤ 1 + 1/8 + 1/12 < 5/4, then use tsum_le_of_sum_le with summability from the p-series test.

```lean
∑' (n : ℕ), 1 / (↑n + 1) ^ 3 ≤ 5 / 4
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_8
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.arith_card_divisors_sq_le`

τ(n) ≤ 2√n — the map d ↦ min(d, n/d) is at most 2-to-1 from divisors into {1..⌊√n⌋}.

```lean
∀ (n : ℕ), n.divisors.card ^ 2 ≤ 4 * n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ab
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.arith_card_odd_choose`

Glaisher: the number of odd entries in row n of Pascal's triangle is 2^(number of binary ones of n) — induct on binary digits using C(2n,2k) ≡ C(n,k), C(2n,2k+1) even, C(2n+1,2k) ≡ C(2n+1,2k+1) ≡ C(n,k) mod 2 (Lucas).

```lean
∀ (n : ℕ), {k ∈ Finset.range (n + 1) | Odd (n.choose k)}.card = 2 ^ (Nat.digits 2 n).sum
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ab
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.arith_dvd_sum_coprime`

For n ≥ 3 the sum of the totatives of n is divisible by n — Uses Mathlib2.nt2_two_mul_sum_coprime_eq_mul_totient at step 1: 2·S = n·φ(n); φ(n) is even for n > 2 (Nat.totient_even), so S = n·(φ(n)/2).

```lean
∀ (n : ℕ), 3 ≤ n → n ∣ ∑ k ∈ Finset.range n with k.Coprime n, k
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_aa
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`nt2_two_mul_sum_coprime_eq_mul_totient`

## `Mathlib2.arith_dvd_two_pow_add_one_three_dvd`

If n > 1 divides 2^n + 1 then 3 | n — let p be the least prime factor of n; the order of 2 mod p divides gcd(2n, p-1) = 2 (n is odd), so p | 2² - 1 = 3.

```lean
∀ (n : ℕ), 1 < n → n ∣ 2 ^ n + 1 → 3 ∣ n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_cb
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.arith_even_gt_46_sum_two_abundant`

Every even integer greater than 46 is a sum of two abundant numbers — Uses Mathlib2.ab_perfect_mul_abundant with Mathlib2.ab_perfect_six at the key step: every multiple 6k with k > 1 is abundant; split n mod 6: n = 12 + (n-12), n = 20 + (n-20), or n = 40 + (n-40) with 20, 40 abundant and the other summand a multiple of 6 that is ≥ 12.

```lean
∀ (n : ℕ), Even n → 46 < n → ∃ a b, a.Abundant ∧ b.Abundant ∧ a + b = n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_aa
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`ab_abundant_def`、`ab_perfect_mul_abundant`、`ab_perfect_six`、`arith_abundant_mul`

## `Mathlib2.arith_even_perfect_mod_nine`

Every even perfect number other than 6 is ≡ 1 (mod 9) — Euclid–Euler gives n = 2^(q-1)(2^q-1) with q an odd prime; 2 has order 6 mod 9 and q-1 is even, check the three residues of q-1 mod 6.

```lean
∀ (n : ℕ), Even n → n.Perfect → n ≠ 6 → n % 9 = 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_aa
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`arith_even_perfect_last_digit_aux1`

## `Mathlib2.arith_fermat_prime_factor_mod_two_pow_add_two`

Lucas' strengthening: for n ≥ 2 every prime factor of the Fermat number F_n is ≡ 1 mod 2^(n+2) — Uses Mathlib2.nt2_fermat_number_prime_factor_form at step 1 to get p ≡ 1 mod 2^(n+1), hence p ≡ 1 mod 8, so 2 is a quadratic residue mod p (ZMod.exists_sq_eq_two_iff); a square root of 2 then has order 2^(n+2), which divides p - 1.

```lean
∀ (n p : ℕ), 2 ≤ n → Nat.Prime p → p ∣ 2 ^ 2 ^ n + 1 → p % 2 ^ (n + 2) = 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_cb
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`nt2_fermat_number_prime_factor_form`

## `Mathlib2.arith_least_odd_abundant`

945 is the least odd abundant number — for odd n < 945: n has at most 3 distinct prime factors unless n ≥ 3·5·7·11; bound σ(n)/n < ∏ p/(p-1) and handle the families 3^a5^b7^c < 945 (or a finite case check).

```lean
∀ (n : ℕ), Odd n → n.Abundant → 945 ≤ n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_aa
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.arith_liouville_sum_card_divisors_cube`

Liouville's identity Σ_{d|n} τ(d)³ = (Σ_{d|n} τ(d))² — both sides are multiplicative in n; on p^a it is Σ_{j=1}^{a+1} j³ = (Σ j)² (Nicomachus).

```lean
∀ (n : ℕ), ∑ d ∈ n.divisors, d.divisors.card ^ 3 = (∑ d ∈ n.divisors, d.divisors.card) ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ab
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.arith_mersenne_prime_factor`

Prime factors q of 2^p - 1 (p odd prime) satisfy q ≡ 1 mod 2p and q ≡ ±1 mod 8 — the order of 2 mod q is p so p | q-1, q odd gives 2p | q-1; 2 = (2^((p+1)/2))² mod q is a square, so q ≡ ±1 mod 8.

```lean
∀ (p q : ℕ), Nat.Prime p → p ≠ 2 → Nat.Prime q → q ∣ 2 ^ p - 1 → q % (2 * p) = 1 ∧ (q % 8 = 1 ∨ q % 8 = 7)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ab
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.arith_mul_sigma_le_sigma_mul`

If every prime factor of m divides n then mσ(n) ≤ σ(mn) — induct on m by peeling off a prime p | m: Uses Mathlib2.p5_sigma_prime_mul_of_dvd at each step (p | (m/p)·n since p | n) to get σ(p·(m/p)n) > pσ((m/p)n).

```lean
∀ (m n : ℕ), m ≠ 0 → n ≠ 0 → m.primeFactors ⊆ n.primeFactors → m * (ArithmeticFunction.sigma 1) n ≤ (ArithmeticFunction.sigma 1) (m * n)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_aa
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`ab_t2_mul_mem_divisors`

## `Mathlib2.arith_odd_dvd_sq_add_one_mod_four`

Every odd divisor of n² + 1 is ≡ 1 (mod 4) — Uses Mathlib2.nt2_prime_three_mod_four_dvd_sq_add_sq at step 1 (with b = 1) to show no prime ≡ 3 mod 4 divides n²+1; so all prime factors of d are ≡ 1 mod 4, and a product of such numbers is ≡ 1 mod 4 (induction on d).

```lean
∀ (n d : ℕ), d ∣ n ^ 2 + 1 → Odd d → d % 4 = 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_aa
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`nt2_prime_three_mod_four_dvd_sq_add_sq`

## `Mathlib2.arith_odd_perfect_not_dvd_105`

No odd perfect number is divisible by 105 — by Euler's form the exponents of 3 and 7 (≡ 3 mod 4) are even, so 3²·5·7² | n and σ(n)/n ≥ (13/9)(6/5)(57/49) > 2 (σ(n)/n is monotone under divisibility), contradiction.

```lean
∀ (n : ℕ), Odd n → n.Perfect → ¬105 ∣ n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_aa
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`ab_abundant_def`、`arith_abundant_mul`、`arith_odd_perfect_euler_form`

## `Mathlib2.arith_orderOf_two_zmod_three_pow`

2 is a primitive root modulo every power of 3: its order mod 3^(n+1) is 2·3^n = φ(3^(n+1)) — the order divides φ; Uses Mathlib2.nt2_lte_three_two_pow_three_pow_add_one at the key step: 2^(3^n) ≡ -1 ≠ 1 rules out divisors of 3^n, and the exact valuation v_3(2^(3^(n-1)) + 1) = n (with 3 ∤ 2^(3^(n-1)) - 1) rules out 2·3^(n-1).

```lean
∀ (n : ℕ), orderOf 2 = 2 * 3 ^ n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_aa
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`nt2_lte_three_two_pow_three_pow_add_one`

## `Mathlib2.arith_padicValNat_two_centralBinom`

v_2(C(2n,n)) equals the number of ones in the binary expansion of n — Kummer/Legendre: v_2 = s_2(n) + s_2(n) - s_2(2n) and s_2(2n) = s_2(n).

```lean
∀ (n : ℕ), padicValNat 2 n.centralBinom = (Nat.digits 2 n).sum
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ab
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.arith_perfect_dvd_perfect_eq`

A perfect number never properly divides another perfect number — write n = k·m; k = 0 is impossible, k = 1 gives equality, and for k > 1 Uses Mathlib2.ab_perfect_mul_abundant at the key step: k·m is abundant, contradicting perfection of n (Nat.Perfect excludes Abundant).

```lean
∀ (m n : ℕ), m.Perfect → n.Perfect → m ∣ n → m = n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_aa
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`ab_perfect_mul_abundant`

## `Mathlib2.arith_prime_mul_prime_deficient`

A product of two primes other than 6 is deficient — Uses Mathlib2.ab_prime_mul_prime_not_abundant at step 1 (not abundant); step 2: not perfect since (p+1)(q+1) = 2pq forces (p-1)(q-1) = 2, i.e. {p,q} = {2,3}, and p² is a prime power; conclude by Nat.deficient_iff_not_abundant_and_not_perfect.

```lean
∀ (p q : ℕ), Nat.Prime p → Nat.Prime q → p * q ≠ 6 → (p * q).Deficient
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_aa
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`ab_prime_mul_prime_not_abundant`

## `Mathlib2.arith_prod_divisors_sq`

The product of the divisors of m² is m^τ(m²) — Uses Mathlib2.nt2_prod_divisors_sq at step 1 with n = m²: (∏ d)² = (m²)^τ = (m^τ)², then take square roots in ℕ.

```lean
∀ (m : ℕ), 0 < m → ∏ d ∈ (m ^ 2).divisors, d = m ^ (m ^ 2).divisors.card
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_aa
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`nt2_prod_divisors_sq`

## `Mathlib2.arith_prod_properDivisors_eq_self_iff`

The product of the proper divisors of n ≥ 2 equals n iff n has exactly four divisors — with P the proper-divisor product, ∏ divisors = n·P; Uses Mathlib2.nt2_prod_divisors_sq at the key step: (nP)² = n^τ(n), so P = n iff n⁴ = n^τ(n) iff τ(n) = 4 (pow injective for n ≥ 2).

```lean
∀ (n : ℕ), 2 ≤ n → (∏ d ∈ n.properDivisors, d = n ↔ n.divisors.card = 4)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_aa
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`nt2_prod_divisors_sq`

## `Mathlib2.arith_sigma_le_mul_log`

σ(n) ≤ n(1 + ⌊log₂ n⌋) — σ(n) = Σ_{d|n} n/d ≤ Σ_{k ≤ n} ⌊n/k⌋·[k|n] ≤ n·H_n and H_n ≤ 1 + ⌊log₂ n⌋ by dyadic grouping.

```lean
∀ (n : ℕ), 0 < n → (ArithmeticFunction.sigma 1) n ≤ n * (Nat.log 2 n + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ab
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.arith_sum_lcm`

Σ_{k=1}^n lcm(k,n) = (n/2)(1 + Σ_{d|n} dφ(d)) — group k by g = gcd(k,n): lcm = n·(k/g) with k/g a totative of d = n/g; Uses Mathlib2.nt2_two_mul_sum_coprime_eq_mul_totient at the inner step for every d > 1 (twice the totative sum is dφ(d)); the d = 1 term contributes the extra 1.

```lean
∀ (n : ℕ), 0 < n → 2 * ∑ k ∈ Finset.Icc 1 n, k.lcm n = n * (1 + ∑ d ∈ n.divisors, d * d.totient)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_cb
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`nt2_two_mul_sum_coprime_eq_mul_totient`

## `Mathlib2.arith_sum_moebius_mul_card_divisors`

Σ_{d|n} μ(d)τ(n/d) = 1 — Dirichlet convolution μ * (ζ * ζ) = ζ, then unfold the convolution over divisorsAntidiagonal.

```lean
∀ (n : ℕ), 0 < n → ∑ d ∈ n.divisors, ArithmeticFunction.moebius d * ↑(n / d).divisors.card = 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ab
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.arith_sum_moebius_mul_totient`

Σ_{d|n} μ(d)φ(d) = ∏_{p|n} (2 - p) — sum over squarefree divisors of a multiplicative function expands as ∏_{p|n}(1 + μ(p)φ(p)) = ∏(1 - (p-1)).

```lean
∀ (n : ℕ), 0 < n → ∑ d ∈ n.divisors, ArithmeticFunction.moebius d * ↑d.totient = ∏ p ∈ n.primeFactors, (2 - ↑p)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ab
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.arith_sum_natAbs_moebius`

Σ_{d|n} |μ(d)| = 2^ω(n) — |μ(d)| is the indicator of squarefree d; squarefree divisors of n biject with subsets of n.primeFactors.

```lean
∀ (n : ℕ), 0 < n → ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d).natAbs = 2 ^ ArithmeticFunction.cardDistinctFactors n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ab
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.arith_sum_sigma_divisors`

Σ_{d|n} σ(d) = Σ_{d|n} (n/d)τ(d) — both are the Dirichlet convolution id * ζ * ζ evaluated at n (associativity/commutativity of convolution).

```lean
∀ (n : ℕ), ∑ d ∈ n.divisors, (ArithmeticFunction.sigma 1) d = ∑ d ∈ n.divisors, n / d * d.divisors.card
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ab
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.arith_totient_add_sigma_eq_two_mul_iff_prime`

Equality case of the Sandor–Atanassov inequality φ(n)+σ(n) ≥ 2n (Mathlib2.p5_lemma2): equality iff n is prime — for composite n with least prime factor p, σ(n) ≥ n + n/p + 1 and φ(n) ≥ n - n/p (count of multiples of p is not all non-coprime... use φ(n) ≥ n - Σ_{q|n} n/q carefully, or induct with Mathlib2.p5_sigma_prime_mul_of_dvd), giving strict inequality.

```lean
∀ (n : ℕ), 2 ≤ n → (n.totient + (ArithmeticFunction.sigma 1) n = 2 * n ↔ Nat.Prime n)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ab
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.arith_totient_dvd_self_iff`

φ(n) | n iff n = 1 or n = 2^a 3^b with a ≥ 1 — n/φ(n) = ∏ p/(p-1) must be an integer; for n>2 φ is even so 2 | n; the largest prime factor q>2 forces ∏(p-1) | ∏ p·…, compare 2-adic valuations: each odd prime contributes a factor 2 to φ, so at most one odd prime, and (q-1) | 2^a q forces q = 3.

```lean
∀ (n : ℕ), 0 < n → (n.totient ∣ n ↔ n = 1 ∨ ∃ a b, n = 2 ^ (a + 1) * 3 ^ b)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ab
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.arith_totient_pow_add_sigma_pow`

Power-mean extension of Sandor–Atanassov: φ(n)^k + σ(n)^k ≥ 2n^k for n ≥ 2 — Uses Mathlib2.p5_lemma2 at step 1 (φ + σ ≥ 2n), then convexity of x^k: ((a+b)/2)^k ≤ (a^k+b^k)/2 (inner_le_nnorm_mul_norm / add_pow_le_pow_mul_pow_of_add_eq_one, or induction on k via Chebyshev).

```lean
∀ (n k : ℕ), 2 ≤ n → 2 * n ^ k ≤ n.totient ^ k + (ArithmeticFunction.sigma 1) n ^ k
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_aa
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p5_lemma2`

## `Mathlib2.arith_two_mul_dvd_totient_pow_add_one`

2n divides φ(a^n + 1) for a > 1, n ≥ 1 — a is a unit mod N = a^n + 1 with a^n = -1 ≠ 1 and a^k < N - 1 for k < n, so its order is exactly 2n, and the order divides φ(N).

```lean
∀ (a n : ℕ), 1 < a → 0 < n → 2 * n ∣ (a ^ n + 1).totient
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_cb
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.arith_two_mul_totient_eq_self_iff`

φ(n) = n/2 iff n is a power of 2 with n ≥ 2 — n must be even; write n = 2^a m with m odd, then φ(n) = 2^(a-1) φ(m) so φ(m) = m forcing m = 1.

```lean
∀ (n : ℕ), 0 < n → (2 * n.totient = n ↔ ∃ k, n = 2 ^ (k + 1))
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ab
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.arith_two_pow_mod_self_ne_one`

For n ≥ 2, 2^n is never ≡ 1 (mod n) — if 2^n % n = 1 then n | 2^n - 1 and Uses Mathlib2.nt2_dvd_two_pow_sub_one_eq_one at this step to get n = 1, contradiction.

```lean
∀ (n : ℕ), 2 ≤ n → 2 ^ n % n ≠ 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_aa
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`nt2_dvd_two_pow_sub_one_eq_one`

## `Mathlib2.bld2_card_le_sum_of_prod_eq_one`

Uses Mathlib2.gen_an_amgm_finset_ordered_ring: with ∏ a = 1 the AM-GM inequality reads card^card ≤ (∑ a)^card; both bases are nonnegative, so for s nonempty taking card-th roots (pow_le_pow_left contrapositive) gives card ≤ ∑ a; s empty is trivial.

```lean
∀ (R : Type u_1) [inst : CommRing R] [inst_1 : LinearOrder R] [IsStrictOrderedRing R] (ι : Type u_2) (s : Finset ι) (a : ι → R), (∀ i ∈ s, 0 ≤ a i) → ∏ i ∈ s, a i = 1 → ↑s.card ≤ ∑ i ∈ s, a i
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.gen_an_amgm_finset_ordered_ring）
- 完成者：r7_prover_4
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`gen_an_amgm_finset_ordered_ring`

## `Mathlib2.bld2_edelstein_no_periodic_points`

Uses Mathlib2.top_edelstein_unique_fixed_point and Mathlib2.bld_edelstein_iterates_tendsto: X is nonempty, so there is a fixed point p and f^[m] x → p; along the subsequence m = n * k the iterates are constantly x, so x = p by uniqueness of limits.

```lean
∀ {X : Type u_1} [inst : MetricSpace X] [CompactSpace X] (f : X → X), (∀ (x y : X), x ≠ y → dist (f x) (f y) < dist x y) → ∀ (x : X) (n : ℕ), 0 < n → f^[n] x = x → f x = x
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.top_edelstein_unique_fixed_point, Mathlib2.bld_edelstein_iterates_tendsto）
- 完成者：r7_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld_edelstein_iterates_tendsto`、`top_edelstein_unique_fixed_point`

## `Mathlib2.bld2_fibsum_sum`

Uses Mathlib2.p3_prop1 twice: p3_fibsum i = fib (i+2) - 1, so the sum is (p3_fibsum (n+2) - fib 1 - fib 2) - n = fib (n+4) - 1 - 2 - n; or induct on n using p3_prop1 in the step.

```lean
∀ (n : ℕ), ∑ i ∈ Finset.Icc 1 n, Mathlib2.p3_fibsum i + n + 3 = Nat.fib (n + 4)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.p3_prop1）
- 完成者：r7_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p3_fibsum`、`p3_prop1`

## `Mathlib2.bld2_involution_iff_rank_add_rank`

Uses Mathlib2.bld_involution_rank_add_rank and Mathlib2.gen_lin_idempotent_rank_complement_field: forward is the involution rank identity; conversely put P = (1/2)(1 + A), so 1 - P = (1/2)(1 - A) and rank P + rank (1 - P) = n, which forces P idempotent (converse of rank complement), i.e. A*A = 1.

```lean
∀ (K : Type u_1) [inst : Field K] [CharZero K] (ι : Type u_2) [inst_2 : Fintype ι] [inst_3 : DecidableEq ι] (A : Matrix ι ι K), A * A = 1 ↔ (1 + A).rank + (1 - A).rank = Fintype.card ι
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_involution_rank_add_rank, Mathlib2.gen_lin_idempotent_rank_complement_field）
- 完成者：r7_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld2_idempotent_iff_rank_add_rank`、`bld_involution_rank_add_rank`

## `Mathlib2.bld2_involution_trace_eq_card`

Uses Mathlib2.bld_involution_trace_rank and Mathlib2.bld_involution_rank_add_rank: the trace formula gives 2 * rank (1 + A) = 2 * card ι in K, hence (CharZero) rank (1 + A) = card ι; the rank identity then gives rank (1 - A) = 0, so 1 - A = 0.

```lean
∀ (K : Type u_1) [inst : Field K] [CharZero K] (ι : Type u_2) [inst_2 : Fintype ι] [inst_3 : DecidableEq ι] (A : Matrix ι ι K), A * A = 1 → A.trace = ↑(Fintype.card ι) → A = 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_involution_trace_rank, Mathlib2.bld_involution_rank_add_rank）
- 完成者：r7_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld_involution_rank_add_rank`、`bld_involution_trace_rank`

## `Mathlib2.bld2_nonexpanding_left_inverse_isometry`

Uses Mathlib2.bld_surjective_nonexpanding_compact_isometry: f is surjective (right inverse g) and non-expanding, hence an isometry, hence injective; so g (f x) = x from f (g (f x)) = f x, and dist (g x) (g y) = dist (f (g x)) (f (g y)) = dist x y.

```lean
∀ {X : Type u_1} [inst : MetricSpace X] [CompactSpace X] (f g : X → X), (∀ (x y : X), dist (f x) (f y) ≤ dist x y) → (∀ (x : X), f (g x) = x) → Isometry g ∧ ∀ (x : X), g (f x) = x
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_surjective_nonexpanding_compact_isometry）
- 完成者：r7_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld_surjective_nonexpanding_compact_isometry`

## `Mathlib2.bld2_pisano_fib_even_eq`

Uses Mathlib2.p3_prop2: the period k divides 2n; being a period forces fib n ∣ fib k, hence n ∣ k (gcd property of Fibonacci numbers, n ≥ 3), so k = n or k = 2n; k = n is impossible because fib (n+1) ≡ fib (n-1) mod fib n and 1 < fib (n-1) < fib n for n ≥ 4.

```lean
∀ (n : ℕ), 4 ≤ n → 2 ∣ n → Mathlib2.p3_pisano (Nat.fib n) = 2 * n
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.p3_prop2）
- 完成者：r7_prover_4
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld2_pisano_fib_odd_eq_aux1`、`bld2_pisano_fib_odd_eq_aux2`、`p3_aux_period`、`p3_pisano`、`p3_prop2`

## `Mathlib2.bld2_sqrt_two_rec_viete_prod_gt`

Uses Mathlib2.bld_sqrt_two_rec_viete_prod: the partial product equals 1 / (2^n * sin (π / 2^(n+1))), and sin x < x for x > 0 gives 2^n * sin (π / 2^(n+1)) < π / 2.

```lean
∀ (a : ℕ → ℝ), a 0 = 0 → (∀ (n : ℕ), a (n + 1) = √(2 + a n)) → ∀ (n : ℕ), 2 / Real.pi < ∏ i ∈ Finset.range n, a (i + 1) / 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_sqrt_two_rec_viete_prod）
- 完成者：r7_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld_sqrt_two_rec_viete_prod`

## `Mathlib2.bld2_triangle_free_min_degree_le_half`

Uses Mathlib2.comb_degree_add_degree_le_of_triangle_free: if d = 0 trivial; otherwise a vertex v has a neighbour u and 2d ≤ deg u + deg v ≤ card V.

```lean
∀ (V : Type) [inst : Fintype V] [DecidableEq V] (G : SimpleGraph V) [inst_2 : DecidableRel G.Adj] [Nonempty V], G.CliqueFree 3 → ∀ (d : ℕ), (∀ (v : V), d ≤ G.degree v) → 2 * d ≤ Fintype.card V
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.comb_degree_add_degree_le_of_triangle_free）
- 完成者：r7_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`comb_degree_add_degree_le_of_triangle_free`

## `Mathlib2.bld2_tripotent_trace_sq_eq_rank`

Uses Mathlib2.gen_lin_idempotent_trace_eq_rank_field: A*A is idempotent, so trace (A*A) = rank (A*A); and rank (A*A) = rank A because A = A * (A*A) gives rank A ≤ rank (A*A) ≤ rank A.

```lean
∀ (K : Type u_1) [inst : Field K] (ι : Type u_2) [inst_1 : Fintype ι] [DecidableEq ι] (A : Matrix ι ι K), A * A * A = A → (A * A).trace = ↑A.rank
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.gen_lin_idempotent_trace_eq_rank_field）
- 完成者：r7_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`gen_lin_idempotent_trace_eq_rank_field`

## `Mathlib2.bld2_two_pow_mul_factorial_le_succ_pow`

Uses Mathlib2.gen_an_amgm_finset_ordered_ring (or Mathlib2.an2_amgm_range_pow): apply AM-GM to a i = i + 1 on Finset.range n: n^n * n! ≤ (n(n+1)/2)^n, i.e. 2^n * n^n * n! ≤ n^n * (n+1)^n; cancel n^n for n > 0.

```lean
∀ (n : ℕ), 2 ^ n * n.factorial ≤ (n + 1) ^ n
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.gen_an_amgm_finset_ordered_ring）
- 完成者：r7_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`gen_an_amgm_finset_ordered_ring`

## `Mathlib2.bld3_card_abelianization_of_card_prime_cube`

Uses Mathlib2.bld2_commutator_eq_center_of_card_prime_cube and Mathlib2.bld_center_card_of_card_prime_cube: Abelianization G = G ⧸ commutator G, the commutator subgroup equals the centre, which has order p; Lagrange gives index p^2.

```lean
∀ (p : ℕ), Nat.Prime p → ∀ (G : Type u_1) [inst : Group G], Nat.card G = p ^ 3 → (∃ a b, a * b ≠ b * a) → Nat.card (Abelianization G) = p ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_commutator_eq_center_of_card_prime_cube, Mathlib2.bld_center_card_of_card_prime_cube）
- 完成者：r8_prover_4
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld2_commutator_eq_center_of_card_prime_cube`、`bld_center_card_of_card_prime_cube`

## `Mathlib2.bld3_card_centralizer_of_card_prime_cube`

Uses Mathlib2.bld_center_card_of_card_prime_cube: the centralizer strictly contains the centre (order p, and it contains g) and is a proper subgroup (g not central), so by Lagrange its order is p^2.

```lean
∀ (p : ℕ), Nat.Prime p → ∀ (G : Type u_1) [inst : Group G], Nat.card G = p ^ 3 → (∃ a b, a * b ≠ b * a) → ∀ g ∉ Subgroup.center G, Nat.card ↥(Subgroup.centralizer {g}) = p ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_center_card_of_card_prime_cube）
- 完成者：r8_prover_4
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld2_card_conjClasses_of_card_prime_cube_aux1`

## `Mathlib2.bld3_compact_mutual_nonexpanding_surjections_isometry`

Uses Mathlib2.bld_surjective_nonexpanding_compact_isometry: g ∘ f is a non-expanding surjection of compact X, hence an isometry, so dist x x' = dist (g (f x)) (g (f x')) ≤ dist (f x) (f x') ≤ dist x x'.

```lean
∀ {X : Type u_1} [inst : MetricSpace X] [CompactSpace X] {Y : Type u_2} [inst_2 : MetricSpace Y] [CompactSpace Y] (f : X → Y) (g : Y → X), Function.Surjective f → (∀ (x x' : X), dist (f x) (f x') ≤ dist x x') → Function.Surjective g → (∀ (y y' : Y), dist (g y) (g y') ≤ dist y y') → Isometry f
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_surjective_nonexpanding_compact_isometry）
- 完成者：r8_prover_4
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld_surjective_nonexpanding_compact_isometry`

## `Mathlib2.bld3_dvd_fibsum_of_pisano_dvd`

Uses Mathlib2.p3_prop1 and Mathlib2.bld2_pisano_fib_odd_eq: if p3_pisano m = 0 then m = 0 and p3_fibsum 0 = 0; otherwise m is a multiple of a period (aux1), so fib (m + 2) ≡ fib 2 = 1 mod m and p3_fibsum m = fib (m + 2) - 1 ≡ 0.

```lean
∀ (m : ℕ), Mathlib2.p3_pisano m ∣ m → m ∣ Mathlib2.p3_fibsum m
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.p3_prop1, Mathlib2.bld2_pisano_fib_odd_eq）
- 完成者：r8_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`lib_pisano_dvd_iff_period`、`p3_fibsum`、`p3_pisano`、`p3_prop1_aux1`

## `Mathlib2.bld3_edelstein_iInter_range_iterate`

Uses Mathlib2.bld_edelstein_iterates_tendsto and Mathlib2.bld2_edelstein_no_periodic_points: p is in every range since f^[n] p = p; conversely if y = f^[n] (x_n) for all n, uniform convergence of the iterates to p (Dini applied to the monotone pointwise convergence from the library) gives dist y p < ε for every ε.

```lean
∀ {X : Type u_1} [inst : MetricSpace X] [CompactSpace X] (f : X → X), (∀ (x y : X), x ≠ y → dist (f x) (f y) < dist x y) → ∀ (p : X), f p = p → ⋂ n, Set.range f^[n] = {p}
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_edelstein_iterates_tendsto, Mathlib2.bld2_edelstein_no_periodic_points）
- 完成者：r8_prover_4
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld3_edelstein_iterates_tendsto_uniformly`

## `Mathlib2.bld3_hardy_means_tendsto_zero`

Uses Mathlib2.bld2_hardy_inequality_tsum: by Hardy the squares of the Cesàro means are summable, so they tend to 0, hence so do the means (continuity of sqrt / abs).

```lean
∀ (a : ℕ → ℝ), (Summable fun k => a k ^ 2) → Filter.Tendsto (fun k => (∑ i ∈ Finset.range (k + 1), a i) / (↑k + 1)) Filter.atTop (nhds 0)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_hardy_inequality_tsum）
- 完成者：r8_prover_4
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld2_hardy_inequality_tsum`

## `Mathlib2.bld3_iterate_shrinking_iterates_tendsto`

Uses Mathlib2.bld_edelstein_iterates_tendsto and Mathlib2.bld_iterate_shrinking_unique_fixed_point: n = 0 forces X subsingleton; otherwise apply Edelstein convergence to g = f^[n] (which fixes p) at each of the n starting points f^[r] x, r < n, and merge the n residue-class subsequences f^[n k + r] x = g^[k] (f^[r] x).

```lean
∀ {X : Type u_1} [inst : MetricSpace X] [CompactSpace X] (f : X → X) (n : ℕ), (∀ (x y : X), x ≠ y → dist (f^[n] x) (f^[n] y) < dist x y) → ∀ (p : X), f p = p → ∀ (x : X), Filter.Tendsto (fun k => f^[k] x) Filter.atTop (nhds p)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_edelstein_iterates_tendsto, Mathlib2.bld_iterate_shrinking_unique_fixed_point）
- 完成者：r8_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld_edelstein_iterates_tendsto`

## `Mathlib2.bld3_mantel_equality_colorable_two`

Uses Mathlib2.bld2_mantel_equality_regular and Mathlib2.bld_mantel_triangle_free: if there is no edge then n = 0; otherwise fix an edge u v: N(u) and N(v) are disjoint with |N(u)| + |N(v)| = n by regularity, so they partition V, and each is independent by triangle-freeness; colour by membership in N(u).

```lean
∀ (V : Type) [inst : Fintype V] [DecidableEq V] (G : SimpleGraph V) [inst_2 : DecidableRel G.Adj], G.CliqueFree 3 → 4 * G.edgeFinset.card = Fintype.card V ^ 2 → G.Colorable 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_mantel_equality_regular, Mathlib2.bld_mantel_triangle_free）
- 完成者：r8_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld3_mantel_equality_same_neighbors`

## `Mathlib2.bld3_pell_five_neg_one_solutions`

Uses Mathlib2.bld2_fib_odd_index_iff_five_sq_sub_four and Mathlib2.bld2_lucas_sq_sub_five_fib_sq: (2x)^2 + 4 = 5 (2y)^2, so 2y = fib (2m+1) and 2x = L_(2m+1) by the odd-index description and the Lucas–Fibonacci identity; fib (2m+1) even forces 3 ∣ 2m+1, i.e. 2m+1 = 6n+3.

```lean
∀ (x y : ℕ), x ^ 2 + 1 = 5 * y ^ 2 → ∃ n, 2 * y = Nat.fib (6 * n + 3) ∧ 2 * x = Mathlib2.p3_lucas (6 * n + 3)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_fib_odd_index_iff_five_sq_sub_four, Mathlib2.bld2_lucas_sq_sub_five_fib_sq）
- 完成者：r8_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld2_fib_odd_index_iff_five_sq_sub_four`、`bld2_lucas_sq_sub_five_fib_sq`、`p3_lucas`

## `Mathlib2.bld3_pisano_even`

Uses Mathlib2.bld2_pisano_fib_odd_eq and Mathlib2.r3_fib_iff_five_sq_pm_four_is_square_s1h1: let k be the Pisano period (if it is 0 done; else a period by bld2_pisano_fib_odd_eq_aux1), so fib k ≡ 0 and fib (k+1) ≡ 1 mod m; Cassini fib(k+1)^2 - fib(k+1) fib k - fib k^2 = (-1)^k then gives (-1)^k ≡ 1 mod m, and m ≥ 3 excludes k odd.

```lean
∀ (m : ℕ), 3 ≤ m → Even (Mathlib2.p3_pisano m)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_pisano_fib_odd_eq, Mathlib2.r3_fib_iff_five_sq_pm_four_is_square_s1h1）
- 完成者：r8_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`lib_pisano_dvd_iff_period`、`p3_pisano`、`r3_fib_iff_five_sq_pm_four_is_square_s1h1`

## `Mathlib2.bld3_pisano_fib_div_fib_tendsto_zero`

Uses Mathlib2.bld2_pisano_fib_dvd_four_mul: the Pisano period of fib n divides 4n so is at most 4n, while fib n grows at least like n^2 (e.g. fib (n+2) ≥ n^2/4 or exponentially), so the ratio is squeezed to 0; strengthens the liminf statement p3_cor1.

```lean
Filter.Tendsto (fun n => ↑(Mathlib2.p3_pisano (Nat.fib n)) / ↑(Nat.fib n)) Filter.atTop (nhds 0)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_pisano_fib_dvd_four_mul）
- 完成者：r8_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld2_pisano_fib_dvd_four_mul`、`p3_pisano`

## `Mathlib2.bld3_rank_involution_defect`

Uses Mathlib2.bld2_rank_add_rank_one_sub and Mathlib2.bld2_involution_iff_rank_add_rank: apply the idempotent-defect identity to B = (1/2) • (1 + A): 1 - B = (1/2) • (1 - A) and B - B * B = (1/4) • (1 - A * A), and nonzero scalars do not change rank; this refines the involution criterion.

```lean
∀ (K : Type u_1) [inst : Field K] [CharZero K] (ι : Type u_2) [inst_2 : Fintype ι] [inst_3 : DecidableEq ι] (A : Matrix ι ι K), (1 + A).rank + (1 - A).rank = Fintype.card ι + (1 - A * A).rank
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_rank_add_rank_one_sub, Mathlib2.bld2_involution_iff_rank_add_rank）
- 完成者：r8_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld2_rank_add_rank_one_sub`、`lib_matrix_rank_smul`

## `Mathlib2.bld3_self_summable_of_two_mul_dvd_fib`

Uses Mathlib2.p3_aux_period and Mathlib2.p3_remark2: write fib n = 2 n k; by the period lemma fib (2 + 2 n k) ≡ fib 2 = 1 mod fib n, so fib n ∣ fib (fib n + 2) - 1, which is self-summability by Remark 2 (e.g. n = 12, 24, 36).

```lean
∀ (n : ℕ), 2 ∣ n → 2 * n ∣ Nat.fib n → Mathlib2.p3_self_summable n
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.p3_aux_period, Mathlib2.p3_remark2）
- 完成者：r8_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p3_aux_period`、`p3_remark2`、`p3_self_summable`

## `Mathlib2.bld3_sq_card_le_sum_mul_sum_inv`

Uses Mathlib2.gen_an_amgm_finset_ordered_ring and Mathlib2.bld2_card_le_sum_of_prod_eq_one: AM-GM for a and for a⁻¹ gives n^n ∏ a ≤ (∑ a)^n and n^n ∏ a⁻¹ ≤ (∑ a⁻¹)^n; multiply (the products cancel) to get (n^2)^n ≤ ((∑ a)(∑ a⁻¹))^n and take n-th roots by monotonicity of powers.

```lean
∀ (K : Type u_1) [inst : Field K] [inst_1 : LinearOrder K] [IsStrictOrderedRing K] (ι : Type u_2) (s : Finset ι) (a : ι → K), (∀ i ∈ s, 0 < a i) → ↑s.card ^ 2 ≤ (∑ i ∈ s, a i) * ∑ i ∈ s, (a i)⁻¹
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.gen_an_amgm_finset_ordered_ring, Mathlib2.bld2_card_le_sum_of_prod_eq_one）
- 完成者：r8_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`gen_an_amgm_finset_ordered_ring`

## `Mathlib2.bld3_sqrt_two_rec_pi_limit`

Uses Mathlib2.bld2_sqrt_two_rec_defect_asymptotic: (2^n √(2 - a n)) = √(4^n (2 - a n)); compose the defect asymptotic 4^n (2 - a n) → π^2/4 with continuity of the square root, √(π^2/4) = π/2 (the classical nested-radical formula for π).

```lean
∀ (a : ℕ → ℝ), a 0 = 0 → (∀ (n : ℕ), a (n + 1) = √(2 + a n)) → Filter.Tendsto (fun n => 2 ^ n * √(2 - a n)) Filter.atTop (nhds (Real.pi / 2))
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_sqrt_two_rec_defect_asymptotic）
- 完成者：r8_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld2_sqrt_two_rec_defect_asymptotic`

## `Mathlib2.bld3_sqrt_two_rec_viete_prod_le`

Uses Mathlib2.bld_sqrt_two_rec_viete_prod and Mathlib2.bld2_sqrt_two_rec_viete_prod_gt: by the finite Viète product the product equals 1/(2^n sin x) with x = π/2^(n+1); sin x ≥ x - x^3/6 and 1/(1-t) ≤ 1 + 2t for t = x^2/6 ≤ 1/2 give the explicit O(4^-n) upper bound matching the library lower bound 2/π.

```lean
∀ (a : ℕ → ℝ), a 0 = 0 → (∀ (n : ℕ), a (n + 1) = √(2 + a n)) → ∀ (n : ℕ), ∏ i ∈ Finset.range n, a (i + 1) / 2 ≤ 2 / Real.pi + 2 * Real.pi / (3 * 4 ^ (n + 1))
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_sqrt_two_rec_viete_prod, Mathlib2.bld2_sqrt_two_rec_viete_prod_gt）
- 完成者：r8_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld_sqrt_two_rec_viete_prod`

## `Mathlib2.bld4_card_pow_prime_eq_one_ge_of_card_prime_cube`

Uses Mathlib2.bld3_pow_prime_mem_center_of_card_prime_cube, Mathlib2.bld3_mul_pow_prime_of_card_prime_cube and Mathlib2.bld_center_card_of_card_prime_cube: the p-th power map is a homomorphism φ : G →* center G (first two theorems); |ker φ| · |range φ| = p^3 and |range φ| ≤ |center G| = p by bld_center_card_of_card_prime_cube, so |ker φ| ≥ p^2, and ker φ is the set {g | g^p = 1}.

```lean
∀ (p : ℕ), Nat.Prime p → ∀ (G : Type u_1) [inst : Group G], Nat.card G = p ^ 3 → (∃ a b, a * b ≠ b * a) → p ≠ 2 → p ^ 2 ≤ Nat.card { g // g ^ p = 1 }
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld3_pow_prime_mem_center_of_card_prime_cube, Mathlib2.bld3_mul_pow_prime_of_card_prime_cube, Mathlib2.bld_center_card_of_card_prime_cube）
- 完成者：r9_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld4_pow_prime_monoidHom_center_of_card_prime_cube`、`bld_center_card_of_card_prime_cube`

## `Mathlib2.bld4_commuting_idempotents_rank_add`

Uses Mathlib2.bld2_commuting_idempotents_rank_join: A + B = (A + B − AB)(1 + AB), and 1 + AB is invertible with inverse 1 − (1/2)AB because (AB)^2 = AB (char ≠ 2); multiplying by a unit preserves rank, so rank(A + B) = rank(A + B − AB), and the cited join formula finishes.

```lean
∀ (K : Type u_1) [inst : Field K] [CharZero K] (ι : Type u_2) [inst_2 : Fintype ι] [DecidableEq ι] (A B : Matrix ι ι K), A * A = A → B * B = B → A * B = B * A → (A + B).rank + (A * B).rank = A.rank + B.rank
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_commuting_idempotents_rank_join）
- 完成者：r9_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld2_commuting_idempotents_rank_join`

## `Mathlib2.bld4_compact_mutual_isometric_embeddings_isometryEquiv`

Uses Mathlib2.bld3_compact_mutual_expanding_isometry: isometries are expanding (dist equality), so the cited theorem gives that f is a surjective isometry; an isometry is injective, so Equiv.ofBijective f packaged with hf is the IsometryEquiv.

```lean
∀ {X : Type u_1} [inst : MetricSpace X] [CompactSpace X] {Y : Type u_2} [inst_2 : MetricSpace Y] [CompactSpace Y] (f : X → Y) (g : Y → X), Isometry f → Isometry g → Nonempty (X ≃ᵢ Y)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld3_compact_mutual_expanding_isometry）
- 完成者：r9_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld3_compact_mutual_expanding_isometry`

## `Mathlib2.bld4_edelstein_diam_range_iterate_tendsto_zero`

Uses Mathlib2.top_edelstein_unique_fixed_point and Mathlib2.bld3_edelstein_iterates_tendsto_uniformly: if X is empty the diameters are 0. Otherwise top_edelstein_unique_fixed_point gives a fixed point p, and bld3_edelstein_iterates_tendsto_uniformly gives N with dist (f^[n] x) p < ε/2 for all n ≥ N and x, so diam (range f^[n]) ≤ ε by Metric.diam_le_of_forall_dist_le.

```lean
∀ {X : Type u_1} [inst : MetricSpace X] [CompactSpace X] (f : X → X), (∀ (x y : X), x ≠ y → dist (f x) (f y) < dist x y) → Filter.Tendsto (fun n => Metric.diam (Set.range f^[n])) Filter.atTop (nhds 0)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.top_edelstein_unique_fixed_point, Mathlib2.bld3_edelstein_iterates_tendsto_uniformly）
- 完成者：r9_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld3_edelstein_iterates_tendsto_uniformly`、`top_edelstein_unique_fixed_point`

## `Mathlib2.bld4_edelstein_surjective_subsingleton`

Uses Mathlib2.bld_surjective_nonexpanding_compact_isometry: f is non-expanding (≤ from <, equality case x = y) and surjective, hence an isometry by the cited theorem; for x ≠ y this gives dist (f x) (f y) = dist x y, contradicting the strict inequality.

```lean
∀ {X : Type u_1} [inst : MetricSpace X] [CompactSpace X] (f : X → X), (∀ (x y : X), x ≠ y → dist (f x) (f y) < dist x y) → Function.Surjective f → Subsingleton X
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_surjective_nonexpanding_compact_isometry）
- 完成者：r9_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld_surjective_nonexpanding_compact_isometry`

## `Mathlib2.bld4_hardy_harmonic_means_tsum_le`

Uses Mathlib2.bld2_hardy_inequality_tsum: apply it to a k = 1/(k+1); the hypothesis is summability of 1/(k+1)^2 and the right side is 4 · ∑' 1/(k+1)^2 = 4 · π^2/6 by Mathlib's Basel sum hasSum_zeta_two (reindexed by k ↦ k + 1).

```lean
∑' (k : ℕ), ((∑ i ∈ Finset.range (k + 1), 1 / (↑i + 1)) / (↑k + 1)) ^ 2 ≤ 2 * Real.pi ^ 2 / 3
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_hardy_inequality_tsum）
- 完成者：r9_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld2_hardy_inequality_tsum`

## `Mathlib2.bld4_pell_five_neg_four_prime_mul_y_not_rat_sum_sq`

Uses Mathlib2.bld3_pell_five_neg_four_solutions_lucas, Mathlib2.nt2_fib_odd_index_no_prime_factor_three_mod_four and Mathlib2.bld2_rat_sq_add_sq_ne_prime_mul_coprime: the Pell classification gives y = F_{2n+1}; nt2_fib_odd_index_no_prime_factor_three_mod_four gives ¬ p ∣ y; then bld2_rat_sq_add_sq_ne_prime_mul_coprime with m = y is the claim.

```lean
∀ (x y p : ℕ), x ^ 2 + 4 = 5 * y ^ 2 → Nat.Prime p → p % 4 = 3 → ∀ (u v : ℚ), u ^ 2 + v ^ 2 ≠ ↑p * ↑y
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld3_pell_five_neg_four_solutions_lucas, Mathlib2.nt2_fib_odd_index_no_prime_factor_three_mod_four, Mathlib2.bld2_rat_sq_add_sq_ne_prime_mul_coprime）
- 完成者：r9_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld2_rat_sq_add_sq_ne_prime_mul_coprime`、`bld3_pell_five_neg_four_solutions_lucas`、`nt2_fib_odd_index_no_prime_factor_three_mod_four`、`p3_lucas`

## `Mathlib2.bld4_pell_five_neg_four_y_sum_two_squares`

Uses Mathlib2.bld3_pell_five_neg_four_solutions_lucas: the classification gives y = F_{2n+1}, and Nat.fib_two_mul_add_one gives F_{2n+1} = F_{n+1}^2 + F_n^2, so a = F_{n+1}, b = F_n.

```lean
∀ (x y : ℕ), x ^ 2 + 4 = 5 * y ^ 2 → ∃ a b, y = a ^ 2 + b ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld3_pell_five_neg_four_solutions_lucas）
- 完成者：r9_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld3_pell_five_neg_four_solutions_lucas`、`p3_lucas`

## `Mathlib2.bld4_pell_five_one_iff`

Uses Mathlib2.bld3_pell_five_one_solutions and Mathlib2.bld2_lucas_sq_sub_five_fib_sq: the forward direction is exactly bld3_pell_five_one_solutions. Conversely bld2_lucas_sq_sub_five_fib_sq at index 6n gives L^2 − 5F^2 = 4 over ℤ; substituting L = 2x, F = 2y and cancelling 4 gives x^2 = 5y^2 + 1.

```lean
∀ (x y : ℕ), x ^ 2 = 5 * y ^ 2 + 1 ↔ ∃ n, 2 * y = Nat.fib (6 * n) ∧ 2 * x = Mathlib2.p3_lucas (6 * n)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld3_pell_five_one_solutions, Mathlib2.bld2_lucas_sq_sub_five_fib_sq）
- 完成者：r9_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld2_lucas_sq_sub_five_fib_sq`、`bld3_pell_five_one_solutions`、`p3_lucas`

## `Mathlib2.bld4_pisano_ten`

Uses Mathlib2.lib_pisano_dvd_iff_period, Mathlib2.lib_fib_period_iff and Mathlib2.bld3_pisano_dvd_pisano_of_dvd: lib_pisano_dvd_iff_period + lib_fib_period_iff reduce 'π(m) ∣ N' to the decidable check F_N ≡ 0, F_{N+1} ≡ 1 mod m; this gives π(10) ∣ 60, and identifies π(2) = 3 and π(5) = 20 (20 works, the divisors 4 and 10 fail). bld3_pisano_dvd_pisano_of_dvd then gives 3 ∣ π(10) and 20 ∣ π(10), so 60 ∣ π(10).

```lean
Mathlib2.p3_pisano 10 = 60
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.lib_pisano_dvd_iff_period, Mathlib2.lib_fib_period_iff, Mathlib2.bld3_pisano_dvd_pisano_of_dvd）
- 完成者：r9_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`lib_fib_period_iff`、`lib_pisano_dvd_iff_period`、`p3_pisano`

## `Mathlib2.bld4_rank_pow_eq_of_card_le`

Uses Mathlib2.bld3_rank_pow_card_stabilizes and Mathlib2.bld2_rank_pow_convex: induct on j showing rank A^(j+1) = rank A^j for j ≥ n. Base case is bld3_rank_pow_card_stabilizes; for the step, bld2_rank_pow_convex gives 2 r_{j+1} ≤ r_j + r_{j+2} = r_{j+1} + r_{j+2}, so r_{j+2} ≥ r_{j+1}, and r_{j+2} ≤ r_{j+1} by Matrix.rank_mul_le_left.

```lean
∀ (K : Type u_1) [inst : Field K] (ι : Type u_2) [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (A : Matrix ι ι K) (j : ℕ), Fintype.card ι ≤ j → (A ^ j).rank = (A ^ Fintype.card ι).rank
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld3_rank_pow_card_stabilizes, Mathlib2.bld2_rank_pow_convex）
- 完成者：r9_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld2_rank_pow_convex`、`bld3_rank_pow_card_stabilizes`

## `Mathlib2.bld4_rat_sq_add_sq_eq_mul_sq_trivial`

Uses Mathlib2.bld3_rat_sq_add_sq_ne_of_odd_padicValNat: if z ≠ 0 then (x/z)^2 + (y/z)^2 = n, contradicting bld3_rat_sq_add_sq_ne_of_odd_padicValNat; so z = 0, and then x^2 + y^2 = 0 in ℚ forces x = y = 0.

```lean
∀ (p n : ℕ), Nat.Prime p → p % 4 = 3 → Odd (padicValNat p n) → ∀ (x y z : ℚ), x ^ 2 + y ^ 2 = ↑n * z ^ 2 → x = 0 ∧ y = 0 ∧ z = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld3_rat_sq_add_sq_ne_of_odd_padicValNat）
- 完成者：r9_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld3_rat_sq_add_sq_ne_of_odd_padicValNat`

## `Mathlib2.bld4_rat_sum_two_squares_iff_nat`

Uses Mathlib2.bld3_rat_sq_add_sq_ne_of_odd_padicValNat: (⇐) is a cast. (⇒) by Mathlib's Nat.eq_sq_add_sq_iff it suffices that padicValNat q n is even for every prime q ≡ 3 mod 4; if it were odd, bld3_rat_sq_add_sq_ne_of_odd_padicValNat would contradict the rational representation.

```lean
∀ (n : ℕ), (∃ x y, x ^ 2 + y ^ 2 = ↑n) ↔ ∃ a b, n = a ^ 2 + b ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld3_rat_sq_add_sq_ne_of_odd_padicValNat）
- 完成者：r9_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld3_rat_sq_add_sq_ne_of_odd_padicValNat`

## `Mathlib2.bld4_sqrt_two_rec_defect_lower`

Uses Mathlib2.ana_sqrt_two_rec_closed_form and Mathlib2.ana_sin_ge_cubic_of_nonneg: the closed form gives 2 − a_n = 2 − 2cos(2θ) = 4 sin^2 θ with θ = π/2^(n+2). ana_sin_ge_cubic_of_nonneg gives sin θ ≥ θ − θ^3/6 ≥ 0, so 4 sin^2 θ ≥ 4θ^2(1 − θ^2/6)^2 ≥ 4θ^2 − 4θ^4/3, which is the stated bound (matching upper bound: bld_sqrt_two_rec_rate).

```lean
∀ (a : ℕ → ℝ), a 0 = 0 → (∀ (n : ℕ), a (n + 1) = √(2 + a n)) → ∀ (n : ℕ), Real.pi ^ 2 / 4 ^ (n + 1) - Real.pi ^ 4 / (192 * 16 ^ n) ≤ 2 - a n
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.ana_sqrt_two_rec_closed_form, Mathlib2.ana_sin_ge_cubic_of_nonneg）
- 完成者：r9_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`ana_sqrt_two_rec_closed_form`、`bld4_sqrt_two_rec_defect_tsum_lower_aux1`

## `Mathlib2.bld4_tripotent_trace_eq_rank_idempotent`

Uses Mathlib2.bld2_tripotent_rank_split, Mathlib2.gen_lin_idempotent_trace_eq_rank_field, Mathlib2.lib_matrix_rank_smul and Mathlib2.lib_matrix_rank_eq_zero_iff: as for the trace formula, tr A = rank(A^2 + A) − rank(A^2 − A) (idempotents (A^2 ± A)/2, trace = rank, rank_smul), while bld2_tripotent_rank_split gives rank A = rank(A^2 + A) + rank(A^2 − A). The hypothesis then forces 2·rank(A^2 − A) = 0 in K, so rank(A^2 − A) = 0 by CharZero and A^2 − A = 0 by lib_matrix_rank_eq_zero_iff.

```lean
∀ (K : Type u_1) [inst : Field K] [CharZero K] (ι : Type u_2) [inst_2 : Fintype ι] [DecidableEq ι] (A : Matrix ι ι K), A * A * A = A → A.trace = ↑A.rank → A * A = A
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_tripotent_rank_split, Mathlib2.gen_lin_idempotent_trace_eq_rank_field, Mathlib2.lib_matrix_rank_smul, Mathlib2.lib_matrix_rank_eq_zero_iff）
- 完成者：r9_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld2_tripotent_rank_split`、`bld4_tripotent_trace_eq_rank_sub_rank`、`lib_matrix_rank_eq_zero_iff`

## `Mathlib2.bld5_card_orderOf_eq_larger_prime_of_card_prime_mul_prime`

Uses Mathlib2.bld4_card_orderOf_eq_prime_of_card_prime_mul_prime: every element has order dividing pq, i.e. in {1, p, q, pq}; order pq is impossible since then G is cyclic (isCyclic_of_orderOf_eq_card) hence commutative. Partition G by order: pq = 1 + q(p−1) + #{order q}, where q(p−1) is the bld4 count of elements of order p; so #{order q} = pq − 1 − q(p−1) = q − 1.

```lean
∀ (p q : ℕ) [Fact (Nat.Prime p)], Nat.Prime q → p < q → ∀ (G : Type u_1) [inst : Group G], Nat.card G = p * q → (∃ a b, a * b ≠ b * a) → Nat.card { g // orderOf g = q } = q - 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld4_card_orderOf_eq_prime_of_card_prime_mul_prime）
- 完成者：prover_bb
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld3_card_conjClasses_of_card_prime_mul_prime_aux1`、`bld4_card_orderOf_eq_prime_of_card_prime_mul_prime`

## `Mathlib2.bld5_card_pow_prime_eq_one_of_card_prime_cube`

Uses Mathlib2.bld4_pow_prime_monoidHom_center_of_card_prime_cube and Mathlib2.bld_center_card_of_card_prime_cube: the bld4 theorem gives a homomorphism φ : G →* Z(G) with φ g = g^p, so {g | g^p = 1} is the carrier of φ.ker. By the first isomorphism theorem |G| = |ker φ|·|range φ|, and |range φ| divides |Z(G)| = p (bld_center_card_of_card_prime_cube, Lagrange), so |range φ| ∈ {1, p} and |ker φ| ∈ {p³, p²}. (Sharpens bld4_card_pow_prime_eq_one_ge_of_card_prime_cube: exponent-p case vs. exponent-p² case.)

```lean
∀ (p : ℕ), Nat.Prime p → ∀ (G : Type u_1) [inst : Group G], Nat.card G = p ^ 3 → (∃ a b, a * b ≠ b * a) → p ≠ 2 → Nat.card { g // g ^ p = 1 } = p ^ 2 ∨ Nat.card { g // g ^ p = 1 } = p ^ 3
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld4_pow_prime_monoidHom_center_of_card_prime_cube, Mathlib2.bld_center_card_of_card_prime_cube）
- 完成者：prover_bb
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld4_pow_prime_monoidHom_center_of_card_prime_cube`、`bld_center_card_of_card_prime_cube`

## `Mathlib2.bld5_carleman_sqrt_two_rec_defect`

Uses Mathlib2.bld4_carleman_finite_three, Mathlib2.bld3_sqrt_two_rec_defect_tsum_bounds, Mathlib2.bld2_sqrt_two_rec_defect_summable and Mathlib2.ana_sqrt_two_rec_lt_two: the defects 2 − a_i are non-negative (ana_sqrt_two_rec_lt_two), so Carleman's inequality with constant 3 (bld4) bounds the sum of geometric means by 3·∑_{k<n}(2 − a_k) ≤ 3·∑'(2 − a_k) (sum_le_tsum with bld2 summability) ≤ 3·π²/3 = π² (bld3).

```lean
∀ (a : ℕ → ℝ), a 0 = 0 → (∀ (n : ℕ), a (n + 1) = √(2 + a n)) → ∀ (n : ℕ), ∑ k ∈ Finset.range n, (∏ i ∈ Finset.range (k + 1), (2 - a i)) ^ (1 / (↑k + 1)) ≤ Real.pi ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld4_carleman_finite_three, Mathlib2.bld3_sqrt_two_rec_defect_tsum_bounds, Mathlib2.bld2_sqrt_two_rec_defect_summable, Mathlib2.ana_sqrt_two_rec_lt_two）
- 完成者：prover_bb
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`ana_sqrt_two_rec_lt_two`、`bld2_sqrt_two_rec_defect_summable`、`bld3_sqrt_two_rec_defect_tsum_bounds`、`bld4_carleman_finite_three`

## `Mathlib2.bld5_commuting_idempotents_rank_sub_iff`

Uses Mathlib2.bld3_commuting_idempotents_rank_sub, Mathlib2.bld_idempotent_sum_rank and Mathlib2.lib_matrix_rank_eq_zero_iff: bld3 gives rank(A−B) + 2·rank(AB) = rank A + rank B, so the left side is equivalent to rank(AB) = rank B. AB and B − AB are idempotents (commutativity) with idempotent sum B, so bld_idempotent_sum_rank gives rank B = rank(AB) + rank(B − AB). Hence rank(AB) = rank B ↔ rank(B − AB) = 0 ↔ B − AB = 0 by lib_matrix_rank_eq_zero_iff.

```lean
∀ (K : Type u_1) [inst : Field K] [CharZero K] (ι : Type u_2) [inst_2 : Fintype ι] [DecidableEq ι] (A B : Matrix ι ι K), A * A = A → B * B = B → A * B = B * A → ((A - B).rank + B.rank = A.rank ↔ A * B = B)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld3_commuting_idempotents_rank_sub, Mathlib2.bld_idempotent_sum_rank, Mathlib2.lib_matrix_rank_eq_zero_iff）
- 完成者：prover_bb
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld3_commuting_idempotents_rank_sub`、`bld_idempotent_sum_rank`、`lib_matrix_rank_eq_zero_iff`

## `Mathlib2.bld5_fib_entry_point_pisano_ratio`

Uses Mathlib2.bld3_pisano_pos_and_period, Mathlib2.bld3_pisano_dvd_pisano_of_dvd and Mathlib2.bld2_pisano_fib_dvd_four_mul: bld3_pisano_pos_and_period at i = 0 gives m ∣ F_π with π = pisano m > 0, so a := Nat.find of {k > 0 | m ∣ F_k} exists (rank of apparition). m ∣ F_k ↔ a ∣ k: (⇐) Nat.fib_dvd; (⇒) m ∣ gcd(F_k, F_a) = F_{gcd(k,a)} by Nat.fib_gcd and minimality forces gcd(k,a) = a. Hence a ∣ π. Conversely m ∣ F_a gives π ∣ pisano(F_a) (bld3_pisano_dvd_pisano_of_dvd) ∣ 4a (bld2_pisano_fib_dvd_four_mul). So π = a·t with t ∣ 4, t ∈ {1,2,4}.

```lean
∀ (m : ℕ), 0 < m → ∃ a, 0 < a ∧ (∀ (k : ℕ), m ∣ Nat.fib k ↔ a ∣ k) ∧ (Mathlib2.p3_pisano m = a ∨ Mathlib2.p3_pisano m = 2 * a ∨ Mathlib2.p3_pisano m = 4 * a)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld3_pisano_pos_and_period, Mathlib2.bld3_pisano_dvd_pisano_of_dvd, Mathlib2.bld2_pisano_fib_dvd_four_mul）
- 完成者：prover_ba
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld2_pisano_fib_dvd_four_mul`、`bld3_pisano_dvd_pisano_of_dvd`、`bld3_pisano_pos_and_period`、`p3_pisano`

## `Mathlib2.bld5_fitting_isCompl_pow_card`

Uses Mathlib2.bld4_fitting_range_inter_ker_pow_card: that theorem says exactly that range(A^n) ⊓ ker(A^n) = ⊥ (a vector A^n v killed by A^n is 0), giving Disjoint. For Codisjoint, rank–nullity (LinearMap.finrank_range_add_finrank_ker) gives finrank range + finrank ker = card ι, so by Submodule.finrank_sup_add_finrank_inf_eq the sup has full finrank and equals ⊤ (Submodule.eq_top_of_finrank_eq). Mathlib only has the 'eventually' version (LinearMap.eventually_isCompl_ker_pow_range_pow); this pins the exponent to card ι.

```lean
∀ (K : Type u_1) [inst : Field K] (ι : Type u_2) [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (A : Matrix ι ι K), IsCompl (LinearMap.range (A ^ Fintype.card ι).mulVecLin) (LinearMap.ker (A ^ Fintype.card ι).mulVecLin)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld4_fitting_range_inter_ker_pow_card）
- 完成者：prover_bb
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld4_fitting_range_inter_ker_pow_card`

## `Mathlib2.bld5_gcd_fib_lucas_dvd_two`

Uses Mathlib2.bld2_lucas_sq_sub_five_fib_sq: with g = gcd(F_n, L_n), g² divides L_n² − 5F_n² = 4·(−1)^n (the bld2 identity, in ℤ), so g² ∣ 4 and hence g ∣ 2 (g ≤ 2 by size, then case check, or Nat.pow_dvd_pow_iff with 4 = 2²).

```lean
∀ (n : ℕ), (Nat.fib n).gcd (Mathlib2.p3_lucas n) ∣ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_lucas_sq_sub_five_fib_sq）
- 完成者：prover_ba
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld2_lucas_sq_sub_five_fib_sq`、`p3_lucas`

## `Mathlib2.bld5_hardy_sqrt_two_rec_defect_means`

Uses Mathlib2.bld2_hardy_inequality_tsum, Mathlib2.bld_sqrt_two_rec_rate and Mathlib2.ana_sqrt_two_rec_lt_two: by ana_sqrt_two_rec_lt_two and bld_sqrt_two_rec_rate, 0 ≤ 2 − a_k ≤ π²/4^(k+1), so (2 − a_k)² ≤ π⁴/16^(k+1), which is summable (geometric) with sum π⁴/15 (tsum_geometric_of_lt_one, tsum_le_tsum). Hardy's inequality bld2_hardy_inequality_tsum applied to the defect sequence bounds the left side by 4·∑'(2 − a_k)² ≤ 4π⁴/15.

```lean
∀ (a : ℕ → ℝ), a 0 = 0 → (∀ (n : ℕ), a (n + 1) = √(2 + a n)) → ∑' (k : ℕ), ((∑ i ∈ Finset.range (k + 1), (2 - a i)) / (↑k + 1)) ^ 2 ≤ 4 * Real.pi ^ 4 / 15
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_hardy_inequality_tsum, Mathlib2.bld_sqrt_two_rec_rate, Mathlib2.ana_sqrt_two_rec_lt_two）
- 完成者：prover_bb
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`ana_sqrt_two_rec_lt_two`、`bld2_hardy_inequality_tsum`、`bld_sqrt_two_rec_rate`

## `Mathlib2.bld5_isometries_compact_simultaneous_recurrence`

Uses Mathlib2.bld4_isometry_compact_uniform_recurrence: apply it to Prod.map f g on the compact metric space X × Y (sup metric; Prod.map of isometries is an isometry, and (Prod.map f g)^[n] = Prod.map f^[n] g^[n]) to get n > 0 with dist((f^[n] x, g^[n] y), (x, y)) < ε for all (x, y); Prod.dist_eq (max) splits it into the two components. If X or Y is empty apply the theorem to the other factor alone.

```lean
∀ {X : Type u_1} [inst : MetricSpace X] [CompactSpace X] {Y : Type u_2} [inst_2 : MetricSpace Y] [CompactSpace Y] (f : X → X) (g : Y → Y), Isometry f → Isometry g → ∀ (ε : ℝ), 0 < ε → ∃ n, 0 < n ∧ (∀ (x : X), dist (f^[n] x) x < ε) ∧ ∀ (y : Y), dist (g^[n] y) y < ε
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld4_isometry_compact_uniform_recurrence）
- 完成者：prover_bb
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld4_isometry_compact_uniform_recurrence`

## `Mathlib2.bld5_isometry_compact_id_uniform_limit`

Uses Mathlib2.bld4_isometry_compact_uniform_recurrence: first upgrade to arbitrarily large return times: for ε > 0 and N ≥ 1, the bld4 theorem with ε/N gives n > 0 with dist(f^[n] x, x) < ε/N for all x; since f^[n] is an isometry, the triangle inequality gives dist(f^[nN] x, x) ≤ N·sup dist(f^[n] y, y) < ε with nN ≥ N. Then build φ recursively (φ(k+1) > φ(k) with sup-distance < 1/(k+2)) and unfold Metric.tendstoUniformly_iff.

```lean
∀ {X : Type u_1} [inst : MetricSpace X] [CompactSpace X] (f : X → X), Isometry f → ∃ φ, StrictMono φ ∧ TendstoUniformly (fun k x => f^[φ k] x) id Filter.atTop
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld4_isometry_compact_uniform_recurrence）
- 完成者：prover_bb
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld4_isometry_compact_uniform_recurrence`

## `Mathlib2.bld5_mantel_equality_connected`

Uses Mathlib2.bld4_mantel_equality_complete_bipartite: it gives s with 2|s| = n and Adj x y ↔ (x ∈ s ↔ y ∉ s). Since n ≥ 2, both s and its complement are non-empty; pick u ∈ s, w ∉ s. Any x ∈ s is adjacent to w and any x ∉ s is adjacent to u, and u ~ w, so every two vertices are joined by a walk of length ≤ 3 through u, w: G is preconnected and V is non-empty.

```lean
∀ (V : Type) [inst : Fintype V] [DecidableEq V] (G : SimpleGraph V) [inst_2 : DecidableRel G.Adj], G.CliqueFree 3 → 4 * G.edgeFinset.card = Fintype.card V ^ 2 → 2 ≤ Fintype.card V → G.Connected
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld4_mantel_equality_complete_bipartite）
- 完成者：prover_bb
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld4_mantel_equality_complete_bipartite`

## `Mathlib2.bld5_nonexpanding_denseRange_compact_recurrence`

Uses Mathlib2.bld_surjective_nonexpanding_compact_isometry and Mathlib2.bld4_isometry_compact_uniform_recurrence: f is 1-Lipschitz hence continuous, so range f is compact, hence closed, and dense, hence everything (DenseRange.closure_range): f is surjective. bld_surjective_nonexpanding_compact_isometry makes f an isometry and bld4_isometry_compact_uniform_recurrence gives the uniform return time.

```lean
∀ {X : Type u_1} [inst : MetricSpace X] [CompactSpace X] (f : X → X), DenseRange f → (∀ (x y : X), dist (f x) (f y) ≤ dist x y) → ∀ (ε : ℝ), 0 < ε → Isometry f ∧ ∃ n, 0 < n ∧ ∀ (x : X), dist (f^[n] x) x < ε
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld_surjective_nonexpanding_compact_isometry, Mathlib2.bld4_isometry_compact_uniform_recurrence）
- 完成者：prover_bb
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld4_isometry_compact_uniform_recurrence`、`bld_surjective_nonexpanding_compact_isometry`

## `Mathlib2.bld5_pell_five_four_prime_y`

Uses Mathlib2.bld2_pell_five_solutions_lucas: it gives n with y = F_{2n}, x = L_{2n}. By Nat.fib_two_mul, y = F_n·L_n (p3_lucas n unfolds to 2F_{n+1} − F_n). For n ≥ 3 both factors exceed 1 (F_n ≥ 2, L_n ≥ 4), contradicting primality; n ≤ 1 gives y ≤ 1; so n = 2, y = F_4 = 3 and x = L_4 = 7.

```lean
∀ (x y : ℕ), x ^ 2 = 5 * y ^ 2 + 4 → Nat.Prime y → y = 3 ∧ x = 7
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_pell_five_solutions_lucas）
- 完成者：prover_ba
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld2_pell_five_solutions_lucas`、`p3_lucas`

## `Mathlib2.bld5_pell_five_neg_four_pisano_mod_eight`

Uses Mathlib2.bld3_pell_five_neg_four_solutions_lucas and Mathlib2.bld2_pisano_fib_odd_eq: the Pell classification gives y = F_{2n+1}; y ≥ 5 forces 2n+1 ≥ 5 (F_1 = 1, F_3 = 2), so bld2_pisano_fib_odd_eq gives pisano y = 4(2n+1) = 8n + 4.

```lean
∀ (x y : ℕ), x ^ 2 + 4 = 5 * y ^ 2 → 5 ≤ y → Mathlib2.p3_pisano y % 8 = 4
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld3_pell_five_neg_four_solutions_lucas, Mathlib2.bld2_pisano_fib_odd_eq）
- 完成者：prover_ba
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld2_pisano_fib_odd_eq`、`bld3_pell_five_neg_four_solutions_lucas`、`p3_lucas`、`p3_pisano`

## `Mathlib2.bld5_permMatrix_involution_rank_one_sub`

Uses Mathlib2.bld4_permMatrix_involution_rank_fixed_points and Mathlib2.bld_involution_rank_add_rank: P = permMatrix σ satisfies P*P = 1 (permMatrix is multiplicative up to order and σ*σ = 1), so bld_involution_rank_add_rank gives rank(1+P) + rank(1−P) = n, and bld4 gives 2·rank(1+P) = n + fix. Subtracting: 2·rank(1−P) = n − fix, i.e. rank(1 − P) is the number of 2-cycles of σ.

```lean
∀ (K : Type u_1) [inst : Field K] [CharZero K] (ι : Type u_2) [inst_2 : Fintype ι] [inst_3 : DecidableEq ι] (σ : Equiv.Perm ι), σ * σ = 1 → 2 * (1 - Equiv.Perm.permMatrix K σ).rank + {i | σ i = i}.card = Fintype.card ι
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld4_permMatrix_involution_rank_fixed_points, Mathlib2.bld_involution_rank_add_rank）
- 完成者：prover_bb
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld4_permMatrix_involution_rank_fixed_points`、`bld_involution_rank_add_rank`

## `Mathlib2.bld5_pisano_lucas_even_eq`

Uses Mathlib2.bld4_pisano_lucas_dvd_four_mul, Mathlib2.lib_pisano_dvd_iff_period, Mathlib2.lib_fib_cassini_cast and Mathlib2.lib_p3_lucas_cast: π := pisano(L_n) ∣ 4n by the bld4 theorem. By lib_pisano_dvd_iff_period (i = 0) L_n ∣ F_π; also L_n ∣ F_{2n} (Nat.fib_two_mul), so by Nat.fib_gcd L_n ∣ F_g with g = gcd(π, 2n) ∣ 2n; since F_{n+1} < L_n ≤ F_g forces g ≥ n+2 > n, g = 2n, i.e. 2n ∣ π. So π ∈ {2n, 4n}. If π = 2n then (lib_pisano_dvd_iff_period, i = 1) F_{2n+1} ≡ 1 mod L_n; but F_{2n+1} = F_{n+1}·L_n − (−1)^n (from lib_p3_lucas_cast, Nat.fib_two_mul_add_one and lib_fib_cassini_cast), which is ≡ −1 for even n, giving L_n ∣ 2, false as L_n ≥ 3.

```lean
∀ (n : ℕ), 2 ≤ n → Even n → Mathlib2.p3_pisano (Mathlib2.p3_lucas n) = 4 * n
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld4_pisano_lucas_dvd_four_mul, Mathlib2.lib_pisano_dvd_iff_period, Mathlib2.lib_fib_cassini_cast, Mathlib2.lib_p3_lucas_cast）
- 完成者：prover_ba
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld4_pisano_lucas_dvd_four_mul`、`bld5_pisano_lucas_odd_eq_aux1`、`bld5_pisano_lucas_odd_eq_aux2`、`bld5_pisano_lucas_odd_eq_aux3`、`lib_pisano_dvd_iff_period`、`p3_lucas`、`p3_pisano`

## `Mathlib2.bld5_pisano_prime_le_four_mul`

Uses Mathlib2.bld4_pisano_prime_dvd_pred_of_isSquare_five, Mathlib2.bld4_pisano_prime_dvd_two_mul_succ_of_not_isSquare_five, Mathlib2.lib_fib_period_iff and Mathlib2.bld3_pisano_dvd_of_period: for p = 2 and p = 5 check F_3 ≡ 0, F_4 ≡ 1 mod 2 and F_20 ≡ 0, F_21 ≡ 1 mod 5, so (lib_fib_period_iff, bld3_pisano_dvd_of_period) pisano ∣ 3 resp. 20 = 4·5 (equality case). Otherwise split on IsSquare (5 : ZMod p): the first bld4 theorem gives pisano ∣ p − 1, the second pisano ∣ 2(p+1) ≤ 4p; conclude with Nat.le_of_dvd.

```lean
∀ (p : ℕ), Nat.Prime p → Mathlib2.p3_pisano p ≤ 4 * p
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld4_pisano_prime_dvd_pred_of_isSquare_five, Mathlib2.bld4_pisano_prime_dvd_two_mul_succ_of_not_isSquare_five, Mathlib2.lib_fib_period_iff, Mathlib2.bld3_pisano_dvd_of_period）
- 完成者：prover_ba
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld3_pisano_dvd_of_period`、`bld4_pisano_prime_dvd_pred_of_isSquare_five`、`bld4_pisano_prime_dvd_two_mul_succ_of_not_isSquare_five`、`lib_fib_period_iff`、`p3_pisano`

## `Mathlib2.bld5_prime_dvd_pred_of_card_prime_mul_prime`

Uses Mathlib2.bld3_card_sylow_of_card_prime_mul_prime: a non-abelian group of order pq (p < q) has exactly q Sylow p-subgroups by the bld3 theorem; Sylow's third theorem (card_sylow_modEq_one) gives q ≡ 1 mod p, i.e. p ∣ q − 1 ((Nat.modEq_iff_dvd' hq.one_le).mp after symmetry).

```lean
∀ (p q : ℕ) [Fact (Nat.Prime p)], Nat.Prime q → p < q → ∀ (G : Type u_1) [inst : Group G], Nat.card G = p * q → (∃ a b, a * b ≠ b * a) → p ∣ q - 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld3_card_sylow_of_card_prime_mul_prime）
- 完成者：prover_bb
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld3_card_sylow_of_card_prime_mul_prime`

## `Mathlib2.bld5_prime_three_mod_four_dvd_lucas`

Uses Mathlib2.bld3_pisano_pos_and_period and Mathlib2.nt2_fib_odd_index_no_prime_factor_three_mod_four: bld3_pisano_pos_and_period at i = 0 gives some k > 0 with p ∣ F_k; take the least such a (Nat.find). The nt2 theorem (no prime ≡ 3 mod 4 divides an odd-indexed Fibonacci number) forces a even, a = 2n with 0 < n < a. Nat.fib_two_mul gives F_{2n} = F_n·L_n (the factor 2F_{n+1} − F_n is p3_lucas n by definition); p ∤ F_n by minimality, so p ∣ L_n.

```lean
∀ (p : ℕ), Nat.Prime p → p % 4 = 3 → ∃ n, p ∣ Mathlib2.p3_lucas n
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld3_pisano_pos_and_period, Mathlib2.nt2_fib_odd_index_no_prime_factor_three_mod_four）
- 完成者：prover_ba
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld3_pisano_pos_and_period`、`nt2_fib_odd_index_no_prime_factor_three_mod_four`、`p3_lucas`、`p3_pisano`

## `Mathlib2.bld5_quadratic_annihilated_iff_rank_add_rank`

Uses Mathlib2.bld2_idempotent_iff_rank_add_rank and Mathlib2.lib_matrix_rank_smul: put P = (b − a)⁻¹ • (A − a•1), so 1 − P = −(b − a)⁻¹ • (A − b•1). A direct computation gives P*P − P = (b − a)⁻² • (A − a•1)(A − b•1), so the left side is equivalent to P*P = P, which by bld2_idempotent_iff_rank_add_rank is rank P + rank(1 − P) = card ι; lib_matrix_rank_smul (non-zero scalars (b−a)⁻¹ and −(b−a)⁻¹) rewrites the ranks as those of A − a•1 and A − b•1. Generalises the idempotent (a,b) = (0,1) and involution (1,−1) criteria to any split quadratic, with no characteristic assumption.

```lean
∀ (K : Type u_1) [inst : Field K] (ι : Type u_2) [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (A : Matrix ι ι K) (a b : K), a ≠ b → ((A - a • 1) * (A - b • 1) = 0 ↔ (A - a • 1).rank + (A - b • 1).rank = Fintype.card ι)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_idempotent_iff_rank_add_rank, Mathlib2.lib_matrix_rank_smul）
- 完成者：prover_bb
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld2_idempotent_iff_rank_add_rank`、`lib_matrix_rank_smul`

## `Mathlib2.bld5_sqrt_two_rec_partial_sum_lower`

Uses Mathlib2.bld2_sqrt_two_rec_defect_summable, Mathlib2.bld3_sqrt_two_rec_defect_tsum_bounds and Mathlib2.ana_sqrt_two_rec_lt_two: ∑_{i<n} (2 − a_i) ≤ ∑' (2 − a_i) by sum_le_tsum (terms non-negative by ana_sqrt_two_rec_lt_two, summable by bld2), and the series is ≤ π²/3 by bld3; rearrange using Finset.sum_sub_distrib and Finset.sum_const.

```lean
∀ (a : ℕ → ℝ), a 0 = 0 → (∀ (n : ℕ), a (n + 1) = √(2 + a n)) → ∀ (n : ℕ), 2 * ↑n - Real.pi ^ 2 / 3 ≤ ∑ i ∈ Finset.range n, a i
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_sqrt_two_rec_defect_summable, Mathlib2.bld3_sqrt_two_rec_defect_tsum_bounds, Mathlib2.ana_sqrt_two_rec_lt_two）
- 完成者：prover_bb
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`ana_sqrt_two_rec_lt_two`、`bld2_sqrt_two_rec_defect_summable`、`bld3_sqrt_two_rec_defect_tsum_bounds`

## `Mathlib2.bld6_abundant_two_mul_totient_lt`

Uses Mathlib2.arith_sigma_mul_totient_lt_sq: 2n·φ(n) ≤ σ(n)·φ(n) < n^2 by the hypothesis and arith_sigma_mul_totient_lt_sq; cancel n > 0. So perfect and abundant numbers have φ(n) < n/2.

```lean
∀ (n : ℕ), 2 ≤ n → 2 * n ≤ (ArithmeticFunction.sigma 1) n → 2 * n.totient < n
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.arith_sigma_mul_totient_lt_sq）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`arith_sigma_mul_totient_lt_sq`

## `Mathlib2.bld6_card_circular_no_adjacent_subsets`

Uses Mathlib2.calc_card_no_adjacent_subsets: split cyclically non-adjacent subsets of Z/(n+1) by whether the last point n belongs to s. If not, s is a linear non-adjacent subset of Fin n: fib(n+2) of them by calc_card_no_adjacent_subsets n; if yes (n ≥ 2), then 0 and n-1 are excluded and the rest is a linear non-adjacent subset of the n-2 middle points: fib n by calc_card_no_adjacent_subsets (n-2); small n by decide. The total is the Lucas number L_(n+1).

```lean
∀ (n : ℕ), {s | ∀ (i j : Fin (n + 1)), i ∈ s → j ∈ s → (↑i + 1) % (n + 1) ≠ ↑j}.card = Nat.fib n + Nat.fib (n + 2)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.calc_card_no_adjacent_subsets）
- 完成者：prover_6x
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`calc_card_no_adjacent_subsets_aux2`

## `Mathlib2.bld6_card_image_two_fin_three`

Uses Mathlib2.calc_card_surjective_fin_three: for n > 0 the image of f : Fin n → Fin 3 has 1, 2 or 3 elements; size 3 means surjective (3^n - 3·2^n + 3 functions by calc_card_surjective_fin_three), size 1 means constant (3 functions), and all functions number 3^n, so size 2 occurs 3^n - (3^n - 3·2^n + 3) - 3 = 3·2^n - 6 times.

```lean
∀ (n : ℕ), 0 < n → {f | (Finset.image f Finset.univ).card = 2}.card = 3 * (2 ^ n - 2)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.calc_card_surjective_fin_three）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`calc_card_surjective_fin_three`

## `Mathlib2.bld6_card_involutions_even`

Uses Mathlib2.calc_card_involutions_rec: two-step induction with I(m+2) = I(m+1) + (m+1)·I(m) from calc_card_involutions_rec; base cases I(2) = 2 and I(3) = I(2) + 2·I(1) = 4 (again from the recurrence, I(0) = I(1) = 1 by decide), and for m ≥ 2 both I(m+1) and I(m) are even.

```lean
∀ (n : ℕ), Even {σ | σ * σ = 1}.card
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.calc_card_involutions_rec）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`calc_card_involutions_rec`

## `Mathlib2.bld6_chebyshev_T_derivative_card_distinct_real_roots`

Uses Mathlib2.poly_chebyshev_T_card_distinct_real_roots and Mathlib2.lib_chebyshev_T_natDegree_le: Rolle (Polynomial.card_roots_toFinset_le_derivative) gives n = #roots(T_n) ≤ #roots(T_n') + 1 using the poly theorem; conversely #roots(T_n') ≤ natDegree T_n' ≤ natDegree T_n - 1 ≤ n - 1 by the lib degree bound (the cases n = 0, 1 give the zero / constant derivative).

```lean
∀ (n : ℕ), (Polynomial.derivative (Polynomial.Chebyshev.T ℝ ↑n)).roots.toFinset.card = n - 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.poly_chebyshev_T_card_distinct_real_roots, Mathlib2.lib_chebyshev_T_natDegree_le）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`lib_chebyshev_T_natDegree_le`、`poly_chebyshev_T_card_distinct_real_roots`

## `Mathlib2.bld6_chebyshev_T_separable`

Uses Mathlib2.poly_chebyshev_T_card_distinct_real_roots and Mathlib2.lib_chebyshev_T_natDegree_le: n = #distinct roots ≤ card roots ≤ natDegree ≤ n (the first equality from the poly theorem, the last bound from the lib lemma), so T_n has natDegree n, splits over ℝ with all roots simple; a polynomial with natDegree-many distinct roots is squarefree, hence separable in characteristic 0.

```lean
∀ (n : ℕ), (Polynomial.Chebyshev.T ℝ ↑n).Separable
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.poly_chebyshev_T_card_distinct_real_roots, Mathlib2.lib_chebyshev_T_natDegree_le）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`lib_chebyshev_T_natDegree_le`、`poly_chebyshev_T_card_distinct_real_roots`

## `Mathlib2.bld6_cyclotomic_coeff_symm`

Uses Mathlib2.poly_cyclotomic_reverse_eq_self: rewrite the left side with reverse Φ_n = Φ_n and apply Polynomial.coeff_reverse with natDegree Φ_n = φ(n) (Polynomial.natDegree_cyclotomic) and revAt φ(n) k = φ(n) - k for k ≤ φ(n).

```lean
∀ (n k : ℕ), 2 ≤ n → k ≤ n.totient → (Polynomial.cyclotomic n ℤ).coeff k = (Polynomial.cyclotomic n ℤ).coeff (n.totient - k)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.poly_cyclotomic_reverse_eq_self）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`poly_cyclotomic_reverse_eq_self`

## `Mathlib2.bld6_cyclotomic_eval_neg_one_of_odd`

Uses Mathlib2.poly_cyclotomic_two_mul_odd_comp_neg: Φ_n(-1) = (Φ_n ∘ (-X))(1) = Φ_(2n)(1) by the library identity (eval_comp); 2n with n odd > 1 is not a prime power, so Polynomial.eval_one_cyclotomic_not_prime_pow gives Φ_(2n)(1) = 1.

```lean
∀ (n : ℕ), Odd n → 1 < n → Polynomial.eval (-1) (Polynomial.cyclotomic n ℤ) = 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.poly_cyclotomic_two_mul_odd_comp_neg）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`poly_cyclotomic_two_mul_odd_comp_neg`

## `Mathlib2.bld6_cyclotomic_two_mul_odd_coeff`

Uses Mathlib2.poly_cyclotomic_two_mul_odd_comp_neg: rewrite Φ_(2n) = Φ_n ∘ (-X) and compute the k-th coefficient of p.comp(-X) as (-1)^k p.coeff k (write -X = C(-1)·X and use the coefficient formula for comp with C a * X).

```lean
∀ (n k : ℕ), Odd n → 1 < n → (Polynomial.cyclotomic (2 * n) ℤ).coeff k = (-1) ^ k * (Polynomial.cyclotomic n ℤ).coeff k
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.poly_cyclotomic_two_mul_odd_comp_neg）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`poly_cyclotomic_two_mul_odd_comp_neg`

## `Mathlib2.bld6_factorial_lt_exp_mul_pow`

Uses Mathlib2.calc_exp_lt_one_add_inv_pow_succ: put a_n = n!·e^n/(n·n^n); a_1 = e and a_(n+1)/a_n = e/(1+1/n)^(n+1) < 1 by calc_exp_lt_one_add_inv_pow_succ (the induction step), so a_n < e for n ≥ 2. This is the upper companion of Mathlib2.calc_factorial_gt_div_exp_pow.

```lean
∀ (n : ℕ), 2 ≤ n → ↑n.factorial < Real.exp 1 * ↑n * (↑n / Real.exp 1) ^ n
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.calc_exp_lt_one_add_inv_pow_succ）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`calc_exp_lt_one_add_inv_pow_succ`

## `Mathlib2.bld6_hardy_odd_harmonic_means`

Uses Mathlib2.bld2_hardy_inequality_tsum and Mathlib2.calc_tsum_inv_odd_sq: apply Hardy's inequality to a_k = 1/(2k+1); summability of a_k^2 and the value ∑ a_k^2 = π^2/8 come from calc_tsum_inv_odd_sq (rewrite (1/(2k+1))^2 = 1/(2k+1)^2), so the bound is 4·π^2/8.

```lean
∑' (k : ℕ), ((∑ i ∈ Finset.range (k + 1), 1 / (2 * ↑i + 1)) / (↑k + 1)) ^ 2 ≤ Real.pi ^ 2 / 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld2_hardy_inequality_tsum, Mathlib2.calc_tsum_inv_odd_sq）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld2_hardy_inequality_tsum`、`calc_tsum_inv_odd_sq`

## `Mathlib2.bld6_integral_dalzell_companion`

Uses Mathlib2.calc_integral_dalzell and Mathlib2.calc_integral_beta_nat: x^6(1-x)^4/(1+x^2) = x^4(1-x)^4 - x^4(1-x)^4/(1+x^2) pointwise; split the integral (intervalIntegral.integral_sub), the first piece is 1/630 by calc_integral_beta_nat 4 4 and the second is 22/7 - π by calc_integral_dalzell.

```lean
∫ (x : ℝ) in 0..1, x ^ 6 * (1 - x) ^ 4 / (1 + x ^ 2) = Real.pi - 22 / 7 + 1 / 630
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.calc_integral_dalzell, Mathlib2.calc_integral_beta_nat）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`calc_integral_beta_nat`、`calc_integral_dalzell`

## `Mathlib2.bld6_lcm_mul_integral_central_beta_nat`

Uses Mathlib2.calc_integral_beta_nat and Mathlib2.arith_centralBinom_dvd_lcm: by mul_pow and calc_integral_beta_nat n n the integral is (n!)^2/(2n+1)! = 1/((2n+1)·centralBinom n) (Nat.centralBinom, Nat.choose factorial formula); so the left side equals lcm(1..2n)/centralBinom n, which is a positive natural number q by arith_centralBinom_dvd_lcm (Nair's integrality argument made explicit).

```lean
∀ (n : ℕ), ∃ q, 0 < q ∧ ↑((Finset.Icc 1 (2 * n)).lcm id) * (2 * ↑n + 1) * ∫ (x : ℝ) in 0..1, (x * (1 - x)) ^ n = ↑q
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.calc_integral_beta_nat, Mathlib2.arith_centralBinom_dvd_lcm）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`arith_centralBinom_dvd_lcm`、`calc_integral_beta_nat`

## `Mathlib2.bld6_nat_pow_lt_pow_swap`

Uses Mathlib2.calc_rpow_lt_rpow_swap_of_exp_le: apply it with x = m, y = n; the hypothesis e ≤ m follows from Real.exp_one_lt_d9 (e < 3 ≤ m); then convert rpow with natural exponents to Nat powers (Real.rpow_natCast, Nat.cast_lt).

```lean
∀ (m n : ℕ), 3 ≤ m → m < n → n ^ m < m ^ n
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.calc_rpow_lt_rpow_swap_of_exp_le）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`calc_rpow_lt_rpow_swap_of_exp_le`

## `Mathlib2.bld6_nilpotent_max_index_iff_rank`

Uses Mathlib2.bld5_nilpotent_max_index_rank and Mathlib2.bld4_nilpotent_corank_one_rank_pow: the forward direction is bld5_nilpotent_max_index_rank; conversely, if rank A + 1 = n then n ≥ 1 and bld4_nilpotent_corank_one_rank_pow with k = n - 1 gives rank(A^(n-1)) = 1, so A^(n-1) ≠ 0.

```lean
∀ (K : Type u_1) [inst : Field K] (ι : Type u_2) [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (A : Matrix ι ι K), IsNilpotent A → (A ^ (Fintype.card ι - 1) ≠ 0 ↔ A.rank + 1 = Fintype.card ι)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld5_nilpotent_max_index_rank, Mathlib2.bld4_nilpotent_corank_one_rank_pow）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld4_nilpotent_corank_one_rank_pow`、`bld5_nilpotent_max_index_rank`

## `Mathlib2.bld6_nilpotent_rank_pow_succ_le_rank_sub`

Uses Mathlib2.lib_matrix_rank_pow_succ_lt_of_isNilpotent_of_ne_zero: induction on k; if A^(k+1) = 0 then A^(k+2) = 0 has rank 0, otherwise the lib lemma gives rank(A^(k+2)) < rank(A^(k+1)) ≤ rank A - k with rank(A^(k+1)) > 0, so rank(A^(k+2)) ≤ rank A - (k+1). Sharpens Mathlib2.bld3_nilpotent_rank_pow_le (card ι - k) and reproves Mathlib2.bld5_nilpotent_pow_rank_succ_eq_zero at k = rank A.

```lean
∀ (K : Type u_1) [inst : Field K] (ι : Type u_2) [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (A : Matrix ι ι K), IsNilpotent A → ∀ (k : ℕ), (A ^ (k + 1)).rank ≤ A.rank - k
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.lib_matrix_rank_pow_succ_lt_of_isNilpotent_of_ne_zero）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`lib_matrix_rank_pow_succ_lt_of_isNilpotent_of_ne_zero`

## `Mathlib2.bld6_pi_dalzell_beta_bounds`

Uses Mathlib2.calc_integral_dalzell and Mathlib2.calc_integral_beta_nat: on (0,1) one has x^4(1-x)^4/2 < x^4(1-x)^4/(1+x^2) < x^4(1-x)^4; integrate (strict monotonicity of the interval integral for continuous functions). The middle integral is 22/7 - π by calc_integral_dalzell, the outer one is 4!4!/9! = 1/630 by calc_integral_beta_nat 4 4.

```lean
22 / 7 - 1 / 630 < Real.pi ∧ Real.pi < 22 / 7 - 1 / 1260
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.calc_integral_dalzell, Mathlib2.calc_integral_beta_nat）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`calc_integral_beta_nat`、`calc_integral_dalzell`

## `Mathlib2.bld6_pisano_prime_not_dvd_succ_of_not_isSquare_five`

Uses Mathlib2.bld5_prime_dvd_fib_succ_of_not_isSquare_five, Mathlib2.lib_pisano_dvd_iff_period and Mathlib2.lib_fib_period_iff: if π(p) ∣ p+1 then (lib_pisano_dvd_iff_period + lib_fib_period_iff) F_(p+2) ≡ 1 mod p. But p ∣ F_(p+1) (bld5 theorem) gives F_(p+2) ≡ F_p, and F_p ≡ 5^((p-1)/2) ≡ -1 mod p (Euler criterion, from 2^(p-1) F_p = ∑ C(p,2j+1) 5^j; or Cassini F_p^2 ≡ 1 plus F_(p-1) ≡ -F_p and p ∤ F_(p-1)·… ), contradiction as p ≠ 2. Complements bld4_pisano_prime_dvd_two_mul_succ_of_not_isSquare_five: the period divides 2(p+1) but not p+1.

```lean
∀ (p : ℕ) [inst : Fact (Nat.Prime p)], p ≠ 2 → ¬IsSquare 5 → ¬Mathlib2.p3_pisano p ∣ p + 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld5_prime_dvd_fib_succ_of_not_isSquare_five, Mathlib2.lib_pisano_dvd_iff_period, Mathlib2.lib_fib_period_iff）
- 完成者：prover_6x
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld5_prime_dvd_fib_succ_of_not_isSquare_five`、`lib_fib_period_iff`、`lib_pisano_dvd_iff_period`、`p3_aux_fib_prime`、`p3_pisano`

## `Mathlib2.bld6_pisano_ten_pow`

Uses Mathlib2.bld4_pisano_mul_of_coprime, Mathlib2.bld5_pisano_two_pow and Mathlib2.bld5_pisano_five_pow: 10^(k+3) = 2^(k+3)·5^(k+3) with coprime factors, so π = lcm(π(2^(k+3)), π(5^(k+3))) (bld4_pisano_mul_of_coprime) = lcm(3·2^(k+2), 4·5^(k+3)) by the two prime-power formulas; since k+2 ≥ 2 the lcm is 3·2^(k+2)·5^(k+3) = 15·10^(k+2).

```lean
∀ (k : ℕ), Mathlib2.p3_pisano (10 ^ (k + 3)) = 15 * 10 ^ (k + 2)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld4_pisano_mul_of_coprime, Mathlib2.bld5_pisano_two_pow, Mathlib2.bld5_pisano_five_pow）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld4_pisano_mul_of_coprime`、`bld5_pisano_five_pow`、`bld5_pisano_two_pow`、`p3_pisano`

## `Mathlib2.bld6_pisano_two_pow_mul_five_pow_eq_six_mul_iff`

Uses Mathlib2.bld4_pisano_mul_of_coprime, Mathlib2.bld5_pisano_two_pow and Mathlib2.bld5_pisano_five_pow: π(2^(a+1)5^(b+1)) = lcm(3·2^a, 4·5^(b+1)) by the coprime-lcm rule and the two prime-power formulas; this equals 12·5^(b+1) for a ≤ 1 and 3·2^a·5^(b+1) for a ≥ 2, i.e. 6n, 3n, 3n/2 respectively — so the extremal ratio π(n) = 6n occurs exactly for a = 0 (n = 2·5^(b+1)).

```lean
∀ (a b : ℕ), Mathlib2.p3_pisano (2 ^ (a + 1) * 5 ^ (b + 1)) = 6 * (2 ^ (a + 1) * 5 ^ (b + 1)) ↔ a = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld4_pisano_mul_of_coprime, Mathlib2.bld5_pisano_two_pow, Mathlib2.bld5_pisano_five_pow）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld4_pisano_mul_of_coprime`、`bld5_pisano_five_pow`、`bld5_pisano_two_pow`、`p3_pisano`

## `Mathlib2.bld6_poly_mul_add_one_eq_pow_const`

Uses Mathlib2.poly_no_consecutive_powerful: f and f+1 are coprime, so in the UFD k[X] any irreducible p dividing f has p-adic multiplicity in f equal to its multiplicity in h^n, a multiple of n ≥ 2, hence p^2 ∣ f; same for f+1. Both powerfulness hypotheses of poly_no_consecutive_powerful hold, giving natDegree f = 0 (last step).

```lean
∀ {k : Type u_1} [inst : Field k] [DecidableEq k] [CharZero k] (n : ℕ), 2 ≤ n → ∀ (f h : Polynomial k), f * (f + 1) = h ^ n → f.natDegree = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.poly_no_consecutive_powerful）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`poly_no_consecutive_powerful`

## `Mathlib2.bld6_rank_cube_sub_self_defect`

Uses Mathlib2.bld3_rank_tripotent_defect and Mathlib2.bld2_rank_add_rank_one_sub: the idempotent-defect identity bld2_rank_add_rank_one_sub applied to A and to -A gives rank(A*A - A) = rank A + rank(A - 1) - n and rank(A*A + A) = rank A + rank(A + 1) - n (ranks invariant under negation); substitute both into bld3_rank_tripotent_defect: rank(A*A+A) + rank(A*A-A) = rank A + rank(A^3 - A). Corollary: A^3 = A iff rank A + rank(A-1) + rank(A+1) = 2n.

```lean
∀ (K : Type u_1) [inst : Field K] [CharZero K] (ι : Type u_2) [inst_2 : Fintype ι] [inst_3 : DecidableEq ι] (A : Matrix ι ι K), A.rank + (A - 1).rank + (A + 1).rank = 2 * Fintype.card ι + (A * A * A - A).rank
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.bld3_rank_tripotent_defect, Mathlib2.bld2_rank_add_rank_one_sub）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld2_rank_add_rank_one_sub`、`bld3_rank_tripotent_defect`

## `Mathlib2.bld6_real_nonneg_poly_root_sq_dvd`

Uses Mathlib2.poly_real_nonneg_eq_sum_two_squares: write p = f^2 + g^2; evaluating at a gives f(a)^2 + g(a)^2 = 0, so f(a) = g(a) = 0, hence X - a divides both f and g (Polynomial.dvd_iff_isRoot) and (X - a)^2 divides f^2 + g^2.

```lean
∀ (p : Polynomial ℝ), (∀ (x : ℝ), 0 ≤ Polynomial.eval x p) → ∀ (a : ℝ), Polynomial.eval a p = 0 → (Polynomial.X - Polynomial.C a) ^ 2 ∣ p
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.poly_real_nonneg_eq_sum_two_squares）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`poly_real_nonneg_eq_sum_two_squares`

## `Mathlib2.bld6_succ_pow_lt_exp_pow_mul_factorial`

Uses Mathlib2.calc_one_add_inv_pow_lt_exp: induction on n via (n+1)^n/n! = ∏_{k=1}^n (1+1/k)^k (ratio of consecutive terms is (1+1/(n+1))^(n+1)); each factor is < e by calc_one_add_inv_pow_lt_exp. Strengthens Mathlib2.calc_factorial_gt_div_exp_pow from n^n to (n+1)^n.

```lean
∀ (n : ℕ), 0 < n → (↑n + 1) ^ n < Real.exp 1 ^ n * ↑n.factorial
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.calc_one_add_inv_pow_lt_exp）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`calc_one_add_inv_pow_lt_exp`

## `Mathlib2.bld6_sum_choose_alternating_div_eq_beta`

Uses Mathlib2.calc_integral_beta_nat: expand (1-x)^n by the binomial theorem, so x^m(1-x)^n = ∑ (-1)^k C(n,k) x^(m+k); integrate termwise over [0,1] (integral_pow) to get the left side, and the right side is the value of the same integral by calc_integral_beta_nat m n (final step).

```lean
∀ (m n : ℕ), ∑ k ∈ Finset.range (n + 1), (-1) ^ k * ↑(n.choose k) / (↑m + ↑k + 1) = ↑m.factorial * ↑n.factorial / ↑(m + n + 1).factorial
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.calc_integral_beta_nat）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`calc_integral_beta_nat`

## `Mathlib2.bld6_sum_fixed_points_sub_one_sq_perm`

Uses Mathlib2.calc_sum_sq_card_fixed_points_perm and Mathlib2.calc_sum_card_fixed_points_perm: expand (X - 1)^2 = X^2 - 2X + 1 and sum over the n! permutations: 2·n! (second moment, calc_sum_sq_card_fixed_points_perm) - 2·n! (first moment, calc_sum_card_fixed_points_perm) + n! (Fintype.card_perm) — the number of fixed points of a random permutation has variance 1.

```lean
∀ (n : ℕ), 2 ≤ n → ∑ σ, (↑{i | σ i = i}.card - 1) ^ 2 = ↑n.factorial
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.calc_sum_sq_card_fixed_points_perm, Mathlib2.calc_sum_card_fixed_points_perm）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`calc_sum_card_fixed_points_perm`、`calc_sum_sq_card_fixed_points_perm`

## `Mathlib2.bld6_tsum_inv_fib_mul_fib_add_two`

Uses Mathlib2.calc_tsum_inv_three_consecutive_aux1 (general telescoping HasSum lemma): take g n = 1/(F_(n+1) F_(n+2)); then g n - g (n+1) = (F_(n+3) - F_(n+1))/(F_(n+1)F_(n+2)F_(n+3)) = 1/(F_(n+1)F_(n+3)) by Nat.fib_add_two, g → 0 since F_(n+1) ≥ n/…→∞ (Nat.fib_lt_fib_succ / le_fib_self), and g 0 = 1.

```lean
∑' (n : ℕ), 1 / (↑(Nat.fib (n + 1)) * ↑(Nat.fib (n + 3))) = 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.calc_tsum_inv_three_consecutive）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`calc_tsum_inv_three_consecutive_aux1`

## `Mathlib2.bld6_tsum_inv_odd_sq_mul_odd_sq`

Uses Mathlib2.calc_tsum_inv_odd_sq and Mathlib2.calc_tsum_inv_odd_consecutive: 1/(a^2(a+2)^2) = (1/4)(1/a^2 + 1/(a+2)^2) - (1/2)·1/(a(a+2)) with a = 2n+1. The sum of 1/a^2 is π^2/8 (calc_tsum_inv_odd_sq), the shifted sum is π^2/8 - 1, and the sum of 1/(a(a+2)) is 1/2 (calc_tsum_inv_odd_consecutive): total (1/4)(π^2/4 - 1) - 1/4.

```lean
∑' (n : ℕ), 1 / ((2 * ↑n + 1) ^ 2 * (2 * ↑n + 3) ^ 2) = Real.pi ^ 2 / 16 - 1 / 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.calc_tsum_inv_odd_sq, Mathlib2.calc_tsum_inv_odd_consecutive）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`calc_tsum_inv_odd_consecutive`、`calc_tsum_inv_odd_sq`

## `Mathlib2.bld6_tsum_lucas_div_two_pow`

Uses Mathlib2.calc_tsum_fib_div_two_pow and Mathlib2.lib_p3_lucas_cast: by lib_p3_lucas_cast L_n = 2F_(n+1) - F_n in ℝ; ∑ F_n/2^n = 2 (calc_tsum_fib_div_two_pow, also giving summability), and dropping the zero term n = 0 gives ∑ F_(n+1)/2^n = 2·2 = 4; so the sum is 2·4 - 2 = 6.

```lean
∑' (n : ℕ), ↑(Mathlib2.p3_lucas n) / 2 ^ n = 6
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.calc_tsum_fib_div_two_pow, Mathlib2.lib_p3_lucas_cast）
- 完成者：prover_6a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`calc_tsum_fib_div_two_pow`、`lib_p3_lucas_cast`、`p3_lucas`

## `Mathlib2.bld_exists_bipartite_subgraph_half_edges`

Uses Mathlib2.comb_exists_cut_half_edges: take the cut s from the library theorem and let H be the subgraph of G consisting of edges between s and sᶜ; it is 2-coloured by membership in s, and its edges biject with the ordered pairs counted in the cut.

```lean
∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], ∃ H ≤ G, H.Colorable 2 ∧ G.edgeSet.ncard ≤ 2 * H.edgeSet.ncard
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.comb_exists_cut_half_edges）
- 完成者：r6_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`comb_exists_cut_half_edges`

## `Mathlib2.bld_fib_consecutive_of_quadratic_form`

Uses Mathlib2.r3_fib_iff_five_sq_pm_four_is_square and Mathlib2.an_cassini_int: (2x-y)^2 = 5y^2 ± 4, so y = fib n by the library characterisation; Cassini shows fib (n+1) is a root of the same quadratic in x, and positivity of x pins it down (small cases y ≤ 1 by hand). Key lemma of IMO 1981 Q3.

```lean
∀ (x y : ℕ), 0 < x → (↑x ^ 2 - ↑x * ↑y - ↑y ^ 2) ^ 2 = 1 → ∃ n, y = Nat.fib n ∧ x = Nat.fib (n + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.r3_fib_iff_five_sq_pm_four_is_square, Mathlib2.an_cassini_int）
- 完成者：r6_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`an_cassini_int`、`r3_fib_iff_five_sq_pm_four_is_square`

## `Mathlib2.bld_hardy_cross_term`

Uses Mathlib2.r3_hardy_inequality_finite: by Cauchy–Schwarz the left side is at most sqrt(∑ σ_k^2) * sqrt(∑ a_k^2), and Hardy bounds ∑ σ_k^2 by 4 ∑ a_k^2.

```lean
∀ (a : ℕ → ℝ) (n : ℕ), ∑ k ∈ Finset.range n, (∑ i ∈ Finset.range (k + 1), a i) / (↑k + 1) * a k ≤ 2 * ∑ k ∈ Finset.range n, a k ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.r3_hardy_inequality_finite）
- 完成者：r6_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`r3_hardy_inequality_finite`

## `Mathlib2.bld_iterate_shrinking_unique_fixed_point`

Uses Mathlib2.top_edelstein_unique_fixed_point applied to f^[n]: its unique fixed point p satisfies f^[n] (f p) = f p, so f p = p by uniqueness; any fixed point of f is fixed by f^[n]. (Shrinking analogue of Mathlib2.top_fixed_of_iterate_contraction.)

```lean
∀ {X : Type u_1} [inst : MetricSpace X] [CompactSpace X] [Nonempty X] (f : X → X) (n : ℕ), (∀ (x y : X), x ≠ y → dist (f^[n] x) (f^[n] y) < dist x y) → ∃! p, f p = p
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.top_edelstein_unique_fixed_point）
- 完成者：r6_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`top_edelstein_unique_fixed_point`

## `Mathlib2.bld_mantel_triangle_free`

Uses Mathlib2.comb_degree_add_degree_le_of_triangle_free: summing deg u + deg v ≤ |V| over edges gives ∑_v deg(v)^2 ≤ |E| |V|; Cauchy–Schwarz and the handshake lemma give (2|E|)^2 ≤ |V| ∑ deg^2 ≤ |V|^2 |E|. Extends Mathlib2.comb_card_edgeFinset_le_of_coloring_bool from bipartite to triangle-free graphs (Mantel).

```lean
∀ (V : Type) [inst : Fintype V] [DecidableEq V] (G : SimpleGraph V) [inst_2 : DecidableRel G.Adj], G.CliqueFree 3 → 4 * G.edgeFinset.card ≤ Fintype.card V ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.comb_degree_add_degree_le_of_triangle_free）
- 完成者：r6_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`comb_degree_add_degree_le_of_triangle_free`

## `Mathlib2.bld_nilpotent_commute_det_add`

Uses Mathlib2.gen_lin_nilpotent_det_one_add_reduced: if B is invertible then B⁻¹A is nilpotent (A, B commute) and det(B + A) = det B * det(1 + B⁻¹A) = det B. For general B apply this to B + t • 1 for the cofinitely many t with det(B + t • 1) ≠ 0 and conclude by the polynomial identity (two polynomials in t agreeing at infinitely many points), then set t = 0.

```lean
∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ), IsNilpotent A → A * B = B * A → (B + A).det = B.det
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.gen_lin_nilpotent_det_one_add_reduced）
- 完成者：r6_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`gen_lin_nilpotent_det_one_add_reduced`

## `Mathlib2.bld_one_add_div_pow_mono`

Uses Mathlib2.an2_amgm_range_pow: apply AM-GM to the n+1 numbers consisting of n copies of 1 + x/n and one copy of 1; their mean is 1 + x/(n+1). Generalises Mathlib2.ana_one_add_inv_pow_mono (x = 1).

```lean
∀ (n : ℕ) (x : ℝ), 0 ≤ x → (1 + x / ↑n) ^ n ≤ (1 + x / (↑n + 1)) ^ (n + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.an2_amgm_range_pow, Mathlib2.ana_one_add_inv_pow_mono）
- 完成者：r6_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`an2_amgm_range_pow`

## `Mathlib2.bld_prod_sin_pi_div_odd`

Uses Mathlib2.geo_prod_sin_pi_mul_div with 2n factors: the reflection k ↦ 2n+1-k pairs the factors (sin(π - t) = sin t), so the square of the half product equals (2n+1)/2^(2n); take the positive square root since every factor is positive.

```lean
∀ (n : ℕ), ∏ k ∈ Finset.range n, Real.sin ((↑k + 1) * Real.pi / (2 * ↑n + 1)) = √(2 * ↑n + 1) / 2 ^ n
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.geo_prod_sin_pi_mul_div）
- 完成者：r6_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`geo_prod_sin_pi_mul_div`

## `Mathlib2.bld_rat_sq_add_sq_ne_prime_three_mod_four`

Uses Mathlib2.gen_nt_sq_add_sq_eq_prime_mul_sq: the circle x^2+y^2=p has no rational point when p ≡ 3 mod 4; clear denominators (x = u/w, y = v/w) to get u^2+v^2 = p*w^2 with w ≠ 0, contradicting the library theorem.

```lean
∀ (p : ℕ), Nat.Prime p → p % 4 = 3 → ∀ (x y : ℚ), x ^ 2 + y ^ 2 ≠ ↑p
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.gen_nt_sq_add_sq_eq_prime_mul_sq）
- 完成者：r6_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`gen_nt_sq_add_sq_eq_prime_mul_sq`

## `Mathlib2.bld_sum_inv_sqrt_div_sqrt_tendsto`

Uses Mathlib2.an2_sum_inv_sqrt_bounds: squeeze between 2(sqrt(n+1) - 1)/sqrt n and 2, both tending to 2.

```lean
Filter.Tendsto (fun n => (∑ i ∈ Finset.range n, 1 / √(↑i + 1)) / √↑n) Filter.atTop (nhds 2)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.an2_sum_inv_sqrt_bounds）
- 完成者：r6_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`an2_sum_inv_sqrt_bounds`

## `Mathlib2.bld_zmod_diag_quadratic_form_surjective`

Uses Mathlib2.alg_card_range_sq_zmod_prime: for odd p the sets {a x^2} and {c - b y^2} each have (p+1)/2 elements, so they intersect by pigeonhole in ZMod p; p = 2 by direct check.

```lean
∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (a b c : ZMod p), a ≠ 0 → b ≠ 0 → ∃ x y, a * x ^ 2 + b * y ^ 2 = c
```
- 结论：证明
- 层级：agent
- 来源：conjecture（builds on Mathlib2.alg_card_range_sq_zmod_prime）
- 完成者：r6_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`alg_card_range_sq_zmod_prime`

## `Mathlib2.calc_card_even_card_subsets`

Exactly half (2ⁿ) of the subsets of an (n+1)-set have even cardinality — involution s ↦ s ∆ {0} flips parity; or ∑ (−1)^|s| = 0 (Finset.sum_powerset_neg_one_pow_card) with total 2^(n+1).

```lean
∀ (n : ℕ), {s | Even s.card}.card = 2 ^ n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_cb
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.calc_card_idempotent_functions`

Number of idempotent self-maps of an n-set is ∑ₖ C(n,k) k^(n−k) — classify by the image S (= fixed-point set) of size k; the n−k other points map arbitrarily into S.

```lean
∀ (n : ℕ), {f | ∀ (i : Fin n), f (f i) = f i}.card = ∑ k ∈ Finset.range (n + 1), n.choose k * k ^ (n - k)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_cb
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.calc_card_perm_one_fixed_point`

Permutations of an (n+1)-set with exactly one fixed point number (n+1)·D(n) — choose the fixed point, derange the remaining n points (card_derangements_eq_numDerangements, Equiv.Perm.subtypeEquivSubtypePerm / derangements.atMostOneFixedPointEquivSum_derangements).

```lean
∀ (n : ℕ), {σ | {i | σ i = i}.card = 1}.card = (n + 1) * numDerangements n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_cb
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.calc_cos_le_quartic`

cos x ≤ 1 − x²/2 + x⁴/24 for all real x — even function so WLOG x ≥ 0; derivative of RHS − LHS is sin x − x + x³/6 ≥ 0 (previous Taylor bound), value 0 at 0.

```lean
∀ (x : ℝ), Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`ana_sin_ge_cubic_of_nonneg`

## `Mathlib2.calc_factorial_gt_div_exp_pow`

n! > (n/e)ⁿ for n ≥ 1 — eⁿ = ∑ nᵏ/k! > nⁿ/n! (a single term of the positive exponential series, Real.sum_le_exp_of_nonneg / strict since other terms are positive); or induction using (1+1/n)ⁿ < e.

```lean
∀ (n : ℕ), 0 < n → (↑n / Real.exp 1) ^ n < ↑n.factorial
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`calc_one_add_inv_pow_lt_exp`

## `Mathlib2.calc_integral_arctan_zero_one`

∫₀¹ arctan x dx = π/4 − (log 2)/2 — antiderivative x arctan x − log(1+x²)/2; FTC, arctan 1 = π/4.

```lean
∫ (x : ℝ) in 0..1, Real.arctan x = Real.pi / 4 - Real.log 2 / 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.calc_integral_log_one_add`

∫₀¹ log(1+x) dx = 2 log 2 − 1 — antiderivative (1+x)log(1+x) − x on [0,1]; FTC.

```lean
∫ (x : ℝ) in 0..1, Real.log (1 + x) = 2 * Real.log 2 - 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.calc_integral_log_sq_one_e`

∫₁^e log² x dx = e − 2 — antiderivative x log²x − 2x log x + 2x on [1,e]; FTC.

```lean
∫ (x : ℝ) in 1..Real.exp 1, Real.log x ^ 2 = Real.exp 1 - 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.calc_integral_sq_div_one_add_sq`

∫₀¹ x²/(1+x²) dx = 1 − π/4 — rewrite integrand as 1 − 1/(1+x²); arctan.

```lean
∫ (x : ℝ) in 0..1, x ^ 2 / (1 + x ^ 2) = 1 - Real.pi / 4
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.calc_integral_x_mul_sin_sq`

∫₀^π x sin²x dx = π²/4 — sin² = (1−cos 2x)/2, antiderivative x²/4 − x sin(2x)/4 − cos(2x)/8; or symmetry x ↦ π−x with integral_sin_sq.

```lean
∫ (x : ℝ) in 0..Real.pi, x * Real.sin x ^ 2 = Real.pi ^ 2 / 4
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.calc_pi_rpow_exp_lt_exp_pi`

π^e < e^π — log x / x is strictly decreasing for x ≥ e, or directly log π < π/e from log t ≤ t − 1 with t = π/e ≠ 1 (Real.log_lt_sub_one_of_pos).

```lean
Real.pi ^ Real.exp 1 < Real.exp Real.pi
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.calc_rpow_self_ge`

xˣ ≥ e^(−1/e) for x > 0 — xˣ = exp(x log x) and x log x ≥ −1/e (apply log t ≤ t − 1 to t = 1/(e x), or Real.mul_log lower bound lemmas).

```lean
∀ (x : ℝ), 0 < x → Real.exp (-Real.exp (-1)) ≤ x ^ x
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.calc_sum_mul_choose_sq`

∑ₖ k·C(n+1,k)² = (n+1)·C(2n+1,n) — absorb k·C(n+1,k) = (n+1)·C(n,k−1), then Vandermonde ∑ C(n,k−1)C(n+1,n+1−k) = C(2n+1,n) (Nat.add_choose_eq).

```lean
∀ (n : ℕ), ∑ k ∈ Finset.range (n + 2), k * (n + 1).choose k ^ 2 = (n + 1) * (2 * n + 1).choose n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_cb
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.calc_tan_ge_cubic`

tan x ≥ x + x³/3 on [0, π/2) — derivative of tan x − x − x³/3 is tan²x − x² ≥ 0 since tan x ≥ x (Real.lt_tan); monotonicity on [0,π/2).

```lean
∀ (x : ℝ), 0 ≤ x → x < Real.pi / 2 → x + x ^ 3 / 3 ≤ Real.tan x
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.calc_tendsto_sum_inv_add_log_two`

lim ∑_{k=1}^{n} 1/(n+k) = log 2 — squeeze: log((n+k+1)/(n+k)) ≤ 1/(n+k) … termwise bounds 1/(m+1) ≤ log(m+1) − log m ≤ 1/m telescope to log((2n+1)/(n+1)) ≤ S_n ≤ log 2; or via H_{2n} − H_n and Euler–Mascheroni asymptotics.

```lean
Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, 1 / (↑n + ↑k + 1)) Filter.atTop (nhds (Real.log 2))
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.calc_tsum_alternating_inv_sq`

∑ (−1)ⁿ/(n+1)² = π²/12 — equals (odd part) − (even part) of Basel sum = π²/8 − π²/24; uses hasSum_zeta_two and even/odd splitting.

```lean
∑' (n : ℕ), (-1) ^ n / (↑n + 1) ^ 2 = Real.pi ^ 2 / 12
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`calc_tsum_inv_odd_sq_aux1`

## `Mathlib2.calc_tsum_cube_div_two_pow`

∑ n³/2ⁿ = 26 — expand n³ in binomials C(n,1)+6C(n,2)+6C(n,3) and use ∑ C(n,k) rⁿ = rᵏ/(1−r)^(k+1) at r = 1/2; or telescoping with S(n)= -(n³+3n²+9n+13)/2^(n-1).

```lean
∑' (n : ℕ), ↑n ^ 3 / 2 ^ n = 26
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`calc_tsum_inv_three_consecutive_aux1`

## `Mathlib2.calc_tsum_inv_mul_two_pow`

∑_{n≥1} 1/(n 2ⁿ) = log 2 — Real.hasSum_pow_div_log_of_abs_lt_one at x = 1/2 gives −log(1/2).

```lean
∑' (n : ℕ), 1 / ((↑n + 1) * 2 ^ (n + 1)) = Real.log 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.calc_tsum_millin`

Millin series ∑_{n≥0} 1/F_{2ⁿ} = (7−√5)/2 — partial sums ∑_{n=0}^{N} 1/F_{2ⁿ} = 3 − F_{2^N − 1}/F_{2^N} for N ≥ 1 (induction, using F_{2m} = F_m L_m and d'Ocagne/Cassini), and F_{k−1}/F_k → 1/φ = (√5−1)/2.

```lean
∑' (n : ℕ), 1 / ↑(Nat.fib (2 ^ n)) = (7 - √5) / 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.calc_tsum_nat_div_factorial`

∑ n/n! = e — drop n = 0 term, n/n! = 1/(n−1)!, reindex and use Real.exp series (NormedSpace.exp / Real.exp_eq_tsum / hasSum_nat_add_iff).

```lean
∑' (n : ℕ), ↑n / ↑n.factorial = Real.exp 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.calc_tsum_sq_div_two_pow`

∑ n²/2ⁿ = 6 — write n² = n(n−1)+n, use hasSum_coe_mul_geometric_of_norm_lt_one and tsum_choose_mul_geometric (or differentiate geometric series twice) at r = 1/2.

```lean
∑' (n : ℕ), ↑n ^ 2 / 2 ^ n = 6
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_ca
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`calc_tsum_inv_three_consecutive_aux1`

## `Mathlib2.comb_card_edgeFinset_le_of_coloring_bool`

A bipartite (2-colourable) graph on n vertices has at most n²/4 edges — edges inject into (colour class true) × (colour class false), of size a·(n-a), and 4a(n-a) ≤ n².

```lean
∀ (V : Type) [inst : Fintype V] [DecidableEq V] (G : SimpleGraph V) [inst_2 : DecidableRel G.Adj] (C : G.Coloring Bool), 4 * G.edgeFinset.card ≤ Fintype.card V ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_7
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.comb_card_even_card_powerset`

A nonempty (n+1)-set has exactly 2^n subsets of even size — toggling membership of a fixed element is an involution of the powerset swapping even-size and odd-size subsets; alternatively use Finset.sum_powerset_neg_one_pow_card or Nat.sum_range_choose with the alternating sum.

```lean
∀ (n : ℕ), {s ∈ (Finset.range (n + 1)).powerset | Even s.card}.card = 2 ^ n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_4
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.comb_card_subset_pairs`

The number of pairs A ⊆ B ⊆ [n] is 3^n — group by B: ∑_B 2^|B| = ∑_k C(n,k)2^k = 3^n; or biject with functions Fin n → Fin 3.

```lean
∀ (n : ℕ), {p | p.1 ⊆ p.2}.card = 3 ^ n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_7
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.comb_card_surjective_bool`

The number of surjections from an n-set onto a 2-set is 2^n - 2 (truncated subtraction covers n = 0) — a function to Bool is non-surjective iff it is one of the two constant functions (for n ≥ 1), count the complement.

```lean
∀ (n : ℕ), Fintype.card { f // Function.Surjective f } = 2 ^ n - 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_4
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.comb_card_surjective_fin_three`

The number of surjections from an m-set (m = n+1 ≥ 1) onto a 3-set is 3^m - 3·2^m + 3 — inclusion–exclusion over the set of missed values: functions missing value i number 2^m, missing two fixed values number 1.

```lean
∀ (n : ℕ), Fintype.card { f // Function.Surjective f } + 3 * 2 ^ (n + 1) = 3 ^ (n + 1) + 3
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_4
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.comb_catalan_succ_mul`

First-order Catalan recurrence (n+2)·C_{n+1} = 2(2n+1)·C_n — from (n+1)·catalan n = centralBinom n and Nat.succ_mul_centralBinom_succ: (n+1)·centralBinom (n+1) = 2(2n+1)·centralBinom n.

```lean
∀ (n : ℕ), (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_7
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.comb_colorable_of_degree_le`

Greedy bound χ(G) ≤ Δ(G) + 1 — induction on the number of vertices: remove a vertex, colour the rest with d+1 colours, and give the removed vertex a colour not used on its ≤ d neighbours.

```lean
∀ (V : Type) [inst : Fintype V] [DecidableEq V] (G : SimpleGraph V) [inst_2 : DecidableRel G.Adj] (d : ℕ), (∀ (v : V), G.degree v ≤ d) → G.Colorable (d + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_9
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.comb_compl_connected_of_not_connected`

The complement of a disconnected graph is connected — pick a, b not G-reachable; for any x, y: if not G-reachable from each other they are adjacent in the complement, otherwise one of a, b is G-unreachable from both and is a common complement-neighbour.

```lean
∀ (V : Type) [Nonempty V] (G : SimpleGraph V), ¬G.Connected → Gᶜ.Connected
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_7
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.comb_connected_of_min_degree_half`

A graph on n vertices with every degree ≥ (n-1)/2 is connected — two non-adjacent vertices u ≠ v have neighbourhoods inside V \ {u,v} (n-2 elements) of total size ≥ n-1, so they share a neighbour; hence any two vertices are at distance ≤ 2.

```lean
∀ (V : Type) [inst : Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [inst_3 : DecidableRel G.Adj], (∀ (v : V), Fintype.card V ≤ 2 * G.degree v + 1) → G.Connected
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_4
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.comb_exists_block_sum_dvd`

Among any n integers a_0..a_{n-1} some nonempty consecutive block has sum divisible by n — the n+1 prefix sums S_0..S_n take two equal values mod n by pigeonhole; their difference is a block sum (Finset.sum_Ico_eq_sub).

```lean
∀ (n : ℕ), 0 < n → ∀ (a : ℕ → ℤ), ∃ i j, i < j ∧ j ≤ n ∧ ↑n ∣ ∑ k ∈ Finset.Ico i j, a k
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_4
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.comb_exists_two_dvd_sub`

Among n+1 integers two differ by a multiple of n — pigeonhole on residues: the map i ↦ (f i : ZMod n) from Fin (n+1) to ZMod n cannot be injective.

```lean
∀ (n : ℕ), 0 < n → ∀ (f : Fin (n + 1) → ℤ), ∃ i j, i ≠ j ∧ ↑n ∣ f i - f j
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_7
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.comb_exists_two_vertices_same_degree`

Every finite simple graph on at least two vertices has two distinct vertices of equal degree — degrees lie in {0..n-1}; if injective, degree is a bijection onto range n, so some vertex has degree 0 and another degree n-1, contradiction since the latter is adjacent to the former.

```lean
∀ (V : Type) [inst : Fintype V] [DecidableEq V] (G : SimpleGraph V) [inst_2 : DecidableRel G.Adj], 2 ≤ Fintype.card V → ∃ u v, u ≠ v ∧ G.degree u = G.degree v
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_4
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.comb_not_acyclic_of_two_le_degree`

A nonempty finite graph with minimum degree ≥ 2 contains a cycle — take a longest path; its end vertex has a second neighbour which must lie on the path, closing a cycle. Alternatively count: an acyclic graph has fewer than n edges while the handshake lemma gives ≥ n.

```lean
∀ (V : Type) [inst : Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [inst_3 : DecidableRel G.Adj], (∀ (v : V), 2 ≤ G.degree v) → ¬G.IsAcyclic
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_7
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.comb_sum_card_fixed_points_perm`

The total number of fixed points over all permutations of an m-set (m ≥ 1) is m!, i.e. the average is 1 — double count pairs (σ, i) with σ i = i: for each i the stabiliser has (m-1)! elements; or Burnside for the transitive action of Perm on Fin m.

```lean
∀ (n : ℕ), ∑ σ, {i | σ i = i}.card = (n + 1).factorial
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_7
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.comb_sum_mul_choose_sq`

∑_k k·C(n,k)² = n·C(2n-1,n-1) — use k·C(n,k) = n·C(n-1,k-1) and C(n,k) = C(n,n-k), then Vandermonde (Nat.add_choose_eq) for ∑ C(n-1,k-1)·C(n,n-k) = C(2n-1,n-1).

```lean
∀ (n : ℕ), ∑ k ∈ Finset.range (n + 1), k * n.choose k ^ 2 = n * (2 * n - 1).choose (n - 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_4
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.comb_tournament_hamiltonian_path`

Rédei: every tournament (indeed every semicomplete digraph) on n vertices has a directed Hamiltonian path — induction on n: given a path through the first n vertices, insert the new vertex v before the first path vertex that v beats (or at the end if none).

```lean
∀ (n : ℕ) (r : Fin n → Fin n → Prop), (∀ (i j : Fin n), i ≠ j → r i j ∨ r j i) → ∃ σ, ∀ (i : Fin n) (hi : ↑i + 1 < n), r (σ i) (σ ⟨↑i + 1, hi⟩)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_9
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.fld_adjoin_sqrt_two_sqrt_three_eq_adjoin_sum`

ℚ(√2, √3) = ℚ(√2 + √3): the sum is a primitive element — ⊇ is clear; for ⊆, with s = √2+√3 one has s^3 = 11√2 + 9√3, so √2 = (s^3 - 9s)/2 and √3 = (11s - s^3)/2 lie in ℚ(s).

```lean
ℚ⟮√2, √3⟯ = ℚ⟮√2 + √3⟯
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_6x
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.fld_card_circle_zmod`

The circle x^2 + y^2 = 1 over F_p (p odd) has p - (-1/p) points: p-1 if p ≡ 1 mod 4 and p+1 if p ≡ 3 mod 4 — if -1 = i^2 the substitution u = x+iy, v = x-iy gives the hyperbola uv = 1 with p-1 points; otherwise count via N = Σ_x (1 + χ(1-x^2)) and the Jacobsthal sum Σ χ(x^2 - 1)·χ(-1) = -χ(-1), or parametrize rationally by lines through (1,0).

```lean
∀ (p : ℕ) [inst : Fact (Nat.Prime p)], p ≠ 2 → {v | v.1 ^ 2 + v.2 ^ 2 = 1}.card = if p % 4 = 1 then p - 1 else p + 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_6x
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`fld_sum_quadraticChar_sq_add`、`fld_sum_quadraticChar_sq_add_aux2`

## `Mathlib2.fld_card_four_sq_add_self_add_one`

In a field with 4 elements every element other than 0, 1 is a root of X^2 + X + 1 — x^3 = 1 by FiniteField.pow_card_sub_one_eq_one, so (x - 1)(x^2 + x + 1) = 0 and x ≠ 1.

```lean
∀ (K : Type) [inst : Field K] [inst_1 : Fintype K], Fintype.card K = 4 → ∀ (x : K), x ≠ 0 → x ≠ 1 → x ^ 2 + x + 1 = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_fa
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.fld_cbrt_two_not_in_Q_sqrt_two`

The cube root of 2 does not lie in ℚ(√2) — expand (a + b√2)^3 = (a^3 + 6ab^2) + (3a^2 b + 2b^3)√2 = 2; irrationality of √2 forces b(3a^2 + 2b^2) = 0, so b = 0 and a^3 = 2; Uses Mathlib2.alg_rat_pow_ne_two at this last step.

```lean
∀ (x : ℝ), x ^ 3 = 2 → ∀ (a b : ℚ), x ≠ ↑a + ↑b * √2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_fa
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`alg_rat_pow_ne_two`

## `Mathlib2.fld_eval_eq_zero_forall_iff_dvd`

A polynomial over a finite field F_q vanishes at every point iff it is divisible by X^q - X — X^q - X = ∏_{a} (X - a) (FiniteField.roots_X_pow_card_sub_X, separable with all q roots); the factors X - a are pairwise coprime, so each dividing f gives the product dividing f; the converse is FiniteField.pow_card.

```lean
∀ (K : Type) [inst : Field K] [inst_1 : Fintype K] (f : Polynomial K), (∀ (a : K), Polynomial.eval a f = 0) ↔ Polynomial.X ^ Fintype.card K - Polynomial.X ∣ f
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_fa
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.fld_finite_field_sum_two_squares`

Every element of a finite field is a sum of two squares — in characteristic 2 every element is a square (FiniteField.isSquare_of_char_two); otherwise apply FiniteField.exists_root_sum_quadratic to X^2 and X^2 - a (card is odd), or pigeonhole on the (q+1)/2 squares.

```lean
∀ (K : Type) [inst : Field K] [Fintype K] (a : K), ∃ x y, x ^ 2 + y ^ 2 = a
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_fa
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.fld_finrank_adjoin_sqrt_two_add_sqrt_three`

[ℚ(√2+√3) : ℚ] = 4 — IntermediateField.adjoin.finrank reduces to the degree of the minimal polynomial, which is X^4 - 10X^2 + 1; Uses Mathlib2.poly_x4_sub_10x2_add_1_irreducible_int (irreducibility over ℤ, hence over ℚ by Gauss) to identify the minimal polynomial.

```lean
Module.finrank ℚ ↥ℚ⟮√2 + √3⟯ = 4
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_6x
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`fld_minpoly_sqrt_two_add_sqrt_three`

## `Mathlib2.fld_gaussianInt_isUnit_iff`

The units of ℤ[i] are exactly 1, -1, i, -i — by Zsqrtd.norm_eq_one_iff' a unit has norm re^2 + im^2 = 1, forcing (re, im) ∈ {(±1, 0), (0, ±1)}; the converse is a direct check.

```lean
∀ (z : GaussianInt), IsUnit z ↔ z = 1 ∨ z = -1 ∨ z = { re := 0, im := 1 } ∨ z = { re := 0, im := -1 }
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_fa
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.fld_gaussianInt_one_add_i_prime`

1 + i is prime in ℤ[i] — its norm is 2, a rational prime, so it is irreducible (a factorization gives norms multiplying to 2, one factor is a unit); ℤ[i] is a Euclidean domain hence a PID, so irreducible implies prime.

```lean
Prime { re := 1, im := 1 }
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_fa
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`fld_gaussianInt_prime_of_norm_prime`

## `Mathlib2.fld_irrational_cbrt_two`

The real cube root of 2 is irrational — Uses Mathlib2.alg_rat_pow_ne_two at the only step: if x = (q : ℝ) then q^3 = 2 in ℚ by Rat.cast injectivity, contradicting alg_rat_pow_ne_two 3.

```lean
∀ (x : ℝ), x ^ 3 = 2 → Irrational x
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_fa
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`alg_rat_pow_ne_two`

## `Mathlib2.fld_irrational_cos_pi_div_nine`

cos(π/9) = cos 20° is irrational — by the triple angle formula c = cos(π/9) satisfies 8c^3 - 6c - 1 = 0 (cos(π/3) = 1/2); 2c is a root of the monic integer polynomial y^3 - 3y - 1, so if rational it is an integer dividing 1, but ±1 are not roots.

```lean
Irrational (Real.cos (Real.pi / 9))
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_fa
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.fld_irrational_exp_one`

e is irrational (Fourier's proof) — if e = a/b then b!·(e - Σ_{k≤b} 1/k!) is an integer, but it equals Σ_{k>b} b!/k!, which lies strictly between 0 and 1/b ≤ 1 (bound the tail by a geometric series; Real.exp_bound / the series expansion of exp).

```lean
Irrational (Real.exp 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_fa
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.fld_irrational_logb_two_three`

log_2 3 is irrational — if log_2 3 = a/b with b > 0 then (a > 0 and) 2^a = 3^b in ℕ after clearing rpow, impossible by parity (2^a even, 3^b odd).

```lean
Irrational (Real.logb 2 3)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_fa
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.fld_irreducible_X_sq_add_X_add_one_zmod_iff`

X^2 + X + 1 is irreducible over F_p iff p ≡ 2 (mod 3) — a monic quadratic is irreducible iff it has no root; for p = 3 it is (X-1)^2; for p ≠ 3 a root is exactly an element of multiplicative order 3, which exists iff 3 | p - 1 (cyclic unit group).

```lean
∀ (p : ℕ) [inst : Fact (Nat.Prime p)], Irreducible (Polynomial.X ^ 2 + Polynomial.X + 1) ↔ p % 3 = 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_6x
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`fld_isSquare_neg_three_zmod_iff_aux1`、`fld_prime_one_mod_three_eq_sq_add_three_sq_aux3`

## `Mathlib2.fld_irreducible_X_sq_add_one_zmod_iff`

X^2 + 1 is irreducible over F_p iff p ≡ 3 (mod 4) — a monic quadratic is irreducible iff it has no root (Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three), and a root is a square root of -1, which exists iff p % 4 ≠ 3 (ZMod.exists_sq_eq_neg_one_iff).

```lean
∀ (p : ℕ) [inst : Fact (Nat.Prime p)], Irreducible (Polynomial.X ^ 2 + 1) ↔ p % 4 = 3
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_fa
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.fld_isSquare_five_zmod_iff`

5 is a quadratic residue mod a prime p ≠ 2, 5 iff p ≡ ±1 (mod 5) — since 5 ≡ 1 mod 4, ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one gives IsSquare (5 : ZMod p) ↔ IsSquare (p : ZMod 5), and the nonzero squares mod 5 are 1 and 4. (Makes the hypotheses of Mathlib2.bld4_pisano_prime_dvd_pred_of_isSquare_five checkable.)

```lean
∀ (p : ℕ) [inst : Fact (Nat.Prime p)], p ≠ 2 → p ≠ 5 → (IsSquare 5 ↔ p % 5 = 1 ∨ p % 5 = 4)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_fa
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.fld_isSquare_three_zmod_iff`

3 is a quadratic residue mod a prime p > 3 iff p ≡ ±1 (mod 12) — quadratic reciprocity (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one / _three) reduces to whether p is a square mod 3, i.e. p ≡ 1 mod 3, with a sign flip when p ≡ 3 mod 4; combine residues mod 4 and mod 3.

```lean
∀ (p : ℕ) [inst : Fact (Nat.Prime p)], 3 < p → (IsSquare 3 ↔ p % 12 = 1 ∨ p % 12 = 11)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_fa
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.fld_minpoly_sqrt_two`

The minimal polynomial of √2 over ℚ is X^2 - 2 — it is monic, annihilates √2, and is irreducible over ℚ (degree 2 without rational root since √2 is irrational); conclude with minpoly.eq_of_irreducible_of_monic.

```lean
minpoly ℚ √2 = Polynomial.X ^ 2 - 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_fa
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`alg_rat_pow_ne_two`

## `Mathlib2.fld_mul_isSquare_of_not_isSquare`

In a finite field the product of two non-squares is a square — in characteristic 2 everything is a square; otherwise the quadratic character is multiplicative with values ±1 on nonzero elements and equals -1 exactly on non-squares (quadraticChar_neg_one_iff_not_isSquare), so χ(ab) = 1.

```lean
∀ (K : Type) [inst : Field K] [Fintype K] (a b : K), ¬IsSquare a → ¬IsSquare b → IsSquare (a * b)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_fa
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.fld_pell_two_pm_one_solutions`

Every solution of x^2 - 2y^2 = ±1 with x > 0, y ≥ 0 is a power of the fundamental unit: x + y√2 = (1 + √2)^n — strong induction on y: if y = 0 then x = 1, n = 0; otherwise multiply by (1+√2)^{-1} = -1 + √2 to get (x', y') = (2y - x, x - y), which is again a solution with x' > 0 and 0 ≤ y' < y (from y ≤ x < 2y for y ≥ 1, with the edge case (1,1)).

```lean
∀ (x y : ℤ), 0 < x → 0 ≤ y → x ^ 2 - 2 * y ^ 2 = 1 ∨ x ^ 2 - 2 * y ^ 2 = -1 → ∃ n, { re := x, im := y } = { re := 1, im := 1 } ^ n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_6x
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.fld_pow_bijective_iff_coprime`

For k > 0 the power map x ↦ x^k is a permutation of F_q iff gcd(k, q-1) = 1 — it fixes 0 and on the cyclic group of units of order q-1 the k-th power map is injective iff gcd(k, q-1) = 1 (if d = gcd > 1 there is an element of order d in the kernel; conversely use Bezout u*k ≡ 1 mod q-1).

```lean
∀ (K : Type) [inst : Field K] [inst_1 : Fintype K] (k : ℕ), 0 < k → ((Function.Bijective fun x => x ^ k) ↔ k.Coprime (Fintype.card K - 1))
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_fa
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.fld_pow_char_eq_self_iff_natCast`

In any field of characteristic p the fixed points of Frobenius are exactly the prime field: x^p = x iff x is the image of a natural number — (←) Fermat's little theorem in ZMod p pushed along the cast; (→) X^p - X has at most p roots in K and the p distinct elements 0, 1, …, p-1 are roots, so they are all the roots.

```lean
∀ (K : Type) [inst : Field K] (p : ℕ) [Fact (Nat.Prime p)] [CharP K p] (x : K), x ^ p = x ↔ ∃ n, x = ↑n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_fa
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.fld_prime_eq_sq_add_mul_add_sq_iff`

A prime is represented by the Eisenstein norm form a^2 + ab + b^2 (a, b ≥ 0) iff p = 3 or p ≡ 1 (mod 3) — (→) a^2 + ab + b^2 mod 3 is never 2; (←) 3 = 1 + 1 + 1, and for p ≡ 1 mod 3 write p = c^2 + 3d^2 (the a^2 + 3b^2 theorem), then with c > d: a = c - d, b = 2d, and with c < d use the equivalent form (d - c, c + d) after symmetry, checking nonnegativity.

```lean
∀ (p : ℕ), Nat.Prime p → ((∃ a b, p = a ^ 2 + a * b + b ^ 2) ↔ p = 3 ∨ p % 3 = 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_6x
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`fld_prime_one_mod_three_eq_sq_add_three_sq`

## `Mathlib2.fld_prime_one_three_mod_eight_eq_sq_add_two_sq`

Every prime p ≡ 1 or 3 (mod 8) is of the form a^2 + 2b^2 — -2 is a square mod p (ZMod.exists_sq_eq_neg_two_iff / FiniteField.isSquare_neg_two_iff), so p | x^2 + 2; Thue's lemma gives 0 < a^2 + 2b^2 < 3p divisible by p, so it is p or 2p; in the latter case a is even and p = b^2 + 2(a/2)^2. Alternatively use that Z[√-2] is Euclidean.

```lean
∀ (p : ℕ), Nat.Prime p → p % 8 = 1 ∨ p % 8 = 3 → ∃ a b, p = a ^ 2 + 2 * b ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_6x
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`fld_prime_one_mod_three_eq_sq_add_three_sq_aux2`

## `Mathlib2.fld_sqrt_three_not_in_Q_sqrt_two`

√3 ∉ ℚ(√2) — squaring gives 3 = a^2 + 2b^2 + 2ab√2, so ab = 0 by irrationality of √2; b = 0 gives √3 = a rational, a = 0 gives 3 = 2b^2, i.e. (2b)^2 = 6, contradicting irrationality of √6.

```lean
∀ (a b : ℚ), √3 ≠ ↑a + ↑b * √2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_fa
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.fld_sum_pow_finite_field`

Complete power-sum formula over a finite field F_q: for k > 0, the sum of x^k over all x is -1 if (q-1) | k and 0 otherwise — since k > 0 the term x = 0 contributes 0, so the sum equals the sum over units, which is FiniteField.sum_pow_units.

```lean
∀ (K : Type) [inst : Field K] [inst_1 : Fintype K] (k : ℕ), 0 < k → ∑ x, x ^ k = if Fintype.card K - 1 ∣ k then -1 else 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_fa
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.fld_sum_quadratic_residues_one_mod_four`

For a prime p ≡ 1 (mod 4) the sum of the quadratic residues in [1, p-1] equals p(p-1)/4 — -1 is a residue, so r ↦ p - r is a fixed-point-free involution on the (p-1)/2 residues, pairing them into (p-1)/4 pairs each of sum p.

```lean
∀ (p : ℕ), Nat.Prime p → p % 4 = 1 → ∑ a ∈ Finset.image (fun x => x ^ 2 % p) (Finset.Icc 1 (p - 1)), a = p * (p - 1) / 4
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_6x
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`fld_card_image_sq_finite_field`

## `Mathlib2.fld_zsqrtd_neg_five_isUnit_iff`

The only units of ℤ[√-5] are ±1 — by Zsqrtd.norm_eq_one_iff' (d ≤ 0) units are the elements with re^2 + 5 im^2 = 1, which forces im = 0 and re = ±1.

```lean
∀ (z : ℤ√(-5)), IsUnit z ↔ z = 1 ∨ z = -1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_fa
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.fld_zsqrtd_neg_five_two_irreducible_not_prime`

In ℤ[√-5] the element 2 is irreducible but not prime (the classical non-UFD example) — norm a^2 + 5b^2 never equals 2, so a factorization 2 = xy (norms multiply to 4) has a factor of norm 1, a unit; yet 2 | 6 = (1+√-5)(1-√-5) while 2 divides neither factor (compare coefficients).

```lean
Irreducible 2 ∧ ¬Prime 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_6x
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.gen_an_chebyshev_index_weighted_ordered_ring`

Generalizes Mathlib2.an2_chebyshev_index_weighted: ℝ → any linearly ordered commutative ring. Proof idea: induction on n, or Chebyshev sum inequality (MonovaryOn.sum_mul_sum_le_card_mul_sum) for the monotone pair (i, a i); no division is used.

```lean
∀ (R : Type u_1) [inst : CommRing R] [inst_1 : LinearOrder R] [IsStrictOrderedRing R] (a : ℕ → R), Monotone a → ∀ (n : ℕ), (↑n - 1) * ∑ i ∈ Finset.range n, a i ≤ 2 * ∑ i ∈ Finset.range n, ↑i * a i
```
- 结论：证明
- 层级：agent
- 来源：conjecture（generalization of Mathlib2.an2_chebyshev_index_weighted）
- 完成者：gen_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.gen_an_hardy_finite_ordered_field`

Generalizes Mathlib2.r3_hardy_inequality_finite: ℝ → any linearly ordered field (no sign hypothesis, as in the original). Proof idea: the original proof is purely algebraic (telescoping bound A_k² − 2 a_k A_k ≤ ... then T ≤ 2Q, Q² ≤ T·B ⇒ T ≤ 4B, which is square-root free); redo the sub-lemmas with K in place of ℝ, using Finset.sum_mul_sq_le_sq_mul_sq for Cauchy–Schwarz.

```lean
∀ (K : Type u_1) [inst : Field K] [inst_1 : LinearOrder K] [IsStrictOrderedRing K] (a : ℕ → K) (n : ℕ), ∑ k ∈ Finset.range n, ((∑ i ∈ Finset.range (k + 1), a i) / (↑k + 1)) ^ 2 ≤ 4 * ∑ k ∈ Finset.range n, a k ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture（generalization of Mathlib2.r3_hardy_inequality_finite）
- 完成者：gen_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.gen_an_nesbitt_finset_ordered_field`

Generalizes Mathlib2.an2_nesbitt_general: ℝ → any linearly ordered field, range (n+2) → arbitrary Finset with at least 2 elements. Also implies an_nesbitt. Proof idea: with S = ∑ a, write a i/(S − a i) = S/(S − a i) − 1 and apply Cauchy–Schwarz / Sedrakyan (Finset.sum_div_pow_le or div_add_div_same style lemmas valid in ordered fields) to ∑ 1/(S − a i) with ∑ (S − a i) = (card − 1) S.

```lean
∀ (K : Type u_1) [inst : Field K] [inst_1 : LinearOrder K] [IsStrictOrderedRing K] (ι : Type u_2) (s : Finset ι) (a : ι → K), (∀ i ∈ s, 0 < a i) → 2 ≤ s.card → ↑s.card / (↑s.card - 1) ≤ ∑ i ∈ s, a i / (∑ j ∈ s, a j - a i)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（generalization of Mathlib2.an2_nesbitt_general）
- 完成者：gen_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.gen_an_perm_div_sum_ge_card`

Generalizes Mathlib2.an2_cyclic_div_ge_card: ℝ → any linearly ordered field, cyclic shift on range → an arbitrary permutation σ of an arbitrary Fintype: card ι ≤ ∑ x i / x (σ i). Also implies an_cyclic_div_ge_three. Proof idea: the ratios y i = x i / x (σ i) are positive with product 1 (Equiv.prod_comp); prove ∑ y ≥ card for positive y with ∏ y = 1 by induction (merge a term ≤ 1 with a term ≥ 1 using u + v ≥ 1 + u v), which needs no roots.

```lean
∀ (K : Type u_1) [inst : Field K] [inst_1 : LinearOrder K] [IsStrictOrderedRing K] (ι : Type u_2) [inst_3 : Fintype ι] (σ : Equiv.Perm ι) (x : ι → K), (∀ (i : ι), 0 < x i) → ↑(Fintype.card ι) ≤ ∑ i, x i / x (σ i)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（generalization of Mathlib2.an2_cyclic_div_ge_card）
- 完成者：gen_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`gen_an_amgm_finset_ordered_ring`

## `Mathlib2.gen_an_schur_nat_pow_ordered_ring`

Generalizes Mathlib2.an_schur_deg_one: ℝ → any linearly ordered commutative ring, and exponent 1 → arbitrary natural exponent t (Schur's inequality; t = 1 is the original). Proof idea: WLOG a ≥ b ≥ c; then a^t(a−b)(a−c) + b^t(b−a)(b−c) = (a−b)(a^t(a−c) − b^t(b−c)) ≥ 0 by monotonicity of x^t on nonnegatives, and the c-term is ≥ 0.

```lean
∀ (R : Type u_1) [inst : CommRing R] [inst_1 : LinearOrder R] [IsStrictOrderedRing R] (a b c : R), 0 ≤ a → 0 ≤ b → 0 ≤ c → ∀ (t : ℕ), 0 ≤ a ^ t * (a - b) * (a - c) + b ^ t * (b - a) * (b - c) + c ^ t * (c - a) * (c - b)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（generalization of Mathlib2.an_schur_deg_one）
- 完成者：gen_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.gen_comb_erdos_szekeres_linear_order`

Generalizes Mathlib2.r3_erdos_szekeres: codomain ℝ → any linear order α; domain Fin (r*s+1) → any finite linear order with more than r*s elements. Proof idea: the original pigeonhole proof on (longest increasing, longest decreasing) labels uses only the order; alternatively transport along the order isomorphism ι ≃o Fin (card ι) and restrict to the first r*s+1 elements.

```lean
∀ (α : Type u_1) [inst : LinearOrder α] (ι : Type u_2) [inst_1 : LinearOrder ι] [inst_2 : Fintype ι] (r s : ℕ), r * s < Fintype.card ι → ∀ (f : ι → α), Function.Injective f → (∃ t, r < t.card ∧ StrictMonoOn f ↑t) ∨ ∃ t, s < t.card ∧ StrictAntiOn f ↑t
```
- 结论：证明
- 层级：agent
- 来源：conjecture（generalization of Mathlib2.r3_erdos_szekeres）
- 完成者：gen_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`r3_erdos_szekeres`

## `Mathlib2.gen_lin_commutator_ne_one_card`

Generalizes Mathlib2.lin_commutator_ne_one: ℝ → any commutative ring in which the size of the matrix is nonzero (covers every characteristic-0 field, and char p with p ∤ n; false when char divides n), Fin (n+1) → Fintype. Proof idea: trace(AB − BA) = 0 but trace 1 = card ι.

```lean
∀ (R : Type u_1) [inst : CommRing R] (ι : Type u_2) [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (A B : Matrix ι ι R), ↑(Fintype.card ι) ≠ 0 → A * B - B * A ≠ 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture（generalization of Mathlib2.lin_commutator_ne_one）
- 完成者：gen_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.gen_lin_eigenvalue_root_of_aeval_eq_zero`

Generalizes Mathlib2.lin_involution_eigenvalue: ℝ → any commutative ring R acting without zero-smul-divisors (e.g. any field), and the relation f*f = 1 → an arbitrary polynomial relation p(f) = 0: every eigenvalue is a root of p (the original is p = X²−1). Proof idea: for an eigenvector v, p(f) v = p(μ) • v (Module.End.aeval_apply_of_hasEigenvector), so p(μ) • v = 0 with v ≠ 0.

```lean
∀ (R : Type u_1) [inst : CommRing R] (V : Type u_2) [inst_1 : AddCommGroup V] [inst_2 : Module R V] [NoZeroSMulDivisors R V] (f : Module.End R V) (p : Polynomial R), (Polynomial.aeval f) p = 0 → ∀ (μ : R), f.HasEigenvalue μ → p.IsRoot μ
```
- 结论：证明
- 层级：agent
- 来源：conjecture（generalization of Mathlib2.lin_involution_eigenvalue）
- 完成者：gen_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.gen_lin_skew_odd_two_mul_det`

Generalizes Mathlib2.lin_skew_odd_det_zero: ℝ → any commutative ring, with conclusion 2·det A = 0 (det A = 0 follows whenever 2 is regular; the plain conclusion is false in characteristic 2, e.g. A = 1), Fin (2n+1) → Fintype of odd cardinality. Proof idea: det A = det Aᵀ = det(−A) = (−1)^card det A = −det A.

```lean
∀ (R : Type u_1) [inst : CommRing R] (ι : Type u_2) [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (A : Matrix ι ι R), Odd (Fintype.card ι) → A.transpose = -A → 2 * A.det = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture（generalization of Mathlib2.lin_skew_odd_det_zero）
- 完成者：gen_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.gen_lin_symm_nilpotent_eq_zero_ordered`

Generalizes Mathlib2.lin_symm_nilpotent_eq_zero: ℝ → any linearly ordered commutative ring, Fin n → Fintype. Proof idea: same induction on the exponent; the key step B symmetric, B*B = 0 ⇒ B = 0 holds because the diagonal of Bᵀ*B is a sum of squares, which vanishes only if all terms vanish in an ordered ring.

```lean
∀ (R : Type u_1) [inst : CommRing R] [inst_1 : LinearOrder R] [IsStrictOrderedRing R] (ι : Type u_2) [inst_3 : Fintype ι] [inst_4 : DecidableEq ι] (A : Matrix ι ι R), A.IsSymm → IsNilpotent A → A = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture（generalization of Mathlib2.lin_symm_nilpotent_eq_zero）
- 完成者：gen_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.gen_nt_sq_sub_add_one_dvd_pow_sum`

Generalizes Mathlib2.nt_seven_dvd_pow_sum: the constants 3, 2, 7 → a, a−1, a²−a+1 for an arbitrary element a of an arbitrary commutative ring (a = 3 in ℤ gives the original). Proof idea: modulo a²−a+1 one has a² ≡ a−1 and (a−1)² ≡ −a, so a^(2n+1) ≡ a(a−1)^n and (a−1)^(n+2) ≡ −a(a−1)^n; formally induct on n with step a^(2n+3)+(a−1)^(n+3) = (a−1)(a^(2n+1)+(a−1)^(n+2)) + (a²−a+1)·a^(2n+1).

```lean
∀ (R : Type u_1) [inst : CommRing R] (a : R) (n : ℕ), a ^ 2 - a + 1 ∣ a ^ (2 * n + 1) + (a - 1) ^ (n + 2)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（generalization of Mathlib2.nt_seven_dvd_pow_sum）
- 完成者：gen_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.geo_centroid_sum_sq_dist`

For the centroid g of triangle abc, |ag|² + |bg|² + |cg|² = (|ab|² + |bc|² + |ca|²)/3 — a − g = ((a−b) + (a−c))/3 etc., expand all squared norms into inner products.

```lean
∀ {V : Type u_1} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] (a b c : V), ‖a - (1 / 3) • (a + b + c)‖ ^ 2 + ‖b - (1 / 3) • (a + b + c)‖ ^ 2 + ‖c - (1 / 3) • (a + b + c)‖ ^ 2 = (‖a - b‖ ^ 2 + ‖b - c‖ ^ 2 + ‖c - a‖ ^ 2) / 3
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.geo_cos_pi_div_five_sub_cos_two_pi_div_five`

cos 36° − cos 72° = 1/2 — double angle formula plus cos(π/5) = (1+√5)/4, or the quadratic 4c² − 2c − 1 = 0 satisfied by c = cos(π/5).

```lean
Real.cos (Real.pi / 5) - Real.cos (2 * Real.pi / 5) = 1 / 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.geo_cos_pi_div_seven_prod`

cos(π/7)cos(2π/7)cos(4π/7) = −1/8 — multiply by 8 sin(π/7) ≠ 0 and apply sin 2x = 2 sin x cos x three times to get sin(8π/7) = −sin(π/7).

```lean
Real.cos (Real.pi / 7) * Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7) = -1 / 8
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.geo_cos_sum_two_pi_div_seven`

cos(2π/7) + cos(4π/7) + cos(6π/7) = −1/2 — multiply by 2 sin(π/7) ≠ 0 and telescope with 2 sin x cos y = sin(x+y) − sin(y−x), leaving sin(π) − sin(π/7); or take real parts of the sum of the 7th roots of unity.

```lean
Real.cos (2 * Real.pi / 7) + Real.cos (4 * Real.pi / 7) + Real.cos (6 * Real.pi / 7) = -1 / 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.geo_equilateral_iff_sum_sq`

A triangle abc in the complex plane is equilateral (possibly degenerate to a point) iff a² + b² + c² = ab + bc + ca — the difference factors as (a + ωb + ω²c)(a + ω²b + ωc) with ω a primitive cube root of unity; a + ωb + ω²c = 0 says c − a is b − a rotated by 60°, and conversely equal side lengths force (c−a)/(b−a) to be a primitive 6th root of unity.

```lean
∀ (a b c : ℂ), ‖a - b‖ = ‖b - c‖ ∧ ‖b - c‖ = ‖c - a‖ ↔ a ^ 2 + b ^ 2 + c ^ 2 = a * b + b * c + c * a
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.geo_euler_quadrilateral`

Euler's quadrilateral theorem: the sum of the squared sides equals the sum of the squared diagonals plus four times the squared distance between the midpoints of the diagonals — expand every squared norm into inner products.

```lean
∀ {V : Type u_1} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] (a b c d : V), ‖a - b‖ ^ 2 + ‖b - c‖ ^ 2 + ‖c - d‖ ^ 2 + ‖d - a‖ ^ 2 = ‖a - c‖ ^ 2 + ‖b - d‖ ^ 2 + 4 * ‖(1 / 2) • (a + c) - (1 / 2) • (b + d)‖ ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.geo_leibniz_centroid`

Leibniz (moment of inertia / parallel axis) identity: for the centroid g of points x_i, Σ|p − x_i|² = n|p − g|² + Σ|g − x_i|² — write p − x_i = (p − g) + (g − x_i), expand, and the cross term vanishes because Σ(g − x_i) = 0 (empty s is trivial).

```lean
∀ {V : Type u_1} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] {ι : Type u_2} (s : Finset ι) (x : ι → V) (p : V), ∑ i ∈ s, ‖p - x i‖ ^ 2 = ↑s.card * ‖p - (↑s.card)⁻¹ • ∑ j ∈ s, x j‖ ^ 2 + ∑ i ∈ s, ‖(↑s.card)⁻¹ • ∑ j ∈ s, x j - x i‖ ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_5
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.geo_median_length`

Apollonius' median length formula: the squared distance from a to the midpoint of b and c is (2|ab|² + 2|ac|² − |bc|²)/4 — expand all squared norms into inner products (or apply the parallelogram law to a−b and a−c).

```lean
∀ {V : Type u_1} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] (a b c : V), ‖a - (1 / 2) • (b + c)‖ ^ 2 = (2 * ‖a - b‖ ^ 2 + 2 * ‖a - c‖ ^ 2 - ‖b - c‖ ^ 2) / 4
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.geo_perp_bisector_iff`

p is equidistant from a and b iff p − midpoint(a,b) is orthogonal to b − a — ‖p−a‖² − ‖p−b‖² = 2⟨p − (a+b)/2, b − a⟩, and norms are nonnegative.

```lean
∀ {V : Type u_1} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] (a b p : V), ‖p - a‖ = ‖p - b‖ ↔ inner ℝ (p - (1 / 2) • (a + b)) (b - a) = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.geo_sin_mul_sin_pi_div_three_sub_add`

sin x · sin(π/3 − x) · sin(π/3 + x) = sin(3x)/4 — expand with addition formulas (sin(π/3)=√3/2, cos(π/3)=1/2) to get sin x (3/4 cos²x − 1/4 sin²x), then use the triple angle formula.

```lean
∀ (x : ℝ), Real.sin x * Real.sin (Real.pi / 3 - x) * Real.sin (Real.pi / 3 + x) = Real.sin (3 * x) / 4
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.geo_sin_pi_div_ten`

sin(π/10) = (√5 − 1)/4 — sin(π/10) = cos(2π/5) = 2cos²(π/5) − 1 and Mathlib's cos(π/5) = (1+√5)/4.

```lean
Real.sin (Real.pi / 10) = (√5 - 1) / 4
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.geo_stewart`

Stewart's theorem in vector form: for d = (1−t)b + tc on line bc, |ad|² = (1−t)|ab|² + t|ac|² − t(1−t)|bc|² — write a − d = (1−t)(a−b) + t(a−c) and expand squared norms via inner products.

```lean
∀ {V : Type u_1} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] (a b c : V) (t : ℝ), ‖a - ((1 - t) • b + t • c)‖ ^ 2 = (1 - t) * ‖a - b‖ ^ 2 + t * ‖a - c‖ ^ 2 - t * (1 - t) * ‖b - c‖ ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.geo_sum_cos_two_pi_mul_div`

The real parts of the n-th roots of unity sum to zero for n ≥ 2 — take the real part of the geometric sum Σ ζ^k = 0 for ζ = exp(2πi/n) (a primitive n-th root, IsPrimitiveRoot.geom_sum_eq_zero).

```lean
∀ (n : ℕ), 2 ≤ n → ∑ k ∈ Finset.range n, Real.cos (2 * Real.pi * ↑k / ↑n) = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.geo_sum_sq_dist_roots_of_unity`

The sum of squared distances from a point of the unit circle to the vertices of the regular n-gon inscribed in it is 2n — ‖z − ζ^k‖² = 2 − 2 Re(z · conj ζ^k), and Σ ζ^k = 0 for the primitive root ζ = exp(2πi/n), n ≥ 2.

```lean
∀ (n : ℕ), 2 ≤ n → ∀ (z : ℂ), ‖z‖ = 1 → ∑ k ∈ Finset.range n, ‖z - Complex.exp (2 * ↑Real.pi * Complex.I * ↑k / ↑n)‖ ^ 2 = 2 * ↑n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.geo_tan_pi_div_eight`

tan(π/8) = √2 − 1 — use tan = sin/cos with Mathlib's closed forms for sin(π/8), cos(π/8), or tan(x/2) = (1 − cos x)/sin x at x = π/4.

```lean
Real.tan (Real.pi / 8) = √2 - 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.geo_unit_one_add_div_conj`

For z on the unit circle with z ≠ -1, (1+z)/(1+conj z) = z — conj z = z⁻¹ since z * conj z = ‖z‖² = 1, then clear denominators.

```lean
∀ (z : ℂ), ‖z‖ = 1 → z ≠ -1 → (1 + z) / (1 + (starRingEnd ℂ) z) = z
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.geo_unit_sum_zero_equilateral`

Three unit complex numbers with sum zero form an equilateral triangle of side √3 — ‖a+b‖² = ‖c‖² = 1 and the parallelogram law give ‖a−b‖² = 2+2−1 = 3; symmetric for the others.

```lean
∀ (a b c : ℂ), ‖a‖ = 1 → ‖b‖ = 1 → ‖c‖ = 1 → a + b + c = 0 → ‖a - b‖ = √3 ∧ ‖b - c‖ = √3 ∧ ‖c - a‖ = √3
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_5
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.geo_unit_sum_zero_sum_sq`

For unit complex numbers with a+b+c = 0, also a²+b²+c² = 0 — conj a = a⁻¹ etc., so ab+bc+ca = abc·conj(a+b+c) = 0, and a²+b²+c² = (a+b+c)² − 2(ab+bc+ca).

```lean
∀ (a b c : ℂ), ‖a‖ = 1 → ‖b‖ = 1 → ‖c‖ = 1 → a + b + c = 0 → a ^ 2 + b ^ 2 + c ^ 2 = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_5
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lib_antitone_convex_nat_seq_eq_of_succ_eq`

promoted from Mathlib2.bld5_nilpotent_pow_rank_succ_eq_zero_aux1 (conclusion simplified): a non-increasing convex sequence of naturals that stalls once is constant from then on.

```lean
∀ (r : ℕ → ℕ), (∀ (k : ℕ), r (k + 1) ≤ r k) → (∀ (k : ℕ), 2 * r (k + 1) ≤ r k + r (k + 2)) → ∀ (k : ℕ), r (k + 1) = r k → ∀ (j : ℕ), r (k + j) = r k
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：curator_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld5_nilpotent_pow_rank_succ_eq_zero_aux1`

## `Mathlib2.lib_convexOn_univ_eq_of_bddAbove`

A convex function on a real vector space that is bounded above is constant (Liouville-type property of convex functions). Promoted and generalised from Mathlib2.ana_convex_bddAbove_const_aux1 (the case E = ℝ).

```lean
∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : Module ℝ E] (f : E → ℝ), ConvexOn ℝ Set.univ f → ∀ (M : ℝ), (∀ (x : E), f x ≤ M) → ∀ (x y : E), f x = f y
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.ana_convex_bddAbove_const_aux1）
- 完成者：curator_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`ana_convex_bddAbove_const`

## `Mathlib2.lib_convex_nat_seq_add_mul_sub_le`

For a convex ℕ-valued sequence, a drop d = f m - f (m+1) ≥ 0 at step m propagates backwards, so f 0 ≥ f (m+1) + (m+1)·d (quantitative form; d ≥ 1 gives f (m+1) + (m+1) ≤ f 0). Promoted and generalised from Mathlib2.bld3_rank_pow_card_stabilizes_aux2 (and _aux1; used for rank stabilisation of matrix powers).

```lean
∀ (f : ℕ → ℕ), (∀ (k : ℕ), 2 * f (k + 1) ≤ f k + f (k + 2)) → ∀ (m : ℕ), f (m + 1) ≤ f m → f (m + 1) + (m + 1) * (f m - f (m + 1)) ≤ f 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.bld3_rank_pow_card_stabilizes_aux2）
- 完成者：curator_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lib_expanding_iterate_dist_le`

Iterates of a distance non-decreasing (expanding) self-map of a pseudometric space are again expanding: dist x y ≤ dist (f^[k] x) (f^[k] y). Promoted from Mathlib2.top_expanding_compact_isometry_aux1 (the isometry analogue is re-derived in top_isometry_compact_surjective); generalised from metric to pseudometric spaces.

```lean
∀ {X : Type u_1} [inst : PseudoMetricSpace X] (f : X → X), (∀ (x y : X), dist x y ≤ dist (f x) (f y)) → ∀ (k : ℕ) (x y : X), dist x y ≤ dist (f^[k] x) (f^[k] y)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.top_expanding_compact_isometry_aux1）
- 完成者：curator_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lib_fib_add_modEq_mul_fib_succ`

Fibonacci shift congruence: if N ∣ F_m then F_(i+m) ≡ F_i * F_(m+1) (mod N), i.e. shifting by a zero of the sequence mod N multiplies by F_(m+1). Promoted and generalised from Mathlib2.p3_cor1_aux3 (the case N = F_(n+1); re-derived in p3_cor1_aux4, p3_aux_period_aux4, bld2_pisano_fib_dvd_four_mul).

```lean
∀ (N m i : ℕ), N ∣ Nat.fib m → Nat.fib (i + m) ≡ Nat.fib i * Nat.fib (m + 1) [MOD N]
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.p3_cor1_aux3）
- 完成者：curator_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lib_fib_add_ring_cast`

promoted from Mathlib2.bld5_pisano_mul_dvd_mul_aux1 (generalised from commutative rings to any ring; same identity as Mathlib2.bld5_pisano_five_pow_aux1 over ℤ): subtraction form of the Fibonacci addition law F_{a+b} = F_a F_{b+1} + F_{a+1} F_b - F_a F_b, with no index shift.

```lean
∀ (R : Type u_1) [inst : Ring R] (a b : ℕ), ↑(Nat.fib (a + b)) = ↑(Nat.fib a) * ↑(Nat.fib (b + 1)) + ↑(Nat.fib (a + 1)) * ↑(Nat.fib b) - ↑(Nat.fib a) * ↑(Nat.fib b)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：curator_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld5_pisano_mul_dvd_mul_aux1`

## `Mathlib2.lib_fib_dvd_fib_iff`

Fibonacci divisibility criterion: for m ≠ 2, F_m ∣ F_n iff m ∣ n (converse of Nat.fib_dvd, via Nat.fib_gcd). Promoted and generalised from Mathlib2.bld2_pisano_fib_odd_eq_aux2 (also used in bld2_pisano_fib_odd_eq / bld2_pisano_fib_even_eq).

```lean
∀ (m n : ℕ), m ≠ 2 → (Nat.fib m ∣ Nat.fib n ↔ m ∣ n)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.bld2_pisano_fib_odd_eq_aux2）
- 完成者：curator_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lib_fib_mul_modEq_sq_of_dvd`

promoted from Mathlib2.bld5_pisano_mul_dvd_mul_aux2 (the square-zero lifting lemma specialised to ZMod (m^2), stated as congruences): if F_N = m·u and F_{N+1} = 1 + m·v then modulo m^2, F_{jN} ≡ j·m·u and F_{jN+1} ≡ 1 + j·m·v. For the general ring form (μ^2 = 0) use the aux lemma directly.

```lean
∀ (m N : ℕ) (u v : ℤ), ↑(Nat.fib N) = ↑m * u → ↑(Nat.fib (N + 1)) = 1 + ↑m * v → ∀ (j : ℕ), ↑(Nat.fib (j * N)) ≡ ↑j * ↑m * u [ZMOD ↑(m ^ 2)] ∧ ↑(Nat.fib (j * N + 1)) ≡ 1 + ↑j * ↑m * v [ZMOD ↑(m ^ 2)]
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：curator_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld5_pisano_mul_dvd_mul_aux2`

## `Mathlib2.lib_fib_sq_modEq_neg_one_pow`

Cassini's identity as a congruence: F_n^2 ≡ (-1)^(n+1) modulo F_(n+1); in particular F_n^4 ≡ 1 (mod F_(n+1)). Sharpens Mathlib2.p3_cor1_aux1 / p3_cor1_aux2 (squared Cassini), which re-derive Cassini although Mathlib2.an_cassini_int exists (also re-proved as p3_aux_period_aux1 and r3_fib_iff_five_sq_pm_four_is_square_s1h1).

```lean
∀ (n : ℕ), ↑(Nat.fib n) ^ 2 ≡ (-1) ^ (n + 1) [ZMOD ↑(Nat.fib (n + 1))]
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.p3_cor1_aux2）
- 完成者：curator_1
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`an_cassini_int`

## `Mathlib2.lib_fib_two_mul_add_one_cast_eq_fib_succ_mul_lucas`

promoted from Mathlib2.bld5_pisano_lucas_odd_eq_aux1 (generalised from ℤ to any commutative ring): F_{2n+1} = F_{n+1} L_n - (-1)^n.

```lean
∀ (R : Type u_1) [inst : CommRing R] (n : ℕ), ↑(Nat.fib (2 * n + 1)) = ↑(Nat.fib (n + 1)) * ↑(Mathlib2.p3_lucas n) - (-1) ^ n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：curator_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld5_pisano_lucas_odd_eq_aux1`、`p3_lucas`

## `Mathlib2.lib_fib_two_mul_ring_cast`

promoted from Mathlib2.bld4_pisano_lucas_dvd_four_mul_aux1 (generalised from commutative rings to any ring): cast form of Nat.fib_two_mul without truncated subtraction, F_{2m} = F_m (2 F_{m+1} - F_m).

```lean
∀ (R : Type u_1) [inst : Ring R] (m : ℕ), ↑(Nat.fib (2 * m)) = ↑(Nat.fib m) * (2 * ↑(Nat.fib (m + 1)) - ↑(Nat.fib m))
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：curator_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld4_pisano_lucas_dvd_four_mul_aux1`

## `Mathlib2.lib_finset_exists_cut_sum_le_four_mul`

Weighted max-cut bound: for a symmetric, zero-diagonal weight f : V → V → ℕ on a finset S there is a cut (s, S \ s) carrying at least half of the total weight (the ordered-pair sum over S × S is ≤ 4 × the one-directional cut sum). Promoted from Mathlib2.comb_exists_cut_half_edges_aux1; generalised to an arbitrary universe.

```lean
∀ (V : Type u_1) [inst : DecidableEq V] (f : V → V → ℕ), (∀ (u v : V), f u v = f v u) → (∀ (u : V), f u u = 0) → ∀ (S : Finset V), ∃ s ⊆ S, ∑ u ∈ S, ∑ v ∈ S, f u v ≤ 4 * ∑ u ∈ s, ∑ v ∈ S \ s, f u v
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.comb_exists_cut_half_edges_aux1）
- 完成者：curator_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lib_isIdempotentElem_of_mul_self_eq_one`

Spectral projections of an involution: if a^2 = 1 and 2 is invertible then (1 + a)/2 and (1 - a)/2 are idempotent, in any ring. Promoted and generalised from Mathlib2.bld_involution_trace_rank_aux2 (the case of matrices over a char-0 field; used in bld_involution_rank_add_rank, bld2_involution_iff_rank_add_rank, bld3_rank_involution_defect).

```lean
∀ (R : Type u_1) [inst : Ring R] [inst_1 : Invertible 2] (a : R), a * a = 1 → IsIdempotentElem (⅟2 * (1 + a)) ∧ IsIdempotentElem (⅟2 * (1 - a))
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.bld_involution_trace_rank_aux2）
- 完成者：curator_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lib_list_exists_perm_isChain_of_pairwise_or`

Rédei's theorem in list form (every tournament has a Hamiltonian path): a duplicate-free list whose distinct elements are pairwise r-comparable (r a b ∨ r b a) can be permuted into an r-chain. Promoted from Mathlib2.comb_tournament_hamiltonian_path_aux2; generalised to an arbitrary universe.

```lean
∀ {α : Type u_1} (r : α → α → Prop) (l : List α), l.Nodup → (∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b ∨ r b a) → ∃ l', l'.Perm l ∧ List.IsChain r l'
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.comb_tournament_hamiltonian_path_aux2）
- 完成者：curator_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lib_lucas_two_mul_ring_cast`

promoted from Mathlib2.bld5_prime_dvd_lucas_four_mul_mod_eight_aux1 (generalised from commutative rings to any ring): Lucas doubling L_{2m} = L_m^2 - 2(-1)^m.

```lean
∀ (R : Type u_1) [inst : Ring R] (m : ℕ), ↑(Mathlib2.p3_lucas (2 * m)) = ↑(Mathlib2.p3_lucas m) ^ 2 - 2 * (-1) ^ m
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：curator_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld5_prime_dvd_lucas_four_mul_mod_eight_aux1`、`p3_lucas`

## `Mathlib2.lib_matrix_charpoly_eq_X_pow_of_isNilpotent`

The characteristic polynomial of a nilpotent square matrix over a reduced commutative ring is X^n (n = size). Promoted from the inline first step of Mathlib2.gen_lin_nilpotent_pow_card_reduced (also re-derived in gen_lin_nilpotent_det_one_add_reduced).

```lean
∀ (R : Type u_1) [inst : CommRing R] [IsReduced R] (ι : Type u_2) [inst_2 : Fintype ι] [inst_3 : DecidableEq ι] (A : Matrix ι ι R), IsNilpotent A → A.charpoly = Polynomial.X ^ Fintype.card ι
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.gen_lin_nilpotent_pow_card_reduced）
- 完成者：curator_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lib_matrix_det_add_of_isNilpotent_of_commute`

A nilpotent perturbation commuting with an invertible matrix does not change the determinant: det (B + A) = det B, over any reduced commutative ring and any finite index type. Promoted and generalised from Mathlib2.bld_nilpotent_commute_det_add_aux1 (which is the case Fin n, ℝ; builds on gen_lin_nilpotent_det_one_add_reduced).

```lean
∀ (R : Type u_1) [inst : CommRing R] [IsReduced R] (ι : Type u_2) [inst_2 : Fintype ι] [inst_3 : DecidableEq ι] (A B : Matrix ι ι R), IsNilpotent A → Commute A B → IsUnit B.det → (B + A).det = B.det
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.bld_nilpotent_commute_det_add_aux1）
- 完成者：curator_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`gen_lin_nilpotent_det_one_add_reduced`

## `Mathlib2.lib_matrix_ker_mulVecLin_le_ker_mul`

Null space of a product: ker N ≤ ker (M * N), over any commutative semiring (dual companion of range (M * N) ≤ range M). Promoted and generalised from Mathlib2.bld3_rank_tripotent_defect_aux1 (kernel companion; used inline in rank-defect proofs).

```lean
∀ (R : Type u_1) [inst : CommSemiring R] (m : Type u_2) (n : Type u_3) (p : Type u_4) [inst_1 : Fintype n] [inst_2 : Fintype p] (M : Matrix m n R) (N : Matrix n p R), LinearMap.ker N.mulVecLin ≤ LinearMap.ker (M * N).mulVecLin
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.bld3_rank_tripotent_defect_aux1）
- 完成者：curator_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lib_matrix_mulVec_eq_zero_of_rank_mul_self_eq`

promoted from Mathlib2.bld4_fitting_range_inter_ker_pow_card_aux2: if rank(N^2) = rank N then range N meets ker N trivially, i.e. N(Nv) = 0 implies Nv = 0.

```lean
∀ (K : Type u_1) [inst : Field K] (ι : Type u_2) [inst_1 : Fintype ι] [DecidableEq ι] (N : Matrix ι ι K), (N * N).rank = N.rank → ∀ (v : ι → K), N.mulVec (N.mulVec v) = 0 → N.mulVec v = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：curator_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld4_fitting_range_inter_ker_pow_card_aux2`

## `Mathlib2.lib_matrix_range_mulVecLin_mul_le`

Column space of a product: range (M * N) ≤ range M, over any commutative semiring and rectangular index types. Promoted and generalised from Mathlib2.bld3_rank_tripotent_defect_aux1 (same step inline in bld3_rank_involution_defect, bld_frobenius_rank_inequality).

```lean
∀ (R : Type u_1) [inst : CommSemiring R] (m : Type u_2) (n : Type u_3) (p : Type u_4) [inst_1 : Fintype n] [inst_2 : Fintype p] (M : Matrix m n R) (N : Matrix n p R), LinearMap.range (M * N).mulVecLin ≤ LinearMap.range M.mulVecLin
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.bld3_rank_tripotent_defect_aux1）
- 完成者：curator_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lib_matrix_rank_le_iff_exists_factorization`

Rank factorisation, as a characterisation of rank: an n×p matrix B over a field has rank ≤ r iff it factors as B = M * N through K^r (M : n×r, N : r×p). The case r = rank B is Mathlib2.bld_frobenius_rank_inequality_aux1, from which this is promoted.

```lean
∀ (K : Type u_1) [inst : Field K] (n : Type u_2) (p : Type u_3) [Fintype n] [inst_2 : Fintype p] (B : Matrix n p K) (r : ℕ), B.rank ≤ r ↔ ∃ M N, B = M * N
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.bld_frobenius_rank_inequality_aux1）
- 完成者：curator_1
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld_frobenius_rank_inequality_aux1`

## `Mathlib2.lib_matrix_transpose_mul_self_eq_zero_iff`

Over a linearly ordered ring, Bᵀ * B = 0 iff B = 0, for rectangular B (the Gram matrix vanishes only for the zero matrix; diagonal entries are sums of squares). Promoted from Mathlib2.gen_lin_symm_nilpotent_eq_zero_ordered_aux1 (also inline in lin_symm_nilpotent_eq_zero); generalised to rectangular matrices and to an iff.

```lean
∀ (R : Type u_1) [inst : Ring R] [inst_1 : LinearOrder R] [IsStrictOrderedRing R] (m : Type u_2) (n : Type u_3) [inst_3 : Fintype m] (B : Matrix m n R), B.transpose * B = 0 ↔ B = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.gen_lin_symm_nilpotent_eq_zero_ordered_aux1）
- 完成者：curator_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lib_monotone_sub_of_convex_seq`

A convex sequence (second differences nonnegative) in an ordered abelian group has monotone increments f(k+1) - f(k). Promoted and generalised from Mathlib2.bld3_rank_pow_card_stabilizes_aux1 (also used with bld2_rank_pow_convex, bld3_nilpotent_rank_pow_le).

```lean
∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : PartialOrder α] [IsOrderedAddMonoid α] (f : ℕ → α), (∀ (k : ℕ), f (k + 1) + f (k + 1) ≤ f k + f (k + 2)) → Monotone fun k => f (k + 1) - f k
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.bld3_rank_pow_card_stabilizes_aux1）
- 完成者：curator_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lib_mul_pow_mul_sub_le_pow_succ_sub_pow_succ`

Two-sided tangent-line (generalised Bernoulli / mean-value) inequality for powers in a linearly ordered commutative ring: for a, b ≥ 0, (m+1) a^m (b - a) ≤ b^(m+1) - a^(m+1) ≤ (m+1) b^m (b - a). Promoted from Mathlib2.gen_an_amgm_finset_ordered_ring_aux1 (the left inequality).

```lean
∀ (R : Type u_1) [inst : CommRing R] [inst_1 : LinearOrder R] [IsStrictOrderedRing R] (a b : R), 0 ≤ a → 0 ≤ b → ∀ (m : ℕ), (↑m + 1) * a ^ m * (b - a) ≤ b ^ (m + 1) - a ^ (m + 1) ∧ b ^ (m + 1) - a ^ (m + 1) ≤ (↑m + 1) * b ^ m * (b - a)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.gen_an_amgm_finset_ordered_ring_aux1）
- 完成者：curator_1
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`gen_an_amgm_finset_ordered_ring_aux1`

## `Mathlib2.lib_orderOf_eq_prime_of_card_prime_mul_prime_of_not_isCyclic`

promoted from Mathlib2.bld3_card_conjClasses_of_card_prime_mul_prime_aux1 (order part, hypothesis weakened from non-abelian to non-cyclic): in a non-cyclic group of order pq every non-identity element has order p or q. (The aux lemma also gives |C(a)| = orderOf a in the non-abelian case.)

```lean
∀ (p q : ℕ), Nat.Prime p → Nat.Prime q → ∀ (G : Type u_1) [inst : Group G], Nat.card G = p * q → ¬IsCyclic G → ∀ (a : G), a ≠ 1 → orderOf a = p ∨ orderOf a = q
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：curator_3
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lib_pisano_lucas_two_mul_dvd_and_dvd_four_mul`

promoted from Mathlib2.bld5_pisano_lucas_odd_eq_aux3 (combined with Mathlib2.bld4_pisano_lucas_dvd_four_mul): for n ≥ 2 the Pisano period of the Lucas number L_n is 2n or 4n — it is a multiple of 2n and a divisor of 4n.

```lean
∀ (n : ℕ), 2 ≤ n → 2 * n ∣ Mathlib2.p3_pisano (Mathlib2.p3_lucas n) ∧ Mathlib2.p3_pisano (Mathlib2.p3_lucas n) ∣ 4 * n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：curator_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld4_pisano_lucas_dvd_four_mul`、`bld5_pisano_lucas_odd_eq_aux3`、`p3_lucas`、`p3_pisano`

## `Mathlib2.lib_polynomial_fermat_quotients_eq_C`

promoted from Mathlib2.poly_ratfunc_fermat_curve_const_aux1 (DecidableEq dropped, both quotients): polynomial FLT without coprimality in quotient form — if A^n + B^n = E^n with n ≥ 3, E ≠ 0 in char 0 then A/E and B/E are constant rational functions.

```lean
∀ {k : Type u_1} [inst : Field k] [CharZero k] (n : ℕ), 3 ≤ n → ∀ (A B E : Polynomial k), E ≠ 0 → A ^ n + B ^ n = E ^ n → ∃ c d, (algebraMap (Polynomial k) (RatFunc k)) A / (algebraMap (Polynomial k) (RatFunc k)) E = RatFunc.C c ∧ (algebraMap (Polynomial k) (RatFunc k)) B / (algebraMap (Polynomial k) (RatFunc k)) E = RatFunc.C d
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：curator_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`poly_ratfunc_fermat_curve_const_aux1`

## `Mathlib2.lib_polynomial_natDegree_radical_eq_card_roots_toFinset`

promoted from Mathlib2.poly_abc_distinct_roots_complex_aux1 (strengthened from ≤ to =): over an algebraically closed field the degree of the radical of a nonzero polynomial is its number of distinct roots.

```lean
∀ {k : Type u_1} [inst : Field k] [inst_1 : DecidableEq k] [IsAlgClosed k] (p : Polynomial k), p ≠ 0 → (UniqueFactorizationMonoid.radical p).natDegree = p.roots.toFinset.card
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：curator_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`poly_abc_distinct_roots_complex_aux1`

## `Mathlib2.lib_pow_mul_pow_eq_of_mul_eq_central_mul`

Commutation of powers when the commutator is central (class-2 / Heisenberg relation): if c commutes with a, b and b*a = c*a*b then b^k * a^l = c^(k*l) * a^l * b^k. Promoted and generalised from Mathlib2.bld3_mul_pow_prime_of_card_prime_cube_aux1 (the l = 1 case; see also _aux2 for (a*b)^k = a^k*b^k*c^(k.choose 2)).

```lean
∀ {M : Type u_1} [inst : Monoid M] (a b c : M), Commute c a → Commute c b → b * a = c * a * b → ∀ (k l : ℕ), b ^ k * a ^ l = c ^ (k * l) * a ^ l * b ^ k
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.bld3_mul_pow_prime_of_card_prime_cube_aux1）
- 完成者：curator_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`bld3_mul_pow_prime_of_card_prime_cube_aux1`

## `Mathlib2.lib_radical_pow_dvd_of_irreducible_pow_dvd`

promoted from Mathlib2.poly_no_consecutive_powerful_aux1 (generalised from k[X], n = 2 to any normalised UFM and any exponent): if every irreducible factor of g occurs to the n-th power then (radical g)^n divides g.

```lean
∀ {M : Type u_1} [inst : CancelCommMonoidWithZero M] [inst_1 : NormalizationMonoid M] [inst_2 : UniqueFactorizationMonoid M] (n : ℕ) (g : M), (∀ (p : M), Irreducible p → p ∣ g → p ^ n ∣ g) → UniqueFactorizationMonoid.radical g ^ n ∣ g
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：curator_3
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lib_real_sqrt_sub_sqrt_bounds`

Two-sided mean-value bound for the square root: (b-a)/(2√b) ≤ √b - √a ≤ (b-a)/(2√a) for 0 < a ≤ b (the telescoping estimate behind ∑ 1/√k ~ 2√n). Promoted and generalised from Mathlib2.an2_sum_inv_sqrt_bounds_aux1 (the case b = a + 1; used in bld_sum_inv_sqrt_div_sqrt_tendsto).

```lean
∀ (a b : ℝ), 0 < a → a ≤ b → (b - a) / (2 * √b) ≤ √b - √a ∧ √b - √a ≤ (b - a) / (2 * √a)
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.an2_sum_inv_sqrt_bounds_aux1）
- 完成者：curator_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lib_simpleGraph_sum_degree_sq_le_card_mul_card_edgeFinset`

In a triangle-free graph on n vertices with e edges the sum of squared degrees is at most n * e (sum deg u + deg v ≤ n over the edges); this is the key step of Mantel's theorem. Promoted from Mathlib2.bld2_mantel_equality_regular_aux1 (also proved inline in bld_mantel_triangle_free); generalised to an arbitrary universe.

```lean
∀ (V : Type u_1) [inst : Fintype V] [DecidableEq V] (G : SimpleGraph V) [inst_2 : DecidableRel G.Adj], G.CliqueFree 3 → ∑ v, G.degree v ^ 2 ≤ Fintype.card V * G.edgeFinset.card
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.bld2_mantel_equality_regular_aux1）
- 完成者：curator_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lib_sylow_card_eq_pow_and_index_eq`

Order and index of a Sylow p-subgroup: if |G| = p^n * m with p ∤ m then |P| = p^n and [G : P] = m. Promoted and generalised from Mathlib2.bld3_card_sylow_of_card_prime_mul_prime_aux1 (the case |G| = r*s; same computation inline in alg_isCyclic_of_card_eq_prime_mul_prime, bld_center_eq_bot_of_card_prime_mul_prime).

```lean
∀ (p : ℕ) [Fact (Nat.Prime p)] (G : Type u_1) [inst : Group G] (n m : ℕ), Nat.card G = p ^ n * m → ¬p ∣ m → ∀ (P : Sylow p G), Nat.card ↥↑P = p ^ n ∧ (↑P).index = m
```
- 结论：证明
- 层级：agent
- 来源：conjecture（curation of Mathlib2.bld3_card_sylow_of_card_prime_mul_prime_aux1）
- 完成者：curator_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lin_commutator_ne_one`

A commutator of real square matrices of positive size is never the identity — take traces: tr(AB − BA) = 0 by trace_mul_comm while tr I = n + 1 ≠ 0.

```lean
∀ (n : ℕ) (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ), A * B - B * A ≠ 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lin_commutator_sq_scalar`

The square of a commutator of 2×2 matrices is the scalar matrix −det(AB−BA)·I — the commutator C has trace 0, so 2×2 Cayley–Hamilton gives C² = −(det C) I.

```lean
∀ (R : Type) [inst : CommRing R] (A B : Matrix (Fin 2) (Fin 2) R), (A * B - B * A) * (A * B - B * A) = -(A * B - B * A).det • 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`lin_cayley_hamilton_two`

## `Mathlib2.lin_gram_det_eq_zero_iff`

The Gram determinant of two vectors vanishes exactly when they are linearly dependent — the determinant is ‖x‖²‖y‖² − ⟨x,y⟩²; use the equality case of Cauchy–Schwarz (inner_mul_inner_self_le with equality iff one vector is a multiple of the other) and LinearIndependent.pair_iff.

```lean
∀ (V : Type) [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] (x y : V), !![inner ℝ x x, inner ℝ x y; inner ℝ y x, inner ℝ y y].det = 0 ↔ ¬LinearIndependent ℝ ![x, y]
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_5
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lin_gram_det_nonneg`

The 2×2 Gram determinant of two vectors in a real inner product space is nonnegative — expand with det_fin_two; it is Cauchy–Schwarz ⟨x,y⟩² ≤ ⟨x,x⟩⟨y,y⟩ plus symmetry of the inner product.

```lean
∀ (V : Type) [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] (x y : V), 0 ≤ !![inner ℝ x x, inner ℝ x y; inner ℝ y x, inner ℝ y y].det
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lin_idempotent_join`

For commuting idempotent matrices A, B the join A + B − AB is idempotent — it equals I − (I − A)(I − B), a product of commuting idempotents; or expand and rewrite with the three hypotheses.

```lean
∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ), A * A = A → B * B = B → A * B = B * A → (A + B - A * B) * (A + B - A * B) = A + B - A * B
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_5
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lin_idempotent_rank_complement`

For an idempotent matrix, rank A + rank(I − A) = n — ≤ from A(I − A) = 0 (Matrix.rank_add_rank_le_card_of_mul_eq_zero), ≥ from subadditivity of rank applied to A + (I − A) = I.

```lean
∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A * A = A → A.rank + (1 - A).rank = n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_5
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lin_idempotent_trace_eq_rank`

The trace of an idempotent rational matrix equals its rank — toLin' A is a projection onto its range (LinearMap.IsProj), so LinearMap.IsProj.trace gives trace = finrank(range) = rank; transfer between Matrix.trace and LinearMap.trace.

```lean
∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ), A * A = A → A.trace = ↑A.rank
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_5
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lin_involution_eigenvalue`

Every eigenvalue of a linear involution is 1 or -1 — take an eigenvector v; v = f (f v) = μ² v with v ≠ 0 gives μ² = 1.

```lean
∀ (V : Type) [inst : AddCommGroup V] [inst_1 : Module ℝ V] (f : Module.End ℝ V), f * f = 1 → ∀ (μ : ℝ), f.HasEigenvalue μ → μ = 1 ∨ μ = -1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lin_nilpotent_det_one_add`

For a nilpotent real matrix A, det(I + A) = 1 — the characteristic polynomial of a nilpotent matrix over a domain is X^n; evaluate det(tI − A) at t = −1 (and fix signs), or show det(I + tA) is a polynomial unit in t hence constant.

```lean
∀ (n k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A ^ k = 0 → (1 + A).det = 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_5
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lin_nilpotent_det_zero`

A nilpotent real matrix of positive size has determinant 0 — det(A)^k = det(A^k) = det 0 = 0 (size positive), and ℝ has no nilpotents.

```lean
∀ (n k : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ), A ^ k = 0 → A.det = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lin_nilpotent_pow_card`

A nilpotent n×n real matrix satisfies Aⁿ = 0 — its characteristic polynomial is Xⁿ (nilpotent over a domain), then Cayley–Hamilton (Matrix.aeval_self_charpoly).

```lean
∀ (n k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A ^ k = 0 → A ^ n = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_5
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lin_skew_odd_det_zero`

A real skew-symmetric matrix of odd size is singular — det A = det Aᵀ = det(−A) = (−1)^(2n+1) det A = −det A, so 2 det A = 0.

```lean
∀ (n : ℕ) (A : Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1)) ℝ), A.transpose = -A → A.det = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lin_sylvester_rank`

Sylvester's rank inequality: rank A + rank B ≤ n + rank(AB) — restrict A to range B: rank(AB) = rank B − dim(ker A ∩ range B) ≥ rank B − dim ker A, and dim ker A = n − rank A by rank–nullity.

```lean
∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ), A.rank + B.rank ≤ n + (A * B).rank
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_5
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lin_symm_nilpotent_eq_zero`

A nilpotent real symmetric matrix is zero — for symmetric B, B² = BᵀB = 0 forces B = 0 (sum of squares of entries); apply repeatedly to A^(2^m) with 2^m ≥ k, noting powers of a symmetric matrix are symmetric.

```lean
∀ (n k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A.IsSymm → A ^ k = 0 → A = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_5
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.lin_two_by_two_order_three`

A real 2×2 matrix with determinant 1 and trace −1 satisfies A³ = I — by 2×2 Cayley–Hamilton A² + A + I = 0, then A³ − I = (A − I)(A² + A + I) = 0.

```lean
∀ (A : Matrix (Fin 2) (Fin 2) ℝ), A.det = 1 → A.trace = -1 → A ^ 3 = 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r4_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`lin_cayley_hamilton_two`

## `Mathlib2.ms_divrad_dvd_wronskian_v2`

For nonzero a in k[t], a/rad(a) divides the Wronskian W(a,b) = ab' - a'b.

```lean
∀ {k : Type u_1} [inst : Field k] [inst_1 : DecidableEq k] (a b : Polynomial k), a ≠ 0 → a / UniqueFactorizationMonoid.radical a ∣ a * Polynomial.derivative b - Polynomial.derivative a * b
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2408.15180v2 Lemma 2, p.4）
- 完成者：paper_1
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 复核（reviewer_1）：faithful — Compared PDF p.4 Lemma 2 with Definition 2 (W(a,b)=ab'-a'b); transcription matches. Wronskian is unfolded literally as a*derivative b - derivative a*b in a commutative ring with true subtraction; b is arbitrary (may be zero) as in the prose; only a != 0 is assumed. Division is exact as in Lemma 1; o

## `Mathlib2.ms_no_param_y2_x3_1`

If char k ≠ 2,3 and rational functions f,g in k(t) satisfy g^2 = f^3 + 1 then f and g are constants.

```lean
∀ {k : Type u_1} [inst : Field k], ringChar k ≠ 2 → ringChar k ≠ 3 → ∀ (f g : RatFunc k), g ^ 2 = f ^ 3 + 1 → (∃ c, f = RatFunc.C c) ∧ ∃ d, g = RatFunc.C d
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2408.15180v2 Theorem 3, p.3）
- 完成者：prover_5
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 复核（reviewer_1）：faithful — Compared PDF p.3 Theorem 3 (and the paper's own Lean on p.11); transcription matches. char != 2,3 is rendered ringChar k != 2 and != 3, equivalent to the paper's 'not ringChar k | 6' since ringChar is 0 or prime. f,g range over all of RatFunc k with no extra hypotheses, and 'constant in k' is exists

## `Mathlib2.nt2_fib_catalan_identity`

Catalan's Fibonacci identity F_{n+r}^2 - F_n F_{n+2r} = (-1)^n F_r^2, generalizing Cassini's identity Mathlib2.an_cassini_int (the case r = 1).

```lean
∀ (n r : ℕ), ↑(Nat.fib (n + r)) ^ 2 - ↑(Nat.fib n) * ↑(Nat.fib (n + 2 * r)) = (-1) ^ n * ↑(Nat.fib r) ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_b
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`an_cassini_int`

## `Mathlib2.nt2_irrational_sqrt_two_add_sqrt_three`

√2 + √3 is irrational (squaring gives 5 + 2√6, and √6 is irrational).

```lean
Irrational (√2 + √3)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_d
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.nt2_pow_four_add_four_pow_factors`

n^4 + 4^n is composite for n > 1. Generalizes Mathlib2.nt_pow4_add_four_not_prime: for odd n apply the Sophie Germain identity a^4 + 4 b^4 with b = 2^((n-1)/2) (cf. nt2_pow_four_add_four_mul_pow_four_not_prime); for even n the number is even and > 2.

```lean
∀ (n : ℕ), 1 < n → ∃ a b, 1 < a ∧ 1 < b ∧ n ^ 4 + 4 ^ n = a * b
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_d
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`nt2_pow_four_add_four_mul_pow_four_not_prime`

## `Mathlib2.nt2_sq_add_sq_eq_seven_mul_sq`

x^2 + y^2 = 7 z^2 has only the trivial integer solution. Consequence of Mathlib2.nt_seven_dvd_sq_add_sq by infinite descent (7 | x, y, then 7 | z, divide through by 49).

```lean
∀ (x y z : ℤ), x ^ 2 + y ^ 2 = 7 * z ^ 2 → x = 0 ∧ y = 0 ∧ z = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_a
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`nt_seven_dvd_sq_add_sq`

## `Mathlib2.nt2_sq_sum_eq_two_mul_prod_descent`

x^2 + y^2 + z^2 = 2xyz has only the zero solution in integers (2-adic infinite descent).

```lean
∀ (x y z : ℤ), x ^ 2 + y ^ 2 + z ^ 2 = 2 * x * y * z → x = 0 ∧ y = 0 ∧ z = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_e
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.nt2_totient_pow_sub_one_multiple`

For a > 1, n divides φ(a^n - 1): a has multiplicative order exactly n modulo a^n - 1. (Stated with an explicit cofactor.)

```lean
∀ (a n : ℕ), 1 < a → ∃ k, (a ^ n - 1).totient = n * k
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_e
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.nt2_wilson_half_factorial_sq`

For a prime p ≡ 1 (mod 4), ((p-1)/2)!^2 ≡ -1 (mod p): explicit square root of -1 from Wilson's theorem.

```lean
∀ (p : ℕ), Nat.Prime p → p % 4 = 1 → p ∣ ((p - 1) / 2).factorial ^ 2 + 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_d
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.nt2_x_pow_four_add_one_irreducible_int`

The polynomial X^4 + 1 is irreducible over the integers (it is the 8th cyclotomic polynomial; Eisenstein after X ↦ X+1).

```lean
Irreducible (Polynomial.X ^ 4 + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r2_prover_e
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.nt_five_consec_prod_dvd_120`

n^5 - 5n^3 + 4n = (n-2)(n-1)n(n+1)(n+2) is divisible by 120.

```lean
∀ (n : ℤ), 120 ∣ n ^ 5 - 5 * n ^ 3 + 4 * n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_5
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.nt_four_consec_add_one_is_square`

The product of four consecutive naturals plus 1 is a perfect square.

```lean
∀ (n : ℕ), IsSquare (n * (n + 1) * (n + 2) * (n + 3) + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.nt_gcd_21n4_14n3`

The fraction (21n+4)/(14n+3) is irreducible (IMO 1959 P1).

```lean
∀ (n : ℕ), (21 * n + 4).gcd (14 * n + 3) = 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.nt_lcm_consecutive`

lcm of consecutive naturals is their product.

```lean
∀ (n : ℕ), n.lcm (n + 1) = n * (n + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_4
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.nt_nine_dvd_sum_cubes_three_dvd_prod`

If 9 divides a^3+b^3+c^3 then 3 divides abc.

```lean
∀ (a b c : ℤ), 9 ∣ a ^ 3 + b ^ 3 + c ^ 3 → 3 ∣ a * b * c
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.nt_odd_sq_add_odd_sq_not_square`

The sum of two odd squares is never a perfect square.

```lean
∀ (a b : ℤ), Odd a → Odd b → ¬IsSquare (a ^ 2 + b ^ 2)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.nt_pow4_add_four_not_prime`

n^4 + 4 is composite for n > 1 (Sophie Germain identity).

```lean
∀ (n : ℕ), 1 < n → ¬Nat.Prime (n ^ 4 + 4)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.nt_pow5_sub_self_dvd_30`

n^5 - n is divisible by 30 for every integer n.

```lean
∀ (n : ℤ), 30 ∣ n ^ 5 - n
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.nt_prime_sq_add_two_prime`

If p and p^2+2 are both prime then p = 3.

```lean
∀ (p : ℕ), Nat.Prime p → Nat.Prime (p ^ 2 + 2) → p = 3
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.nt_prime_sq_sub_one_dvd_24`

For a prime p > 3, 24 divides p^2 - 1.

```lean
∀ (p : ℕ), Nat.Prime p → 3 < p → 24 ∣ p ^ 2 - 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.nt_seven_dvd_pow_sum`

7 divides 3^(2n+1) + 2^(n+2) for all n.

```lean
∀ (n : ℕ), 7 ∣ 3 ^ (2 * n + 1) + 2 ^ (n + 2)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.nt_sq_sub_three_sq_ne_two`

The equation x^2 - 3y^2 = 2 has no integer solutions.

```lean
∀ (x y : ℤ), x ^ 2 - 3 * y ^ 2 ≠ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_4
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.p3_cor1`

lim_{N→∞} min{π(n)/n : 0 < n < N} = 0

```lean
Filter.Tendsto (fun N => sInf ((fun n => ↑(Mathlib2.p3_pisano n) / ↑n) '' Set.Ioo 0 N)) Filter.atTop (nhds 0)
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2504.09938 Corollary 1）
- 完成者：r5_prover_5
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p3_pisano`
- 复核（reviewer_3）：faithful — Paper: lim_{N->inf} min{pi(n)/n : n in N, n<N} = 0. Lean: Tendsto of sInf of the image of Ioo 0 N in the reals; sInf of a finite nonempty set is its min, and n ranges over positive naturals as in the paper (pi(0)/0 is meaningless). Only difference: for N<=1 the set is empty and Lean gives sInf = 0, 

## `Mathlib2.p3_cor2`

infinitely many odd k divide F_1+...+F_k (also Conjecture 1 of the paper)

```lean
{k | Odd k ∧ k ∣ Mathlib2.p3_fibsum k}.Infinite
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2504.09938 Corollary 2 (= Conjecture 1)）
- 完成者：paper_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p3_fibsum`、`p3_prop1_aux1`、`p3_thm2`
- 复核（reviewer_3）：faithful — Paper Cor 2: infinitely many odd k with k | sum of first k Fibonacci numbers; Conjecture 1 says 'first n nonzero Fibonacci numbers'. With the paper's convention F_1=1 both are k | S_k, as in Lean. Wording difference (Cor 2 drops 'nonzero') is harmless under the paper's convention; also the paper's p

## `Mathlib2.p3_remark3`

F_a - F_b = F_u L_v if a = b mod 4, = F_v L_u if a = b+2 mod 4, where u=(a-b)/2, v=(a+b)/2

```lean
∀ (a b : ℕ), b ≤ a → (a ≡ b [MOD 4] → ↑(Nat.fib a) - ↑(Nat.fib b) = ↑(Nat.fib ((a - b) / 2)) * ↑(Mathlib2.p3_lucas ((a + b) / 2))) ∧ (a ≡ b + 2 [MOD 4] → ↑(Nat.fib a) - ↑(Nat.fib b) = ↑(Nat.fib ((a + b) / 2)) * ↑(Mathlib2.p3_lucas ((a - b) / 2)))
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2504.09938 Remark 3）
- 完成者：paper_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p3_aux_period_aux1`、`p3_lucas`
- 复核（reviewer_3）：faithful — Paper: F_a-F_b = F_u L_v if a=b mod 4, F_v L_u if a=b+2 mod 4, (u,v)=((a-b)/2,(a+b)/2). Lean matches, with integer subtraction on the left; differences: adds hypothesis b<=a and a,b natural (paper leaves range implicit), natural division is exact under the congruence hypotheses. Slight restriction o

## `Mathlib2.p3_thm1_not_dvd`

for a prime p > 5, p does not divide S_p

```lean
∀ (p : ℕ), Nat.Prime p → 5 < p → ¬p ∣ Mathlib2.p3_fibsum p
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2504.09938 Theorem 1 (last sentence)）
- 完成者：paper_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p3_fibsum`、`p3_thm1_corrected`
- 复核（reviewer_3）：faithful — Matches the last sentence of Theorem 1 ('In particular, S_p is not divisible by p') for primes p>5. True (S_p = 1 or -2 mod p, p>5); checked numerically for p<200. This part of the paper's theorem, and hence its use in the paper, survives.

## `Mathlib2.p4_ex1_table`

The table of values of x(n) in Exercise 1.

```lean
List.map Mathlib2.p4_x [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 20, 50, 100, 200, 300, 400, 500, 1000] = [-1, -3, -5, -4, -9, -9, -8, -11, -15, -14, -13, -13, -17, -23, -37, -46, -47, -41, -14, 23, 182]
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Exercise 1）
- 完成者：paper_4
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p4_x`、`p4_x_block`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). All 21 table entries (n=1..13,20,50,100,200,300,400,500,1000) match the paper's table digit for digit; I recomputed them from the raw definitions.

## `Mathlib2.p4_lem1_ii`

Lemma 1(ii): if x(a) < 0 and b is the largest integer with 2b <= 3(r(a)+1)m(a), then x(n) < 0 for a <= n <= b.

```lean
∀ (a b n : ℕ), 0 < a → a ≤ n → n ≤ b → Mathlib2.p4_x a < 0 → 2 * b ≤ 3 * (Mathlib2.p4_r a + 1) * Mathlib2.p4_m a → (∀ (c : ℕ), 2 * c ≤ 3 * (Mathlib2.p4_r a + 1) * Mathlib2.p4_m a → c ≤ b) → Mathlib2.p4_x n < 0
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Lemma 1(ii)）
- 完成者：paper_4
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p4_lem1_i`、`p4_m`、`p4_r`、`p4_x`、`p4_z`、`p4_z_spec`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). Hypotheses x(a)<0 and 'b largest integer with 2b<=3(r(a)+1)m(a)' are both encoded (hb+hbmax), conclusion x(n)<0 for a<=n<=b as in the paper. Note: the paper's own proof uses neither x(a)<0 nor maximality of b, so calling them sup

## `Mathlib2.p4_lem1_iii`

Lemma 1(iii): if x(b) > 0 and a is the least integer with 2a >= 3(r(b)+1)m(b)+4, then x(n) > 0 for a <= n <= b.

```lean
∀ (a b n : ℕ), 0 < a → a ≤ n → n ≤ b → 0 < Mathlib2.p4_x b → 3 * (Mathlib2.p4_r b + 1) * Mathlib2.p4_m b + 4 ≤ 2 * a → (∀ (c : ℕ), 3 * (Mathlib2.p4_r b + 1) * Mathlib2.p4_m b + 4 ≤ 2 * c → a ≤ c) → 0 < Mathlib2.p4_x n
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Lemma 1(iii)）
- 完成者：paper_4
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p4_lem1_i`、`p4_m`、`p4_r`、`p4_x`、`p4_z`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). Hypotheses x(b)>0 and 'a least integer with 2a>=3(r(b)+1)m(b)+4' are encoded (hamin+haleast), conclusion x(n)>0. As in (ii), the paper's proof uses neither x(b)>0 nor minimality, so the superfluity remark is accurate.

## `Mathlib2.p4_lem2_chain`

Lemma 2, second part: for a <= n1 <= n2 <= b(a): x(a) <= x(n1) = z(n1)-(r(a)+1)m(a) <= x(n2) <= x(b(a)).

```lean
∀ (a q : ℕ), 0 < a → 2 * q < (Mathlib2.p4_m a + 1) ^ 2 → (∀ (c : ℕ), 2 * c < (Mathlib2.p4_m a + 1) ^ 2 → c ≤ q) → ∀ (n1 n2 : ℕ), a ≤ n1 → n1 ≤ n2 → n2 ≤ min q (2 ^ Mathlib2.p4_r a) → Mathlib2.p4_x a ≤ Mathlib2.p4_x n1 ∧ Mathlib2.p4_x n1 = Mathlib2.p4_z n1 - (↑(Mathlib2.p4_r a) + 1) * ↑(Mathlib2.p4_m a) ∧ Mathlib2.p4_x n1 ≤ Mathlib2.p4_x n2 ∧ Mathlib2.p4_x n2 ≤ Mathlib2.p4_x (min q (2 ^ Mathlib2.p4_r a))
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Lemma 2）
- 完成者：paper_4
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p4_ex1_mono`、`p4_m`、`p4_r`、`p4_r_spec`、`p4_x`、`p4_z`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). Paper chain x(a)<=x(n1)=z(n1)-(r(a)+1)m(a)<=x(n2)<=x(b(a)) for a<=n1<=n2<=b(a); Lean is the same four-part conjunction with b(a)=min q (2^r(a)). No difference found.

## `Mathlib2.p4_lem2_greatest`

Lemma 2, first part: with s=r(a), t=m(a), q the largest integer with 2q < (t+1)^2 and b(a)=min(q,2^s), b(a) is the largest positive integer k with r(k)=s and m(k)=t.

```lean
∀ (a q : ℕ), 0 < a → 2 * q < (Mathlib2.p4_m a + 1) ^ 2 → (∀ (c : ℕ), 2 * c < (Mathlib2.p4_m a + 1) ^ 2 → c ≤ q) → IsGreatest {k | 0 < k ∧ Mathlib2.p4_r k = Mathlib2.p4_r a ∧ Mathlib2.p4_m k = Mathlib2.p4_m a} (min q (2 ^ Mathlib2.p4_r a))
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Lemma 2）
- 完成者：paper_4
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p4_ex1_mono`、`p4_m`、`p4_r`、`p4_r_spec`、`p4_z`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). Paper: s=r(a), t=m(a), q largest integer with 2q<(t+1)^2, b(a)=min(q,2^s) is the largest positive k with r(k)=s, m(k)=t. Lean encodes q by hq+hqmax and uses IsGreatest on the same set; I brute-forced it for a<1200.

## `Mathlib2.p4_m_spec`

The Lean definition p4_m agrees with the paper's: m(n) is the largest integer with m(n)^2 <= 2n.

```lean
∀ (n : ℕ), ↑(Mathlib2.p4_m n) ^ 2 ≤ 2 * ↑n ∧ ∀ (k : ℤ), k ^ 2 ≤ 2 * ↑n → k ≤ ↑(Mathlib2.p4_m n)
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Introduction, definition (b)）
- 完成者：paper_4
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p4_m`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). States definition (b): m(n)^2<=2n and any integer k with k^2<=2n is <= m(n). Matches the paper.

## `Mathlib2.p4_rem1_4096`

Remark 1: z(4096)=2730, m(4096)=90, r(4096)=12, x(4096)=1560.

```lean
Mathlib2.p4_z 4096 = 2730 ∧ Mathlib2.p4_m 4096 = 90 ∧ Mathlib2.p4_r 4096 = 12 ∧ Mathlib2.p4_x 4096 = 1560
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Remark 1）
- 完成者：paper_4
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p4_ex1_levels`、`p4_m`、`p4_r`、`p4_x`、`p4_x_block`、`p4_z`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). Paper: z(4096)=2730, m(4096)=90, r(4096)=12, x(4096)=1560. Identical; recomputed.

## `Mathlib2.p4_rem2`

Remark 2: 547 is the least positive integer N such that x(m) > 0 for all m >= N.

```lean
IsLeast {N | 0 < N ∧ ∀ (m : ℕ), N ≤ m → 0 < Mathlib2.p4_x m} 547
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Remark 2）
- 完成者：paper_4
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p4_thm1_i`、`p4_thm1_iv`、`p4_x`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). Paper: 547 is the least positive n with x(m)>0 for all m>=n. Lean IsLeast on that set. The numerological asides (547 is the 101st prime, digit sums) are not formalised; 547 is indeed the 101st prime.

## `Mathlib2.p4_thm1_ii`

Theorem 1(ii): x(n)<0 iff n <= 435 or n = 450 or 513 <= n <= 528.

```lean
∀ (n : ℕ), 0 < n → (Mathlib2.p4_x n < 0 ↔ n ≤ 435 ∨ n = 450 ∨ 513 ≤ n ∧ n ≤ 528)
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Theorem 1(ii)）
- 完成者：paper_4
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p4_rem1_large`、`p4_small_classify`、`p4_x`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). x(n)<0 iff n<=435 or n=450 or 513<=n<=528. Identical; confirmed numerically to 300000.

## `Mathlib2.p4_thm1_v`

Theorem 1(v): x(n) has no maximal value (over positive integers n).

```lean
¬∃ n0, 0 < n0 ∧ ∀ (n : ℕ), 0 < n → Mathlib2.p4_x n ≤ Mathlib2.p4_x n0
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Theorem 1(v)）
- 完成者：paper_4
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p4_thm1_v_step_fixed`、`p4_x`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). Paper: 'x(n) has no maximal value'. Lean: no positive n0 with x(n)<=x(n0) for all positive n. For an integer-valued function this is equivalent to unbounded above, which is what the paper's proof argues, so it is a fair reading.

## `Mathlib2.p4_thm1_vi`

Theorem 1(vi): x(129) = -59 and x(n) >= -58 for every positive n other than 129.

```lean
Mathlib2.p4_x 129 = -59 ∧ ∀ (n : ℕ), 0 < n → n ≠ 129 → -58 ≤ Mathlib2.p4_x n
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2503.03469v1 Theorem 1(vi)）
- 完成者：paper_4
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p4_rem1_large`、`p4_small_classify`、`p4_x`、`p4_x_block`
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). x(129)=-59 and x(n)>=-58 for n not 129 (n positive). Identical; confirmed numerically to 300000.

## `Mathlib2.p5_cited_atanassov`

Cited result (Atanassov 2013): phi psi sigma >= n^3+n^2-n-1 for n >= 2 (subtractions moved across).

```lean
∀ (n : ℕ), 2 ≤ n → n ^ 3 + n ^ 2 ≤ n.totient * Mathlib2.p5_dedekind_psi n * (ArithmeticFunction.sigma 1) n + n + 1
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2404.19332v1 Section 2 (cited, Atanassov 2013)）
- 完成者：paper_5
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p5_dedekind_psi`、`p5_psi_ge_succ`、`p5_psi_ge_succ_aux1`、`p5_psi_prime_mul_of_dvd`、`p5_psi_prime_pow`、`p5_sigma_prime_mul_of_dvd`
- 复核（reviewer_5）：faithful — Sec.2 verbatim: phi psi sigma >= n^3+n^2-n-1 for n>=2; Lean moves -n-1 across as +n+1, equivalent over N. Numerically true 1..100000, equality at primes. Sandor's refinement with unitary analogues in the same paragraph is not formalized.

## `Mathlib2.p5_cited_products`

Cited result (Dimitrov 2023): phi psi + phi sigma + sigma psi >= 3n^2+2n-1 for n >= 2 (the -1 moved across).

```lean
∀ (n : ℕ), 2 ≤ n → 3 * n ^ 2 + 2 * n ≤ n.totient * Mathlib2.p5_dedekind_psi n + n.totient * (ArithmeticFunction.sigma 1) n + (ArithmeticFunction.sigma 1) n * Mathlib2.p5_dedekind_psi n + 1
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2404.19332v1 Section 2 (cited, Dimitrov 2023)）
- 完成者：paper_5
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p5_dedekind_psi`、`p5_lemma1`、`p5_lemma2`、`p5_psi_ge_succ`、`p5_sigma_ge_succ`
- 复核（reviewer_5）：faithful — Sec.2 verbatim: phi psi+phi sigma+sigma psi >= 3n^2+2n-1 for n>=2; Lean moves -1 across as +1. Numerically true 2..100000, equality at primes.

## `Mathlib2.p5_cited_squares`

Cited result (Dimitrov 2023): phi^2+psi^2+sigma^2 >= 3n^2+2n+3 for n >= 2.

```lean
∀ (n : ℕ), 2 ≤ n → 3 * n ^ 2 + 2 * n + 3 ≤ n.totient ^ 2 + Mathlib2.p5_dedekind_psi n ^ 2 + (ArithmeticFunction.sigma 1) n ^ 2
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2404.19332v1 Section 2 (cited, Dimitrov 2023)）
- 完成者：paper_5
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p5_dedekind_psi`、`p5_lemma1`、`p5_lemma2`、`p5_psi_ge_succ`、`p5_sigma_ge_succ`
- 复核（reviewer_5）：faithful — Sec.2 verbatim: phi^2+psi^2+sigma^2 >= 3n^2+2n+3 for n>=2; Lean identical. Numerically true 2..100000, equality at primes.

## `Mathlib2.p5_thm1`

Theorem 1: phi^3+psi^3+sigma^3 >= 3n^3+3n^2+9n+1 for n >= 2.

```lean
∀ (n : ℕ), 2 ≤ n → 3 * n ^ 3 + 3 * n ^ 2 + 9 * n + 1 ≤ n.totient ^ 3 + Mathlib2.p5_dedekind_psi n ^ 3 + (ArithmeticFunction.sigma 1) n ^ 3
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2404.19332v1 Theorem 1）
- 完成者：paper_5
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p5_dedekind_psi`、`p5_lemma1`、`p5_lemma2`、`p5_psi_ge_succ`、`p5_sigma_ge_succ`
- 复核（reviewer_5）：faithful — Verbatim (1): phi^3+psi^3+sigma^3 >= 3n^3+3n^2+9n+1, n>=2; Lean coefficients/exponents/range identical; sigma 1 = sum of divisors, Nat.totient = Euler phi. Python 2..100000: holds, equality exactly at primes; fails at n=1 so hypothesis is needed.

## `Mathlib2.p5_thm2`

Theorem 2: phi^4+psi^4+sigma^4 >= 3n^4+4n^3+18n^2+4n+3 for n >= 2.

```lean
∀ (n : ℕ), 2 ≤ n → 3 * n ^ 4 + 4 * n ^ 3 + 18 * n ^ 2 + 4 * n + 3 ≤ n.totient ^ 4 + Mathlib2.p5_dedekind_psi n ^ 4 + (ArithmeticFunction.sigma 1) n ^ 4
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2404.19332v1 Theorem 2）
- 完成者：paper_5
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p5_dedekind_psi`、`p5_lemma1`、`p5_lemma2`、`p5_psi_ge_succ`、`p5_sigma_ge_succ`
- 复核（reviewer_5）：faithful — Verbatim (2): phi^4+psi^4+sigma^4 >= 3n^4+4n^3+18n^2+4n+3, n>=2; Lean identical. Python 2..100000: holds, equality exactly at primes.

## `Mathlib2.p5_thm3`

Theorem 3: phi^2 psi^2 + phi^2 sigma^2 + sigma^2 psi^2 >= 3n^4+4n^3+2n^2+4n+3 for n >= 2.

```lean
∀ (n : ℕ), 2 ≤ n → 3 * n ^ 4 + 4 * n ^ 3 + 2 * n ^ 2 + 4 * n + 3 ≤ n.totient ^ 2 * Mathlib2.p5_dedekind_psi n ^ 2 + n.totient ^ 2 * (ArithmeticFunction.sigma 1) n ^ 2 + (ArithmeticFunction.sigma 1) n ^ 2 * Mathlib2.p5_dedekind_psi n ^ 2
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2404.19332v1 Theorem 3）
- 完成者：paper_5
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p5_dedekind_psi`、`p5_lemma1`、`p5_lemma2`、`p5_psi_ge_succ`、`p5_sigma_ge_succ`
- 复核（reviewer_5）：faithful — Verbatim (3): phi^2psi^2+phi^2sigma^2+sigma^2psi^2 >= 3n^4+4n^3+2n^2+4n+3, n>=2; Lean identical term by term. Python 2..100000: holds, equality exactly at primes.

## `Mathlib2.p5_thm4`

Theorem 4: phi^2(psi+sigma)+psi^2(phi+sigma)+sigma^2(phi+psi) >= 6n^3+6n^2+2n+2 for n >= 2.

```lean
∀ (n : ℕ), 2 ≤ n → 6 * n ^ 3 + 6 * n ^ 2 + 2 * n + 2 ≤ n.totient ^ 2 * (Mathlib2.p5_dedekind_psi n + (ArithmeticFunction.sigma 1) n) + Mathlib2.p5_dedekind_psi n ^ 2 * (n.totient + (ArithmeticFunction.sigma 1) n) + (ArithmeticFunction.sigma 1) n ^ 2 * (n.totient + Mathlib2.p5_dedekind_psi n)
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2404.19332v1 Theorem 4）
- 完成者：paper_5
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p5_dedekind_psi`、`p5_lemma1`、`p5_lemma2`、`p5_psi_ge_succ`、`p5_sigma_ge_succ`
- 复核（reviewer_5）：faithful — Verbatim (4): phi^2(psi+sigma)+psi^2(phi+sigma)+sigma^2(phi+psi) >= 6n^3+6n^2+2n+2, n>=2; Lean identical. Python 2..100000: holds, equality exactly at primes.

## `Mathlib2.p5_thm5`

Theorem 5: phi^3(psi+sigma)+psi^3(phi+sigma)+sigma^3(phi+psi) >= 6n^4+8n^3+12n^2+8n-2 for n >= 2 (the -2 moved to the other side to avoid natural subtraction).

```lean
∀ (n : ℕ), 2 ≤ n → 6 * n ^ 4 + 8 * n ^ 3 + 12 * n ^ 2 + 8 * n ≤ n.totient ^ 3 * (Mathlib2.p5_dedekind_psi n + (ArithmeticFunction.sigma 1) n) + Mathlib2.p5_dedekind_psi n ^ 3 * (n.totient + (ArithmeticFunction.sigma 1) n) + (ArithmeticFunction.sigma 1) n ^ 3 * (n.totient + Mathlib2.p5_dedekind_psi n) + 2
```
- 结论：证明
- 层级：agent
- 来源：paper（arXiv:2404.19332v1 Theorem 5）
- 完成者：paper_5
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`p5_dedekind_psi`、`p5_lemma1`、`p5_lemma2`、`p5_psi_ge_succ`、`p5_sigma_ge_succ`
- 复核（reviewer_5）：faithful — Verbatim (5): phi^3(psi+sigma)+psi^3(phi+sigma)+sigma^3(phi+psi) >= 6n^4+8n^3+12n^2+8n-2, n>=2; Lean has the same coefficients with the -2 moved to the other side as +2 (equivalent over N). Python 2..100000: holds, equality exactly at primes.
- 复核（reviewer_5）：faithful — Verbatim (5): phi^3(psi+sigma)+psi^3(phi+sigma)+sigma^3(phi+psi) >= 6n^4+8n^3+12n^2+8n-2, n>=2; Lean has the same coefficients with the -2 moved across as +2 (equivalent over N). Python 2..100000: holds, equality exactly at primes.

## `Mathlib2.poly_catalan_pow_add_one`

Catalan for polynomials: in char 0 two perfect powers g^m, h^n (m,n ≥ 2) differing by 1 are constants — Uses Mathlib2.ms_mason_stothers_v2 with a = g^m, b = 1, c = -h^n (pairwise coprime since g^m and h^n differ by a unit): if g is non-constant, D = m·deg g = n·deg h < deg rad(g^m h^n) ≤ deg g + deg h = D/m + D/n ≤ D, contradiction; g = 0 or g constant handled separately.

```lean
∀ {k : Type u_1} [inst : Field k] [DecidableEq k] [CharZero k] (m n : ℕ), 2 ≤ m → 2 ≤ n → ∀ (g h : Polynomial k), g ^ m + 1 = h ^ n → g.natDegree = 0 ∧ h.natDegree = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pa
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`poly_abc_radical_bound_of_coprime`

## `Mathlib2.poly_chebyshev_T_abs_le_one`

Chebyshev polynomials of the first kind are bounded by 1 on [-1,1] — write x = cos θ with θ = arccos x, then T_n(cos θ) = cos(nθ) (Polynomial.Chebyshev.T_real_cos) and |cos| ≤ 1.

```lean
∀ (n : ℤ) (x : ℝ), |x| ≤ 1 → |Polynomial.eval x (Polynomial.Chebyshev.T ℝ n)| ≤ 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pb
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.poly_cubic_real_roots_newton`

Newton's inequality for a real cubic with three real roots (with multiplicity): X^3 + aX^2 + bX + c splitting over ℝ forces a^2 ≥ 3b — the polynomial equals (X-r)(X-s)(X-t), so a = -(r+s+t), b = rs+st+tr and a^2 - 3b = ((r-s)^2 + (s-t)^2 + (t-r)^2)/2 ≥ 0.

```lean
∀ (a b c : ℝ), (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c).roots.card = 3 → 3 * b ≤ a ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pb
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.poly_davenport_sharp_deg_two`

Davenport's bound is sharp in degree (2,3): the least possible degree of f^3 - g^2 ≠ 0 with deg f = 2, deg g = 3 over ℚ is exactly 2 — membership by f = X^2 + 2, g = X^3 + 3X (f^3 - g^2 = 3X^2 + 8); lower bound Uses Mathlib2.ms_davenport: f.natDegree + 2 = 4 ≤ 2·d.

```lean
IsLeast {d | ∃ f g, f.natDegree = 2 ∧ g.natDegree = 3 ∧ f ^ 3 ≠ g ^ 2 ∧ (f ^ 3 - g ^ 2).natDegree = d} 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pa
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`ms_davenport`

## `Mathlib2.poly_derivative_dvd_self_char_zero`

In char 0, a non-constant f with f' ∣ f is c·(X-a)^n — f = f'·q with q linear, q = (X-a)/n by comparing leading coefficients; then n·f = (X-a)f', and induction on n (or comparing root multiplicities at a: f = (X-a)^m g with g(a) ≠ 0 forces m = n) gives the claim.

```lean
∀ {k : Type u_1} [inst : Field k] [CharZero k] (f : Polynomial k), 0 < f.natDegree → Polynomial.derivative f ∣ f → ∃ c a, f = Polynomial.C c * (Polynomial.X - Polynomial.C a) ^ f.natDegree
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pb
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.poly_fermat_catalan_2_3_7`

In characteristic 0, a^2 + b^3 = c^7 has no non-constant pairwise coprime polynomial solutions (1/2+1/3+1/7 < 1) — Uses Mathlib2.ms_fermat_catalan with (p,q,r)=(2,3,7), u=v=1, w=-1; ringChar k = 0 divides none of 2,3,7; rewrite heq as C 1 * a^2 + C 1 * b^3 + C (-1) * c^7 = 0.

```lean
∀ {k : Type u_1} [inst : Field k] [DecidableEq k] [CharZero k] (a b c : Polynomial k), a ≠ 0 → b ≠ 0 → c ≠ 0 → IsCoprime a b → IsCoprime b c → IsCoprime c a → a ^ 2 + b ^ 3 = c ^ 7 → a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pa
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`ms_fermat_catalan`

## `Mathlib2.poly_fermat_quartic_4_4_2`

Polynomial analogue of Fermat's quartic theorem: a^4 + b^4 = c^2 forces coprime nonzero a, b, c to be constant in char 0 (borderline case 1/4+1/4+1/2 = 1) — Uses Mathlib2.ms_fermat_catalan with (p,q,r)=(4,4,2), u=v=1, w=-1; the only work is the ringChar and the 1/p+1/q+1/r ≤ 1 side conditions.

```lean
∀ {k : Type u_1} [inst : Field k] [DecidableEq k] [CharZero k] (a b c : Polynomial k), a ≠ 0 → b ≠ 0 → c ≠ 0 → IsCoprime a b → IsCoprime b c → IsCoprime c a → a ^ 4 + b ^ 4 = c ^ 2 → a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pa
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`ms_fermat_catalan`

## `Mathlib2.poly_int_odd_at_zero_one_no_root`

An integer polynomial with p(0) and p(1) odd has no integer root — n - 0 ∣ p(n) - p(0) and n - 1 ∣ p(n) - p(1) (Polynomial.sub_dvd_eval_sub); if p(n) = 0 then both n and n-1 divide odd numbers, but one of them is even.

```lean
∀ (p : Polynomial ℤ), Odd (Polynomial.eval 0 p) → Odd (Polynomial.eval 1 p) → ∀ (n : ℤ), Polynomial.eval n p ≠ 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pb
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.poly_int_three_ones_no_root`

An integer polynomial taking the value 1 at three distinct integers has no integer root — if p(r) = 0 then r-a, r-b, r-c each divide p(r) - 1 = -1 (sub_dvd_eval_sub), so they are three distinct elements of {1,-1}, impossible.

```lean
∀ (p : Polynomial ℤ) (a b c : ℤ), a ≠ b → b ≠ c → a ≠ c → Polynomial.eval a p = 1 → Polynomial.eval b p = 1 → Polynomial.eval c p = 1 → ∀ (r : ℤ), Polynomial.eval r p ≠ 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pb
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.poly_radical_coprime_derivative_quot`

Snyder's ingredient, sharp form in char 0: the cofactor f' / (f / rad f) is coprime to rad f (so gcd(f, f') is associated to f / rad f) — Uses Mathlib2.ms_divrad_dvd_derivative_v2 to know the division is exact; then for each prime p ∣ f with multiplicity e, f = p^e·g gives f'/(f/rad f) ≡ e·p'·rad(g)·(g/..) mod p, which is nonzero mod p since e ≠ 0 in char 0 and p ∤ p'.

```lean
∀ {k : Type u_1} [inst : Field k] [inst_1 : DecidableEq k] [CharZero k] (f : Polynomial k), f ≠ 0 → IsCoprime (UniqueFactorizationMonoid.radical f) (Polynomial.derivative f / (f / UniqueFactorizationMonoid.radical f))
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pa
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`ms_divrad_dvd_derivative_v2`

## `Mathlib2.poly_real_nonneg_coeff_no_pos_root`

A nonzero real polynomial with nonnegative coefficients has no positive root (trivial case of Descartes' rule) — eval x p = Σ coeff i * x^i is a sum of nonnegative terms, at least one (the leading one) strictly positive.

```lean
∀ (p : Polynomial ℝ), p ≠ 0 → (∀ (i : ℕ), 0 ≤ p.coeff i) → ∀ (x : ℝ), 0 < x → Polynomial.eval x p ≠ 0
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pb
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.poly_sophie_germain_not_irreducible`

Sophie Germain: X^4 + 4a^4 is reducible over ℤ for every integer a — X^4 + 4a^4 = (X^2 + 2aX + 2a^2)(X^2 - 2aX + 2a^2), both monic of degree 2 hence non-units.

```lean
∀ (a : ℤ), ¬Irreducible (Polynomial.X ^ 4 + Polynomial.C (4 * a ^ 4))
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pb
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.poly_trinomial_3k2_not_irreducible_int`

X^n + X + 1 is reducible over ℤ for n ≡ 2 mod 3, n ≥ 5 (e.g. X^5+X+1 = (X^2+X+1)(X^3-X^2+1)) — X^2+X+1 divides it since X^3 ≡ 1; the monic cofactor has degree 3k ≥ 3 so neither factor is a unit.

```lean
∀ (k : ℕ), 1 ≤ k → ¬Irreducible (Polynomial.X ^ (3 * k + 2) + Polynomial.X + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pb
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`poly_x2_x_1_dvd_trinomial`

## `Mathlib2.poly_x3_x_1_irreducible_rat`

X^3 + X + 1 is irreducible over ℚ — a cubic is irreducible iff it has no root; by the rational root theorem a rational root would be ±1, and neither is a root.

```lean
Irreducible (Polynomial.X ^ 3 + Polynomial.X + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pb
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.poly_x4_sub_10x2_add_1_reducible_zmod`

X^4 - 10X^2 + 1 is reducible modulo every prime — one of 2, 3, 6 is a square mod p (Legendre symbol multiplicativity; p = 2, 3 by hand), and X^4-10X^2+1 = (X^2-1)^2 - 8X^2 = (X^2+1)^2 - 12X^2 = (X^2-5)^2 - 24, each a difference of squares when 2, 3, 6 respectively is a square.

```lean
∀ (p : ℕ) [inst : Fact (Nat.Prime p)], ¬Irreducible (Polynomial.X ^ 4 - 10 * Polynomial.X ^ 2 + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pb
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`alg_x_pow_four_add_one_not_irreducible_zmod_aux1`

## `Mathlib2.poly_x4_x_1_irreducible_zmod2`

X^4 + X + 1 is irreducible over F_2 — no roots in F_2, and the only irreducible quadratic is X^2+X+1 whose square is X^4+X^2+1 ≠ X^4+X+1.

```lean
Irreducible (Polynomial.X ^ 4 + Polynomial.X + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：prover_pb
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.r3_exists_dvd_pair_of_card_gt`

Erdős: among any n+1 numbers from {1,...,2n} one divides another. Proof idea: map each m to its odd part m / 2^{v_2(m)}; the odd parts lie in the n odd numbers below 2n, so by pigeonhole two distinct elements share an odd part, and then the one with the smaller 2-adic valuation divides the other.

```lean
∀ (n : ℕ), ∀ S ⊆ Finset.Icc 1 (2 * n), n < S.card → ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a ∣ b
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r3_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`r3_exists_dvd_pair_of_card_gt_s1h1`、`r3_exists_dvd_pair_of_card_gt_s1h2`

## `Mathlib2.r3_fermat_fourth_pow_sub_ne_sq`

Fermat: x^4 - y^4 = z^2 has no integer solutions with yz ≠ 0 (equivalently, no Pythagorean triangle has square area). Mathlib only has the companion not_fermat_42 (a^4 + b^4 ≠ c^2). Proof idea: infinite descent on x: reduce to gcd(x,y)=1; if z odd then (z, y^2, x^2) is a primitive Pythagorean triple, parametrize x^2 = m^2+n^2, y^2 = m^2-n^2 giving m^4 - n^4 = (xy)^2 with smaller m; if z even then y^2 = m^2-n^2... z = 2mn, x^2 = m^2+n^2 with m, n squares-times-units leading again to a smaller solution (or to not_fermat_42).

```lean
∀ (x y z : ℤ), y ≠ 0 → z ≠ 0 → x ^ 4 - y ^ 4 ≠ z ^ 2
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r3_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`r3_fermat_fourth_pow_sub_ne_sq_s1h1v1`、`r3_fermat_fourth_pow_sub_ne_sq_s1h2`、`r3_fermat_fourth_pow_sub_ne_sq_s1h3`、`r3_fermat_fourth_pow_sub_ne_sq_s1h4`

## `Mathlib2.r3_imo1988_vieta_jumping`

IMO 1988 Q6: if ab+1 divides a^2+b^2 then the quotient is a perfect square. Proof idea: Vieta jumping — fix the quotient q, take a solution with a+b minimal and a ≥ b, the other root a' = q b - a = (b^2 - q)/a of the quadratic satisfies 0 ≤ a' < a (needs a' ≥ 0 from positivity of a'b+1), so minimality forces a' = 0 and q = b^2.

```lean
∀ (a b : ℕ), a * b + 1 ∣ a ^ 2 + b ^ 2 → ∃ k, a ^ 2 + b ^ 2 = k ^ 2 * (a * b + 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r3_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`r3_imo1988_vieta_jumping_s1h1`、`r3_imo1988_vieta_jumping_s1h2`、`r3_imo1988_vieta_jumping_s1h3`

## `Mathlib2.r3_imo1990_sq_dvd_two_pow_add_one`

IMO 1990 Q3: n^2 | 2^n + 1 only for n = 1, 3. Builds on Mathlib2.nt2_lte_three_two_pow_three_pow_add_one (LTE at 3; here one needs the general form v_3(2^n+1) = v_3(n)+1 for odd n) and the least-prime-factor/order technique of Mathlib2.nt2_dvd_two_pow_sub_one_eq_one. Proof idea: n is odd; least prime factor is 3 (order of 2 mod p divides gcd(2n, p-1) = 2); LTE gives 2 v_3(n) ≤ v_3(n)+1 so n = 3m with 3 ∤ m; the least prime factor q of m has ord_q(2) | gcd(6m, q-1) | 6, so q | 63, q = 7, but 2^n+1 mod 7 ∈ {2,3,5}: contradiction, so m = 1.

```lean
∀ (n : ℕ), n ^ 2 ∣ 2 ^ n + 1 → n = 1 ∨ n = 3
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r3_prover_1
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`r3_imo1990_sq_dvd_two_pow_add_one_s2h1`、`r3_imo1990_sq_dvd_two_pow_add_one_s2h2`、`r3_imo1990_sq_dvd_two_pow_add_one_s2h3`

## `Mathlib2.r3_imo2000_q2`

IMO 2000 Q2. Proof idea: substitute a = x/y, b = y/z, c = z/x to get (x-y+z)(y-z+x)(z-x+y) ≤ xyz (Schur-type); at most one factor is negative (sum of any two is positive), in which case the product is ≤ 0; otherwise multiply the three pairwise AM-GM bounds (x-y+z)(y-z+x) ≤ x^2 and take square roots.

```lean
∀ (a b c : ℝ), 0 < a → 0 < b → 0 < c → a * b * c = 1 → (a - 1 + 1 / b) * (b - 1 + 1 / c) * (c - 1 + 1 / a) ≤ 1
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r3_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`r3_imo2000_q2_s1h1`、`r3_imo2000_q2_s1h2`、`r3_imo2000_q2_s1h3`、`r3_imo2000_q2_s1h4`

## `Mathlib2.r3_mordell_y_sq_eq_x_cube_add_seven`

V. A. Lebesgue: the Mordell equation y^2 = x^3 + 7 has no integer solutions. Builds on Mathlib2.nt2_prime_three_mod_four_dvd_sq_add_sq (a prime p ≡ 3 mod 4 dividing y^2+1^2 would divide 1). Proof idea: x even gives y^2 ≡ 7 mod 8, impossible; for x odd write y^2 + 1 = (x+2)(x^2-2x+4), where x^2-2x+4 = (x-1)^2+3 is positive and ≡ 3 mod 4, hence has a prime factor p ≡ 3 mod 4 (lemma: a product of primes each ≡ 1 mod 4 is ≡ 1 mod 4), and p | y^2+1 contradicts the catalog theorem.

```lean
∀ (x y : ℤ), y ^ 2 ≠ x ^ 3 + 7
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r3_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`nt2_prime_three_mod_four_dvd_sq_add_sq`、`r3_mordell_y_sq_eq_x_cube_add_seven_s1h1`、`r3_mordell_y_sq_eq_x_cube_add_seven_s1h2`、`r3_mordell_y_sq_eq_x_cube_add_seven_s1h3`

## `Mathlib2.r3_ramsey_three_three`

R(3,3) ≤ 6: every graph on at least 6 vertices contains a triangle or its complement does. Proof idea: pick a vertex v; among the ≥ 5 other vertices, pigeonhole gives 3 neighbours or 3 non-neighbours; if two of the 3 neighbours are adjacent we get a triangle in G with v, otherwise they form a triangle in the complement (and symmetrically).

```lean
∀ (V : Type) [inst : Fintype V], 6 ≤ Fintype.card V → ∀ (G : SimpleGraph V), ¬G.CliqueFree 3 ∨ ¬Gᶜ.CliqueFree 3
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r3_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`r3_ramsey_three_three_pigeonhole`、`r3_ramsey_three_three_s1h1`

## `Mathlib2.r3_recursive_seq_add_inv_bounds`

Classic: for a_0 = 1, a_{n+1} = a_n + 1/a_n one has 14 < a_100 < 15. Proof idea: a_n > 0 and a_{n+1}^2 = a_n^2 + 2 + 1/a_n^2, so by induction a_n^2 ≥ 2n+1 (lower bound 201 > 196); feeding this back, a_n^2 ≤ 2n + 1 + Σ_{k<n} 1/(2k+1), and the sum for n = 100 must be bounded numerically (e.g. < 24) to get a_100^2 < 225.

```lean
∀ (a : ℕ → ℝ), a 0 = 1 → (∀ (n : ℕ), a (n + 1) = a n + 1 / a n) → 14 < a 100 ∧ a 100 < 15
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r3_prover_4
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.r3_sylvester_nonrepresentable_count_v2`

Sylvester's theorem (1884): for coprime positive a, b the set of natural numbers not of the form ax+by (x,y ≥ 0) is finite with exactly (a-1)(b-1)/2 elements. Mathlib has only the Frobenius number (frobeniusNumber_pair), not the count. Proof idea: every n has a unique representation n = ax+by with 0 ≤ x < b, y ∈ ℤ, and n is representable iff y ≥ 0; hence everything ≥ (a-1)(b-1) is representable, and for 0 ≤ n ≤ ab-a-b the reflection n ↦ ab-a-b-n (sending (x,y) to (b-1-x, -1-y)) swaps representable and non-representable numbers, so exactly half of range((a-1)(b-1)) is non-representable.

```lean
∀ (a b : ℕ), 0 < a → 0 < b → a.Coprime b → ∃ S, (∀ (n : ℕ), n ∈ S ↔ ¬∃ x y, a * x + b * y = n) ∧ 2 * S.card = (a - 1) * (b - 1)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r3_prover_5
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`r3_sylvester_nonrepresentable_count_v2_s1h1`、`r3_sylvester_nonrepresentable_count_v2_s1h2`、`r3_sylvester_nonrepresentable_count_v2_s1h3`

## `Mathlib2.r3_wolstenholme_harmonic`

Wolstenholme's theorem: for a prime p ≥ 5 the numerator of H_{p-1} is divisible by p^2, stated as p^2 | (p-1)! * (1 + 1/2 + ... + 1/(p-1)) with exact natural-number divisions. Proof idea: pair k with p-k: 1/k + 1/(p-k) = p/(k(p-k)), so 2·S = p·Σ (p-1)!/(k(p-k)); modulo p the inner sum is -(p-1)!·Σ k^{-2} ≡ -(p-1)!·Σ_{j=1}^{p-1} j^2 = -(p-1)!·(p-1)p(2p-1)/6 ≡ 0 for p ≥ 5 (inversion permutes the units of ZMod p); finally p odd lets one cancel the 2.

```lean
∀ (p : ℕ), Nat.Prime p → 5 ≤ p → p ^ 2 ∣ ∑ k ∈ Finset.Icc 1 (p - 1), (p - 1).factorial / k
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r3_prover_5
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`r3_wolstenholme_harmonic_s1h1`、`r3_wolstenholme_harmonic_s1h2`、`r3_wolstenholme_harmonic_s1h3`、`r3_wolstenholme_harmonic_s1h4`

## `Mathlib2.sophie_germain_gt_three_mod_six`

大于 3 的 Sophie Germain 素数模 6 余 5

```lean
∀ (p : ℕ), Mathlib2.is_sophie_germain_prime p → 3 < p → p % 6 = 5
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r3_prover_5
- 尝试次数：1
- 被引用：0 次
- 分数：3
- 依赖：`is_sophie_germain_prime`

## `Mathlib2.top_closure_open_inter_closure`

For open U, closure (U ∩ closure A) = closure (U ∩ A) — one inclusion is monotonicity, the other is IsOpen.inter_closure followed by closure_minimal.

```lean
∀ {X : Type u_1} [inst : TopologicalSpace X] (U A : Set X), IsOpen U → closure (U ∩ closure A) = closure (U ∩ A)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.top_compact_closed_disjoint_dist_pos`

A compact set and a disjoint closed set in a metric space are a positive distance apart — transfer EMetric.exists_pos_forall_lt_edist to dist, or minimize infDist · C over K.

```lean
∀ {X : Type u_1} [inst : MetricSpace X] (K C : Set X), IsCompact K → IsClosed C → Disjoint K C → ∃ δ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ C, δ ≤ dist x y
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.top_connected_metric_sphere_nonempty`

In a connected metric space every radius between 0 and dist x y is attained as a distance from x — intermediate value theorem for the continuous map z ↦ dist x z on a preconnected space, with values 0 at x and dist x y at y.

```lean
∀ {X : Type u_1} [inst : MetricSpace X] [PreconnectedSpace X] (x y : X) (r : ℝ), 0 ≤ r → r ≤ dist x y → ∃ z, dist x z = r
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.top_connected_metric_uncountable`

A connected metric space with two distinct points is uncountable — the image of z ↦ dist x z contains the interval [0, dist x y] by the intermediate value theorem, a nondegenerate real interval is uncountable, and images of countable sets are countable.

```lean
∀ {X : Type u_1} [inst : MetricSpace X] [PreconnectedSpace X] (x y : X), x ≠ y → ¬Set.univ.Countable
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.top_countable_compact_t2_isolated_point`

A nonempty countable compact Hausdorff space has an isolated point — compact Hausdorff spaces are Baire; if no singleton were open, each complement {x}ᶜ would be open and dense, so their countable intersection (which is empty) would be dense, contradicting nonemptiness.

```lean
∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X] [CompactSpace X] [Countable X] [Nonempty X], ∃ x, IsOpen {x}
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_4
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.top_disjoint_interior_closure_of_open`

Disjoint open sets have disjoint regularizations — an open set disjoint from V is disjoint from closure V; apply this twice (Disjoint.closure_left/right for open sets) and shrink to interiors.

```lean
∀ {X : Type u_1} [inst : TopologicalSpace X] (U V : Set X), IsOpen U → IsOpen V → Disjoint U V → Disjoint (interior (closure U)) (interior (closure V))
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.top_dist_div_one_add_triangle`

The bounded metric d/(1+d) satisfies the triangle inequality — t ↦ t/(1+t) is monotone and subadditive on [0,∞); combine with dist_triangle.

```lean
∀ {X : Type u_1} [inst : MetricSpace X] (x y z : X), dist x z / (1 + dist x z) ≤ dist x y / (1 + dist x y) + dist y z / (1 + dist y z)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.top_distrib_lattice_median`

The median identity in a distributive lattice — ≤ holds in every lattice (each meet is below each join); for ≥ expand the right side using distributivity and absorb.

```lean
∀ {α : Type u_1} [inst : DistribLattice α] (a b c : α), a ⊓ b ⊔ b ⊓ c ⊔ c ⊓ a = (a ⊔ b) ⊓ (b ⊔ c) ⊓ (c ⊔ a)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.top_finite_monotone_iterate_bot_fixed`

On a finite poset with bottom, iterating a monotone map from ⊥ reaches a fixed point — n ↦ f^[n] ⊥ is monotone; if never stationary it would be strictly monotone hence injective ℕ → α, contradicting finiteness.

```lean
∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : OrderBot α] [Finite α] (f : α → α), Monotone f → ∃ n, f (f^[n] ⊥) = f^[n] ⊥
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.top_fixed_of_iterate_contraction`

If an iterate f^[n] is a contraction with fixed point p then p is already a fixed point of f — f p is also fixed by f^[n] (iterates commute with f) and a contraction with K < 1 has at most one fixed point.

```lean
∀ {X : Type u_1} [inst : MetricSpace X] (f : X → X) (n : ℕ), ∀ K < 1, (∀ (x y : X), dist (f^[n] x) (f^[n] y) ≤ K * dist x y) → ∀ (p : X), f^[n] p = p → f p = p
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.top_frontier_frontier_frontier`

The frontier operator is idempotent from the second application on — frontier A is closed, so frontier (frontier A) = frontier A \ interior (frontier A) is closed with empty interior (interior_frontier), and a closed set with empty interior is its own frontier.

```lean
∀ {X : Type u_1} [inst : TopologicalSpace X] (A : Set X), frontier (frontier (frontier A)) = frontier (frontier A)
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.top_galois_u_eq_sSup`

The upper adjoint of a Galois connection between complete lattices is given by u b = sSup {a | l a ≤ b} — the set equals Set.Iic (u b) by the adjunction, whose supremum is u b.

```lean
∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] [inst_1 : CompleteLattice β] (l : α → β) (u : β → α), GaloisConnection l u → ∀ (b : β), u b = sSup {a | l a ≤ b}
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_2
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.top_lfp_comp_self`

The least fixed point of f∘f equals that of f — ≤ since lfp f is fixed by f∘f; for ≥ put a = lfp (f∘f): f a is a fixed point of f∘f so a ≤ f a, hence f a ≤ f (f a) = a, so a is a fixed point of f.

```lean
∀ {α : Type u_1} [inst : CompleteLattice α] (f : α →o α), OrderHom.lfp (f.comp f) = OrderHom.lfp f
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.top_uniformly_discrete_complete`

A metric space whose distinct points are at distance at least 1 is complete — a Cauchy sequence is eventually within 1/2 of itself hence eventually constant, hence convergent (Metric.complete_of_cauchySeq_tendsto).

```lean
∀ {X : Type u_1} [inst : MetricSpace X], (∀ (x y : X), x ≠ y → 1 ≤ dist x y) → CompleteSpace X
```
- 结论：证明
- 层级：agent
- 来源：conjecture
- 完成者：r5_prover_3
- 尝试次数：1
- 被引用：0 次
- 分数：3

## `Mathlib2.ab_fine_add`

Sum of two fine functions (vanishing at every integer) is fine.

```lean
∀ (f g : ℝ → ℝ), (∀ (n : ℤ), f ↑n = 0) → (∀ (n : ℤ), g ↑n = 0) → ∀ (n : ℤ), (f + g) ↑n = 0
```
- 结论：证明
- 层级：auto
- 来源：paper（s40753-021-00140-1 p.28 Appendix 2 Task 2(a)）
- 完成者：auto:aesop
- 尝试次数：1
- 被引用：0 次
- 分数：0
- 复核（reviewer_2）：faithful — Appendix 2 Task 2(a): f fine iff f(n) = 0 for all n in Z; f, g : R -> R fine implies f + g fine, with (f+g)(x) = f(x)+g(x). Lean inlines the definition of fine and uses pointwise Pi addition, which is the paper's stated meaning. No differences.

## `Mathlib2.ab_t2_mul_ne_one`

Table 2 step 6: k d_i ≠ 1 since k > 1.

```lean
∀ (k d : ℕ), 1 < k → k * d ≠ 1
```
- 结论：证明
- 层级：auto
- 来源：paper（s40753-021-00140-1 p.11 Table 2 step [6]）
- 完成者：auto:aesop
- 尝试次数：1
- 被引用：0 次
- 分数：0
- 复核（reviewer_2）：faithful — Table 2 step [6]: k d_i != 1 for each i as k > 1. Lean: for all d, 1 < k implies k*d != 1 (d arbitrary natural, not just a divisor) — a harmless generalization. Transcription matches.

# 新引入的定义

定义只由内核保证良构；是否忠实于原文见复核栏。

## `Mathlib2.is_sophie_germain_prime`

Sophie Germain 素数：p 与 2p+1 都是素数

```lean
def is_sophie_germain_prime (p : ℕ) : Prop := Nat.Prime p ∧ Nat.Prime (2 * p + 1)
```
- 来源：标准定义（冒烟测试）
- 被引用：1 次

## `Mathlib2.p3_fibsum`

S_n = F_1 + ... + F_n, the sum of the first n nonzero Fibonacci numbers (F_1 = F_2 = 1)

```lean
def p3_fibsum (n : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 n, Nat.fib i
```
- 来源：arXiv:2504.09938 Section 1 (notation S_n)
- 被引用：8 次
- 复核（reviewer_3）：faithful — Compared with v3 Sec.1: 'Fibonacci sequence is taken to start at 1, F_1=1, F_2=1' and S_n = sum_{i=1}^n F_i. Lean sums Nat.fib i over Icc 1 n with Nat.fib 1 = Nat.fib 2 = 1. Identical; no differences.

## `Mathlib2.p3_pisano`

Pisano period pi(n): the least positive period of the Fibonacci sequence modulo n

```lean
noncomputable def p3_pisano (n : ℕ) : ℕ := sInf {k : ℕ | 0 < k ∧ ∀ i : ℕ, Nat.fib (i + k) ≡ Nat.fib i [MOD n]}
```
- 来源：arXiv:2504.09938 Section 1 (Pisano period)
- 被引用：31 次
- 复核（reviewer_3）：faithful — Paper: 'the period with which the sequence of Fibonacci numbers, taken modulo n, repeats' (standard Pisano period, used with Wall's results). Lean: least k>0 with fib(i+k)=fib(i) mod n for all i>=0, which equals the standard definition for n>=1 (pi(1)=1). Only difference is the junk value at n=0, ne

## `Mathlib2.p3_lucas`

Lucas number L_n (L_0 = 2, L_1 = 1), written as 2 F_{n+1} - F_n

```lean
def p3_lucas (n : ℕ) : ℕ := 2 * Nat.fib (n + 1) - Nat.fib n
```
- 来源：arXiv:2504.09938 Remark 3
- 被引用：23 次
- 复核（reviewer_3）：faithful — Paper Remark 3 only says 'L_v is the v-th Lucas number'. Lean 2*fib(n+1)-fib(n) gives 2,1,3,4,7,... = standard L_n; natural subtraction is safe since 2F_{n+1}>=F_n. No differences.

## `Mathlib2.p3_self_summable`

k is a self-summable Fibonacci number if F_k divides F_1 + ... + F_{F_k}

```lean
def p3_self_summable (k : ℕ) : Prop := Nat.fib k ∣ ∑ i ∈ Finset.Icc 1 (Nat.fib k), Nat.fib i
```
- 来源：arXiv:2504.09938 Definition 1
- 被引用：2 次
- 复核（reviewer_3）：faithful — Matches v3 Definition 1 verbatim: F_k | sum_{i=1}^{F_k} F_i. Only difference: Lean k ranges over naturals incl. k=0 (trivially true, 0|0) while paper says 'integer k' and lists terms from 1; immaterial.

## `Mathlib2.p4_z`

z(n): the largest integer z with 3z < 2n, i.e. floor((2n-1)/3) (integer floor division)

```lean
def p4_z (n : ℕ) : ℤ := (2 * (n : ℤ) - 1) / 3
```
- 来源：arXiv:2503.03469v1 Introduction, definition (a)
- 被引用：17 次
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). Paper: largest integer with 3z(n)<2n; Lean floor((2n-1)/3) in Int. I checked 3z<2n<=3(z+1) for n<=1e5 and against a brute-force search for n<=3000; no difference (n=0 is outside the paper's domain).

## `Mathlib2.p4_m`

m(n): the largest integer m with m^2 <= 2n, i.e. floor(sqrt(2n))

```lean
def p4_m (n : ℕ) : ℕ := Nat.sqrt (2 * n)
```
- 来源：arXiv:2503.03469v1 Introduction, definition (b)
- 被引用：17 次
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). Paper: largest integer with m^2<=2n; Lean Nat.sqrt(2n). Checked m^2<=2n<(m+1)^2 for n<=1e5 and brute force for n<=3000; no difference.

## `Mathlib2.p4_r`

r(n): the least non-negative integer r with n <= 2^r, i.e. ceil(log2 n)

```lean
def p4_r (n : ℕ) : ℕ := Nat.clog 2 n
```
- 来源：arXiv:2503.03469v1 Introduction, definition (c)
- 被引用：15 次
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). Paper: least non-negative integer with n<=2^r; Lean Nat.clog 2 n. Checked defining property for n<=1e5 (r(1)=0) and brute force for n<=3000; no difference.

## `Mathlib2.p4_x`

x(n) = z(n) - (r(n)+1) m(n), the quantity whose sign the paper determines

```lean
def p4_x (n : ℕ) : ℤ := p4_z n - ((p4_r n : ℤ) + 1) * (p4_m n : ℤ)
```
- 来源：arXiv:2503.03469v1 Introduction, definition (d)
- 被引用：21 次
- 复核（reviewer_4）：faithful — Compared with verbatim text of arXiv:2503.03469v1 HTML (only version). Paper (d): x(n)=z(n)-(r(n)+1)m(n); Lean is the same expression in Int. Reproduces the paper's Exercise 1 table and x(4096)=1560.

## `Mathlib2.p5_dedekind_psi`

Dedekind psi function: psi(n) = prod over primes p | n of p^(a_p - 1) (p+1), where a_p is the exponent of p in n; psi(1) = 1 (and psi(0) = 1 by the empty-product convention).

```lean
def p5_dedekind_psi (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p + 1)
```
- 来源：arXiv:2404.19332v1 Section 1 (definition of psi)
- 被引用：14 次
- 复核（reviewer_5）：faithful — Compared with verbatim LaTeX of v1 Sec.1: psi(n)=prod p_i^(a_i-1)(p_i+1), psi(1)=1; Lean product over primeFactors with factorization exponents is identical (equals n*prod(1+1/p)); checked numerically vs both formulas. Only extra: psi(0)=1 junk value, never used since all statements have n>=2 or n!=

## `Mathlib2.p6_kfib`

k-Fibonacci number f_n for all integer n (f_0=0, f_1=1, f_{n+1}=k f_n+f_{n-1}), defined as the (0,1) entry of M^n, M=[[k,1],[1,0]], as in the paper's matrix formula

```lean
noncomputable def p6_kfib (k : ℤ) (n : ℤ) : ℤ := ((!![k, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) ^ n) 0 1
```
- 来源：arXiv:2611.07141v1 Section 2.2
- 被引用：0 次
