/- Mathlib2 分片 25（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0002
import Mathlib2.Shard.S0003
import Mathlib2.Shard.S0014
import Mathlib2.Shard.S0015
import Mathlib2.Shard.S0017
import Mathlib2.Shard.S0021
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry bld4_commuting_idempotents_rank_add kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_commuting_idempotents_rank_join: A + B = (A + B − AB)(1 + AB), and 1 + AB is invertible with inverse 1 − (1/2)AB because (AB)^2 = AB (char ≠ 2); multiplying by a unit preserves rank, so rank(A + B) = rank(A + B − AB), and the cited join formula finishes. -/
theorem bld4_commuting_idempotents_rank_add (K : Type*) [Field K] [CharZero K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (B : Matrix ι ι K) (hA : A * A = A) (hB : B * B = B) (hAB : A * B = B * A) : (A + B).rank + (A * B).rank = A.rank + B.rank := by
  have hAP : A * (A * B) = A * B := by rw [← mul_assoc, hA]
  have hBP : B * (A * B) = A * B := by rw [← mul_assoc, ← hAB, mul_assoc, hB]
  have hPP : A * B * (A * B) = A * B := by rw [mul_assoc, hBP, hAP]
  have e1 : A + B = (A + B - A * B) * (1 + A * B) := by
    rw [mul_add, mul_one, sub_mul, add_mul, hAP, hBP, hPP]; abel
  have e2 : A + B - A * B = (A + B) * (1 - (1 / 2 : K) • (A * B)) := by
    rw [mul_sub, mul_one, Matrix.mul_smul, add_mul, hAP, hBP, ← two_smul K (A * B), smul_smul]
    norm_num
  have h1 : (A + B).rank ≤ (A + B - A * B).rank := by
    conv_lhs => rw [e1]
    exact Matrix.rank_mul_le_left _ _
  have h2 : (A + B - A * B).rank ≤ (A + B).rank := by
    conv_lhs => rw [e2]
    exact Matrix.rank_mul_le_left _ _
  rw [le_antisymm h1 h2]
  exact bld2_commuting_idempotents_rank_join K ι A B hA hB hAB
end

-- forge:entry bld4_edelstein_surjective_subsingleton kind=proved origin=conjecture
section
/- Uses Mathlib2.bld_surjective_nonexpanding_compact_isometry: f is non-expanding (≤ from <, equality case x = y) and surjective, hence an isometry by the cited theorem; for x ≠ y this gives dist (f x) (f y) = dist x y, contradicting the strict inequality. -/
theorem bld4_edelstein_surjective_subsingleton {X : Type*} [MetricSpace X] [CompactSpace X] (f : X → X) (hf : ∀ x y : X, x ≠ y → dist (f x) (f y) < dist x y) (hs : Function.Surjective f) : Subsingleton X := by
  have hiso : Isometry f := by
    apply bld_surjective_nonexpanding_compact_isometry f hs
    intro x y
    by_cases hxy : x = y
    · subst hxy; simp
    · exact (hf x y hxy).le
  refine ⟨fun x y => ?_⟩
  by_contra hxy
  have := hf x y hxy
  rw [hiso.dist_eq] at this
  exact lt_irrefl _ this
end

-- forge:entry bld4_edelstein_diam_range_iterate_tendsto_zero kind=proved origin=conjecture
section
/- Uses Mathlib2.top_edelstein_unique_fixed_point and Mathlib2.bld3_edelstein_iterates_tendsto_uniformly: if X is empty the diameters are 0. Otherwise top_edelstein_unique_fixed_point gives a fixed point p, and bld3_edelstein_iterates_tendsto_uniformly gives N with dist (f^[n] x) p < ε/2 for all n ≥ N and x, so diam (range f^[n]) ≤ ε by Metric.diam_le_of_forall_dist_le. -/
theorem bld4_edelstein_diam_range_iterate_tendsto_zero {X : Type*} [MetricSpace X] [CompactSpace X] (f : X → X) (hf : ∀ x y : X, x ≠ y → dist (f x) (f y) < dist x y) : Filter.Tendsto (fun n : ℕ => Metric.diam (Set.range (f^[n]))) Filter.atTop (nhds 0) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · have : ∀ n : ℕ, Metric.diam (Set.range (f^[n])) = 0 := by
      intro n
      rw [Set.range_eq_empty, Metric.diam_empty]
    simp only [this]
    exact tendsto_const_nhds
  obtain ⟨p, hp, -⟩ := top_edelstein_unique_fixed_point f hf
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := bld3_edelstein_iterates_tendsto_uniformly f hf p hp (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.diam_nonneg]
  have : Metric.diam (Set.range (f^[n])) ≤ 2 * (ε / 3) := by
    apply Metric.diam_le_of_forall_dist_le (by positivity)
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have h1 := hN n hn x
    have h2 := hN n hn y
    have h3 := dist_triangle_right (f^[n] x) (f^[n] y) p
    linarith
  linarith
end

-- forge:entry bld4_carleman_finite_three kind=proved origin=conjecture
section
/- Uses Mathlib2.an2_amgm_range_pow and Mathlib2.an2_succ_pow_lt_three_mul_pow (Carleman's inequality with constant 3 > e): with weights c_i = (i+2)^(i+1)/(i+1)^i (0-indexed) one has ∏_{i≤k} c_i = (k+2)^(k+1), so by an2_amgm_range_pow applied to a_i c_i, (∏_{i≤k} a_i)^(1/(k+1)) ≤ (∑_{i≤k} a_i c_i)/((k+1)(k+2)). Summing over k < n, swapping sums and telescoping ∑_{k≥i} 1/((k+1)(k+2)) ≤ 1/(i+1) gives ≤ ∑ a_i c_i/(i+1) = ∑ a_i ((i+2)/(i+1))^(i+1) ≤ 3 ∑ a_i by an2_succ_pow_lt_three_mul_pow. -/
lemma bld4_carleman_finite_three_aux1 (m : ℕ) : ∏ i ∈ Finset.range m, (((i : ℝ) + 2) ^ (i + 1) / ((i : ℝ) + 1) ^ i) = ((m : ℝ) + 1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ih]
    have h : ((m : ℝ) + 1) ^ m ≠ 0 := by positivity
    rw [mul_div_cancel₀ _ h]
    push_cast
    ring

lemma bld4_carleman_finite_three_aux2 (b : ℕ → ℝ) (n : ℕ) : ∑ k ∈ Finset.range n, (∑ i ∈ Finset.range (k + 1), b i) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) = ∑ i ∈ Finset.range n, b i * (1 / ((i : ℝ) + 1) - 1 / ((n : ℝ) + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    have e : ∑ i ∈ Finset.range n, b i * (1 / ((i : ℝ) + 1) - 1 / (((n + 1 : ℕ) : ℝ) + 1)) = ∑ i ∈ Finset.range n, b i * (1 / ((i : ℝ) + 1) - 1 / ((n : ℝ) + 1)) + (∑ i ∈ Finset.range n, b i) * (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring
    rw [Finset.sum_range_succ (fun i => b i * (1 / ((i : ℝ) + 1) - 1 / (((n + 1 : ℕ) : ℝ) + 1))) n, e, Finset.sum_range_succ b n]
    push_cast
    field_simp
    ring

lemma bld4_carleman_finite_three_aux3 (a : ℕ → ℝ) (ha : ∀ i : ℕ, 0 ≤ a i) (k : ℕ) : (∏ i ∈ Finset.range (k + 1), a i) ^ (1 / ((k : ℝ) + 1)) ≤ (∑ i ∈ Finset.range (k + 1), a i * (((i : ℝ) + 2) ^ (i + 1) / ((i : ℝ) + 1) ^ i)) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
  have hb : ∀ i : ℕ, 0 ≤ a i * (((i : ℝ) + 2) ^ (i + 1) / ((i : ℝ) + 1) ^ i) := fun i =>
    mul_nonneg (ha i) (by positivity)
  set S := ∑ i ∈ Finset.range (k + 1), a i * (((i : ℝ) + 2) ^ (i + 1) / ((i : ℝ) + 1) ^ i) with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => hb i
  have hamgm := an2_amgm_range_pow k (fun i => a i * (((i : ℝ) + 2) ^ (i + 1) / ((i : ℝ) + 1) ^ i)) hb
  rw [Finset.prod_mul_distrib, bld4_carleman_finite_three_aux1] at hamgm
  have hk2 : (0 : ℝ) < ((k : ℝ) + 2) ^ (k + 1) := by positivity
  have hP : ∏ i ∈ Finset.range (k + 1), a i ≤ (S / (((k : ℝ) + 1) * ((k : ℝ) + 2))) ^ (k + 1) := by
    rw [← div_div, div_pow (S / ((k : ℝ) + 1)), le_div_iff₀ hk2]
    refine le_trans (le_of_eq ?_) hamgm
    push_cast
    ring
  have hx : 0 ≤ S / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by positivity
  calc (∏ i ∈ Finset.range (k + 1), a i) ^ (1 / ((k : ℝ) + 1))
      ≤ ((S / (((k : ℝ) + 1) * ((k : ℝ) + 2))) ^ (k + 1)) ^ (1 / ((k : ℝ) + 1)) :=
        Real.rpow_le_rpow (Finset.prod_nonneg fun i _ => ha i) hP (by positivity)
    _ = S / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
        have := Real.pow_rpow_inv_natCast hx (Nat.succ_ne_zero k)
        rw [one_div]
        push_cast at this
        exact this

theorem bld4_carleman_finite_three (a : ℕ → ℝ) (ha : ∀ i : ℕ, 0 ≤ a i) (n : ℕ) : ∑ k ∈ Finset.range n, (∏ i ∈ Finset.range (k + 1), a i) ^ (1 / ((k : ℝ) + 1)) ≤ 3 * ∑ k ∈ Finset.range n, a k := by
  calc ∑ k ∈ Finset.range n, (∏ i ∈ Finset.range (k + 1), a i) ^ (1 / ((k : ℝ) + 1))
      ≤ ∑ k ∈ Finset.range n, (∑ i ∈ Finset.range (k + 1), a i * (((i : ℝ) + 2) ^ (i + 1) / ((i : ℝ) + 1) ^ i)) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) :=
        Finset.sum_le_sum fun k _ => bld4_carleman_finite_three_aux3 a ha k
    _ = ∑ i ∈ Finset.range n, a i * (((i : ℝ) + 2) ^ (i + 1) / ((i : ℝ) + 1) ^ i) * (1 / ((i : ℝ) + 1) - 1 / ((n : ℝ) + 1)) :=
        bld4_carleman_finite_three_aux2 _ n
    _ ≤ ∑ i ∈ Finset.range n, 3 * a i := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hN := an2_succ_pow_lt_three_mul_pow (i + 1) (Nat.succ_pos i)
        have hN' : ((i : ℝ) + 2) ^ (i + 1) ≤ 3 * ((i : ℝ) + 1) ^ (i + 1) := by
          have : (((i + 1 + 1) ^ (i + 1) : ℕ) : ℝ) ≤ ((3 * (i + 1) ^ (i + 1) : ℕ) : ℝ) := by
            exact_mod_cast hN.le
          push_cast at this
          have e : (i : ℝ) + 1 + 1 = (i : ℝ) + 2 := by ring
          rw [e] at this
          exact this
        have hc : 0 ≤ a i * (((i : ℝ) + 2) ^ (i + 1) / ((i : ℝ) + 1) ^ i) :=
          mul_nonneg (ha i) (by positivity)
        have hn : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
        have h1 : a i * (((i : ℝ) + 2) ^ (i + 1) / ((i : ℝ) + 1) ^ i) * (1 / ((i : ℝ) + 1) - 1 / ((n : ℝ) + 1)) ≤ a i * (((i : ℝ) + 2) ^ (i + 1) / ((i : ℝ) + 1) ^ i) * (1 / ((i : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (by linarith) hc
        have h2 : a i * (((i : ℝ) + 2) ^ (i + 1) / ((i : ℝ) + 1) ^ i) * (1 / ((i : ℝ) + 1)) = a i * (((i : ℝ) + 2) ^ (i + 1) / ((i : ℝ) + 1) ^ (i + 1)) := by
          rw [pow_succ ((i : ℝ) + 1) i]
          field_simp
        have h3 : ((i : ℝ) + 2) ^ (i + 1) / ((i : ℝ) + 1) ^ (i + 1) ≤ 3 := by
          rw [div_le_iff₀ (by positivity)]
          exact hN'
        calc _ ≤ _ := h1
          _ = _ := h2
          _ ≤ a i * 3 := mul_le_mul_of_nonneg_left h3 (ha i)
          _ = 3 * a i := mul_comm _ _
    _ = 3 * ∑ k ∈ Finset.range n, a k := by rw [Finset.mul_sum]
end

-- forge:entry bld4_card_orderOf_eq_prime_of_card_prime_mul_prime kind=proved origin=conjecture
section
/- Uses Mathlib2.bld3_card_sylow_of_card_prime_mul_prime: there are exactly q Sylow p-subgroups, each of order p; two distinct ones meet trivially, and every element of order p generates one. So the elements of order p are the disjoint union over the q Sylow p-subgroups of their p − 1 non-identity elements. -/
theorem bld4_card_orderOf_eq_prime_of_card_prime_mul_prime (p q : ℕ) [Fact p.Prime] (hq : q.Prime) (hpq : p < q) (G : Type*) [Group G] (hG : Nat.card G = p * q) (hna : ∃ a b : G, a * b ≠ b * a) : Nat.card {g : G // orderOf g = p} = q * (p - 1) := by
  have hp : p.Prime := Fact.out
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact (Nat.mul_pos hp.pos hq.pos).ne')
  have hcard : ∀ P : Sylow p G, Nat.card ↥(P : Subgroup G) = p := fun P =>
    (bld3_card_sylow_of_card_prime_mul_prime_aux1 p q hq (ne_of_lt hpq) G hG P).1
  have hord : ∀ (P : Sylow p G) (g : G), g ∈ (P : Subgroup G) → g ≠ 1 → orderOf g = p := by
    intro P g hg hg1
    have hd := Subgroup.orderOf_dvd_natCard (P : Subgroup G) hg
    rw [hcard P] at hd
    rcases (Nat.dvd_prime hp).mp hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hg1
    · exact h1
  have hzp : ∀ (P : Sylow p G) (g : G), g ∈ (P : Subgroup G) → g ≠ 1 →
      Subgroup.zpowers g = (P : Subgroup G) := by
    intro P g hg hg1
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg)
    rw [Nat.card_zpowers, hord P g hg hg1, hcard P]
  have hfib : ∀ P : Sylow p G, Nat.card ↥(((P : Subgroup G) : Set G) \ {1}) = p - 1 := by
    intro P
    rw [Nat.card_coe_set_eq, Set.ncard_diff_singleton_of_mem (P : Subgroup G).one_mem,
      ← Nat.card_coe_set_eq]
    exact congrArg (· - 1) (hcard P)
  have hbij : Function.Bijective
      (fun x : (Σ P : Sylow p G, ↥(((P : Subgroup G) : Set G) \ {1})) =>
        (⟨x.2.1, hord x.1 x.2.1 x.2.2.1 x.2.2.2⟩ : {g : G // orderOf g = p})) := by
    constructor
    · rintro ⟨P, g, hg⟩ ⟨P', g', hg'⟩ h
      simp only [Subtype.mk.injEq] at h
      subst h
      have hPP : P = P' := Sylow.ext ((hzp P g hg.1 hg.2).symm.trans (hzp P' g hg'.1 hg'.2))
      subst hPP
      rfl
    · rintro ⟨g, hg⟩
      have hpg : IsPGroup p ↥(Subgroup.zpowers g) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
      obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
      have hg1 : g ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at hg
        exact hp.one_lt.ne hg
      exact ⟨⟨Q, ⟨g, hQ (Subgroup.mem_zpowers g), hg1⟩⟩, rfl⟩
  haveI : Fintype (Sylow p G) := Fintype.ofFinite _
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_sigma]
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, bld3_card_sylow_of_card_prime_mul_prime p q hq hpq G hG hna]
end

-- forge:entry poly_fermat_catalan_2_3_7 kind=proved origin=conjecture
section
/- In characteristic 0, a^2 + b^3 = c^7 has no non-constant pairwise coprime polynomial solutions (1/2+1/3+1/7 < 1) — Uses Mathlib2.ms_fermat_catalan with (p,q,r)=(2,3,7), u=v=1, w=-1; ringChar k = 0 divides none of 2,3,7; rewrite heq as C 1 * a^2 + C 1 * b^3 + C (-1) * c^7 = 0. -/
theorem poly_fermat_catalan_2_3_7 {k : Type*} [Field k] [DecidableEq k] [CharZero k] (a b c : Polynomial k) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b) (hbc : IsCoprime b c) (hca : IsCoprime c a) (heq : a ^ 2 + b ^ 3 = c ^ 7) : a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 := by
  have h0 : ringChar k = 0 := ringChar.eq_zero
  refine Mathlib2.ms_fermat_catalan (k := k) 2 3 7 (by norm_num) (by norm_num) (by norm_num)
    (by rw [h0]; norm_num) (by rw [h0]; norm_num) (by rw [h0]; norm_num) (by norm_num)
    1 1 (-1) one_ne_zero one_ne_zero (by simp) a b c ha hb hc hab hbc hca ?_
  rw [← heq]; simp
end

-- forge:entry poly_fermat_quartic_4_4_2 kind=proved origin=conjecture
section
/- Polynomial analogue of Fermat's quartic theorem: a^4 + b^4 = c^2 forces coprime nonzero a, b, c to be constant in char 0 (borderline case 1/4+1/4+1/2 = 1) — Uses Mathlib2.ms_fermat_catalan with (p,q,r)=(4,4,2), u=v=1, w=-1; the only work is the ringChar and the 1/p+1/q+1/r ≤ 1 side conditions. -/
theorem poly_fermat_quartic_4_4_2 {k : Type*} [Field k] [DecidableEq k] [CharZero k] (a b c : Polynomial k) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b) (hbc : IsCoprime b c) (hca : IsCoprime c a) (heq : a ^ 4 + b ^ 4 = c ^ 2) : a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 := by
  have h0 : ringChar k = 0 := ringChar.eq_zero
  refine Mathlib2.ms_fermat_catalan (k := k) 4 4 2 (by norm_num) (by norm_num) (by norm_num)
    (by rw [h0]; norm_num) (by rw [h0]; norm_num) (by rw [h0]; norm_num) (by norm_num)
    1 1 (-1) one_ne_zero one_ne_zero (by simp) a b c ha hb hc hab hbc hca ?_
  rw [← heq]; simp
end

-- forge:entry poly_x2_x_1_dvd_trinomial kind=proved origin=conjecture
section
/- X^2+X+1 divides X^(3k+2) + X^(3m+1) + 1 over ℤ — X^3 ≡ 1 mod X^2+X+1 (since X^3 - 1 = (X-1)(X^2+X+1)), so the trinomial is ≡ X^2 + X + 1 ≡ 0. -/
open Polynomial in
theorem poly_x2_x_1_dvd_trinomial (k m : ℕ) : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial ℤ) ∣ Polynomial.X ^ (3 * k + 2) + Polynomial.X ^ (3 * m + 1) + 1 := by
  have h3 : (X ^ 2 + X + 1 : ℤ[X]) ∣ X ^ 3 - 1 := ⟨X - 1, by ring⟩
  have hk : (X ^ 2 + X + 1 : ℤ[X]) ∣ (X ^ 3) ^ k - 1 := by
    have := sub_dvd_pow_sub_pow (X ^ 3 : ℤ[X]) 1 k
    rw [one_pow] at this
    exact h3.trans this
  have hm : (X ^ 2 + X + 1 : ℤ[X]) ∣ (X ^ 3) ^ m - 1 := by
    have := sub_dvd_pow_sub_pow (X ^ 3 : ℤ[X]) 1 m
    rw [one_pow] at this
    exact h3.trans this
  have e : (X ^ (3 * k + 2) + X ^ (3 * m + 1) + 1 : ℤ[X]) = X ^ 2 * ((X ^ 3) ^ k - 1) + X * ((X ^ 3) ^ m - 1) + (X ^ 2 + X + 1) := by
    ring
  rw [e]
  exact dvd_add (dvd_add (hk.mul_left _) (hm.mul_left _)) dvd_rfl
end

-- forge:entry poly_int_odd_at_zero_one_no_root kind=proved origin=conjecture
section
/- An integer polynomial with p(0) and p(1) odd has no integer root — n - 0 ∣ p(n) - p(0) and n - 1 ∣ p(n) - p(1) (Polynomial.sub_dvd_eval_sub); if p(n) = 0 then both n and n-1 divide odd numbers, but one of them is even. -/
theorem poly_int_odd_at_zero_one_no_root (p : Polynomial ℤ) (h0 : Odd (Polynomial.eval 0 p)) (h1 : Odd (Polynomial.eval 1 p)) (n : ℤ) : Polynomial.eval n p ≠ 0 := by
  intro hn
  have a0 := Polynomial.sub_dvd_eval_sub n 0 p
  have a1 := Polynomial.sub_dvd_eval_sub n 1 p
  rw [hn] at a0 a1
  obtain ⟨u, hu⟩ := a0
  obtain ⟨v, hv⟩ := a1
  obtain ⟨s, hs⟩ := h0
  obtain ⟨t, ht⟩ := h1
  rw [hs] at hu
  rw [ht] at hv
  rcases Int.even_or_odd n with ⟨w, hw⟩ | ⟨w, hw⟩
  · subst hw
    have : (2:ℤ) ∣ 0 - (2 * s + 1) := ⟨w * u, by rw [hu]; ring⟩
    omega
  · subst hw
    have : (2:ℤ) ∣ 0 - (2 * t + 1) := ⟨w * v, by rw [hv]; ring⟩
    omega
end

-- forge:entry poly_int_three_ones_no_root kind=proved origin=conjecture
section
/- An integer polynomial taking the value 1 at three distinct integers has no integer root — if p(r) = 0 then r-a, r-b, r-c each divide p(r) - 1 = -1 (sub_dvd_eval_sub), so they are three distinct elements of {1,-1}, impossible. -/
theorem poly_int_three_ones_no_root (p : Polynomial ℤ) (a b c : ℤ) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ha : Polynomial.eval a p = 1) (hb : Polynomial.eval b p = 1) (hc : Polynomial.eval c p = 1) (r : ℤ) : Polynomial.eval r p ≠ 0 := by
  intro hr
  have key : ∀ x : ℤ, Polynomial.eval x p = 1 → (r - x = 1 ∨ r - x = -1) := by
    intro x hx
    have h := Polynomial.sub_dvd_eval_sub r x p
    rw [hr, hx] at h
    have h' : r - x ∣ 1 := by
      have := (dvd_neg).mpr h
      simpa using this
    exact Int.isUnit_iff.mp (isUnit_of_dvd_one h')
  have := key a ha
  have := key b hb
  have := key c hc
  omega
end

-- forge:entry poly_real_nonneg_coeff_no_pos_root kind=proved origin=conjecture
section
/- A nonzero real polynomial with nonnegative coefficients has no positive root (trivial case of Descartes' rule) — eval x p = Σ coeff i * x^i is a sum of nonnegative terms, at least one (the leading one) strictly positive. -/
theorem poly_real_nonneg_coeff_no_pos_root (p : Polynomial ℝ) (hp : p ≠ 0) (h : ∀ i : ℕ, 0 ≤ p.coeff i) (x : ℝ) (hx : 0 < x) : Polynomial.eval x p ≠ 0 := by
  have hl : 0 < p.leadingCoeff := lt_of_le_of_ne (h _) (Ne.symm (Polynomial.leadingCoeff_ne_zero.mpr hp))
  rw [Polynomial.eval_eq_sum_range]
  apply ne_of_gt
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (h i) (pow_nonneg hx.le i)
  · exact ⟨p.natDegree, by simp, mul_pos hl (pow_pos hx _)⟩
end

-- forge:entry poly_sophie_germain_not_irreducible kind=proved origin=conjecture
section
/- Sophie Germain: X^4 + 4a^4 is reducible over ℤ for every integer a — X^4 + 4a^4 = (X^2 + 2aX + 2a^2)(X^2 - 2aX + 2a^2), both monic of degree 2 hence non-units. -/
open Polynomial in
theorem poly_sophie_germain_not_irreducible (a : ℤ) : ¬ Irreducible (Polynomial.X ^ 4 + Polynomial.C (4 * a ^ 4) : Polynomial ℤ) := by
  intro h
  have e : (X ^ 4 + C (4 * a ^ 4) : ℤ[X]) = (X ^ 2 + C (2 * a) * X + C (2 * a ^ 2)) * (X ^ 2 - C (2 * a) * X + C (2 * a ^ 2)) := by
    simp only [map_mul, map_pow, map_ofNat]
    ring
  rcases h.isUnit_or_isUnit e with hu | hu
  · obtain ⟨r, -, hr⟩ := Polynomial.isUnit_iff.mp hu
    have := congrArg (fun q => Polynomial.coeff q 2) hr
    simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X] at this
    norm_num at this
  · obtain ⟨r, -, hr⟩ := Polynomial.isUnit_iff.mp hu
    have := congrArg (fun q => Polynomial.coeff q 2) hr
    simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X] at this
    norm_num at this
end

-- forge:entry poly_abc_radical_bound_of_coprime kind=proved origin=conjecture
section
/- ABC for polynomials in two-variable form: coprime a, b in char 0 with a non-constant satisfy max(deg a, deg b) + 1 ≤ deg rad(ab(a+b)) — b ≠ 0 and a+b ≠ 0 follow from coprimality and deg a > 0; Uses Mathlib2.ms_mason_stothers_v2 with c = -(a+b) (derivative a ≠ 0 in char 0 kills the first alternative), and radical(a*b*(-(a+b))) = radical(a*b*(a+b)) by associatedness. -/
theorem poly_abc_radical_bound_of_coprime {k : Type*} [Field k] [DecidableEq k] [CharZero k] (a b : Polynomial k) (hab : IsCoprime a b) (ha : 0 < a.natDegree) : max a.natDegree b.natDegree + 1 ≤ (UniqueFactorizationMonoid.radical (a * b * (a + b))).natDegree := by
  have hnu : ¬ IsUnit a := fun h => by
    have := Polynomial.natDegree_eq_zero_of_isUnit h
    omega
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hnu (isCoprime_zero_right.mp hab)
  have hc0 : -(a + b) ≠ 0 := by
    intro h
    have hb : b = -a := by linear_combination -h
    rw [hb] at hab
    exact hnu (isCoprime_self.mp (by simpa using hab.neg_right))
  have hbc : IsCoprime b (-(a + b)) := by
    have : IsCoprime b (a + b) := by
      have := hab.symm.add_mul_left_right 1
      simpa using this
    exact this.neg_right
  have hca : IsCoprime (-(a + b)) a := by
    have : IsCoprime a (b + a) := by
      have := hab.add_mul_left_right 1
      simpa using this
    rw [add_comm] at this
    exact this.symm.neg_left
  have hda : Polynomial.derivative a ≠ 0 := fun h => by
    have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero h
    omega
  rcases Mathlib2.ms_mason_stothers_v2 a b (-(a + b)) ha0 hb0 hc0 hab hbc hca (by ring) with h | h
  · exact absurd h.1 hda
  · have e : a * b * (-(a + b)) = -(a * b * (a + b)) := by ring
    rw [e, UniqueFactorizationDomain.radical_neg] at h
    have : max a.natDegree b.natDegree ≤ max (max a.natDegree b.natDegree) (-(a + b)).natDegree := le_max_left _ _
    omega
end

-- forge:entry poly_catalan_pow_add_one kind=proved origin=conjecture
section
/- Catalan for polynomials: in char 0 two perfect powers g^m, h^n (m,n ≥ 2) differing by 1 are constants — Uses Mathlib2.ms_mason_stothers_v2 with a = g^m, b = 1, c = -h^n (pairwise coprime since g^m and h^n differ by a unit): if g is non-constant, D = m·deg g = n·deg h < deg rad(g^m h^n) ≤ deg g + deg h = D/m + D/n ≤ D, contradiction; g = 0 or g constant handled separately. -/
theorem poly_catalan_pow_add_one {k : Type*} [Field k] [DecidableEq k] [CharZero k] (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (g h : Polynomial k) (heq : g ^ m + 1 = h ^ n) : g.natDegree = 0 ∧ h.natDegree = 0 := by
  have hdh : (h ^ n).natDegree = n * h.natDegree := Polynomial.natDegree_pow h n
  have hdg : (g ^ m).natDegree = m * g.natDegree := Polynomial.natDegree_pow g m
  by_cases hg : g.natDegree = 0
  · refine ⟨hg, ?_⟩
    have h1 : (g ^ m + 1).natDegree ≤ max (g ^ m).natDegree (1 : Polynomial k).natDegree :=
      Polynomial.natDegree_add_le _ _
    rw [heq, hdh, hdg, hg] at h1
    simp at h1
    omega
  · exfalso
    have hgpos : 0 < g.natDegree := Nat.pos_of_ne_zero hg
    have hpos : 0 < (g ^ m).natDegree := by rw [hdg]; positivity
    have hd : (g ^ m + 1).natDegree = (g ^ m).natDegree :=
      Polynomial.natDegree_add_eq_left_of_natDegree_lt (by simpa using hpos)
    rw [heq, hdh, hdg] at hd
    have hg0 : g ≠ 0 := by rintro rfl; simp at hg
    have hh0 : h ≠ 0 := by
      rintro rfl
      simp at hd
      omega
    have key := Mathlib2.poly_abc_radical_bound_of_coprime (g ^ m) 1 isCoprime_one_right hpos
    rw [heq, mul_one, hdg] at key
    have hdvd : UniqueFactorizationMonoid.radical (g ^ m * h ^ n) ∣ g * h := by
      refine UniqueFactorizationMonoid.radical_mul_dvd.trans ?_
      rw [UniqueFactorizationMonoid.radical_pow g (by omega), UniqueFactorizationMonoid.radical_pow h (by omega)]
      exact mul_dvd_mul UniqueFactorizationMonoid.radical_dvd_self UniqueFactorizationMonoid.radical_dvd_self
    have hle := Polynomial.natDegree_le_of_dvd hdvd (mul_ne_zero hg0 hh0)
    rw [Polynomial.natDegree_mul hg0 hh0] at hle
    have e1 : 2 * g.natDegree ≤ m * g.natDegree := Nat.mul_le_mul_right _ hm
    have e2 : 2 * h.natDegree ≤ n * h.natDegree := Nat.mul_le_mul_right _ hn
    have : m * g.natDegree ≤ max (m * g.natDegree) (1 : Polynomial k).natDegree := le_max_left _ _
    omega
end

-- forge:entry poly_chebyshev_T_abs_le_one kind=proved origin=conjecture
section
/- Chebyshev polynomials of the first kind are bounded by 1 on [-1,1] — write x = cos θ with θ = arccos x, then T_n(cos θ) = cos(nθ) (Polynomial.Chebyshev.T_real_cos) and |cos| ≤ 1. -/
theorem poly_chebyshev_T_abs_le_one (n : ℤ) (x : ℝ) (hx : |x| ≤ 1) : |Polynomial.eval x (Polynomial.Chebyshev.T ℝ n)| ≤ 1 := by
  obtain ⟨h1, h2⟩ := abs_le.mp hx
  have := Polynomial.Chebyshev.T_real_cos (Real.arccos x) n
  rw [Real.cos_arccos h1 h2] at this
  rw [this]
  exact Real.abs_cos_le_one _
end

-- forge:entry poly_x3_x_1_irreducible_rat kind=proved origin=conjecture
section
/- X^3 + X + 1 is irreducible over ℚ — a cubic is irreducible iff it has no root; by the rational root theorem a rational root would be ±1, and neither is a root. -/
open Polynomial in
theorem poly_x3_x_1_irreducible_rat : Irreducible (Polynomial.X ^ 3 + Polynomial.X + 1 : Polynomial ℚ) := by
  have hd : (X ^ 3 + X + 1 : ℚ[X]).natDegree = 3 := by compute_degree!
  have hne : (X ^ 3 + X + 1 : ℚ[X]) ≠ 0 := by
    intro h; rw [h] at hd; simp at hd
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  apply Multiset.eq_zero_of_forall_notMem
  intro r hr
  rw [mem_roots hne] at hr
  have hm : (X ^ 3 + X + 1 : ℤ[X]).Monic := by monicity!
  have ha : aeval r (X ^ 3 + X + 1 : ℤ[X]) = 0 := by
    simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one] at hr
    simpa using hr
  obtain ⟨n, hn⟩ := isInteger_of_is_root_of_monic hm ha
  have hn' : (n : ℚ) = r := by simpa using hn
  subst hn'
  simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one] at hr
  have hz : n ^ 3 + n + 1 = 0 := by exact_mod_cast hr
  have hdvd : n ∣ 1 := ⟨-(n ^ 2 + 1), by linarith⟩
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h <;> subst h <;> norm_num at hz
end

-- forge:entry poly_flt_noncoprime_proportional kind=proved origin=conjecture
section
/- FLT for polynomials without coprimality: in char 0, any nonzero solution of a^n + b^n = c^n (n ≥ 3) is a common polynomial d times a constant solution — take d = gcd(a,b); d^n ∣ c^n gives d ∣ c; the quotients are pairwise coprime and satisfy the same equation, so Uses Mathlib2.ms_flt_poly to make them constants. -/
theorem poly_flt_noncoprime_proportional {k : Type*} [Field k] [DecidableEq k] [CharZero k] (n : ℕ) (hn : 3 ≤ n) (a b c : Polynomial k) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (heq : a ^ n + b ^ n = c ^ n) : ∃ (d : Polynomial k) (α β γ : k), a = Polynomial.C α * d ∧ b = Polynomial.C β * d ∧ c = Polynomial.C γ * d := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : 0 < n := by omega
  have hbez := EuclideanDomain.gcd_eq_gcd_ab a b
  obtain ⟨a', ha'⟩ := EuclideanDomain.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ := EuclideanDomain.gcd_dvd_right a b
  generalize EuclideanDomain.gcd a b = d at hbez ha' hb'
  generalize EuclideanDomain.gcdA a b = x at hbez
  generalize EuclideanDomain.gcdB a b = y at hbez
  subst ha' hb'
  have hd0 : d ≠ 0 := left_ne_zero_of_mul ha
  have ha0 : a' ≠ 0 := right_ne_zero_of_mul ha
  have hb0 : b' ≠ 0 := right_ne_zero_of_mul hb
  have hab : IsCoprime a' b' := by
    refine ⟨x, y, ?_⟩
    apply mul_left_cancel₀ hd0
    linear_combination -hbez
  have hdc : d ∣ c := by
    rw [← IsIntegrallyClosed.pow_dvd_pow_iff hn0]
    exact ⟨a' ^ n + b' ^ n, by rw [← heq]; ring⟩
  obtain ⟨c', rfl⟩ := hdc
  have hc0 : c' ≠ 0 := right_ne_zero_of_mul hc
  have heq' : a' ^ n + b' ^ n = c' ^ n := by
    apply mul_left_cancel₀ (pow_ne_zero n hd0)
    linear_combination heq
  have hbc : IsCoprime b' c' := by
    rw [← IsCoprime.pow_iff hnpos hnpos]
    obtain ⟨u, v, huv⟩ := (IsCoprime.pow hab.symm : IsCoprime (b' ^ n) (a' ^ n))
    exact ⟨u - v, v, by rw [← heq']; linear_combination huv⟩
  have hca : IsCoprime c' a' := by
    rw [← IsCoprime.pow_iff hnpos hnpos]
    obtain ⟨u, v, huv⟩ := (IsCoprime.pow hab : IsCoprime (a' ^ n) (b' ^ n))
    exact ⟨v, u - v, by rw [← heq']; linear_combination huv⟩
  have hchar : ¬ ringChar k ∣ n := by
    rw [ringChar.eq_zero]
    simpa using hn0
  obtain ⟨h1, h2, h3⟩ := Mathlib2.ms_flt_poly n hn hchar a' b' c' ha0 hb0 hc0 hab hbc hca heq'
  refine ⟨d, a'.coeff 0, b'.coeff 0, c'.coeff 0, ?_, ?_, ?_⟩
  · rw [← Polynomial.eq_C_of_natDegree_eq_zero h1, mul_comm]
  · rw [← Polynomial.eq_C_of_natDegree_eq_zero h2, mul_comm]
  · rw [← Polynomial.eq_C_of_natDegree_eq_zero h3, mul_comm]
end

-- forge:entry poly_cubic_real_roots_newton kind=proved origin=conjecture
section
/- Newton's inequality for a real cubic with three real roots (with multiplicity): X^3 + aX^2 + bX + c splitting over ℝ forces a^2 ≥ 3b — the polynomial equals (X-r)(X-s)(X-t), so a = -(r+s+t), b = rs+st+tr and a^2 - 3b = ((r-s)^2 + (s-t)^2 + (t-r)^2)/2 ≥ 0. -/
open Polynomial in
theorem poly_cubic_real_roots_newton (a b c : ℝ) (h : (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c : Polynomial ℝ).roots.card = 3) : 3 * b ≤ a ^ 2 := by
  have hm : (X ^ 3 + C a * X ^ 2 + C b * X + C c : ℝ[X]).Monic := by monicity!
  have hd : (X ^ 3 + C a * X ^ 2 + C b * X + C c : ℝ[X]).natDegree = 3 := by compute_degree!
  have hp := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := (X ^ 3 + C a * X ^ 2 + C b * X + C c : ℝ[X])) (by rw [h, hd])
  obtain ⟨x, y, z, hxyz⟩ := Multiset.card_eq_three.mp h
  rw [hxyz, hm.leadingCoeff] at hp
  have e : (C (1:ℝ) * (Multiset.map (fun a => X - C a) ({x, y, z} : Multiset ℝ)).prod : ℝ[X]) = X ^ 3 + C (-(x + y + z)) * X ^ 2 + C (x * y + x * z + y * z) * X + C (-(x * y * z)) := by
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.map_singleton, Multiset.prod_singleton, map_add, map_mul, map_neg, map_one]
    ring
  rw [e] at hp
  have c1 := congrArg (fun q => coeff q 1) hp
  have c2 := congrArg (fun q => coeff q 2) hp
  simp only [coeff_add, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X] at c1 c2
  norm_num at c1 c2
  rw [← c1, ← c2]
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
end

-- forge:entry poly_ratfunc_fermat_curve_const kind=proved origin=conjecture
section
/- The Fermat curve x^n + y^n = 1 (n ≥ 3) has no non-constant rational parametrisation in char 0 — write f = a/c, g = b/c with common denominator, cancel gcd(a,b,c) to get pairwise coprime a^n + b^n = c^n, then Uses Mathlib2.ms_flt_poly to conclude a, b, c constant; the cases a = 0 or b = 0 (g^n = 1 forces g constant) are separate. -/
open Polynomial

theorem poly_ratfunc_fermat_curve_const_aux1 {k : Type*} [Field k] [DecidableEq k] [CharZero k] (n : ℕ) (hn : 3 ≤ n) (A B E : k[X]) (hE : E ≠ 0) (heq : A ^ n + B ^ n = E ^ n) : ∃ c : k, algebraMap k[X] (RatFunc k) A / algebraMap k[X] (RatFunc k) E = RatFunc.C c := by
  have hn0 : n ≠ 0 := by omega
  have hinj := RatFunc.algebraMap_injective k
  have hE0 : algebraMap k[X] (RatFunc k) E ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact hE
  by_cases hA : A = 0
  · exact ⟨0, by simp [hA]⟩
  by_cases hB : B = 0
  · subst hB
    have hdvd : E ∣ A := by
      rw [← IsIntegrallyClosed.pow_dvd_pow_iff hn0]
      exact ⟨1, by rw [← heq, zero_pow hn0]; ring⟩
    obtain ⟨e, rfl⟩ := hdvd
    have he : e ^ n = 1 := by
      apply mul_left_cancel₀ (pow_ne_zero n hE)
      rw [zero_pow hn0] at heq
      linear_combination heq
    have hdeg := congrArg Polynomial.natDegree he
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_one] at hdeg
    have hdeg0 : e.natDegree = 0 := by
      rcases Nat.mul_eq_zero.mp hdeg with h | h
      · omega
      · exact h
    refine ⟨e.coeff 0, ?_⟩
    rw [← RatFunc.algebraMap_C, ← Polynomial.eq_C_of_natDegree_eq_zero hdeg0, map_mul, mul_div_cancel_left₀ _ hE0]
  obtain ⟨d, α, β, γ, h1, h2, h3⟩ := Mathlib2.poly_flt_noncoprime_proportional n hn A B E hA hB hE heq
  have hd : d ≠ 0 := by rintro rfl; exact hE (by simp [h3])
  have hd0 : algebraMap k[X] (RatFunc k) d ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact hd
  refine ⟨α / γ, ?_⟩
  rw [h1, h3, map_mul, map_mul, mul_div_mul_right _ _ hd0, RatFunc.algebraMap_C, RatFunc.algebraMap_C, map_div₀]

theorem poly_ratfunc_fermat_curve_const {k : Type*} [Field k] [DecidableEq k] [CharZero k] (n : ℕ) (hn : 3 ≤ n) (f g : RatFunc k) (heq : f ^ n + g ^ n = 1) : (∃ c : k, f = RatFunc.C c) ∧ (∃ d : k, g = RatFunc.C d) := by
  have hf : f = algebraMap k[X] (RatFunc k) f.num / algebraMap k[X] (RatFunc k) f.denom :=
    (RatFunc.num_div_denom f).symm
  have hg : g = algebraMap k[X] (RatFunc k) g.num / algebraMap k[X] (RatFunc k) g.denom :=
    (RatFunc.num_div_denom g).symm
  have hinj := RatFunc.algebraMap_injective k
  have hc0 : algebraMap k[X] (RatFunc k) f.denom ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact f.denom_ne_zero
  have hd0 : algebraMap k[X] (RatFunc k) g.denom ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact g.denom_ne_zero
  have key : (f.num * g.denom) ^ n + (g.num * f.denom) ^ n = (f.denom * g.denom) ^ n := by
    apply hinj
    simp only [map_mul, map_pow, map_add]
    have h := heq
    rw [hf, hg] at h
    rw [div_pow, div_pow, div_add_div _ _ (pow_ne_zero n hc0) (pow_ne_zero n hd0),
      div_eq_one_iff_eq (mul_ne_zero (pow_ne_zero n hc0) (pow_ne_zero n hd0))] at h
    rw [mul_pow, mul_pow, mul_pow]
    linear_combination h
  have key' : (g.num * f.denom) ^ n + (f.num * g.denom) ^ n = (f.denom * g.denom) ^ n := by
    rw [add_comm]; exact key
  have hE : f.denom * g.denom ≠ 0 := mul_ne_zero f.denom_ne_zero g.denom_ne_zero
  obtain ⟨c, hc⟩ := poly_ratfunc_fermat_curve_const_aux1 n hn _ _ _ hE key
  obtain ⟨d, hd⟩ := poly_ratfunc_fermat_curve_const_aux1 n hn _ _ _ hE key'
  refine ⟨⟨c, ?_⟩, ⟨d, ?_⟩⟩
  · rw [← hc, map_mul, map_mul, mul_div_mul_right _ _ hd0]
    exact hf
  · rw [← hd, map_mul, map_mul, mul_comm (algebraMap k[X] (RatFunc k) g.num), mul_div_mul_left _ _ hc0]
    exact hg
end

-- forge:entry poly_davenport_sharp_deg_two kind=proved origin=conjecture
section
/- Davenport's bound is sharp in degree (2,3): the least possible degree of f^3 - g^2 ≠ 0 with deg f = 2, deg g = 3 over ℚ is exactly 2 — membership by f = X^2 + 2, g = X^3 + 3X (f^3 - g^2 = 3X^2 + 8); lower bound Uses Mathlib2.ms_davenport: f.natDegree + 2 = 4 ≤ 2·d. -/
open Polynomial

theorem poly_davenport_sharp_deg_two : IsLeast {d : ℕ | ∃ f g : Polynomial ℚ, f.natDegree = 2 ∧ g.natDegree = 3 ∧ f ^ 3 ≠ g ^ 2 ∧ (f ^ 3 - g ^ 2).natDegree = d} 2 := by
  constructor
  · have e : ((X ^ 2 + C 2 : ℚ[X]) ^ 3 - (X ^ 3 + C 3 * X) ^ 2) = C 3 * X ^ 2 + C 8 := by
      have h1 : (C 3 : ℚ[X]) = 3 := map_ofNat C 3
      have h2 : (C 2 : ℚ[X]) = 2 := map_ofNat C 2
      have h3 : (C 8 : ℚ[X]) = 8 := map_ofNat C 8
      rw [h1, h2, h3]; ring
    have hd : ((C 3 : ℚ[X]) * X ^ 2 + C 8).natDegree = 2 := by
      rw [Polynomial.natDegree_add_C, Polynomial.natDegree_C_mul_X_pow 2 3 (by norm_num)]
    refine ⟨X ^ 2 + C 2, X ^ 3 + C 3 * X, ?_, ?_, ?_, ?_⟩
    · rw [Polynomial.natDegree_add_C, Polynomial.natDegree_X_pow]
    · compute_degree!
    · intro h
      rw [← sub_eq_zero, e] at h
      rw [h] at hd
      simp at hd
    · rw [e, hd]
  · rintro d ⟨f, g, hf, hg, hne, rfl⟩
    have := Mathlib2.ms_davenport f g (by omega) (by omega) hne
    omega
end

end Mathlib2
