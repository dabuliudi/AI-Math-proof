/- Mathlib2 分片 27（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0026
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry poly_radical_coprime_derivative_quot kind=proved origin=conjecture
section
/- Snyder's ingredient, sharp form in char 0: the cofactor f' / (f / rad f) is coprime to rad f (so gcd(f, f') is associated to f / rad f) — Uses Mathlib2.ms_divrad_dvd_derivative_v2 to know the division is exact; then for each prime p ∣ f with multiplicity e, f = p^e·g gives f'/(f/rad f) ≡ e·p'·rad(g)·(g/..) mod p, which is nonzero mod p since e ≠ 0 in char 0 and p ∤ p'. -/
open UniqueFactorizationMonoid Polynomial

theorem poly_radical_coprime_derivative_quot {k : Type*} [Field k] [DecidableEq k] [CharZero k] (f : Polynomial k) (hf : f ≠ 0) : IsCoprime (UniqueFactorizationMonoid.radical f) (Polynomial.derivative f / (f / UniqueFactorizationMonoid.radical f)) := by
  have hsq : Squarefree (radical f) := squarefree_radical
  have hr0 : radical f ≠ 0 := radical_ne_zero
  have hdiv := Mathlib2.ms_divrad_dvd_derivative_v2 f hf
  obtain ⟨q, hq⟩ := radical_dvd_self (a := f)
  generalize radical f = r at *
  have hq0 : q ≠ 0 := by rintro rfl; exact hf (by simp [hq])
  have hfr : f / r = q := by rw [hq, mul_div_cancel_left₀ _ hr0]
  rw [hfr] at hdiv ⊢
  obtain ⟨h, hh⟩ := hdiv
  have hfq : derivative f / q = h := by rw [hh, mul_div_cancel_left₀ _ hq0]
  rw [hfq]
  apply isCoprime_of_irreducible_dvd
  · exact fun hc => hr0 hc.1
  rintro p hp ⟨s, rfl⟩ ⟨h', rfl⟩
  have hps : ¬ p ∣ s := by
    rintro ⟨t, rfl⟩
    exact hp.not_isUnit (hsq p ⟨t, by ring⟩)
  have hprime : Prime p := hp.prime
  obtain ⟨g, hg, hpg⟩ := (FiniteMultiplicity.of_not_isUnit hp.not_isUnit hf).exists_eq_pow_mul_and_not_dvd
  generalize multiplicity p f = e at hg
  have hp0 : p ≠ 0 := hp.ne_zero
  rcases e with _ | e
  · apply hpg
    rw [pow_zero, one_mul] at hg
    rw [← hg, hq]
    exact ⟨s * q, by ring⟩
  have h1 : p ^ e * g = s * q := by
    apply mul_left_cancel₀ hp0
    rw [← mul_assoc, ← pow_succ', ← hg, hq]; ring
  have hcop : IsCoprime (p ^ e) s := ((hp.coprime_iff_not_dvd).mpr hps).pow_left
  obtain ⟨q', rfl⟩ : p ^ e ∣ q := hcop.dvd_of_dvd_mul_left ⟨g, h1.symm⟩
  have hd : derivative f = C ((e : k) + 1) * p ^ e * derivative p * g + p ^ (e + 1) * derivative g := by
    rw [hg, derivative_mul, derivative_pow_succ]
  have h2 : C ((e : k) + 1) * derivative p * g = p * (q' * h' - derivative g) := by
    apply mul_left_cancel₀ (pow_ne_zero e hp0)
    linear_combination hh - hd
  have hdvd : p ∣ C ((e : k) + 1) * derivative p * g := ⟨_, h2⟩
  rcases hprime.dvd_or_dvd hdvd with h3 | h3
  · rcases hprime.dvd_or_dvd h3 with h4 | h4
    · have hne : ((e : k) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero e
      exact hp.not_isUnit (isUnit_of_dvd_unit h4 (Polynomial.isUnit_C.mpr (IsUnit.mk0 _ hne)))
    · have hpos := hp.natDegree_pos
      have hlt := Polynomial.natDegree_derivative_lt (p := p) (by omega)
      have hd0 : derivative p ≠ 0 := fun h0 => by
        have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero h0
        omega
      have := Polynomial.natDegree_le_of_dvd h4 hd0
      omega
  · exact hpg h3
end

-- forge:entry bld5_prime_dvd_lucas_four_mul_mod_eight kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_lucas_sq_sub_five_fib_sq and Mathlib2.lib_p3_lucas_cast: first the duplication formula L_{2m} = L_m² − 2(−1)^m in ℤ (from lib_p3_lucas_cast, Nat.fib_two_mul, Nat.fib_two_mul_add_one, giving 2L_{2m} = L_m² + 5F_m², then the bld2 identity L_m² − 5F_m² = 4(−1)^m). With m = 2n: L_{4n} = L_{2n}² − 2, so p ∣ L_{4n} makes 2 a square in ZMod p, and ZMod.exists_sq_eq_two_iff (p ≠ 2) gives p ≡ ±1 mod 8. -/
theorem bld5_prime_dvd_lucas_four_mul_mod_eight_aux1 (R : Type*) [CommRing R] (m : ℕ) :
    ((p3_lucas (2 * m) : ℕ) : R) = ((p3_lucas m : ℕ) : R) ^ 2 - 2 * (-1) ^ m := by
  have e1 : Nat.fib (2*m) = Nat.fib m * p3_lucas m := by rw [Nat.fib_two_mul]; rfl
  have e2 : Nat.fib (2*m+1) = Nat.fib (m+1)^2 + Nat.fib m^2 := Nat.fib_two_mul_add_one m
  have c := lib_fib_cassini_cast R m
  rw [Nat.fib_add_two] at c
  rw [lib_p3_lucas_cast R (2*m), e1, e2]
  push_cast
  rw [lib_p3_lucas_cast R m]
  push_cast at c
  linear_combination 2 * c

theorem bld5_prime_dvd_lucas_four_mul_mod_eight (p n : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ p3_lucas (4 * n)) : p % 8 = 1 ∨ p % 8 = 7 := by
  haveI := Fact.mk hp
  have h0 : ((p3_lucas (4 * n) : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have e : 4 * n = 2 * (2 * n) := by ring
  rw [e, bld5_prime_dvd_lucas_four_mul_mod_eight_aux1, pow_mul, neg_one_sq, one_pow] at h0
  refine (ZMod.exists_sq_eq_two_iff hp2).mp ⟨((p3_lucas (2 * n) : ℕ) : ZMod p), ?_⟩
  linear_combination -h0
end

-- forge:entry bld5_commuting_idempotents_rank_sub_iff kind=proved origin=conjecture
section
/- Uses Mathlib2.bld3_commuting_idempotents_rank_sub, Mathlib2.bld_idempotent_sum_rank and Mathlib2.lib_matrix_rank_eq_zero_iff: bld3 gives rank(A−B) + 2·rank(AB) = rank A + rank B, so the left side is equivalent to rank(AB) = rank B. AB and B − AB are idempotents (commutativity) with idempotent sum B, so bld_idempotent_sum_rank gives rank B = rank(AB) + rank(B − AB). Hence rank(AB) = rank B ↔ rank(B − AB) = 0 ↔ B − AB = 0 by lib_matrix_rank_eq_zero_iff. -/
theorem bld5_commuting_idempotents_rank_sub_iff (K : Type*) [Field K] [CharZero K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι K) (hA : A * A = A) (hB : B * B = B) (hAB : A * B = B * A) : (A - B).rank + B.rank = A.rank ↔ A * B = B := by
  have h3 := bld3_commuting_idempotents_rank_sub K ι A B hA hB hAB
  have e1 : B * (A * B) = A * B := by rw [← Matrix.mul_assoc, ← hAB, Matrix.mul_assoc, hB]
  have e2 : A * B * (A * B) = A * B := by rw [Matrix.mul_assoc, e1, ← Matrix.mul_assoc, hA]
  have e3 : (B - A * B) * (B - A * B) = B - A * B := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hB, e1, e2, Matrix.mul_assoc, hB]; simp
  have hs := bld_idempotent_sum_rank K ι (A * B) (B - A * B) e2 e3 (by rw [add_sub_cancel, hB])
  rw [add_sub_cancel] at hs
  constructor
  · intro h
    have h0 : (B - A * B).rank = 0 := by omega
    have := (lib_matrix_rank_eq_zero_iff K ι ι (B - A * B)).mp h0
    exact (sub_eq_zero.mp this).symm
  · intro h
    rw [h] at h3
    omega
end

-- forge:entry bld5_isometries_compact_simultaneous_recurrence kind=proved origin=conjecture
section
/- Uses Mathlib2.bld4_isometry_compact_uniform_recurrence: apply it to Prod.map f g on the compact metric space X × Y (sup metric; Prod.map of isometries is an isometry, and (Prod.map f g)^[n] = Prod.map f^[n] g^[n]) to get n > 0 with dist((f^[n] x, g^[n] y), (x, y)) < ε for all (x, y); Prod.dist_eq (max) splits it into the two components. If X or Y is empty apply the theorem to the other factor alone. -/
theorem bld5_isometries_compact_simultaneous_recurrence {X : Type*} [MetricSpace X] [CompactSpace X] {Y : Type*} [MetricSpace Y] [CompactSpace Y] (f : X → X) (g : Y → Y) (hf : Isometry f) (hg : Isometry g) (ε : ℝ) (hε : 0 < ε) : ∃ n : ℕ, 0 < n ∧ (∀ x : X, dist (f^[n] x) x < ε) ∧ ∀ y : Y, dist (g^[n] y) y < ε := by
  by_cases hX : Nonempty X
  · by_cases hY : Nonempty Y
    · obtain ⟨x0⟩ := hX
      obtain ⟨y0⟩ := hY
      obtain ⟨n, hn, h⟩ := bld4_isometry_compact_uniform_recurrence (Prod.map f g) (hf.prodMap hg) ε hε
      refine ⟨n, hn, fun x => ?_, fun y => ?_⟩
      · have := h (x, y0)
        rw [Prod.map_iterate, Prod.map_apply, Prod.dist_eq] at this
        exact lt_of_le_of_lt (le_max_left _ _) this
      · have := h (x0, y)
        rw [Prod.map_iterate, Prod.map_apply, Prod.dist_eq] at this
        exact lt_of_le_of_lt (le_max_right _ _) this
    · obtain ⟨n, hn, h⟩ := bld4_isometry_compact_uniform_recurrence f hf ε hε
      exact ⟨n, hn, h, fun y => absurd ⟨y⟩ hY⟩
  · obtain ⟨n, hn, h⟩ := bld4_isometry_compact_uniform_recurrence g hg ε hε
    exact ⟨n, hn, fun x => absurd ⟨x⟩ hX, h⟩
end

-- forge:entry bld5_isometry_compact_id_uniform_limit kind=proved origin=conjecture
section
/- Uses Mathlib2.bld4_isometry_compact_uniform_recurrence: first upgrade to arbitrarily large return times: for ε > 0 and N ≥ 1, the bld4 theorem with ε/N gives n > 0 with dist(f^[n] x, x) < ε/N for all x; since f^[n] is an isometry, the triangle inequality gives dist(f^[nN] x, x) ≤ N·sup dist(f^[n] y, y) < ε with nN ≥ N. Then build φ recursively (φ(k+1) > φ(k) with sup-distance < 1/(k+2)) and unfold Metric.tendstoUniformly_iff. -/
theorem bld5_isometry_compact_id_uniform_limit_aux1 {X : Type*} [MetricSpace X] [CompactSpace X] (f : X → X) (hf : Isometry f) (ε : ℝ) (hε : 0 < ε) (N : ℕ) : ∃ m : ℕ, N < m ∧ ∀ x : X, dist (f^[m] x) x < ε := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  obtain ⟨n, hn, h⟩ := bld4_isometry_compact_uniform_recurrence f hf (ε / 2 / (N + 1)) (by positivity)
  have key : ∀ j : ℕ, ∀ x : X, dist (f^[n * j] x) x ≤ j * (ε / 2 / (N + 1)) := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [Nat.mul_succ, Function.iterate_add_apply]
      have h1 := dist_triangle (f^[n * j] (f^[n] x)) (f^[n] x) x
      have h2 := ih (f^[n] x)
      have h3 := h x
      push_cast
      linarith
  refine ⟨n * (N + 1), ?_, fun x => ?_⟩
  · nlinarith
  · have := key (N + 1) x
    have e : ((N + 1 : ℕ) : ℝ) * (ε / 2 / (N + 1)) = ε / 2 := by
      push_cast; field_simp
    rw [e] at this
    linarith

theorem bld5_isometry_compact_id_uniform_limit {X : Type*} [MetricSpace X] [CompactSpace X] (f : X → X) (hf : Isometry f) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ TendstoUniformly (fun k x => f^[φ k] x) id Filter.atTop := by
  have H : ∀ k N : ℕ, ∃ m : ℕ, N < m ∧ ∀ x : X, dist (f^[m] x) x < 1 / ((k : ℝ) + 1) := fun k N =>
    bld5_isometry_compact_id_uniform_limit_aux1 f hf _ (by positivity) N
  choose F hF1 hF2 using H
  refine ⟨fun k => Nat.rec (F 0 0) (fun k r => F (k + 1) r) k, strictMono_nat_of_lt_succ fun k => hF1 _ _, ?_⟩
  have hφ : ∀ k : ℕ, ∀ x : X, dist (f^[(Nat.rec (F 0 0) (fun k r => F (k + 1) r) k : ℕ)] x) x < 1 / ((k : ℝ) + 1) := by
    intro k
    cases k with
    | zero => exact hF2 0 0
    | succ k => exact hF2 (k + 1) _
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt hε
  filter_upwards [Filter.eventually_ge_atTop M] with k hk x
  have h1 := hφ k x
  have h2 : 1 / ((k : ℝ) + 1) ≤ 1 / ((M : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    have : (M : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rw [id, dist_comm]
  linarith
end

-- forge:entry poly_chebyshev_T_card_distinct_real_roots kind=proved origin=conjecture
section
/- T_n has exactly n distinct real roots — the n points cos((2k+1)π/(2n)), k < n, are distinct (cos is injective on [0,π]) roots since T_n(cos θ) = cos(nθ); and T_n has degree n so at most n roots. -/
open Polynomial

theorem poly_chebyshev_T_card_distinct_real_roots_aux1 (R : Type*) [CommRing R] (n : ℕ) : (Polynomial.Chebyshev.T R (n : ℤ)).natDegree ≤ n ∧ (Polynomial.Chebyshev.T R ((n + 1 : ℕ) : ℤ)).natDegree ≤ n + 1 := by
  induction n with
  | zero =>
    constructor
    · simp
    · simp only [zero_add, Nat.cast_one, Polynomial.Chebyshev.T_one]
      exact Polynomial.natDegree_X_le
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have e : ((n + 1 + 1 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
    have e' : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [e, Polynomial.Chebyshev.T_add_two]
    rw [e'] at ih
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ (by omega))
    refine (Polynomial.natDegree_mul_le).trans ?_
    have h2 : (2 * X : R[X]).natDegree ≤ 1 := by
      refine (Polynomial.natDegree_mul_le).trans ?_
      have h3 : (2 : R[X]).natDegree = 0 := Polynomial.natDegree_ofNat 2
      have := Polynomial.natDegree_X_le (R := R)
      omega
    omega

theorem poly_chebyshev_T_card_distinct_real_roots (n : ℕ) : (Polynomial.Chebyshev.T ℝ (n : ℤ)).roots.toFinset.card = n := by
  apply le_antisymm
  · refine (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans ?_)
    exact (poly_chebyshev_T_card_distinct_real_roots_aux1 ℝ n).1
  · have hne : Polynomial.Chebyshev.T ℝ (n : ℤ) ≠ 0 := by
      intro h
      have := Polynomial.Chebyshev.T_real_cos 0 (n : ℤ)
      rw [h] at this
      simp at this
    have hcard := Finset.card_le_card_of_injOn (s := Finset.range n) (t := (Polynomial.Chebyshev.T ℝ (n : ℤ)).roots.toFinset)
      (fun i : ℕ => Real.cos ((2 * (i : ℝ) + 1) * Real.pi / (2 * n))) ?_ ?_
    · simpa using hcard
    · intro i hi
      have hi' : i < n := Finset.mem_range.mp (by simpa using hi)
      have hn0 : (n : ℝ) ≠ 0 := by
        have : n ≠ 0 := by omega
        exact_mod_cast this
      simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def]
      rw [Polynomial.Chebyshev.T_real_cos, Real.cos_eq_zero_iff]
      refine ⟨i, ?_⟩
      push_cast
      field_simp
    · intro i hi j hj hij
      have hi' : i < n := Finset.mem_range.mp (by simpa using hi)
      have hj' : j < n := Finset.mem_range.mp (by simpa using hj)
      have hnpos : (0 : ℝ) < n := by
        have : 0 < n := by omega
        exact_mod_cast this
      have hmem : ∀ l : ℕ, l < n → (2 * (l : ℝ) + 1) * Real.pi / (2 * n) ∈ Set.Icc 0 Real.pi := by
        intro l hl
        have hl' : (l : ℝ) + 1 ≤ n := by exact_mod_cast hl
        constructor
        · positivity
        · rw [div_le_iff₀ (by positivity)]
          nlinarith [Real.pi_pos]
      have h := Real.injOn_cos (hmem i hi') (hmem j hj') hij
      have hpi := Real.pi_pos
      field_simp at h
      have h' : (i : ℝ) = j := by linarith
      exact_mod_cast h'
end

-- forge:entry bld5_quadratic_annihilated_iff_rank_add_rank kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_idempotent_iff_rank_add_rank and Mathlib2.lib_matrix_rank_smul: put P = (b − a)⁻¹ • (A − a•1), so 1 − P = −(b − a)⁻¹ • (A − b•1). A direct computation gives P*P − P = (b − a)⁻² • (A − a•1)(A − b•1), so the left side is equivalent to P*P = P, which by bld2_idempotent_iff_rank_add_rank is rank P + rank(1 − P) = card ι; lib_matrix_rank_smul (non-zero scalars (b−a)⁻¹ and −(b−a)⁻¹) rewrites the ranks as those of A − a•1 and A − b•1. Generalises the idempotent (a,b) = (0,1) and involution (1,−1) criteria to any split quadratic, with no characteristic assumption. -/
theorem bld5_quadratic_annihilated_iff_rank_add_rank (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (a b : K) (hab : a ≠ b) : (A - a • (1 : Matrix ι ι K)) * (A - b • (1 : Matrix ι ι K)) = 0 ↔ (A - a • (1 : Matrix ι ι K)).rank + (A - b • (1 : Matrix ι ι K)).rank = Fintype.card ι := by
  have hc : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  obtain ⟨c, hcdef⟩ : ∃ c : K, c = (b - a)⁻¹ := ⟨_, rfl⟩
  have hc' : c ≠ 0 := by rw [hcdef]; exact inv_ne_zero hc
  have hone : c * b - c * a = 1 := by rw [← mul_sub, hcdef]; exact inv_mul_cancel₀ hc
  have h1 : (1 : Matrix ι ι K) - c • (A - a • 1) = (-c) • (A - b • 1) := by
    have key : ∀ I : Matrix ι ι K, (c * b - c * a) • I - c • (A - a • I) = (-c) • (A - b • I) := by
      intro I; module
    have := key 1
    rwa [hone, one_smul] at this
  have h2 := bld2_idempotent_iff_rank_add_rank K ι (c • (A - a • (1 : Matrix ι ι K)))
  rw [h1, lib_matrix_rank_smul K ι ι c hc', lib_matrix_rank_smul K ι ι (-c) (neg_ne_zero.mpr hc')] at h2
  rw [← h2]
  have h3 : c • (A - a • (1 : Matrix ι ι K)) * (c • (A - a • (1 : Matrix ι ι K))) = c • (A - a • (1 : Matrix ι ι K)) ↔ c • (A - a • (1 : Matrix ι ι K)) * (1 - c • (A - a • (1 : Matrix ι ι K))) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero, eq_comm]
  rw [h3, h1, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_eq_zero]
  constructor
  · intro h; exact Or.inr h
  · rintro (h | h)
    · exact absurd h (by simp [hc'])
    · exact h
end

-- forge:entry bld5_fib_entry_point_pisano_ratio kind=proved origin=conjecture
section
/- Uses Mathlib2.bld3_pisano_pos_and_period, Mathlib2.bld3_pisano_dvd_pisano_of_dvd and Mathlib2.bld2_pisano_fib_dvd_four_mul: bld3_pisano_pos_and_period at i = 0 gives m ∣ F_π with π = pisano m > 0, so a := Nat.find of {k > 0 | m ∣ F_k} exists (rank of apparition). m ∣ F_k ↔ a ∣ k: (⇐) Nat.fib_dvd; (⇒) m ∣ gcd(F_k, F_a) = F_{gcd(k,a)} by Nat.fib_gcd and minimality forces gcd(k,a) = a. Hence a ∣ π. Conversely m ∣ F_a gives π ∣ pisano(F_a) (bld3_pisano_dvd_pisano_of_dvd) ∣ 4a (bld2_pisano_fib_dvd_four_mul). So π = a·t with t ∣ 4, t ∈ {1,2,4}. -/
theorem bld5_fib_entry_point_pisano_ratio (m : ℕ) (hm : 0 < m) : ∃ a : ℕ, 0 < a ∧ (∀ k : ℕ, m ∣ Nat.fib k ↔ a ∣ k) ∧ (p3_pisano m = a ∨ p3_pisano m = 2 * a ∨ p3_pisano m = 4 * a) := by
  classical
  obtain ⟨hpos, hper⟩ := bld3_pisano_pos_and_period m hm
  have hpi : m ∣ Nat.fib (p3_pisano m) := by
    have := hper 0; rw [zero_add, Nat.fib_zero] at this; exact (Nat.modEq_zero_iff_dvd).mp this
  have hex : ∃ k, 0 < k ∧ m ∣ Nat.fib k := ⟨_, hpos, hpi⟩
  obtain ⟨a, ⟨ha0, had⟩, hmin⟩ : ∃ a, (0 < a ∧ m ∣ Nat.fib a) ∧ ∀ j < a, ¬ (0 < j ∧ m ∣ Nat.fib j) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hiff : ∀ k, m ∣ Nat.fib k ↔ a ∣ k := by
    intro k
    constructor
    · intro hk
      have hg : m ∣ Nat.fib (Nat.gcd k a) := by rw [Nat.fib_gcd]; exact Nat.dvd_gcd hk had
      have hgpos : 0 < Nat.gcd k a := Nat.gcd_pos_of_pos_right _ ha0
      have hle : Nat.gcd k a ≤ a := Nat.gcd_le_right _ ha0
      have : Nat.gcd k a = a := by
        by_contra hne
        exact hmin _ (lt_of_le_of_ne hle hne) ⟨hgpos, hg⟩
      rw [← this]; exact Nat.gcd_dvd_left _ _
    · intro hk; exact had.trans (Nat.fib_dvd _ _ hk)
  refine ⟨a, ha0, hiff, ?_⟩
  obtain ⟨t, ht⟩ := (hiff _).mp hpi
  have h4 : p3_pisano m ∣ 4 * a := (bld3_pisano_dvd_pisano_of_dvd m _ had).trans (bld2_pisano_fib_dvd_four_mul a ha0)
  rw [ht] at h4 ⊢
  have ht4 : t ∣ 4 := by
    rw [mul_comm 4 a] at h4; exact (Nat.mul_dvd_mul_iff_left ha0).mp h4
  have : t ≤ 4 := Nat.le_of_dvd (by norm_num) ht4
  interval_cases t <;> omega
end

-- forge:entry bld5_mantel_equality_connected kind=proved origin=conjecture
section
/- Uses Mathlib2.bld4_mantel_equality_complete_bipartite: it gives s with 2|s| = n and Adj x y ↔ (x ∈ s ↔ y ∉ s). Since n ≥ 2, both s and its complement are non-empty; pick u ∈ s, w ∉ s. Any x ∈ s is adjacent to w and any x ∉ s is adjacent to u, and u ~ w, so every two vertices are joined by a walk of length ≤ 3 through u, w: G is preconnected and V is non-empty. -/
theorem bld5_mantel_equality_connected (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.CliqueFree 3) (he : 4 * G.edgeFinset.card = Fintype.card V ^ 2) (hn : 2 ≤ Fintype.card V) : G.Connected := by
  obtain ⟨s, hs, hadj⟩ := bld4_mantel_equality_complete_bipartite V G hG he
  have hs1 : 0 < s.card := by omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hs1
  have hex : ∃ w, w ∉ s := by
    by_contra hc
    push_neg at hc
    have : s = Finset.univ := Finset.eq_univ_iff_forall.mpr hc
    rw [this, Finset.card_univ] at hs
    omega
  obtain ⟨w, hw⟩ := hex
  have huw : G.Adj u w := (hadj u w).mpr (by tauto)
  have hR : ∀ x, G.Reachable x u := by
    intro x
    by_cases hx : x ∈ s
    · exact ((hadj x w).mpr (by tauto)).reachable.trans huw.reachable.symm
    · exact ((hadj x u).mpr (by tauto)).reachable
  exact (SimpleGraph.connected_iff G).mpr ⟨fun x y => (hR x).trans (hR y).symm, ⟨u⟩⟩
end

-- forge:entry bld5_pisano_lucas_odd_eq kind=proved origin=conjecture
section
/- Uses Mathlib2.lib_fib_period_iff, Mathlib2.bld3_pisano_dvd_of_period, Mathlib2.lib_pisano_dvd_iff_period, Mathlib2.lib_fib_cassini_cast and Mathlib2.lib_p3_lucas_cast: F_{2n} = F_n·L_n ≡ 0 (Nat.fib_two_mul) and F_{2n+1} = F_{n+1}·L_n − (−1)^n ≡ 1 mod L_n for odd n (lib_p3_lucas_cast, Nat.fib_two_mul_add_one, lib_fib_cassini_cast); so lib_fib_period_iff + bld3_pisano_dvd_of_period give π ∣ 2n (improving bld4_pisano_lucas_dvd_four_mul). Conversely lib_pisano_dvd_iff_period (i = 0) gives L_n ∣ F_π, hence by Nat.fib_gcd L_n ∣ F_{gcd(π,2n)}; F_{n+1} < L_n forces gcd(π, 2n) ≥ n + 2, and the only divisor of 2n above n is 2n, so 2n ∣ π. -/
theorem bld5_pisano_lucas_odd_eq_aux1 (n : ℕ) :
    (Nat.fib (2 * n + 1) : ℤ) = (Nat.fib (n + 1) : ℤ) * (p3_lucas n : ℤ) - (-1) ^ n := by
  have e2 : Nat.fib (2*n+1) = Nat.fib (n+1)^2 + Nat.fib n^2 := Nat.fib_two_mul_add_one n
  have c := lib_fib_cassini_cast ℤ n
  rw [Nat.fib_add_two] at c
  rw [lib_p3_lucas_cast ℤ n, e2]
  push_cast
  push_cast at c
  linear_combination c

theorem bld5_pisano_lucas_odd_eq_aux2 (n : ℕ) (hn : 2 ≤ n) : Nat.fib (n + 1) < p3_lucas n := by
  unfold p3_lucas
  have := Nat.fib_lt_fib_succ hn
  omega

theorem bld5_pisano_lucas_odd_eq_aux3 (n : ℕ) (hn : 2 ≤ n) : 2 * n ∣ p3_pisano (p3_lucas n) := by
  have hL := bld5_pisano_lucas_odd_eq_aux2 n hn
  have hLpos : 0 < p3_lucas n := by omega
  obtain ⟨hpos, hper⟩ := bld3_pisano_pos_and_period _ hLpos
  have h1 : p3_lucas n ∣ Nat.fib (p3_pisano (p3_lucas n)) := by
    have := hper 0; rw [zero_add, Nat.fib_zero] at this; exact (Nat.modEq_zero_iff_dvd).mp this
  have h2 : p3_lucas n ∣ Nat.fib (2*n) := by
    rw [Nat.fib_two_mul]; exact Dvd.intro_left (Nat.fib n) rfl
  generalize p3_pisano (p3_lucas n) = π at *
  have hg : p3_lucas n ∣ Nat.fib (Nat.gcd π (2*n)) := by rw [Nat.fib_gcd]; exact Nat.dvd_gcd h1 h2
  have hgpos : 0 < Nat.gcd π (2*n) := Nat.gcd_pos_of_pos_left _ hpos
  have hgd : Nat.gcd π (2*n) ∣ 2*n := Nat.gcd_dvd_right _ _
  have hgn : n + 2 ≤ Nat.gcd π (2*n) := by
    by_contra hc
    have a := Nat.fib_mono (show Nat.gcd π (2*n) ≤ n+1 by omega)
    have b := Nat.le_of_dvd (Nat.fib_pos.mpr hgpos) hg
    omega
  have hgl : Nat.gcd π (2*n) ∣ π := Nat.gcd_dvd_left _ _
  generalize Nat.gcd π (2*n) = g at *
  have : g = 2*n := by
    obtain ⟨c, hc⟩ := hgd
    rcases c with _ | _ | c
    · omega
    · omega
    · have : g * 2 ≤ g * (c+1+1) := Nat.mul_le_mul_left _ (by omega)
      omega
  rw [← this]; exact hgl

theorem bld5_pisano_lucas_odd_eq (n : ℕ) (hn : 3 ≤ n) (ho : Odd n) : p3_pisano (p3_lucas n) = 2 * n := by
  apply Nat.dvd_antisymm _ (bld5_pisano_lucas_odd_eq_aux3 n (by omega))
  apply bld3_pisano_dvd_of_period
  rw [lib_fib_period_iff]
  constructor
  · apply (Nat.modEq_zero_iff_dvd).mpr; rw [Nat.fib_two_mul]; exact Dvd.intro_left (Nat.fib n) rfl
  · rw [Nat.modEq_iff_dvd]
    have := bld5_pisano_lucas_odd_eq_aux1 n
    rw [ho.neg_one_pow] at this
    exact ⟨-(Nat.fib (n+1) : ℤ), by rw [this]; push_cast; ring⟩
end

-- forge:entry poly_cyclotomic_two_mul_odd_comp_neg kind=proved origin=conjecture
section
/- For odd n > 1, Φ_{2n}(X) = Φ_n(-X) — Polynomial.cyclotomic_mul_prime_of_not_dvd-type identity Φ_{2n}(X)·Φ_n(X) = Φ_n(X^2) (expand by the prime 2 ∤ n), together with Φ_n(X^2) = Φ_n(X)·Φ_n(-X) up to sign, proved via strong induction on n using X^n - 1 = ∏_{d ∣ n} Φ_d and (-X)^n - 1 = -(X^n + 1) for odd n; φ(n) even for n > 1 fixes the sign. -/
open Polynomial in
theorem poly_cyclotomic_two_mul_odd_comp_neg (n : ℕ) (hn : Odd n) (h1 : 1 < n) : Polynomial.cyclotomic (2 * n) ℤ = (Polynomial.cyclotomic n ℤ).comp (-Polynomial.X) := by
  have hn0 : n ≠ 0 := by omega
  have hn3 : 2 < n := by
    rcases hn with ⟨j, hj⟩; omega
  obtain ⟨η, hη⟩ : ∃ η : ℂ, IsPrimitiveRoot η n := ⟨_, Complex.isPrimitiveRoot_exp n hn0⟩
  have hcop : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hn
  have ho : orderOf (-η) = 2 * n := by
    have h1 : orderOf (-1 : ℂ) = 2 := by rw [orderOf_neg_one]; simp [ringChar.eq_zero]
    have h2 : orderOf η = n := hη.eq_orderOf.symm
    have := Commute.orderOf_mul_eq_mul_orderOf_of_coprime (Commute.all (-1 : ℂ) η) (by rw [h1, h2]; exact hcop)
    rw [h1, h2, neg_one_mul] at this
    exact this
  have hprim : IsPrimitiveRoot (-η) (2 * n) := IsPrimitiveRoot.iff_orderOf.mpr ho
  have hmin := cyclotomic_eq_minpoly hprim (by omega)
  have hroot : aeval (-η) ((cyclotomic n ℤ).comp (-X)) = 0 := by
    rw [aeval_comp]
    simp only [map_neg, aeval_X, neg_neg]
    rw [cyclotomic_eq_minpoly hη (by omega)]; exact minpoly.aeval _ _
  have hdvd : cyclotomic (2 * n) ℤ ∣ (cyclotomic n ℤ).comp (-X) := by
    have := minpoly.isIntegrallyClosed_dvd (hprim.isIntegral (by omega)) hroot
    rwa [← hmin] at this
  have hdeg : ((cyclotomic n ℤ).comp (-X)).natDegree = n.totient := by
    rw [natDegree_comp, natDegree_neg, natDegree_X, mul_one, natDegree_cyclotomic]
  have hmc : ((cyclotomic n ℤ).comp (-X)).Monic := by
    rw [Monic, leadingCoeff_comp (by rw [natDegree_neg, natDegree_X]; exact one_ne_zero), leadingCoeff_neg, leadingCoeff_X, (cyclotomic.monic n ℤ).leadingCoeff, natDegree_cyclotomic, (Nat.totient_even hn3).neg_one_pow, one_mul]
  refine (eq_of_monic_of_dvd_of_natDegree_le (cyclotomic.monic (2 * n) ℤ) hmc hdvd ?_).symm
  rw [hdeg, natDegree_cyclotomic, Nat.totient_mul hcop, Nat.totient_two, one_mul]
end

-- forge:entry poly_cyclotomic_reverse_eq_self kind=proved origin=conjecture
section
/- Cyclotomic polynomials Φ_n (n ≥ 2) are palindromic — strong induction: X^n - 1 = ∏_{d ∣ n} Φ_d, reverse is multiplicative, reverse(X^n - 1) = -(X^n - 1), reverse(Φ_1) = -Φ_1, and cancel the product over proper divisors d ≥ 2 by the induction hypothesis. -/
open Polynomial in
theorem poly_cyclotomic_reverse_eq_self (n : ℕ) (hn : 2 ≤ n) : (Polynomial.cyclotomic n ℤ).reverse = Polynomial.cyclotomic n ℤ := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ n := ⟨_, Complex.isPrimitiveRoot_exp n hn0⟩
  have hζi : IsPrimitiveRoot ζ⁻¹ n := hζ.inv
  have hmin : cyclotomic n ℤ = minpoly ℤ ζ⁻¹ := cyclotomic_eq_minpoly hζi (by omega)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hn0
  have hroot : eval₂ (algebraMap ℤ ℂ) ζ (cyclotomic n ℤ) = 0 := by
    rw [cyclotomic_eq_minpoly hζ (by omega), ← aeval_def]; exact minpoly.aeval _ _
  have hrev : aeval ζ⁻¹ (cyclotomic n ℤ).reverse = 0 := by
    letI := invertibleOfNonzero hζ0
    have := eval₂_reverse_mul_pow (algebraMap ℤ ℂ) ζ (cyclotomic n ℤ)
    rw [invOf_eq_inv, hroot] at this
    rw [aeval_def]
    exact (mul_eq_zero.mp this).resolve_right (pow_ne_zero _ hζ0)
  have hdvd : cyclotomic n ℤ ∣ (cyclotomic n ℤ).reverse := by
    have := minpoly.isIntegrallyClosed_dvd (hζi.isIntegral (by omega)) hrev
    rwa [← hmin] at this
  have hc0 : (cyclotomic n ℤ).coeff 0 = 1 := cyclotomic_coeff_zero ℤ (by omega)
  have hmr : (cyclotomic n ℤ).reverse.Monic := by
    rw [Monic, reverse_leadingCoeff, trailingCoeff, natTrailingDegree_eq_zero.mpr (Or.inr (by rw [hc0]; exact one_ne_zero)), hc0]
  exact eq_of_monic_of_dvd_of_natDegree_le (cyclotomic.monic n ℤ) hmr hdvd (reverse_natDegree_le _)
end

-- forge:entry bld5_nilpotent_pow_rank_succ_eq_zero kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_rank_pow_convex, Mathlib2.gen_lin_nilpotent_pow_card_reduced, Mathlib2.bld4_rank_pow_eq_of_card_le and Mathlib2.lib_matrix_rank_eq_zero_iff (nilpotency index ≤ rank + 1): let r_k = rank(A^k). If r_{k+1} = r_k for some k then by bld2_rank_pow_convex (non-increasing non-negative drops) r_j = r_k for all j ≥ k, and by gen_lin_nilpotent_pow_card_reduced / bld4_rank_pow_eq_of_card_le r_j = 0 for large j, so r_k = 0. Hence r_k strictly decreases until it reaches 0, so r_{k+1} ≤ r_1 − k while positive; thus r_{r_1 + 1} = 0 and lib_matrix_rank_eq_zero_iff gives A^(rank A + 1) = 0. -/
theorem bld5_nilpotent_pow_rank_succ_eq_zero_aux1 (r : ℕ → ℕ) (hmono : ∀ k, r (k + 1) ≤ r k) (hconv : ∀ k, 2 * r (k + 1) ≤ r k + r (k + 2)) (k : ℕ) (h : r (k + 1) = r k) (j : ℕ) : r (k + j) = r k ∧ r (k + j + 1) = r k := by
  induction j with
  | zero => exact ⟨rfl, h⟩
  | succ j ih =>
    have h1 : 2 * r (k + j + 1) ≤ r (k + j) + r (k + j + 1 + 1) := hconv (k + j)
    have h2 := hmono (k + j + 1)
    show r (k + j + 1) = r k ∧ r (k + j + 1 + 1) = r k
    refine ⟨ih.2, ?_⟩
    omega

theorem bld5_nilpotent_pow_rank_succ_eq_zero_aux2 (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (hA : IsNilpotent A) (k : ℕ) (h : (A ^ k).rank ≠ 0) : (A ^ (k + 1)).rank < (A ^ k).rank := by
  have hmono : ∀ k, (A ^ (k + 1)).rank ≤ (A ^ k).rank := fun k => by
    rw [pow_succ]; exact Matrix.rank_mul_le_left _ _
  by_contra hc
  have he : (A ^ (k + 1)).rank = (A ^ k).rank := le_antisymm (hmono k) (not_lt.mp hc)
  have h1 := (bld5_nilpotent_pow_rank_succ_eq_zero_aux1 (fun k => (A ^ k).rank) hmono
    (fun k => bld2_rank_pow_convex K ι A k) k he (Fintype.card ι)).1
  have h2 : A ^ (k + Fintype.card ι) = 0 :=
    pow_eq_zero_of_le (Nat.le_add_left _ _) (gen_lin_nilpotent_pow_card_reduced K ι A hA)
  simp only [h2, Matrix.rank_zero] at h1
  exact h h1.symm

theorem bld5_nilpotent_pow_rank_succ_eq_zero (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (hA : IsNilpotent A) : A ^ (A.rank + 1) = 0 := by
  have hP : ∀ k : ℕ, (A ^ (k + 1)).rank + k ≤ A.rank ∨ (A ^ (k + 1)).rank = 0 := by
    intro k
    induction k with
    | zero => left; simp
    | succ k ih =>
      have hm : (A ^ (k + 1 + 1)).rank ≤ (A ^ (k + 1)).rank := by
        rw [pow_succ]; exact Matrix.rank_mul_le_left _ _
      by_cases h0 : (A ^ (k + 1)).rank = 0
      · right; omega
      · have := bld5_nilpotent_pow_rank_succ_eq_zero_aux2 K ι A hA (k + 1) h0
        left; omega
  apply (lib_matrix_rank_eq_zero_iff K ι ι _).mp
  rcases hP A.rank with h | h <;> omega
end

-- forge:entry bld5_nilpotent_max_index_rank kind=proved origin=conjecture
section
/- Uses Mathlib2.bld2_rank_pow_convex, Mathlib2.gen_lin_nilpotent_pow_card_reduced and Mathlib2.lib_matrix_rank_eq_zero_iff (converse of bld4_nilpotent_corank_one_rank_pow): let r_k = rank(A^k), n = card ι, d_k = r_k − r_{k+1} ≥ 0 (Matrix.rank_mul_le_left). gen_lin_nilpotent_pow_card_reduced gives r_n = 0, and lib_matrix_rank_eq_zero_iff with the hypothesis gives r_{n−1} ≥ 1, so d_{n−1} ≥ 1. bld2_rank_pow_convex says d_k is non-increasing, so d_k ≥ 1 for all k ≤ n−1. Since d_0 + … + d_{n−1} = r_0 − r_n = n, every d_k = 1; in particular rank A = r_1 = n − 1. -/
theorem bld5_nilpotent_max_index_rank (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (hA : IsNilpotent A) (h : A ^ (Fintype.card ι - 1) ≠ 0) : A.rank + 1 = Fintype.card ι := by
  have hmono : ∀ k, (A ^ (k + 1)).rank ≤ (A ^ k).rank := fun k => by
    rw [pow_succ]; exact Matrix.rank_mul_le_left _ _
  have hanti : Antitone (fun k => (A ^ k).rank) := antitone_nat_of_succ_le hmono
  have hlast : (A ^ (Fintype.card ι - 1)).rank ≠ 0 := fun h0 =>
    h ((lib_matrix_rank_eq_zero_iff K ι ι _).mp h0)
  have hn0 : (A ^ Fintype.card ι).rank = 0 := by
    rw [gen_lin_nilpotent_pow_card_reduced K ι A hA, Matrix.rank_zero]
  have hpos : 1 ≤ Fintype.card ι := by
    by_contra hc
    have : Fintype.card ι - 1 = Fintype.card ι := by omega
    rw [this] at hlast
    exact hlast hn0
  have hstep : ∀ k, k + 1 ≤ Fintype.card ι → (A ^ (k + 1)).rank < (A ^ k).rank := by
    intro k hk
    apply bld5_nilpotent_pow_rank_succ_eq_zero_aux2 K ι A hA k
    have : (A ^ (Fintype.card ι - 1)).rank ≤ (A ^ k).rank := hanti (by omega)
    omega
  have hlow : ∀ j, j + 1 ≤ Fintype.card ι → j + 1 ≤ (A ^ (Fintype.card ι - 1 - j)).rank := by
    intro j
    induction j with
    | zero => intro _; simp only [Nat.sub_zero]; omega
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := hstep (Fintype.card ι - 1 - (j + 1)) (by omega)
      have e : Fintype.card ι - 1 - (j + 1) + 1 = Fintype.card ι - 1 - j := by omega
      rw [e] at h2
      omega
  have h0 : (A ^ 0).rank = Fintype.card ι := by rw [pow_zero, Matrix.rank_one]
  have h1 := hstep 0 hpos
  rw [h0] at h1
  simp only [zero_add, pow_one] at h1
  by_cases hc : Fintype.card ι = 1
  · omega
  · have h2 := hlow (Fintype.card ι - 2) (by omega)
    have e : Fintype.card ι - 1 - (Fintype.card ι - 2) = 1 := by omega
    rw [e, pow_one] at h2
    omega
end

-- forge:entry poly_real_nonneg_eq_sum_two_squares kind=proved origin=conjecture
section
/- A real polynomial that is nonnegative on ℝ is a sum of two squares of real polynomials — strong induction on degree: real roots have even multiplicity (factor out (X-r)^2), irreducible quadratic factors are (X-u)^2 + v^2, and sums of two squares are closed under multiplication (Brahmagupta identity). -/
open Polynomial

theorem poly_real_nonneg_eq_sum_two_squares (p : Polynomial ℝ) (h : ∀ x : ℝ, 0 ≤ Polynomial.eval x p) : ∃ f g : Polynomial ℝ, p = f ^ 2 + g ^ 2 := by
  induction' hd : p.natDegree using Nat.strong_induction_on with d ih generalizing p
  by_cases hd0 : d = 0
  · subst hd0
    have hp := Polynomial.eq_C_of_natDegree_eq_zero hd
    have hc : 0 ≤ p.coeff 0 := by
      have := h 0
      rw [hp] at this
      simpa using this
    refine ⟨C (Real.sqrt (p.coeff 0)), 0, ?_⟩
    rw [← C_pow, Real.sq_sqrt hc]
    simpa using hp
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hd
    omega
  have hdegpos : 0 < (p.map (algebraMap ℝ ℂ)).degree := by
    rw [degree_map]
    exact natDegree_pos_iff_degree_pos.mp (by omega)
  obtain ⟨z, hz⟩ := Complex.exists_root hdegpos
  have hz' : aeval z p = 0 := by
    rw [aeval_def, eval₂_eq_eval_map]
    exact hz
  by_cases him : z.im = 0
  · have hr : eval z.re p = 0 := by
      have hzr : z = algebraMap ℝ ℂ z.re := by
        apply Complex.ext <;> simp [him]
      rw [hzr, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at hz'
      simpa using hz'
    generalize z.re = r at hr
    obtain ⟨q1, hq1⟩ := dvd_iff_isRoot.mpr hr
    have hder : eval r (derivative p) = 0 := by
      have hmin : IsLocalMin (fun x => eval x p) r :=
        Filter.Eventually.of_forall (fun x => by
          show eval r p ≤ eval x p
          rw [hr]; exact h x)
      have := hmin.deriv_eq_zero
      rwa [Polynomial.deriv] at this
    have hq1r : eval r q1 = 0 := by
      rw [hq1] at hder
      simpa [derivative_mul] using hder
    obtain ⟨q2, hq2⟩ := dvd_iff_isRoot.mpr hq1r
    have hp2 : p = (X - C r) ^ 2 * q2 := by rw [hq1, hq2]; ring
    have hq2nn : ∀ x, 0 ≤ eval x q2 := by
      have hcl : IsClosed {x : ℝ | 0 ≤ eval x q2} := isClosed_le continuous_const q2.continuous
      have hsub : ({r}ᶜ : Set ℝ) ⊆ {x | 0 ≤ eval x q2} := by
        intro x hx
        have hx' : x - r ≠ 0 := sub_ne_zero.mpr hx
        have := h x
        rw [hp2] at this
        simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C] at this
        exact (mul_nonneg_iff_of_pos_left (by positivity)).mp this
      intro x
      have := hcl.closure_subset_iff.mpr hsub
      rw [(dense_compl_singleton r).closure_eq] at this
      exact this (Set.mem_univ x)
    have hq20 : q2 ≠ 0 := by
      rintro rfl
      exact hp0 (by simp [hp2])
    have hdeg : q2.natDegree < d := by
      rw [← hd, hp2, natDegree_mul (pow_ne_zero 2 (X_sub_C_ne_zero r)) hq20, natDegree_pow, natDegree_X_sub_C]
      omega
    obtain ⟨f, g, hfg⟩ := ih _ hdeg q2 hq2nn rfl
    exact ⟨(X - C r) * f, (X - C r) * g, by rw [hp2, hfg]; ring⟩
  · obtain ⟨q, hq⟩ := Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero p hz' him
    have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hQdeg : (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) : ℝ[X]).natDegree = 2 := by
      compute_degree!
    have hQ : (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) : ℝ[X]) = (X - C z.re) ^ 2 + (C z.im) ^ 2 := by
      rw [hnorm]
      simp only [map_mul, map_add, map_pow, map_ofNat]
      ring
    have hQ0 : (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) : ℝ[X]) ≠ 0 := by
      intro h0
      rw [h0] at hQdeg
      simp at hQdeg
    have hq0 : q ≠ 0 := by
      rintro rfl
      exact hp0 (by simp [hq])
    have hdeg : q.natDegree < d := by
      rw [← hd, hq, natDegree_mul hQ0 hq0, hQdeg]
      omega
    rw [hQ] at hq
    have hqnn : ∀ x, 0 ≤ eval x q := by
      intro x
      have := h x
      rw [hq] at this
      simp only [eval_mul, eval_add, eval_pow, eval_sub, eval_X, eval_C] at this
      have h1 : 0 < z.im ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 him))
      have hpos : 0 < (x - z.re) ^ 2 + z.im ^ 2 := by nlinarith [sq_nonneg (x - z.re)]
      exact (mul_nonneg_iff_of_pos_left hpos).mp this
    obtain ⟨f, g, hfg⟩ := ih _ hdeg q hqnn rfl
    exact ⟨(X - C z.re) * f - C z.im * g, (X - C z.re) * g + C z.im * f, by rw [hq, hfg]; ring⟩
end

-- forge:entry bld5_card_orderOf_eq_larger_prime_of_card_prime_mul_prime kind=proved origin=conjecture
section
/- Uses Mathlib2.bld4_card_orderOf_eq_prime_of_card_prime_mul_prime: every element has order dividing pq, i.e. in {1, p, q, pq}; order pq is impossible since then G is cyclic (isCyclic_of_orderOf_eq_card) hence commutative. Partition G by order: pq = 1 + q(p−1) + #{order q}, where q(p−1) is the bld4 count of elements of order p; so #{order q} = pq − 1 − q(p−1) = q − 1. -/
theorem bld5_card_orderOf_eq_larger_prime_of_card_prime_mul_prime (p q : ℕ) [Fact p.Prime] (hq : q.Prime) (hpq : p < q) (G : Type*) [Group G] (hG : Nat.card G = p * q) (hna : ∃ a b : G, a * b ≠ b * a) : Nat.card {g : G // orderOf g = q} = q - 1 := by
  have hp : p.Prime := Fact.out
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact (Nat.mul_pos hp.pos hq.pos).ne')
  have h4 := bld4_card_orderOf_eq_prime_of_card_prime_mul_prime p q hq hpq G hG hna
  have hU : (Set.univ : Set G) = ({1} ∪ {g | orderOf g = p}) ∪ {g | orderOf g = q} := by
    ext g
    simp only [Set.mem_univ, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, true_iff]
    by_cases hg : g = 1
    · exact Or.inl (Or.inl hg)
    · rcases (bld3_card_conjClasses_of_card_prime_mul_prime_aux1 p q hp hq G hG hna g hg).2 with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  have hd1 : Disjoint ({1} : Set G) {g | orderOf g = p} := by
    rw [Set.disjoint_singleton_left]
    intro h
    have h' : orderOf (1 : G) = p := h
    rw [orderOf_one] at h'
    have := hp.one_lt
    omega
  have hd2 : Disjoint (({1} : Set G) ∪ {g | orderOf g = p}) {g | orderOf g = q} := by
    rw [Set.disjoint_union_left, Set.disjoint_singleton_left]
    refine ⟨?_, ?_⟩
    · intro h
      have h' : orderOf (1 : G) = q := h
      rw [orderOf_one] at h'
      have := hq.one_lt
      omega
    · rw [Set.disjoint_left]
      intro g h1 h2
      have h1' : orderOf g = p := h1
      have h2' : orderOf g = q := h2
      omega
  have hc := congrArg Set.ncard hU
  rw [Set.ncard_univ, Set.ncard_union_eq hd2, Set.ncard_union_eq hd1, Set.ncard_singleton, hG] at hc
  have e1 : Nat.card {g : G // orderOf g = p} = Set.ncard {g : G | orderOf g = p} :=
    Set.Nat.card_coe_set_eq _
  have e2 : Nat.card {g : G // orderOf g = q} = Set.ncard {g : G | orderOf g = q} :=
    Set.Nat.card_coe_set_eq _
  rw [e2]
  rw [e1] at h4
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  simp only [Nat.add_sub_cancel] at h4
  have : Set.ncard {g : G | orderOf g = q} + 1 = q := by nlinarith
  omega
end

-- forge:entry bld5_card_pow_prime_eq_one_of_card_prime_cube kind=proved origin=conjecture
section
/- Uses Mathlib2.bld4_pow_prime_monoidHom_center_of_card_prime_cube and Mathlib2.bld_center_card_of_card_prime_cube: the bld4 theorem gives a homomorphism φ : G →* Z(G) with φ g = g^p, so {g | g^p = 1} is the carrier of φ.ker. By the first isomorphism theorem |G| = |ker φ|·|range φ|, and |range φ| divides |Z(G)| = p (bld_center_card_of_card_prime_cube, Lagrange), so |range φ| ∈ {1, p} and |ker φ| ∈ {p³, p²}. (Sharpens bld4_card_pow_prime_eq_one_ge_of_card_prime_cube: exponent-p case vs. exponent-p² case.) -/
theorem bld5_card_pow_prime_eq_one_of_card_prime_cube (p : ℕ) (hp : p.Prime) (G : Type*) [Group G] (hG : Nat.card G = p ^ 3) (hna : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) : Nat.card {g : G // g ^ p = 1} = p ^ 2 ∨ Nat.card {g : G // g ^ p = 1} = p ^ 3 := by
  obtain ⟨φ, hφ⟩ := bld4_pow_prime_monoidHom_center_of_card_prime_cube p hp G hG hna hp2
  have hZ := bld_center_card_of_card_prime_cube p hp G hG hna
  have hker : Nat.card {g : G // g ^ p = 1} = Nat.card φ.ker := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun g => by
      rw [MonoidHom.mem_ker, ← OneMemClass.coe_eq_one, hφ])
  have hL := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hG] at hL
  have hd : Nat.card φ.range ∣ p := by
    rw [← hZ]; exact Subgroup.card_subgroup_dvd_card _
  rw [hker]
  rcases (Nat.dvd_prime hp).mp hd with h | h
  · right
    rw [h, mul_one] at hL
    exact hL
  · left
    rw [h] at hL
    have : p ^ 3 = p ^ 2 * p := by ring
    rw [this] at hL
    exact Nat.eq_of_mul_eq_mul_right hp.pos hL
end

-- forge:entry bld5_pisano_lucas_even_eq kind=proved origin=conjecture
section
/- Uses Mathlib2.bld4_pisano_lucas_dvd_four_mul, Mathlib2.lib_pisano_dvd_iff_period, Mathlib2.lib_fib_cassini_cast and Mathlib2.lib_p3_lucas_cast: π := pisano(L_n) ∣ 4n by the bld4 theorem. By lib_pisano_dvd_iff_period (i = 0) L_n ∣ F_π; also L_n ∣ F_{2n} (Nat.fib_two_mul), so by Nat.fib_gcd L_n ∣ F_g with g = gcd(π, 2n) ∣ 2n; since F_{n+1} < L_n ≤ F_g forces g ≥ n+2 > n, g = 2n, i.e. 2n ∣ π. So π ∈ {2n, 4n}. If π = 2n then (lib_pisano_dvd_iff_period, i = 1) F_{2n+1} ≡ 1 mod L_n; but F_{2n+1} = F_{n+1}·L_n − (−1)^n (from lib_p3_lucas_cast, Nat.fib_two_mul_add_one and lib_fib_cassini_cast), which is ≡ −1 for even n, giving L_n ∣ 2, false as L_n ≥ 3. -/
theorem bld5_pisano_lucas_even_eq (n : ℕ) (hn : 2 ≤ n) (he : Even n) : p3_pisano (p3_lucas n) = 4 * n := by
  have hL := bld5_pisano_lucas_odd_eq_aux2 n hn
  have h4 := bld4_pisano_lucas_dvd_four_mul n
  obtain ⟨t, ht⟩ := bld5_pisano_lucas_odd_eq_aux3 n hn
  rw [ht] at h4 ⊢
  have ht2 : t ∣ 2 := by
    have e : 4 * n = 2 * n * 2 := by ring
    rw [e] at h4; exact (Nat.mul_dvd_mul_iff_left (by omega)).mp h4
  have hle : t ≤ 2 := Nat.le_of_dvd (by norm_num) ht2
  interval_cases t
  · simp at ht2
  · exfalso
    have hper := (lib_pisano_dvd_iff_period (p3_lucas n) (2*n) (by omega)).mp (by rw [ht]; simp)
    have h1 := hper 1
    rw [add_comm 1 (2*n), Nat.fib_one, Nat.modEq_iff_dvd] at h1
    have a := bld5_pisano_lucas_odd_eq_aux1 n
    rw [he.neg_one_pow] at a
    have hd : (p3_lucas n : ℤ) ∣ 2 := by
      have : (2:ℤ) = (((1:ℕ):ℤ) - ((Nat.fib (2*n+1) : ℕ) : ℤ)) + (Nat.fib (n+1) : ℤ) * (p3_lucas n : ℤ) := by
        rw [a]; push_cast; ring
      rw [this]; exact dvd_add h1 (dvd_mul_left _ _)
    have h2 : p3_lucas n ∣ 2 := by exact_mod_cast hd
    have := Nat.le_of_dvd (by norm_num) h2
    have f3 : Nat.fib 3 ≤ Nat.fib (n+1) := Nat.fib_mono (by omega)
    have e : Nat.fib 3 = 2 := by norm_num
    omega
  · omega
end

-- forge:entry bld5_pisano_mul_dvd_mul kind=proved origin=conjecture
section
/- Uses Mathlib2.bld3_pisano_pos_and_period, Mathlib2.lib_fib_period_iff and Mathlib2.bld3_pisano_dvd_of_period: (m = 0 is trivial.) Let N = pisano m; bld3_pisano_pos_and_period + lib_fib_period_iff give F_N ≡ 0, F_{N+1} ≡ 1 mod m, i.e. Q^N = 1 + m•M for the Fibonacci matrix Q = !![1,1;1,0] over ℤ (Matrix.fib-style identity Q^n = [[F_{n+1},F_n],[F_n,F_{n-1}]]). Binomial expansion (Commute.add_pow) of (1 + m•M)^d: the j = 1 term is d·m·M and for j ≥ 2 m^j is divisible by m·d since d ∣ m; so Q^{dN} ≡ 1 mod d·m, i.e. F_{dN} ≡ 0, F_{dN+1} ≡ 1 mod d·m. lib_fib_period_iff turns this into dN being a period and bld3_pisano_dvd_of_period concludes. Special case: π(p^(k+1)) ∣ p·π(p^k). -/
theorem bld5_pisano_mul_dvd_mul_aux1 (R : Type*) [CommRing R] (a b : ℕ) :
    (Nat.fib (a + b) : R) = Nat.fib a * Nat.fib (b+1) + Nat.fib (a+1) * Nat.fib b - Nat.fib a * Nat.fib b := by
  have h1 : Nat.fib (a+b+1) = Nat.fib a * Nat.fib b + Nat.fib (a+1) * Nat.fib (b+1) := Nat.fib_add a b
  have h2 : Nat.fib (a+b+2) = Nat.fib (a+1) * Nat.fib b + Nat.fib (a+2) * Nat.fib (b+1) := by
    have := Nat.fib_add (a+1) b
    have e : a+1+b+1 = a+b+2 := by ring
    rw [e] at this; exact this
  have h3 : Nat.fib (a+b+2) = Nat.fib (a+b) + Nat.fib (a+b+1) := Nat.fib_add_two
  have h4 : Nat.fib (a+2) = Nat.fib a + Nat.fib (a+1) := Nat.fib_add_two
  have h1' : (Nat.fib (a+b+1) : R) = Nat.fib a * Nat.fib b + Nat.fib (a+1) * Nat.fib (b+1) := by
    have := congrArg (Nat.cast : ℕ → R) h1
    push_cast at this; exact this
  have h2' : (Nat.fib (a+b+2) : R) = Nat.fib (a+1) * Nat.fib b + Nat.fib (a+2) * Nat.fib (b+1) := by
    have := congrArg (Nat.cast : ℕ → R) h2
    push_cast at this; exact this
  have h3' : (Nat.fib (a+b+2) : R) = Nat.fib (a+b) + Nat.fib (a+b+1) := by
    have := congrArg (Nat.cast : ℕ → R) h3
    push_cast at this; exact this
  have h4' : (Nat.fib (a+2) : R) = Nat.fib a + Nat.fib (a+1) := by
    have := congrArg (Nat.cast : ℕ → R) h4
    push_cast at this; exact this
  linear_combination h2' - h1' - h3' + (Nat.fib (b+1) : R) * h4'

theorem bld5_pisano_mul_dvd_mul_aux2 (R : Type*) [CommRing R] (N : ℕ) (μ u v : R) (hμ : μ ^ 2 = 0)
    (h0 : (Nat.fib N : R) = μ * u) (h1 : (Nat.fib (N + 1) : R) = 1 + μ * v) (j : ℕ) :
    (Nat.fib (j * N) : R) = j * μ * u ∧ (Nat.fib (j * N + 1) : R) = 1 + j * μ * v := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨i0, i1⟩ := ih
    have e : (j + 1) * N = j * N + N := by ring
    constructor
    · rw [e, bld5_pisano_mul_dvd_mul_aux1, i0, i1, h0, h1]; push_cast
      linear_combination (2*j*u*v - j*u^2) * hμ
    · have h : (Nat.fib (j*N+N+1) : R) = Nat.fib (j*N) * Nat.fib N + Nat.fib (j*N+1) * Nat.fib (N+1) := by
        have := congrArg (Nat.cast : ℕ → R) (Nat.fib_add (j*N) N)
        push_cast at this; exact this
      rw [e, h, i0, i1, h0, h1]; push_cast
      linear_combination (j*u^2 + j*v^2) * hμ

theorem bld5_pisano_mul_dvd_mul (d m : ℕ) (hd : d ∣ m) : p3_pisano (d * m) ∣ d * p3_pisano m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  obtain ⟨hpos, hper⟩ := bld3_pisano_pos_and_period m hm
  obtain ⟨p0, p1⟩ := (lib_fib_period_iff m _).mp hper
  generalize p3_pisano m = N at *
  apply bld3_pisano_dvd_of_period
  rw [lib_fib_period_iff]
  obtain ⟨u, hu⟩ := (Nat.modEq_zero_iff_dvd).mp p0
  obtain ⟨v, hv⟩ := (Nat.modEq_iff_dvd).mp p1
  have hμ : ((m : ℕ) : ZMod (d * m)) ^ 2 = 0 := by
    obtain ⟨e, he⟩ := hd
    have : ((m^2 : ℕ) : ZMod (d*m)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      refine ⟨e, ?_⟩
      calc m^2 = m * m := pow_two m
        _ = (d*e)*m := by rw [← he]
        _ = d*m*e := by ring
    exact_mod_cast this
  have h0 : ((Nat.fib N : ℕ) : ZMod (d*m)) = (m : ZMod (d*m)) * (u : ZMod (d*m)) := by rw [hu]; push_cast; ring
  have h1 : ((Nat.fib (N+1) : ℕ) : ZMod (d*m)) = 1 + (m : ZMod (d*m)) * (-(v : ZMod (d*m))) := by
    have : ((Nat.fib (N+1) : ℕ) : ℤ) = 1 + (m:ℤ) * (-v) := by push_cast at hv; linarith
    have := congrArg (Int.cast : ℤ → ZMod (d*m)) this
    push_cast at this; exact this
  obtain ⟨r0, r1⟩ := bld5_pisano_mul_dvd_mul_aux2 (ZMod (d*m)) N _ _ _ hμ h0 h1 d
  have dm0 : ((d : ℕ) : ZMod (d*m)) * (m : ZMod (d*m)) = 0 := by
    rw [← Nat.cast_mul]; exact ZMod.natCast_self _
  constructor
  · rw [← ZMod.natCast_eq_natCast_iff, r0, dm0]; simp
  · rw [← ZMod.natCast_eq_natCast_iff, r1, dm0]; simp
end

-- forge:entry bld5_pisano_two_pow kind=proved origin=conjecture
section
/- Uses Mathlib2.lib_fib_period_iff, Mathlib2.bld3_pisano_dvd_of_period, Mathlib2.bld3_pisano_dvd_pisano_of_dvd and Mathlib2.lib_pisano_dvd_iff_period: prove by induction on j ≥ 1, using Nat.fib_two_mul and Nat.fib_two_mul_add_one, that F_{3·2^j} ≡ 2^(j+2) mod 2^(j+3) and F_{3·2^j+1} ≡ 1 + 2^(j+1) mod 2^(j+2) (base F_6 = 8, F_7 = 13). Upper bound: F_{3·2^k} ≡ 0, F_{3·2^k+1} ≡ 1 mod 2^(k+1), so lib_fib_period_iff + bld3_pisano_dvd_of_period give pisano ∣ 3·2^k. Lower bound by induction on k: bld3_pisano_dvd_pisano_of_dvd gives 3·2^(k-1) = pisano(2^k) ∣ pisano(2^(k+1)), so the value is 3·2^(k-1) or 3·2^k; the former is not a period (lib_pisano_dvd_iff_period at i = 1, or i = 0 when k = 1) because F_{3·2^(k-1)+1} ≡ 1 + 2^k ≢ 1 mod 2^(k+1). Base: pisano 2 = 3 by direct check. -/
theorem bld5_pisano_two_pow_aux1 (i : ℕ) : ∃ u v : ℤ, ((Nat.fib (3 * 2 ^ (i + 1)) : ℕ) : ℤ) = 2 ^ (i + 3) * (2 * u + 1) ∧ ((Nat.fib (3 * 2 ^ (i + 1) + 1) : ℕ) : ℤ) = 1 + 2 ^ (i + 2) * (2 * v + 1) := by
  induction i with
  | zero => exact ⟨0, 1, by norm_num, by norm_num⟩
  | succ i ih =>
    obtain ⟨u, v, hu, hv⟩ := ih
    have e : 3 * 2 ^ (i + 1 + 1) = 2 * (3 * 2 ^ (i + 1)) := by ring
    refine ⟨u + 2 ^ (i + 2) * (v - u) * (2 * u + 1), v + 2 ^ (i + 2) * (2 * u + 1) ^ 2 + 2 ^ i * (2 * v + 1) ^ 2, ?_, ?_⟩
    · rw [e, bld4_pisano_lucas_dvd_four_mul_aux1 ℤ, hu, hv]; ring
    · rw [e, Nat.fib_two_mul_add_one]; push_cast; rw [hu, hv]; ring

theorem bld5_pisano_two_pow_aux2 (k : ℕ) : p3_pisano (2 ^ (k + 1)) ∣ 3 * 2 ^ k := by
  apply bld3_pisano_dvd_of_period
  rw [lib_fib_period_iff]
  cases k with
  | zero => constructor <;> decide
  | succ i =>
    obtain ⟨u, v, hu, hv⟩ := bld5_pisano_two_pow_aux1 i
    constructor
    · rw [Nat.modEq_zero_iff_dvd]
      have : ((2 ^ (i + 1 + 1) : ℕ) : ℤ) ∣ ((Nat.fib (3 * 2 ^ (i + 1)) : ℕ) : ℤ) := by
        rw [hu]; push_cast; exact ⟨2 * (2 * u + 1), by ring⟩
      exact_mod_cast this
    · apply Nat.ModEq.symm
      rw [Nat.modEq_iff_dvd, hv]
      push_cast
      exact ⟨2 * v + 1, by ring⟩

theorem bld5_pisano_two_pow (k : ℕ) : p3_pisano (2 ^ (k + 1)) = 3 * 2 ^ k := by
  induction k with
  | zero =>
    have h1 : p3_pisano (2 ^ (0 + 1)) ∣ 3 := bld5_pisano_two_pow_aux2 0
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exfalso
      have hper := (lib_pisano_dvd_iff_period (2 ^ (0 + 1)) 1 one_pos).mp (by rw [h])
      have := hper 0
      revert this
      decide
    · exact h
  | succ k ih =>
    have h1 := bld5_pisano_two_pow_aux2 (k + 1)
    have h2 := bld3_pisano_dvd_pisano_of_dvd (2 ^ (k + 1)) (2 ^ (k + 1 + 1)) (pow_dvd_pow 2 (by omega))
    rw [ih] at h2
    obtain ⟨c, hc⟩ := h2
    have e : 3 * 2 ^ (k + 1) = 3 * 2 ^ k * 2 := by ring
    rw [hc, e] at h1
    rw [hc, e]
    have hc2 : c ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (by positivity) h1
    rcases (Nat.dvd_prime Nat.prime_two).mp hc2 with rfl | rfl
    · exfalso
      rw [mul_one] at hc
      have hper := (lib_pisano_dvd_iff_period (2 ^ (k + 1 + 1)) (3 * 2 ^ k) (by positivity)).mp (by rw [hc])
      have h3 := hper 1
      clear ih h1 hc hc2 e hper
      cases k with
      | zero => revert h3; decide
      | succ i =>
        obtain ⟨u, v, hu, hv⟩ := bld5_pisano_two_pow_aux1 i
        rw [show 1 + 3 * 2 ^ (i + 1) = 3 * 2 ^ (i + 1) + 1 from add_comm _ _, Nat.fib_one] at h3
        have h4 := Nat.modEq_iff_dvd.mp h3.symm
        rw [hv] at h4
        push_cast at h4
        obtain ⟨w, hw⟩ := h4
        have h5 : (2 : ℤ) ^ (i + 2) * (2 * v + 1) = 2 ^ (i + 2) * (2 * w) := by
          linear_combination hw
        have h6 := mul_left_cancel₀ (by positivity) h5
        omega
    · rfl
end

end Mathlib2
