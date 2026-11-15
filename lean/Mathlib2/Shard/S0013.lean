/- Mathlib2 分片 13（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0012
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry geo_unit_one_add_div_conj kind=proved origin=conjecture
section
/- For z on the unit circle with z ≠ -1, (1+z)/(1+conj z) = z — conj z = z⁻¹ since z * conj z = ‖z‖² = 1, then clear denominators. -/
theorem geo_unit_one_add_div_conj (z : ℂ) (hz : ‖z‖ = 1) (h : z ≠ -1) : (1 + z) / (1 + (starRingEnd ℂ) z) = z := by
  have h1 : z * (starRingEnd ℂ) z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp
  have h2 : 1 + (starRingEnd ℂ) z ≠ 0 := by
    intro h0
    apply h
    have h3 : (starRingEnd ℂ) z = -1 := by linear_combination h0
    rw [h3] at h1
    linear_combination -h1
  rw [div_eq_iff h2]
  linear_combination -h1
end

-- forge:entry geo_median_length kind=proved origin=conjecture
section
/- Apollonius' median length formula: the squared distance from a to the midpoint of b and c is (2|ab|² + 2|ac|² − |bc|²)/4 — expand all squared norms into inner products (or apply the parallelogram law to a−b and a−c). -/
theorem geo_median_length {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a b c : V) : ‖a - (1 / 2 : ℝ) • (b + c)‖ ^ 2 = (2 * ‖a - b‖ ^ 2 + 2 * ‖a - c‖ ^ 2 - ‖b - c‖ ^ 2) / 4 := by
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, real_inner_comm, RCLike.conj_to_real]
  have h1 := real_inner_comm a b
  have h2 := real_inner_comm a c
  have h3 := real_inner_comm b c
  rw [h1, h2, h3] at *
  ring
end

-- forge:entry geo_tan_pi_div_eight kind=proved origin=conjecture
section
/- tan(π/8) = √2 − 1 — use tan = sin/cos with Mathlib's closed forms for sin(π/8), cos(π/8), or tan(x/2) = (1 − cos x)/sin x at x = π/4. -/
theorem geo_tan_pi_div_eight : Real.tan (Real.pi / 8) = Real.sqrt 2 - 1 := by
  have hc : 0 < Real.cos (Real.pi / 8) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have h1 : Real.sin (Real.pi / 4) = 2 * Real.sin (Real.pi / 8) * Real.cos (Real.pi / 8) := by
    rw [← Real.sin_two_mul]; congr 1; ring
  have h2 : Real.cos (Real.pi / 4) = 2 * Real.cos (Real.pi / 8) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]; congr 1; ring
  rw [Real.sin_pi_div_four] at h1
  rw [Real.cos_pi_div_four] at h2
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [Real.tan_eq_sin_div_cos, div_eq_iff hc.ne']
  have h3 : (Real.sin (Real.pi / 8) - (Real.sqrt 2 - 1) * Real.cos (Real.pi / 8)) * (2 * Real.cos (Real.pi / 8)) = 0 := by
    linear_combination -h1 + (Real.sqrt 2 - 1) * h2 - (1/2 : ℝ) * hs
  rcases mul_eq_zero.mp h3 with h4 | h4
  · linarith
  · linarith
end

-- forge:entry geo_prod_sin_pi_mul_div kind=proved origin=conjecture
section
/- ∏_{k=1}^{m−1} sin(kπ/m) = m / 2^{m−1} (with m = n+1) — from ∏_{k=1}^{m−1}(1 − ζ^k) = m for ζ = exp(2πi/m) (IsPrimitiveRoot.prod_one_sub_pow_eq_order), take norms and use |1 − e^{2iθ}| = 2 sin θ for θ ∈ [0, π]. -/
theorem geo_prod_sin_pi_mul_div_aux1 (θ : ℝ) (h : 0 ≤ Real.sin θ) :
    ‖(1 : ℂ) - Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖ = 2 * Real.sin θ := by
  have hre : ((1 : ℂ) - Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)).re = 1 - Real.cos (2 * θ) := by
    rw [Complex.sub_re, Complex.exp_ofReal_mul_I_re]; simp
  have him : ((1 : ℂ) - Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)).im = - Real.sin (2 * θ) := by
    rw [Complex.sub_im, Complex.exp_ofReal_mul_I_im]; simp
  have h2 : ‖(1 : ℂ) - Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖ ^ 2 = (2 * Real.sin θ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him, Real.cos_two_mul, Real.sin_two_mul]
    linear_combination (4 * Real.cos θ ^ 2 - 4) * Real.sin_sq_add_cos_sq θ
  exact (sq_eq_sq₀ (norm_nonneg _) (by linarith)).mp h2

theorem geo_prod_sin_pi_mul_div (n : ℕ) : ∏ k ∈ Finset.range n, Real.sin (((k : ℝ) + 1) * Real.pi / ((n : ℝ) + 1)) = ((n : ℝ) + 1) / 2 ^ n := by
  have hζ := Complex.isPrimitiveRoot_exp (n + 1) (Nat.succ_ne_zero n)
  have hp := hζ.prod_one_sub_pow_eq_order
  have hn := congrArg norm hp
  rw [norm_prod] at hn
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hne : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have each : ∀ k ∈ Finset.range n,
      ‖(1 : ℂ) - Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((n + 1 : ℕ) : ℂ)) ^ (k + 1)‖
        = 2 * Real.sin (((k : ℝ) + 1) * Real.pi / ((n : ℝ) + 1)) := by
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hkr : (k : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk'.le
      linarith
    rw [← Complex.exp_nat_mul]
    have e : ((k + 1 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / ((n + 1 : ℕ) : ℂ))
        = (((2 * (((k : ℝ) + 1) * Real.pi / ((n : ℝ) + 1)) : ℝ)) : ℂ) * Complex.I := by
      push_cast
      field_simp
    rw [e]
    apply geo_prod_sin_pi_mul_div_aux1
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · rw [div_le_iff₀ hpos]
      nlinarith [Real.pi_pos]
  rw [Finset.prod_congr rfl each, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at hn
  have hr : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_natCast]; push_cast; ring
  rw [hr] at hn
  rw [eq_div_iff (by positivity)]
  linarith
end

-- forge:entry p3_aux_fib_prime kind=proved origin=conjecture
section
/- auxiliary (used in proofs of Thm 1 and Thm 2): L_p = 1 and F_p = 5^((p-1)/2) mod p for odd primes p -/
theorem p3_aux_fib_prime_aux1 (n : ℕ) : (⟨2, 0⟩ : ℤ√5) * (⟨1, 1⟩ : ℤ√5) ^ n = (⟨2, 0⟩ : ℤ√5) ^ n * ⟨2 * Nat.fib (n+1) - Nat.fib n, Nat.fib n⟩ := by
  induction n with
  | zero => ext <;> simp
  | succ n ih =>
    have key : (⟨2 * Nat.fib (n+1) - Nat.fib n, Nat.fib n⟩ : ℤ√5) * ⟨1, 1⟩ = ⟨2, 0⟩ * ⟨2 * Nat.fib (n+1+1) - Nat.fib (n+1), Nat.fib (n+1)⟩ := by
      rw [Nat.fib_add_two]
      ext <;> simp <;> ring
    rw [pow_succ, ← mul_assoc, ih, pow_succ, mul_assoc, key]
    ring
theorem p3_aux_fib_prime_aux2 (n : ℕ) : ((⟨2, 0⟩ : ℤ√5) ^ n) = ⟨2 ^ n, 0⟩ := by
  induction n with
  | zero => ext <;> simp
  | succ n ih => rw [pow_succ, ih]; ext <;> simp [pow_succ]
theorem p3_aux_fib_prime_aux3 (n : ℕ) : ((⟨0, 1⟩ : ℤ√5) ^ (2 * n + 1)) = ⟨0, 5 ^ n⟩ := by
  induction n with
  | zero => ext <;> simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by ring, pow_succ, pow_succ, ih]
    ext <;> simp [pow_succ] <;> ring
theorem p3_aux_fib_prime (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) : (2 * Nat.fib (p + 1) : ℤ) - Nat.fib p ≡ 1 [ZMOD p] ∧ (Nat.fib p : ℤ) ≡ 5 ^ (p / 2) [ZMOD p] := by
  haveI := Fact.mk hp
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (1 : ℤ√5) (⟨0, 1⟩ : ℤ√5)
  have h11 : (1 : ℤ√5) + ⟨0, 1⟩ = ⟨1, 1⟩ := by ext <;> simp
  have hodd : p = 2 * (p / 2) + 1 := by
    have := hp.eq_one_or_self_of_dvd 2
    rcases Nat.even_or_odd p with ⟨k, hk⟩ | ⟨k, hk⟩
    · exfalso; have := this ⟨k, by omega⟩; omega
    · omega
  have h3 := p3_aux_fib_prime_aux3 (p / 2)
  rw [← hodd] at h3
  have h1 := p3_aux_fib_prime_aux1 p
  rw [p3_aux_fib_prime_aux2, ← h11, hr, h3] at h1
  have hre := congrArg Zsqrtd.re h1
  have him := congrArg Zsqrtd.im h1
  simp at hre him
  have hre' := congrArg (Int.cast : ℤ → ZMod p) hre
  have him' := congrArg (Int.cast : ℤ → ZMod p) him
  push_cast at hre' him'
  have two_ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    have := hp.two_le
    omega
  have fermat : (2 : ZMod p) ^ p = 2 := ZMod.pow_card 2
  rw [fermat] at hre' him'
  simp at hre' him'
  constructor
  · rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    apply mul_left_cancel₀ two_ne
    first | linear_combination hre' | linear_combination -hre' | trace_state
  · rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rcases him' with h | h
    · rw [h]
    · exact absurd h two_ne
end

-- forge:entry top_frontier_frontier_frontier kind=proved origin=conjecture
section
/- The frontier operator is idempotent from the second application on — frontier A is closed, so frontier (frontier A) = frontier A \ interior (frontier A) is closed with empty interior (interior_frontier), and a closed set with empty interior is its own frontier. -/
theorem top_frontier_frontier_frontier {X : Type*} [TopologicalSpace X] (A : Set X) : frontier (frontier (frontier A)) = frontier (frontier A) := by
  rw [IsClosed.frontier_eq isClosed_frontier, interior_frontier isClosed_frontier, Set.diff_empty]
end

-- forge:entry geo_sin_pi_div_ten kind=proved origin=conjecture
section
/- sin(π/10) = (√5 − 1)/4 — sin(π/10) = cos(2π/5) = 2cos²(π/5) − 1 and Mathlib's cos(π/5) = (1+√5)/4. -/
theorem geo_sin_pi_div_ten : Real.sin (Real.pi / 10) = (Real.sqrt 5 - 1) / 4 := by
  have h1 : Real.sin (Real.pi / 10) = Real.cos (2 * (Real.pi / 5)) := by
    rw [← Real.cos_pi_div_two_sub]; congr 1; ring
  have hs : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  rw [h1, Real.cos_two_mul, Real.cos_pi_div_five]
  linear_combination (1/8 : ℝ) * hs
end

-- forge:entry top_disjoint_interior_closure_of_open kind=proved origin=conjecture
section
/- Disjoint open sets have disjoint regularizations — an open set disjoint from V is disjoint from closure V; apply this twice (Disjoint.closure_left/right for open sets) and shrink to interiors. -/
theorem top_disjoint_interior_closure_of_open {X : Type*} [TopologicalSpace X] (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hd : Disjoint U V) : Disjoint (interior (closure U)) (interior (closure V)) := by
  have h1 : Disjoint (interior (closure U)) V := (hd.closure_left hV).mono_left interior_subset
  exact (h1.closure_right isOpen_interior).mono_right interior_subset
end

-- forge:entry geo_cos_pi_div_five_sub_cos_two_pi_div_five kind=proved origin=conjecture
section
/- cos 36° − cos 72° = 1/2 — double angle formula plus cos(π/5) = (1+√5)/4, or the quadratic 4c² − 2c − 1 = 0 satisfied by c = cos(π/5). -/
theorem geo_cos_pi_div_five_sub_cos_two_pi_div_five : Real.cos (Real.pi / 5) - Real.cos (2 * Real.pi / 5) = 1 / 2 := by
  have h1 : Real.cos (2 * Real.pi / 5) = Real.cos (2 * (Real.pi / 5)) := by
    congr 1; ring
  have hs : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  rw [h1, Real.cos_two_mul, Real.cos_pi_div_five]
  linear_combination (-1/8 : ℝ) * hs
end

-- forge:entry geo_equilateral_iff_sum_sq kind=proved origin=conjecture
section
/- A triangle abc in the complex plane is equilateral (possibly degenerate to a point) iff a² + b² + c² = ab + bc + ca — the difference factors as (a + ωb + ω²c)(a + ω²b + ωc) with ω a primitive cube root of unity; a + ωb + ω²c = 0 says c − a is b − a rotated by 60°, and conversely equal side lengths force (c−a)/(b−a) to be a primitive 6th root of unity. -/
theorem geo_equilateral_iff_sum_sq (a b c : ℂ) : (‖a - b‖ = ‖b - c‖ ∧ ‖b - c‖ = ‖c - a‖) ↔ a ^ 2 + b ^ 2 + c ^ 2 = a * b + b * c + c * a := by
  constructor
  · rintro ⟨h1, h2⟩
    have e1 : (a - b) * (starRingEnd ℂ) (a - b) = (b - c) * (starRingEnd ℂ) (b - c) := by
      rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, h1]
    have e2 : (b - c) * (starRingEnd ℂ) (b - c) = (c - a) * (starRingEnd ℂ) (c - a) := by
      rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, h2]
    by_cases hx : a - b = 0
    · have hy : b - c = 0 := by
        rw [hx, norm_zero] at h1
        exact norm_eq_zero.mp h1.symm
      have ha : a = b := sub_eq_zero.mp hx
      have hb : b = c := sub_eq_zero.mp hy
      subst ha; subst hb; ring
    · have hy : b - c ≠ 0 := by
        intro h
        rw [h, norm_zero] at h1
        exact hx (norm_eq_zero.mp h1)
      have hX : (starRingEnd ℂ) (a - b) ≠ 0 := (map_ne_zero _).mpr hx
      have hY : (starRingEnd ℂ) (b - c) ≠ 0 := (map_ne_zero _).mpr hy
      have e3 : (starRingEnd ℂ) (c - a) = -((starRingEnd ℂ) (a - b) + (starRingEnd ℂ) (b - c)) := by
        rw [← map_add, ← map_neg]; congr 1; ring
      rw [e3] at e2
      have key : (a ^ 2 + b ^ 2 + c ^ 2 - (a * b + b * c + c * a)) * ((starRingEnd ℂ) (a - b) * (starRingEnd ℂ) (b - c)) = 0 := by
        generalize (starRingEnd ℂ) (a - b) = X at *
        generalize (starRingEnd ℂ) (b - c) = Y at *
        linear_combination (-((a - b) * X + (b - c) * X)) * e1 - ((a - b) * X) * e2
      rcases mul_eq_zero.mp key with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h (mul_ne_zero hX hY)
  · intro h
    have k : (a - b) ^ 2 + (a - b) * (b - c) + (b - c) ^ 2 = 0 := by linear_combination h
    have c1 : (a - b) ^ 3 = (b - c) ^ 3 := by linear_combination (a - b - (b - c)) * k
    have c2 : (b - c) ^ 3 = (c - a) ^ 3 := by linear_combination ((b - c) - (c - a)) * k
    have n1 := congrArg norm c1
    have n2 := congrArg norm c2
    rw [norm_pow, norm_pow] at n1 n2
    exact ⟨(pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp n1,
      (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp n2⟩
end

-- forge:entry top_closure_open_inter_closure kind=proved origin=conjecture
section
/- For open U, closure (U ∩ closure A) = closure (U ∩ A) — one inclusion is monotonicity, the other is IsOpen.inter_closure followed by closure_minimal. -/
theorem top_closure_open_inter_closure {X : Type*} [TopologicalSpace X] (U A : Set X) (hU : IsOpen U) : closure (U ∩ closure A) = closure (U ∩ A) := by
  apply subset_antisymm
  · exact closure_minimal hU.inter_closure isClosed_closure
  · exact closure_mono (Set.inter_subset_inter_right U subset_closure)
end

-- forge:entry geo_perp_bisector_iff kind=proved origin=conjecture
section
/- p is equidistant from a and b iff p − midpoint(a,b) is orthogonal to b − a — ‖p−a‖² − ‖p−b‖² = 2⟨p − (a+b)/2, b − a⟩, and norms are nonnegative. -/
theorem geo_perp_bisector_iff {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a b p : V) : ‖p - a‖ = ‖p - b‖ ↔ inner ℝ (p - (1 / 2 : ℝ) • (a + b)) (b - a) = 0 := by
  have key : ‖p - a‖ ^ 2 - ‖p - b‖ ^ 2 = 2 * inner ℝ (p - (1 / 2 : ℝ) • (a + b)) (b - a) := by
    simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
    have h1 := real_inner_comm a b
    have h2 := real_inner_comm a p
    have h3 := real_inner_comm b p
    rw [h1, h2, h3]
    ring
  constructor
  · intro h
    rw [h] at key
    linarith
  · intro h
    rw [h] at key
    have h2 : ‖p - a‖ ^ 2 = ‖p - b‖ ^ 2 := by linarith
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2
end

-- forge:entry top_dist_div_one_add_triangle kind=proved origin=conjecture
section
/- The bounded metric d/(1+d) satisfies the triangle inequality — t ↦ t/(1+t) is monotone and subadditive on [0,∞); combine with dist_triangle. -/
theorem top_dist_div_one_add_triangle {X : Type*} [MetricSpace X] (x y z : X) : dist x z / (1 + dist x z) ≤ dist x y / (1 + dist x y) + dist y z / (1 + dist y z) := by
  have ha : 0 ≤ dist x y := dist_nonneg
  have hb : 0 ≤ dist y z := dist_nonneg
  have hc : 0 ≤ dist x z := dist_nonneg
  have ht : dist x z ≤ dist x y + dist y z := dist_triangle x y z
  generalize dist x y = a at *
  generalize dist y z = b at *
  generalize dist x z = c at *
  rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg ha hb, mul_nonneg (mul_nonneg ha hb) hc]
end

-- forge:entry p3_thm1 kind=disproved origin=paper
section
/- Theorem 1 as literally written: S_p = 3 mod p if p = 1,4 mod 5 and S_p = 1 mod p if p = 2,3 mod 5 -/
theorem p3_thm1_disproof : ¬ (∀ (p : ℕ) (hp : p.Prime) (h5 : 5 < p), ((p % 5 = 1 ∨ p % 5 = 4) → (p3_fibsum p : ℤ) ≡ 3 [ZMOD p]) ∧ ((p % 5 = 2 ∨ p % 5 = 3) → (p3_fibsum p : ℤ) ≡ 1 [ZMOD p])) := by
  intro h
  have h7 := (h 7 (by norm_num) (by norm_num)).2 (Or.inl rfl)
  have e : p3_fibsum 7 = 33 := by decide
  rw [e] at h7
  revert h7
  decide
end

-- forge:entry geo_sin_mul_sin_pi_div_three_sub_add kind=proved origin=conjecture
section
/- sin x · sin(π/3 − x) · sin(π/3 + x) = sin(3x)/4 — expand with addition formulas (sin(π/3)=√3/2, cos(π/3)=1/2) to get sin x (3/4 cos²x − 1/4 sin²x), then use the triple angle formula. -/
theorem geo_sin_mul_sin_pi_div_three_sub_add (x : ℝ) : Real.sin x * Real.sin (Real.pi / 3 - x) * Real.sin (Real.pi / 3 + x) = Real.sin (3 * x) / 4 := by
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hcs := Real.cos_sq_add_sin_sq x
  rw [Real.sin_sub, Real.sin_add, Real.sin_three_mul, Real.sin_pi_div_three, Real.cos_pi_div_three]
  linear_combination (Real.sin x * Real.cos x ^ 2 / 4) * hs + (3 * Real.sin x / 4) * hcs
end

-- forge:entry geo_cos_sum_two_pi_div_seven kind=proved origin=conjecture
section
/- cos(2π/7) + cos(4π/7) + cos(6π/7) = −1/2 — multiply by 2 sin(π/7) ≠ 0 and telescope with 2 sin x cos y = sin(x+y) − sin(y−x), leaving sin(π) − sin(π/7); or take real parts of the sum of the 7th roots of unity. -/
theorem geo_cos_sum_two_pi_div_seven_aux1 (x y : ℝ) :
    2 * Real.sin x * Real.cos y = Real.sin (y + x) - Real.sin (y - x) := by
  rw [Real.sin_add, Real.sin_sub]; ring

theorem geo_cos_sum_two_pi_div_seven : Real.cos (2 * Real.pi / 7) + Real.cos (4 * Real.pi / 7) + Real.cos (6 * Real.pi / 7) = -1 / 2 := by
  have hs : 0 < Real.sin (Real.pi / 7) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have h1 := geo_cos_sum_two_pi_div_seven_aux1 (Real.pi / 7) (2 * Real.pi / 7)
  have h2 := geo_cos_sum_two_pi_div_seven_aux1 (Real.pi / 7) (4 * Real.pi / 7)
  have h3 := geo_cos_sum_two_pi_div_seven_aux1 (Real.pi / 7) (6 * Real.pi / 7)
  rw [show 2 * Real.pi / 7 + Real.pi / 7 = 3 * Real.pi / 7 by ring,
    show 2 * Real.pi / 7 - Real.pi / 7 = Real.pi / 7 by ring] at h1
  rw [show 4 * Real.pi / 7 + Real.pi / 7 = 5 * Real.pi / 7 by ring,
    show 4 * Real.pi / 7 - Real.pi / 7 = 3 * Real.pi / 7 by ring] at h2
  rw [show 6 * Real.pi / 7 + Real.pi / 7 = Real.pi by ring,
    show 6 * Real.pi / 7 - Real.pi / 7 = 5 * Real.pi / 7 by ring, Real.sin_pi] at h3
  apply mul_left_cancel₀ hs.ne'
  linear_combination (1 / 2) * (h1 + h2 + h3)
end

-- forge:entry top_fixed_of_iterate_contraction kind=proved origin=conjecture
section
/- If an iterate f^[n] is a contraction with fixed point p then p is already a fixed point of f — f p is also fixed by f^[n] (iterates commute with f) and a contraction with K < 1 has at most one fixed point. -/
theorem top_fixed_of_iterate_contraction {X : Type*} [MetricSpace X] (f : X → X) (n : ℕ) (K : ℝ) (hK : K < 1) (h : ∀ x y : X, dist (f^[n] x) (f^[n] y) ≤ K * dist x y) (p : X) (hp : f^[n] p = p) : f p = p := by
  have h1 : f^[n] (f p) = f p := by
    have := (Function.iterate_succ_apply f n p).symm.trans (Function.iterate_succ_apply' f n p)
    rw [this, hp]
  have h2 := h (f p) p
  rw [h1, hp] at h2
  have h3 : 0 ≤ dist (f p) p := dist_nonneg
  have h4 : dist (f p) p = 0 := by
    by_contra hne
    have hpos : 0 < dist (f p) p := lt_of_le_of_ne h3 (Ne.symm hne)
    nlinarith
  exact dist_eq_zero.mp h4
end

-- forge:entry p3_aux_period kind=proved origin=conjecture
section
/- auxiliary: for even n, 2n is a period of Fibonacci mod F_n -/
theorem p3_aux_period_aux1 (n : ℕ) : (Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib n * Nat.fib (n + 2) = (-1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.fib_add_two (n := n + 1), Nat.fib_add_two (n := n)] at *
    push_cast at *
    rw [pow_succ]
    linear_combination -ih
theorem p3_aux_period_aux2 (N m : ℕ) (h0 : Nat.fib m ≡ 0 [MOD N]) (h1 : Nat.fib (m + 1) ≡ 1 [MOD N]) (i : ℕ) : Nat.fib (i + m) ≡ Nat.fib i [MOD N] := by
  cases i with
  | zero => simpa using h0
  | succ j =>
    rw [show j + 1 + m = m + j + 1 by ring, Nat.fib_add]
    have := (h0.mul_right (Nat.fib j)).add (h1.mul_right (Nat.fib (j + 1)))
    simpa using this
theorem p3_aux_period_aux3 (N m : ℕ) (h0 : Nat.fib m ≡ 0 [MOD N]) (h1 : Nat.fib (m + 1) ≡ 1 [MOD N]) (k i : ℕ) : Nat.fib (i + m * k) ≡ Nat.fib i [MOD N] := by
  induction k with
  | zero => simp [Nat.ModEq]
  | succ k ih =>
    rw [show i + m * (k + 1) = (i + m * k) + m by ring]
    exact (p3_aux_period_aux2 N m h0 h1 _).trans ih
theorem p3_aux_period_aux4 (n : ℕ) (h2 : 2 ∣ n) : Nat.fib (2 * n) ≡ 0 [MOD Nat.fib n] ∧ Nat.fib (2 * n + 1) ≡ 1 [MOD Nat.fib n] := by
  constructor
  · exact (Nat.modEq_zero_iff_dvd).mpr (Nat.fib_dvd _ _ (dvd_mul_left n 2))
  · have hc := p3_aux_period_aux1 n
    rw [Even.neg_one_pow ((even_iff_two_dvd).mpr h2)] at hc
    rw [Nat.fib_two_mul_add_one]
    have hz : ((Nat.fib (n + 1) ^ 2 + Nat.fib n ^ 2 : ℕ) : ℤ) ≡ ((1 : ℕ) : ℤ) [ZMOD (Nat.fib n : ℕ)] := by
      rw [Int.modEq_iff_dvd]
      refine ⟨-(Nat.fib (n + 2) : ℤ) - Nat.fib n, ?_⟩
      push_cast
      linear_combination -hc
    exact (Int.natCast_modEq_iff).mp hz
theorem p3_aux_period (n k i : ℕ) (h2 : 2 ∣ n) : Nat.fib (i + 2 * n * k) ≡ Nat.fib i [MOD Nat.fib n] := by
  obtain ⟨h0, h1⟩ := p3_aux_period_aux4 n h2
  exact p3_aux_period_aux3 _ _ h0 h1 k i
end

-- forge:entry geo_stewart kind=proved origin=conjecture
section
/- Stewart's theorem in vector form: for d = (1−t)b + tc on line bc, |ad|² = (1−t)|ab|² + t|ac|² − t(1−t)|bc|² — write a − d = (1−t)(a−b) + t(a−c) and expand squared norms via inner products. -/
theorem geo_stewart {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a b c : V) (t : ℝ) : ‖a - ((1 - t) • b + t • c)‖ ^ 2 = (1 - t) * ‖a - b‖ ^ 2 + t * ‖a - c‖ ^ 2 - t * (1 - t) * ‖b - c‖ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  have h1 := real_inner_comm a b
  have h2 := real_inner_comm a c
  have h3 := real_inner_comm b c
  rw [h1, h2, h3]
  ring
end

-- forge:entry top_lfp_comp_self kind=proved origin=conjecture
section
/- The least fixed point of f∘f equals that of f — ≤ since lfp f is fixed by f∘f; for ≥ put a = lfp (f∘f): f a is a fixed point of f∘f so a ≤ f a, hence f a ≤ f (f a) = a, so a is a fixed point of f. -/
theorem top_lfp_comp_self {α : Type*} [CompleteLattice α] (f : α →o α) : OrderHom.lfp (f.comp f) = OrderHom.lfp f := by
  apply le_antisymm
  · apply OrderHom.lfp_le
    show f (f (OrderHom.lfp f)) ≤ OrderHom.lfp f
    rw [OrderHom.map_lfp, OrderHom.map_lfp]
  · have ha : f (f (OrderHom.lfp (f.comp f))) = OrderHom.lfp (f.comp f) := (f.comp f).map_lfp
    have h1 : OrderHom.lfp (f.comp f) ≤ f (OrderHom.lfp (f.comp f)) := by
      apply OrderHom.lfp_le
      show f (f (f (OrderHom.lfp (f.comp f)))) ≤ f (OrderHom.lfp (f.comp f))
      rw [ha]
    apply OrderHom.lfp_le
    calc f (OrderHom.lfp (f.comp f)) ≤ f (f (OrderHom.lfp (f.comp f))) := f.monotone h1
      _ = _ := ha
end

end Mathlib2
