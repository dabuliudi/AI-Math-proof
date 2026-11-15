/- Mathlib2 分片 7（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0006
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry r3_fib_iff_five_sq_pm_four_is_square_s1h2 kind=proved origin=decomposition
section
/- r3_fib_iff_five_sq_pm_four_is_square 的证明骨架中第 2 个空洞 -/
theorem r3_fib_iff_five_sq_pm_four_is_square_s1h2 : ∀ (v u : ℕ), u ≤ v → ((v : ℤ) ^ 2 - (v : ℤ) * (u : ℤ) - (u : ℤ) ^ 2 = 1 ∨ (v : ℤ) ^ 2 - (v : ℤ) * (u : ℤ) - (u : ℤ) ^ 2 = -1) → ∃ (n : ℕ), u = Nat.fib n ∧ v = Nat.fib (n + 1) := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro u huv hq
    have huv' : (u : ℤ) ≤ v := by exact_mod_cast huv
    have hu0 : (0 : ℤ) ≤ u := Nat.cast_nonneg u
    rcases Nat.eq_zero_or_pos u with rfl | hupos
    · refine ⟨0, by simp, ?_⟩
      have hv : (v : ℤ) ^ 2 = 1 := by
        rcases hq with h | h
        · simpa using h
        · simp at h; nlinarith [sq_nonneg (v : ℤ)]
      have : (v : ℤ) = 1 := by nlinarith [Nat.cast_nonneg (α := ℤ) v]
      simpa using (by exact_mod_cast this : v = 1)
    · have hu1 : (1 : ℤ) ≤ u := by exact_mod_cast hupos
      rcases Nat.eq_or_lt_of_le huv with rfl | hlt
      · refine ⟨1, ?_, ?_⟩ <;>
        · have : (u : ℤ) = 1 := by rcases hq with h | h <;> nlinarith
          simpa using (by exact_mod_cast this : u = 1)
      · have hlt' : (u : ℤ) < v := by exact_mod_cast hlt
        have hle2 : v - u ≤ u := by
          by_contra hc
          have hc' : (2 : ℤ) * u + 1 ≤ v := by
            have : 2 * u + 1 ≤ v := by omega
            exact_mod_cast this
          rcases hq with h | h <;> nlinarith
        have hcast : ((v - u : ℕ) : ℤ) = (v : ℤ) - u := by push_cast [Nat.cast_sub huv]; ring
        have hq' : ((u : ℤ) ^ 2 - (u : ℤ) * ((v - u : ℕ) : ℤ) - ((v - u : ℕ) : ℤ) ^ 2 = 1 ∨ (u : ℤ) ^ 2 - (u : ℤ) * ((v - u : ℕ) : ℤ) - ((v - u : ℕ) : ℤ) ^ 2 = -1) := by
          rw [hcast]
          rcases hq with h | h
          · right; linear_combination -h
          · left; linear_combination -h
        obtain ⟨n, hn1, hn2⟩ := ih u hlt (v - u) hle2 hq'
        refine ⟨n + 1, hn2, ?_⟩
        rw [Nat.fib_add_two, ← hn1, ← hn2]; omega
end

-- forge:entry r3_fib_iff_five_sq_pm_four_is_square_s1h3 kind=proved origin=decomposition
section
/- r3_fib_iff_five_sq_pm_four_is_square 的证明骨架中第 3 个空洞 -/
theorem r3_fib_iff_five_sq_pm_four_is_square_s1h3 : ∀ (x u : ℕ), x ^ 2 = 5 * u ^ 2 + 4 ∨ x ^ 2 + 4 = 5 * u ^ 2 → ∃ (v : ℕ), x + u = 2 * v ∧ u ≤ v := by
  intro x u h
  have hpar : x % 2 = u % 2 := by
    have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
    have hu : u % 2 = 0 ∨ u % 2 = 1 := by omega
    rcases h with h | h <;> have h2 := congrArg (· % 2) h <;>
      rcases hx with hx | hx <;> rcases hu with hu | hu <;>
      simp [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, hx, hu] at h2 <;> omega
  have hle : u ≤ x := by
    by_contra hc
    have : x + 1 ≤ u := by omega
    rcases h with h | h <;> nlinarith
  exact ⟨(x + u) / 2, by omega, by omega⟩
end

-- forge:entry r3_fib_iff_five_sq_pm_four_is_square kind=proved origin=conjecture
section
/- Gessel's criterion: y is a Fibonacci number iff 5y^2+4 or 5y^2-4 is a perfect square. Builds on Cassini's identity Mathlib2.an_cassini_int (the forward direction is L_n^2 - 5F_n^2 = 4(-1)^n with L_n = F_{n-1}+F_{n+1}, a rewriting of Cassini). Proof idea for the converse: descent on the Pell-type equation x^2 - 5y^2 = ±4: x ≡ y mod 2, and for y ≥ 2 the map (x,y) ↦ ((3y - x)/2 ... ) i.e. (y, (x-y)/2) ↦ ((x-y)/2, (3y-x)/2) steps down to a smaller solution of the opposite sign, mirroring (F_{n+1},F_n) ↦ (F_n,F_{n-1}); strong induction with base cases y ≤ 1. -/
theorem r3_fib_iff_five_sq_pm_four_is_square (y : ℕ) : (∃ n : ℕ, y = Nat.fib n) ↔ ∃ x : ℕ, x ^ 2 = 5 * y ^ 2 + 4 ∨ x ^ 2 + 4 = 5 * y ^ 2 := by
  have cassini : ∀ n : ℕ, ((Nat.fib (n + 1) : ℤ)) ^ 2 - (Nat.fib (n + 1) : ℤ) * (Nat.fib n : ℤ) - (Nat.fib n : ℤ) ^ 2 = (-1) ^ n := by
    clear y
    (first | exact Mathlib2.r3_fib_iff_five_sq_pm_four_is_square_s1h1 | apply Mathlib2.r3_fib_iff_five_sq_pm_four_is_square_s1h1 <;> assumption | simpa using Mathlib2.r3_fib_iff_five_sq_pm_four_is_square_s1h1)
  have descent : ∀ v u : ℕ, u ≤ v → ((v : ℤ) ^ 2 - (v : ℤ) * (u : ℤ) - (u : ℤ) ^ 2 = 1 ∨ (v : ℤ) ^ 2 - (v : ℤ) * (u : ℤ) - (u : ℤ) ^ 2 = -1) → ∃ n : ℕ, u = Nat.fib n ∧ v = Nat.fib (n + 1) := by
    clear y cassini
    (first | exact Mathlib2.r3_fib_iff_five_sq_pm_four_is_square_s1h2 | apply Mathlib2.r3_fib_iff_five_sq_pm_four_is_square_s1h2 <;> assumption | simpa using Mathlib2.r3_fib_iff_five_sq_pm_four_is_square_s1h2)
  have half : ∀ x u : ℕ, (x ^ 2 = 5 * u ^ 2 + 4 ∨ x ^ 2 + 4 = 5 * u ^ 2) → ∃ v : ℕ, x + u = 2 * v ∧ u ≤ v := by
    clear y cassini descent
    (first | exact Mathlib2.r3_fib_iff_five_sq_pm_four_is_square_s1h3 | apply Mathlib2.r3_fib_iff_five_sq_pm_four_is_square_s1h3 <;> assumption | simpa using Mathlib2.r3_fib_iff_five_sq_pm_four_is_square_s1h3)
  constructor
  · rintro ⟨n, rfl⟩
    have hle : Nat.fib n ≤ 2 * Nat.fib (n + 1) := by
      have := Nat.fib_le_fib_succ (n := n); omega
    have hc := cassini n
    refine ⟨2 * Nat.fib (n + 1) - Nat.fib n, ?_⟩
    have hx : ((2 * Nat.fib (n + 1) - Nat.fib n : ℕ) : ℤ) = 2 * (Nat.fib (n + 1) : ℤ) - (Nat.fib n : ℤ) := by
      push_cast [Nat.cast_sub hle]; ring
    rcases Nat.even_or_odd n with he | ho
    · left
      rw [he.neg_one_pow] at hc
      have : ((2 * Nat.fib (n + 1) - Nat.fib n : ℕ) : ℤ) ^ 2 = 5 * (Nat.fib n : ℤ) ^ 2 + 4 := by
        rw [hx]; linear_combination 4 * hc
      exact_mod_cast this
    · right
      rw [ho.neg_one_pow] at hc
      have : ((2 * Nat.fib (n + 1) - Nat.fib n : ℕ) : ℤ) ^ 2 + 4 = 5 * (Nat.fib n : ℤ) ^ 2 := by
        rw [hx]; linear_combination 4 * hc
      exact_mod_cast this
  · rintro ⟨x, hx⟩
    obtain ⟨v, hxv, huv⟩ := half x y hx
    have hxv' : (x : ℤ) + (y : ℤ) = 2 * (v : ℤ) := by exact_mod_cast hxv
    have hq : (v : ℤ) ^ 2 - (v : ℤ) * (y : ℤ) - (y : ℤ) ^ 2 = 1 ∨ (v : ℤ) ^ 2 - (v : ℤ) * (y : ℤ) - (y : ℤ) ^ 2 = -1 := by
      rcases hx with h1 | h1
      · left
        have h1' : (x : ℤ) ^ 2 = 5 * (y : ℤ) ^ 2 + 4 := by exact_mod_cast h1
        have : 4 * ((v : ℤ) ^ 2 - (v : ℤ) * (y : ℤ) - (y : ℤ) ^ 2) = 4 := by
          linear_combination h1' - ((x : ℤ) + 2 * v - y) * hxv'
        linarith
      · right
        have h1' : (x : ℤ) ^ 2 + 4 = 5 * (y : ℤ) ^ 2 := by exact_mod_cast h1
        have : 4 * ((v : ℤ) ^ 2 - (v : ℤ) * (y : ℤ) - (y : ℤ) ^ 2) = -4 := by
          linear_combination h1' - ((x : ℤ) + 2 * v - y) * hxv'
        linarith
    obtain ⟨n, hn, -⟩ := descent v y huv hq
    exact ⟨n, hn⟩
end

-- forge:entry r3_fermat_fourth_pow_sub_ne_sq_s1h1v1 kind=proved origin=decomposition
section
/- r3_fermat_fourth_pow_sub_ne_sq 的证明骨架中第 1 个空洞 -/
theorem r3_fermat_fourth_pow_sub_ne_sq_s1h1v1 : (∀ (x y z : ℤ), x.gcd y = 1 → y ≠ 0 → z ≠ 0 → x ^ 4 - y ^ 4 ≠ z ^ 2) → ∀ (x y z : ℤ), y ≠ 0 → z ≠ 0 → x ^ 4 - y ^ 4 ≠ z ^ 2 := by
  intro hprim x y z hy hz he
  have hgpos : 0 < Int.gcd x y := Int.gcd_pos_of_ne_zero_right x hy
  obtain ⟨x', y', hg', hx', hy'⟩ := Int.exists_gcd_one hgpos
  generalize (Int.gcd x y : ℤ) = g at hx' hy'
  have hg0 : g ≠ 0 := by
    rintro rfl
    apply hy; rw [hy']; ring
  have hy'0 : y' ≠ 0 := by
    rintro rfl
    apply hy; rw [hy']; ring
  have hdvd : (g ^ 2) ^ 2 ∣ z ^ 2 := ⟨x' ^ 4 - y' ^ 4, by rw [← he, hx', hy']; ring⟩
  obtain ⟨z', hz'⟩ := (Int.pow_dvd_pow_iff two_ne_zero).mp hdvd
  have hz'0 : z' ≠ 0 := by
    rintro rfl
    apply hz; rw [hz']; ring
  refine hprim x' y' z' hg' hy'0 hz'0 ?_
  have hg4 : g ^ 4 ≠ 0 := pow_ne_zero 4 hg0
  apply mul_left_cancel₀ hg4
  rw [hx', hy', hz'] at he
  linear_combination he
end

-- forge:entry r3_erdos_szekeres_s1h1 kind=proved origin=decomposition
section
/- r3_erdos_szekeres 的证明骨架中第 1 个空洞 -/
open Finset in
theorem r3_erdos_szekeres_s1h1 : ∀ (n : ℕ) (g : Fin n → ℝ), ∃ (a : Fin n → ℕ), (∀ (i : Fin n), 1 ≤ a i ∧ ∃ (t : Finset (Fin n)), t.card = a i ∧ StrictMonoOn g (t : Set (Fin n))) ∧ ∀ (i j : Fin n), i < j → g i < g j → a i < a j := by
  classical
  intro n g
  let S : Fin n → Finset (Finset (Fin n)) := fun i =>
    univ.filter (fun t => i ∈ t ∧ (∀ x ∈ t, x ≤ i) ∧ StrictMonoOn g (t : Set (Fin n)))
  have hS : ∀ i, {i} ∈ S i := by
    intro i
    refine mem_filter.2 ⟨mem_univ _, mem_singleton_self _, ?_, ?_⟩
    · intro x hx; exact (mem_singleton.1 hx).le
    · intro x hx y hy hxy
      rw [mem_coe, mem_singleton] at hx hy
      rw [hx, hy] at hxy
      exact absurd hxy (lt_irrefl _)
  have hex : ∀ i, ∃ t ∈ S i, (S i).sup card = t.card := fun i =>
    Finset.exists_mem_eq_sup (S i) ⟨{i}, hS i⟩ card
  refine ⟨fun i => (S i).sup card, ?_, ?_⟩
  · intro i
    obtain ⟨t, ht, hte⟩ := hex i
    refine ⟨?_, t, hte.symm, (mem_filter.1 ht).2.2.2⟩
    have h1 : card ({i} : Finset (Fin n)) ≤ (S i).sup card := Finset.le_sup (f := card) (hS i)
    simpa using h1
  · intro i j hij hg
    obtain ⟨t, ht, hte⟩ := hex i
    obtain ⟨-, hit, hmax, hmono⟩ := mem_filter.1 ht
    have hjt : j ∉ t := fun h => absurd (hmax j h) (not_le.2 hij)
    have hmem : insert j t ∈ S j := by
      refine mem_filter.2 ⟨mem_univ _, mem_insert_self _ _, ?_, ?_⟩
      · intro x hx
        rcases mem_insert.1 hx with hx | hx
        · exact hx.le
        · exact (hmax x hx).trans hij.le
      · intro x hx y hy hxy
        rw [mem_coe, mem_insert] at hx hy
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · rw [hx, hy] at hxy; exact absurd hxy (lt_irrefl _)
        · rw [hx] at hxy; exact absurd (hmax y hy) (not_le.2 (hij.trans hxy))
        · rw [hy]
          rcases eq_or_lt_of_le (hmax x hx) with h | h
          · rw [h]; exact hg
          · exact (hmono hx hit h).trans hg
        · exact hmono hx hy hxy
    have h2 : card (insert j t) ≤ (S j).sup card := Finset.le_sup (f := card) hmem
    rw [card_insert_of_notMem hjt] at h2
    show (S i).sup card < (S j).sup card
    omega
end

-- forge:entry r3_fermat_fourth_pow_sub_ne_sq_s1h2 kind=proved origin=decomposition
section
/- r3_fermat_fourth_pow_sub_ne_sq 的证明骨架中第 2 个空洞 -/
theorem r3_fermat_fourth_pow_sub_ne_sq_s1h2 : ∀ (x y z : ℤ), x.gcd y = 1 → y % 2 = 1 → z ≠ 0 → x ^ 4 - y ^ 4 = z ^ 2 → ∃ m n w, |m| < |x| ∧ m.gcd n = 1 ∧ n ≠ 0 ∧ w ≠ 0 ∧ m ^ 4 - n ^ 4 = w ^ 2 := by
  intro x y z hg hy1 hz he
  have hy0 : y ≠ 0 := by
    rintro rfl
    norm_num at hy1
  have hx0 : x ≠ 0 := by
    rintro rfl
    have h1 : 0 < z ^ 2 := by positivity
    have h2 : 0 ≤ y ^ 4 := by positivity
    nlinarith
  have hpt : PythagoreanTriple (y ^ 2) z (x ^ 2) := by
    unfold PythagoreanTriple
    linear_combination (-1 : ℤ) * he
  have hc : IsCoprime x y := Int.isCoprime_iff_gcd_eq_one.mpr hg
  have hc1 : IsCoprime (x ^ 4) (y ^ 2) := hc.pow
  have hc2 : IsCoprime (x ^ 4 + y ^ 2 * (-y ^ 2)) (y ^ 2) := hc1.add_mul_left_left _
  have e : x ^ 4 + y ^ 2 * (-y ^ 2) = z ^ 2 := by linear_combination he
  rw [e] at hc2
  have hc4 : IsCoprime z (y ^ 2) := (IsCoprime.pow_left_iff (by norm_num)).mp hc2
  have hg2 : Int.gcd (y ^ 2) z = 1 := Int.isCoprime_iff_gcd_eq_one.mp hc4.symm
  have hpar : y ^ 2 % 2 = 1 := by
    rw [sq, Int.mul_emod, hy1]; rfl
  have hpos : 0 < x ^ 2 := by positivity
  obtain ⟨m, n, h1, h2, h3, hmn, -, -⟩ := hpt.coprime_classification' hg2 hpar hpos
  have hn : n ≠ 0 := by
    rintro rfl
    apply hz; rw [h2]; ring
  refine ⟨m, n, x * y, ?_, hmn, hn, mul_ne_zero hx0 hy0, ?_⟩
  · apply sq_lt_sq.mp
    have : 0 < n ^ 2 := by positivity
    rw [h3]; linarith
  · linear_combination (-(y ^ 2)) * h3 - (m ^ 2 + n ^ 2) * h1
end

-- forge:entry r3_fermat_fourth_pow_sub_ne_sq_s1h3 kind=proved origin=decomposition
section
/- r3_fermat_fourth_pow_sub_ne_sq 的证明骨架中第 3 个空洞 -/
theorem r3_fermat_fourth_pow_sub_ne_sq_s1h3 : ∀ (x y z : ℤ), x.gcd y = 1 → y % 2 = 0 → y ≠ 0 → x ^ 4 - y ^ 4 = z ^ 2 → ∃ a b, x ^ 2 = (2 * a ^ 2) ^ 2 + (b ^ 2) ^ 2 ∧ a ≠ 0 ∧ (2 * a ^ 2).gcd (b ^ 2) = 1 := by
  intro x y z hg hy0 hyne he
  have hye : Even y := Int.even_iff.mpr hy0
  have hc : IsCoprime x y := Int.isCoprime_iff_gcd_eq_one.mpr hg
  have hxo : ¬ Even x := by
    intro hxe
    have hd := Int.dvd_coe_gcd hxe.two_dvd hye.two_dvd
    rw [hg] at hd
    norm_num at hd
  have hzo : ¬ Even z := by
    intro hze
    have h := congrArg Even he
    simp [Int.even_sub, Int.even_pow, hze, hye, hxo] at h
  have hz1 : z % 2 = 1 := Int.not_even_iff.mp hzo
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxo ⟨0, by ring⟩
  have hpt : PythagoreanTriple z (y ^ 2) (x ^ 2) := by
    unfold PythagoreanTriple
    linear_combination (-1 : ℤ) * he
  have hc1 : IsCoprime (x ^ 4) (y ^ 2) := hc.pow
  have hc2 : IsCoprime (x ^ 4 + y ^ 2 * (-y ^ 2)) (y ^ 2) := hc1.add_mul_left_left _
  have e : x ^ 4 + y ^ 2 * (-y ^ 2) = z ^ 2 := by linear_combination he
  rw [e] at hc2
  have hc4 : IsCoprime z (y ^ 2) := (IsCoprime.pow_left_iff (by norm_num)).mp hc2
  have hg2 : Int.gcd z (y ^ 2) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hc4
  have hpos : 0 < x ^ 2 := by positivity
  obtain ⟨l, hl⟩ := hye
  have hl0 : l ≠ 0 := by
    rintro rfl
    apply hyne; rw [hl]; ring
  have core : ∀ k v : ℤ, Int.gcd (2 * k) v = 1 → k * v = l ^ 2 → (0 ≤ k ∨ 0 ≤ v) →
      x ^ 2 = (2 * k) ^ 2 + v ^ 2 →
      ∃ (a : ℤ) (b : ℤ), x ^ 2 = (2 * a ^ 2) ^ 2 + (b ^ 2) ^ 2 ∧ a ≠ 0 ∧ Int.gcd (2 * a ^ 2) (b ^ 2) = 1 := by
    intro k v hkv hprod hsign hx2
    have hl2 : 0 < l ^ 2 := by positivity
    have hpos' : 0 < k * v := by rw [hprod]; exact hl2
    have hkvpos : 0 < k ∧ 0 < v := by
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos hpos' with h | h
      · exact h
      · rcases hsign with hs | hs
        · exact absurd h.1 (not_lt.mpr hs)
        · exact absurd h.2 (not_lt.mpr hs)
    have hkv' : Int.gcd k v = 1 :=
      Int.isCoprime_iff_gcd_eq_one.mp (Int.isCoprime_iff_gcd_eq_one.mpr hkv).of_mul_left_right
    have hvk' : Int.gcd v k = 1 := by rw [Int.gcd_comm]; exact hkv'
    obtain ⟨a, ha⟩ := Int.sq_of_gcd_eq_one hkv' hprod
    obtain ⟨b, hb⟩ := Int.sq_of_gcd_eq_one hvk' (by rw [mul_comm]; exact hprod)
    have ha' : k = a ^ 2 := by
      rcases ha with ha | ha
      · exact ha
      · nlinarith [sq_nonneg a, hkvpos.1]
    have hb' : v = b ^ 2 := by
      rcases hb with hb | hb
      · exact hb
      · nlinarith [sq_nonneg b, hkvpos.2]
    have ha0 : a ≠ 0 := by
      rintro rfl
      have := hkvpos.1
      rw [ha'] at this
      norm_num at this
    subst ha' hb'
    exact ⟨a, b, hx2, ha0, hkv⟩
  obtain ⟨m, n, h1, h2, h3, hmn, hpar, hm0⟩ := hpt.coprime_classification' hg2 hz1 hpos
  rcases hpar with ⟨hm, hn⟩ | ⟨hm, hn⟩
  · obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero hm
    subst hk
    refine core k n hmn ?_ (Or.inl (by linarith)) h3
    rw [hl] at h2
    linarith
  · obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero hn
    subst hk
    refine core k m (by rw [Int.gcd_comm]; exact hmn) ?_ (Or.inr hm0) (by rw [h3]; ring)
    rw [hl] at h2
    linarith
end

-- forge:entry r3_erdos_szekeres_s1h2 kind=proved origin=decomposition
section
/- r3_erdos_szekeres 的证明骨架中第 2 个空洞 -/
theorem r3_erdos_szekeres_s1h2 : ∀ (r s : ℕ) (a b : Fin (r * s + 1) → ℕ), (∀ (i : Fin (r * s + 1)), 1 ≤ a i ∧ a i ≤ r) → (∀ (i : Fin (r * s + 1)), 1 ≤ b i ∧ b i ≤ s) → ∃ (i : Fin (r * s + 1)) (j : Fin (r * s + 1)), i < j ∧ a i = a j ∧ b i = b j := by
  intro r s a b ha hb
  have hcard : (Finset.Icc 1 r ×ˢ Finset.Icc 1 s).card < (Finset.univ : Finset (Fin (r * s + 1))).card := by
    simp
  obtain ⟨x, -, y, -, hne, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
    (f := fun i => (a i, b i)) (fun i _ => by
      rw [Finset.mem_coe, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      exact ⟨ha i, hb i⟩)
  simp only [Prod.mk.injEq] at he
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨x, y, h, he.1, he.2⟩
  · exact ⟨y, x, h, he.1.symm, he.2.symm⟩
end

-- forge:entry r3_fermat_fourth_pow_sub_ne_sq_s1h4 kind=proved origin=decomposition
section
/- r3_fermat_fourth_pow_sub_ne_sq 的证明骨架中第 4 个空洞 -/
theorem r3_fermat_fourth_pow_sub_ne_sq_s1h4 : ∀ (x a b : ℤ), a ≠ 0 → (2 * a ^ 2).gcd (b ^ 2) = 1 → x ^ 2 = (2 * a ^ 2) ^ 2 + (b ^ 2) ^ 2 → ∃ c d w, |c| < |x| ∧ c.gcd d = 1 ∧ d ≠ 0 ∧ w ≠ 0 ∧ c ^ 4 - d ^ 4 = w ^ 2 := by
  intro x a b ha hgcd hx2
  have hpar : b ^ 2 % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one (b ^ 2) with h0 | h1
    · have h2b : (2 : ℤ) ∣ b ^ 2 := Int.dvd_of_emod_eq_zero h0
      have hd := Int.dvd_coe_gcd (dvd_mul_right 2 (a ^ 2)) h2b
      rw [hgcd] at hd
      norm_num at hd
    · exact h1
  have hb0 : b ≠ 0 := by
    rintro rfl
    norm_num at hpar
  have ha2 : 0 < a ^ 2 := by positivity
  have hx0 : x ≠ 0 := by
    rintro rfl
    nlinarith [sq_nonneg (b ^ 2), sq_nonneg (a ^ 2)]
  have hpt : PythagoreanTriple (b ^ 2) (2 * a ^ 2) |x| := by
    unfold PythagoreanTriple
    rw [abs_mul_abs_self]
    linear_combination (-1 : ℤ) * hx2
  have hg2 : Int.gcd (b ^ 2) (2 * a ^ 2) = 1 := by rw [Int.gcd_comm]; exact hgcd
  obtain ⟨p, q, h1, h2, h3, hpq, -, hp0⟩ := hpt.coprime_classification' hg2 hpar (abs_pos.mpr hx0)
  have hpqa : p * q = a ^ 2 := by linarith
  have hqpa : q * p = a ^ 2 := by linarith
  have hqp : Int.gcd q p = 1 := by rw [Int.gcd_comm]; exact hpq
  obtain ⟨c, hc⟩ := Int.sq_of_gcd_eq_one hpq hpqa
  obtain ⟨d, hd⟩ := Int.sq_of_gcd_eq_one hqp hqpa
  have hpos : 0 < p * q := by rw [hpqa]; exact ha2
  have hpq0 : 0 < p ∧ 0 < q := by
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hpos with h | h
    · exact h
    · exact absurd h.1 (not_lt.mpr hp0)
  have hc' : p = c ^ 2 := by
    rcases hc with hc | hc
    · exact hc
    · nlinarith [sq_nonneg c, hpq0.1]
  have hd' : q = d ^ 2 := by
    rcases hd with hd | hd
    · exact hd
    · nlinarith [sq_nonneg d, hpq0.2]
  have hd0 : d ≠ 0 := by
    rintro rfl
    have := hpq0.2
    rw [hd'] at this
    norm_num at this
  have hcd : Int.gcd c d = 1 := by
    rw [hc', hd'] at hpq
    exact Int.isCoprime_iff_gcd_eq_one.mp
      ((IsCoprime.pow_iff (by norm_num) (by norm_num)).mp (Int.isCoprime_iff_gcd_eq_one.mpr hpq))
  refine ⟨c, d, b, ?_, hcd, hd0, hb0, ?_⟩
  · rw [h3, hc', hd']
    have hd4 : 0 < (d ^ 2) ^ 2 := by positivity
    have hc1 : |c| ≤ (c ^ 2) ^ 2 := by
      rcases eq_or_ne c 0 with rfl | hc0
      · simp
      · have h1c : 1 ≤ |c| := Int.one_le_abs hc0
        have h4 : |c| ≤ |c| ^ 4 := le_self_pow₀ h1c (by norm_num)
        have e4 : |c| ^ 4 = c ^ 4 := Even.pow_abs (by decide) c
        rw [e4] at h4
        calc |c| ≤ c ^ 4 := h4
          _ = (c ^ 2) ^ 2 := by ring
    linarith
  · rw [hc', hd'] at h1
    linear_combination -h1
end

-- forge:entry r3_erdos_szekeres kind=proved origin=conjecture
section
/- Erdős–Szekeres: any sequence of rs+1 distinct reals has an increasing subsequence of length r+1 or a decreasing one of length s+1. Proof idea: label each index i with (length of longest increasing subsequence ending at i, longest decreasing ending at i); labels are pairwise distinct (for i<j one of the two coordinates strictly grows); if all labels lay in [1,r]×[1,s] pigeonhole would be violated. -/
theorem r3_erdos_szekeres (r s : ℕ) (f : Fin (r * s + 1) → ℝ) (hf : Function.Injective f) : (∃ t : Finset (Fin (r * s + 1)), r < t.card ∧ StrictMonoOn f (t : Set (Fin (r * s + 1)))) ∨ (∃ t : Finset (Fin (r * s + 1)), s < t.card ∧ StrictAntiOn f (t : Set (Fin (r * s + 1)))) := by
  have labels : ∀ (n : ℕ) (g : Fin n → ℝ), ∃ a : Fin n → ℕ, (∀ i, 1 ≤ a i ∧ ∃ t : Finset (Fin n), t.card = a i ∧ StrictMonoOn g (t : Set (Fin n))) ∧ ∀ i j, i < j → g i < g j → a i < a j := by
    clear hf f r s
    (first | exact Mathlib2.r3_erdos_szekeres_s1h1 | apply Mathlib2.r3_erdos_szekeres_s1h1 <;> assumption | simpa using Mathlib2.r3_erdos_szekeres_s1h1)
  have pigeon : ∀ (r s : ℕ) (a b : Fin (r * s + 1) → ℕ), (∀ i, 1 ≤ a i ∧ a i ≤ r) → (∀ i, 1 ≤ b i ∧ b i ≤ s) → ∃ i j, i < j ∧ a i = a j ∧ b i = b j := by
    clear labels hf f r s
    (first | exact Mathlib2.r3_erdos_szekeres_s1h2 | apply Mathlib2.r3_erdos_szekeres_s1h2 <;> assumption | simpa using Mathlib2.r3_erdos_szekeres_s1h2)
  by_contra hcon
  push_neg at hcon
  obtain ⟨hinc, hdec⟩ := hcon
  obtain ⟨a, ha1, ha2⟩ := labels _ f
  obtain ⟨b, hb1, hb2⟩ := labels _ (fun i => - f i)
  have hA : ∀ i, 1 ≤ a i ∧ a i ≤ r := by
    intro i
    obtain ⟨h1, t, ht, hmono⟩ := ha1 i
    refine ⟨h1, ?_⟩
    by_contra hc
    exact hinc t (by omega) hmono
  have hB : ∀ i, 1 ≤ b i ∧ b i ≤ s := by
    intro i
    obtain ⟨h1, t, ht, hmono⟩ := hb1 i
    refine ⟨h1, ?_⟩
    by_contra hc
    refine hdec t (by omega) ?_
    intro x hx y hy hxy
    have := hmono hx hy hxy
    simp only at this
    linarith
  obtain ⟨i, j, hij, hae, hbe⟩ := pigeon r s a b hA hB
  have hne : f i ≠ f j := fun h => (ne_of_lt hij) (hf h)
  rcases lt_or_gt_of_ne hne with h | h
  · have := ha2 i j hij h; omega
  · have := hb2 i j hij (neg_lt_neg h); omega
end

-- forge:entry r3_fermat_fourth_pow_sub_ne_sq kind=proved origin=conjecture
section
/- Fermat: x^4 - y^4 = z^2 has no integer solutions with yz ≠ 0 (equivalently, no Pythagorean triangle has square area). Mathlib only has the companion not_fermat_42 (a^4 + b^4 ≠ c^2). Proof idea: infinite descent on x: reduce to gcd(x,y)=1; if z odd then (z, y^2, x^2) is a primitive Pythagorean triple, parametrize x^2 = m^2+n^2, y^2 = m^2-n^2 giving m^4 - n^4 = (xy)^2 with smaller m; if z even then y^2 = m^2-n^2... z = 2mn, x^2 = m^2+n^2 with m, n squares-times-units leading again to a smaller solution (or to not_fermat_42). -/
theorem r3_fermat_fourth_pow_sub_ne_sq (x y z : ℤ) (hy : y ≠ 0) (hz : z ≠ 0) : x ^ 4 - y ^ 4 ≠ z ^ 2 := by
  revert x y z
  have H : ((∀ x y z : ℤ, Int.gcd x y = 1 → y ≠ 0 → z ≠ 0 → x ^ 4 - y ^ 4 ≠ z ^ 2) →
        ∀ x y z : ℤ, y ≠ 0 → z ≠ 0 → x ^ 4 - y ^ 4 ≠ z ^ 2) ∧
      (∀ x y z : ℤ, Int.gcd x y = 1 → y % 2 = 1 → z ≠ 0 → x ^ 4 - y ^ 4 = z ^ 2 →
        ∃ m n w : ℤ, |m| < |x| ∧ Int.gcd m n = 1 ∧ n ≠ 0 ∧ w ≠ 0 ∧ m ^ 4 - n ^ 4 = w ^ 2) ∧
      (∀ x y z : ℤ, Int.gcd x y = 1 → y % 2 = 0 → y ≠ 0 → x ^ 4 - y ^ 4 = z ^ 2 →
        ∃ a b : ℤ, x ^ 2 = (2 * a ^ 2) ^ 2 + (b ^ 2) ^ 2 ∧ a ≠ 0 ∧ Int.gcd (2 * a ^ 2) (b ^ 2) = 1) ∧
      (∀ x a b : ℤ, a ≠ 0 → Int.gcd (2 * a ^ 2) (b ^ 2) = 1 →
        x ^ 2 = (2 * a ^ 2) ^ 2 + (b ^ 2) ^ 2 →
        ∃ c d w : ℤ, |c| < |x| ∧ Int.gcd c d = 1 ∧ d ≠ 0 ∧ w ≠ 0 ∧ c ^ 4 - d ^ 4 = w ^ 2) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · (first | exact Mathlib2.r3_fermat_fourth_pow_sub_ne_sq_s1h1v1 | apply Mathlib2.r3_fermat_fourth_pow_sub_ne_sq_s1h1v1 <;> assumption | simpa using Mathlib2.r3_fermat_fourth_pow_sub_ne_sq_s1h1v1)
    · (first | exact Mathlib2.r3_fermat_fourth_pow_sub_ne_sq_s1h2 | apply Mathlib2.r3_fermat_fourth_pow_sub_ne_sq_s1h2 <;> assumption | simpa using Mathlib2.r3_fermat_fourth_pow_sub_ne_sq_s1h2)
    · (first | exact Mathlib2.r3_fermat_fourth_pow_sub_ne_sq_s1h3 | apply Mathlib2.r3_fermat_fourth_pow_sub_ne_sq_s1h3 <;> assumption | simpa using Mathlib2.r3_fermat_fourth_pow_sub_ne_sq_s1h3)
    · (first | exact Mathlib2.r3_fermat_fourth_pow_sub_ne_sq_s1h4 | apply Mathlib2.r3_fermat_fourth_pow_sub_ne_sq_s1h4 <;> assumption | simpa using Mathlib2.r3_fermat_fourth_pow_sub_ne_sq_s1h4)
  obtain ⟨h_red, h_odd, h_even1, h_even2⟩ := H
  have h_prim : ∀ N : ℕ, ∀ x y z : ℤ, |x| ≤ (N : ℤ) → Int.gcd x y = 1 → y ≠ 0 → z ≠ 0 →
      x ^ 4 - y ^ 4 ≠ z ^ 2 := by
    intro N
    induction N with
    | zero =>
      intro x y z hx hg hy hz he
      have hx0 : x = 0 := abs_nonpos_iff.mp (by simpa using hx)
      subst hx0
      have h4 : 0 < y ^ 4 := by positivity
      nlinarith [sq_nonneg z]
    | succ N ih =>
      intro x y z hx hg hy hz he
      have hx' : |x| ≤ (N : ℤ) + 1 := by push_cast at hx; exact hx
      rcases Int.emod_two_eq_zero_or_one y with h0 | h1
      · obtain ⟨a, b, hx2, ha, hab⟩ := h_even1 x y z hg h0 hy he
        obtain ⟨c, d, w, hlt, hcd, hd, hw, hcdw⟩ := h_even2 x a b ha hab hx2
        exact ih c d w (Int.le_of_lt_add_one (lt_of_lt_of_le hlt hx')) hcd hd hw hcdw
      · obtain ⟨m, n, w, hlt, hmn, hn, hw, hmnw⟩ := h_odd x y z hg h1 hz he
        exact ih m n w (Int.le_of_lt_add_one (lt_of_lt_of_le hlt hx')) hmn hn hw hmnw
  exact h_red (fun x y z hg hy hz => h_prim x.natAbs x y z (by simp) hg hy hz)
end

-- forge:entry sophie_germain_gt_three_mod_six kind=proved origin=conjecture
section
/- 大于 3 的 Sophie Germain 素数模 6 余 5 -/
theorem sophie_germain_gt_three_mod_six (p : ℕ) (hp : is_sophie_germain_prime p) (h3 : 3 < p) : p % 6 = 5 := by
  obtain ⟨hp1, hp2⟩ := hp
  have h2 : p % 2 ≠ 0 := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp1).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  have h3' : p % 3 ≠ 0 := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp1).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  have h4 : p % 3 ≠ 1 := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp2).mp (Nat.dvd_of_mod_eq_zero (by omega))
    omega
  omega
end

-- forge:entry alg_unique_right_inverse_is_left_inverse kind=proved origin=conjecture
section
/- In a ring, if a has a unique right inverse b then b is also a left inverse — apply uniqueness to c = b + (1 - b*a), which satisfies a*c = 1. -/
theorem alg_unique_right_inverse_is_left_inverse (R : Type*) [Ring R] (a b : R) (h : a * b = 1) (hu : ∀ c : R, a * c = 1 → c = b) : b * a = 1 := by
  have h1 : a * (b + (1 - b * a)) = 1 := by
    rw [mul_add, mul_sub, ← mul_assoc, h]
    simp
  have h2 := hu _ h1
  have h3 : 1 - b * a = 0 := by simpa using h2
  exact (sub_eq_zero.mp h3).symm
end

-- forge:entry ana_tendsto_quadratic_ratio kind=proved origin=conjecture
section
/- (n^2+1)/(2n^2+3) tends to 1/2 — divide numerator and denominator by n^2 and use 1/n^2 → 0, or bound |difference| = 1/(2(2n^2+3)) and squeeze. -/
theorem ana_tendsto_quadratic_ratio : Filter.Tendsto (fun n : ℕ => (((n : ℝ)) ^ 2 + 1) / (2 * ((n : ℝ)) ^ 2 + 3)) Filter.atTop (nhds (1 / 2)) := by
  have h : Filter.Tendsto (fun n : ℕ => (1/2:ℝ) - (1/2) * (2*(n:ℝ)^2+3)⁻¹) Filter.atTop (nhds (1/2 - (1/2)*0)) := by
    refine tendsto_const_nhds.sub (tendsto_const_nhds.mul ?_)
    apply tendsto_inv_atTop_zero.comp
    apply Filter.tendsto_atTop_add_const_right
    apply Filter.Tendsto.const_mul_atTop (by norm_num)
    exact (Filter.tendsto_pow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h2 : (1/2:ℝ) - 1/2*0 = 1/2 := by norm_num
  rw [h2] at h
  refine h.congr (fun n => ?_)
  have : (2*(n:ℝ)^2+3) ≠ 0 := by positivity
  field_simp
  ring
end

-- forge:entry alg_three_consecutive_pow_mul_comm kind=proved origin=conjecture
section
/- If (ab)^i = a^i b^i for three consecutive exponents i then the group is abelian (Herstein) — from n and n+1 get a^n b = b a^n, from n+1 and n+2 get a^(n+1) b = b a^(n+1), then cancel. -/
theorem alg_three_consecutive_pow_mul_comm_aux1 (G : Type*) [Group G] (n : ℕ) (h0 : ∀ a b : G, (a * b) ^ n = a ^ n * b ^ n) (h1 : ∀ a b : G, (a * b) ^ (n + 1) = a ^ (n + 1) * b ^ (n + 1)) : ∀ a b : G, b ^ n * a = a * b ^ n := by
  intro a b
  have h := h1 a b
  rw [pow_succ (a * b), h0, pow_succ a, pow_succ b] at h
  have h' : a ^ n * (b ^ n * a) * b = a ^ n * (a * b ^ n) * b := by
    simpa [mul_assoc] using h
  exact mul_left_cancel (mul_right_cancel h')

theorem alg_three_consecutive_pow_mul_comm (G : Type*) [Group G] (n : ℕ) (h0 : ∀ a b : G, (a * b) ^ n = a ^ n * b ^ n) (h1 : ∀ a b : G, (a * b) ^ (n + 1) = a ^ (n + 1) * b ^ (n + 1)) (h2 : ∀ a b : G, (a * b) ^ (n + 2) = a ^ (n + 2) * b ^ (n + 2)) : ∀ a b : G, a * b = b * a := by
  intro a b
  have k0 := alg_three_consecutive_pow_mul_comm_aux1 G n h0 h1 a b
  have k1 := alg_three_consecutive_pow_mul_comm_aux1 G (n + 1) h1 h2 a b
  rw [pow_succ, mul_assoc, ← mul_assoc a, ← k0, mul_assoc] at k1
  exact (mul_left_cancel k1).symm
end

-- forge:entry ana_hasSum_inv_mul_succ kind=proved origin=conjecture
section
/- The telescoping series sum 1/((n+1)(n+2)) equals 1 — partial sums are 1 - 1/(N+1) by induction; conclude with hasSum_iff_tendsto_nat_of_nonneg. -/
theorem ana_hasSum_inv_mul_succ : HasSum (fun n : ℕ => 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => by positivity)]
  have hs : ∀ N : ℕ, ∑ i ∈ Finset.range N, 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2)) = 1 - 1 / ((N : ℝ) + 1) := by
    intro N
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      field_simp
      ring
  have h : Filter.Tendsto (fun N : ℕ => (1:ℝ) - 1 / ((N : ℝ) + 1)) Filter.atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
  rw [sub_zero] at h
  exact h.congr (fun N => (hs N).symm)
end

-- forge:entry alg_card_two_pow_of_mul_self_eq_one kind=proved origin=conjecture
section
/- A finite group in which every element squares to 1 has order a power of 2 — it is a 2-group (IsPGroup 2), then use IsPGroup.iff_card; or Cauchy's theorem for an odd prime divisor. -/
theorem alg_card_two_pow_of_mul_self_eq_one (G : Type*) [Group G] [Finite G] (h : ∀ g : G, g * g = 1) : ∃ k : ℕ, Nat.card G = 2 ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 G := fun g => ⟨1, by rw [pow_one, pow_two]; exact h g⟩
  exact IsPGroup.iff_card.mp hp
end

-- forge:entry ana_integral_x_mul_exp kind=proved origin=conjecture
section
/- The integral of x e^x over [0,1] is 1 — the antiderivative is (x-1)e^x; apply the fundamental theorem of calculus (integral_eq_sub_of_hasDerivAt). -/
theorem ana_integral_x_mul_exp : (∫ x in (0 : ℝ)..1, x * Real.exp x) = 1 := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun x : ℝ => (x - 1) * Real.exp x) (x * Real.exp x) x := by
    intro x _
    have h := ((hasDerivAt_id x).sub_const 1).mul (Real.hasDerivAt_exp x)
    convert! h using 1
    simp only [id]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_id.mul Real.continuous_exp).intervalIntegrable _ _)]
  simp
end

-- forge:entry alg_rat_pow_ne_two kind=proved origin=conjecture
section
/- X^n - 2 has no rational root for n ≥ 2 — rational root theorem / compare 2-adic valuations: n * v_2(q) = 1 is impossible. -/
theorem alg_rat_pow_ne_two (n : ℕ) (hn : 2 ≤ n) (q : ℚ) : q ^ n ≠ 2 := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : q ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at h
    norm_num at h
  have h1 : padicValRat 2 (q ^ n) = (n : ℤ) * padicValRat 2 q := padicValRat.pow q
  have h2 : padicValRat 2 ((2 : ℕ) : ℚ) = 1 := padicValRat.self (by norm_num)
  rw [h] at h1
  norm_num at h2
  rw [h2] at h1
  have h3 : (n : ℤ) ∣ 1 := ⟨_, h1⟩
  have h4 := Int.le_of_dvd one_pos h3
  omega
end

-- forge:entry ana_integral_x_mul_sin kind=proved origin=conjecture
section
/- The integral of x sin x over [0,π] is π — the antiderivative is sin x - x cos x; apply the fundamental theorem of calculus. -/
theorem ana_integral_x_mul_sin : (∫ x in (0 : ℝ)..Real.pi, x * Real.sin x) = Real.pi := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) Real.pi, HasDerivAt (fun x : ℝ => Real.sin x - x * Real.cos x) (x * Real.sin x) x := by
    intro x _
    have h := (Real.hasDerivAt_sin x).sub ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x))
    convert! h using 1
    simp only [id]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_id.mul Real.continuous_sin).intervalIntegrable _ _)]
  simp
end

end Mathlib2
