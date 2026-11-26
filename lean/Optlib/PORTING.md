# Porting notes

The KL + BCD part of Optlib (optsuite/optlib, commit 5da27c5f95aa6a8a45b8c14b968ade4c13ff18c3, Apache-2.0) was ported from Lean/Mathlib v4.13.0 to v4.33.1, one file at a time in dependency order, by Claude Opus 5.5 agents.

Verification:
- `lake build Optlib` succeeds; no `sorry`, `admit`, `native_decide` or new `axiom`.
- `#print axioms` for `Convergence_to_critpt` and `Limited_length`: only `propext`, `Classical.choice`, `Quot.sound`.
- All 309 declarations of the original 14 files are present under the same names. 257 statements are textually identical; the other 52 changed only through Mathlib API changes: `∑ x in s` → `∑ x ∈ s` (bodies already parenthesised, precedence unchanged), `inner` → `inner ℝ`, `WithLp` became a structure (`z.1` → `z.fst`, explicit `WithLp.toLp 2`), and `LinearOrderedRing` → `Ring` + `LinearOrder` + `IsStrictOrderedRing`.

Per-file notes from the porting agents follow.

## Algorithm/BCD/Convergence.port.md

# Port note: Optlib.Algorithm.BCD.Convergence (Mathlib v4.13.0 → v4.33.1)

`lake build Optlib.Algorithm.BCD.Convergence` succeeds with no errors.

- The file has no `sorry`, `admit`, `axiom` or `native_decide`.
- `#print axioms Convergence_to_critpt` lists only `propext`, `Classical.choice` and `Quot.sound`.
- Every declaration is kept, with the same name, in the same order.

## Statements whose text changed (old → new)

All of these changes come from one Mathlib change: `WithLp p V` is now a one-field structure, not a type synonym. `Scheme.port.md` uses the same convention.

- `f_subdiff_block`:
  - The pairs `⟨u, v⟩` and `⟨x, y⟩` used as `WithLp 2 (E × F)` became `WithLp.toLp 2 (u, v)` and `WithLp.toLp 2 (x, y)`.
  - `z.1` / `z.2` became `z.fst` / `z.snd`.
- `fconv`: `f (alg.z (α n)).1` and `f z_.1` became `.fst`.
- `gconv`: `g (alg.z (α n)).2` and `g z_.2` became `.snd`.
- `Limited_length`: the deprecated big-operator syntax `∑ k in …` became `∑ k ∈ …`. This is notation only.

None of these changes the meaning of a statement.

`EMetric.infEdist` is kept in the statements of `infEdist_bound` and `limitset_property_2`, so they match `Optlib.Function.KL`. It is now a deprecated alias of `Metric.infEDist`, and these uses produce deprecation warnings only.

## Proof changes

- `f_subdiff_block`: `𝓝` on `WithLp` is no longer the product filter by defeq. The proof now pulls `Eventually.prod_nhds` back along the continuous map `WithLp.ofLp` (`WithLp.prod_continuous_ofLp`).
- `Sufficient_Descent1`: local `have`s now write `H (WithLp.toLp 2 (x, y))` instead of `H (x, y)`.
- `Ψ_subdiff_bound`:
  - The two block bounds `h1` / `h2` were rewritten.
  - They now use `grad_fst_eq` / `grad_snd_eq` with `WithLp.add_fst` / `WithLp.sub_fst` (and the `snd` versions), and `norm_prod_left_zero`.
  - The old proof relied on `Prod.fst_sub` and on pair casts into `WithLp`, which no longer work.
- `fconv` / `gconv`:
  - The convergence of the components now comes from `WithLp.continuous_fst` / `continuous_snd` (via `fun_prop`) instead of `Tendsto.fst_nhds`.
  - The gradient bounds use `z ↦ grad_fst H z.snd z.fst` on the compact ball, with `fst_norm_le_prod_L2` / `snd_norm_le_prod_L2`.
- `limitset_property_3`:
  - Proof-internal uses moved to `Metric.infEDist` and its lemmas.
  - Membership in the closed set `A` / `B` now comes from `IsClosed.closure_eq`.
- Lemma renames:
  - `mul_le_mul_left` became `le_of_mul_le_mul_left`.
  - `mul_lt_mul_left` became `mul_lt_mul_iff_right₀`.
  - `div_lt_div_right` became `div_lt_div_iff_of_pos_right`.
  - `le_of_eq_of_le'` became `le_of_le_of_eq`.
  - `mapClusterPt_iff` became `mapClusterPt_iff_frequently`.
  - `unbounded_of_tendsto_atBot` became `not_bddBelow_of_tendsto_atBot`.
  - `GCongr.finset_range_subset_of_le` became `Finset.range_subset_range.mpr`.
  - `left_mem_Ici` became `Set.mem_Ici.mpr le_rfl`.
  - `mul_le_mul_right'` was replaced by a `gcongr` step.
- Syntax: `induction'` was removed, so it is now `induction … with | zero | succ`.
- Small tactic fixes:
  - Some `field_simp` / `positivity` steps became explicit `div_pos` / `mul_nonneg` terms.
  - The `summable_of_sum_range_le` call now names its argument `(c := M)`.


## Algorithm/BCD/Scheme.port.md

# Port note: Optlib.Algorithm.BCD.Scheme (Mathlib v4.13.0 → v4.33.1)

`lake build Optlib.Algorithm.BCD.Scheme` succeeds with no errors. The file has no `sorry`, `admit`, `axiom` or `native_decide`. Every declaration is kept, with the same name.

## Why statements changed

`WithLp p V` is now a one-field structure, not a type synonym. Three consequences:

- A pair `(x, y) : E × F` is no longer a term of `WithLp 2 (E × F)`. It is now written `WithLp.toLp 2 (x, y)`.
- `z.1` / `z.2` on `z : WithLp 2 (E × F)` no longer give the blocks. The blocks are now `z.fst` / `z.snd`, which are Mathlib's `WithLp.fst` / `WithLp.snd`.
- `(WithLp.equiv 2 _).symm` still exists and equals `toLp`, so it is kept where it was used.

These follow the same convention as the already-ported `Optlib.Differential.Lemmas`. None of them changes the meaning of a statement.

## Statements whose text changed (old → new)

- `diff_from_l2`:
  - Old: `@Differentiable ℝ _ (E × F) _ _ ℝ _ _ H`, which treated `H` as a function on `E × F` through the old defeq.
  - New: `Differentiable ℝ (fun p : E × F ↦ H (WithLp.toLp 2 p))`.
- `diff_prod₁` / `diff_prod₂`: `fun x ↦ H (x, y)` became `fun x ↦ H (WithLp.toLp 2 (x, y))`, and the same for `y`.
- `grad_fst` / `grad_snd` (defs): `H (t, y)` became `H (WithLp.toLp 2 (t, y))`, and the same for `(x, t)`.
- `grad_comp` (def): `grad_fst H z.2 z.1, grad_snd H z.1 z.2` became `grad_fst H z.snd z.fst, grad_snd H z.fst z.snd`.
- `grad_fst_eq`: `(gradient H z).1 = grad_fst H z.2 z.1` became `(gradient H z).fst = grad_fst H z.snd z.fst`.
- `grad_snd_eq`: changed in the same way, using `.fst` / `.snd`.
- `lip_grad_fst_of_lip` / `lip_grad_snd_of_lip`: `z.1` / `z.2` became `z.fst` / `z.snd` inside the lambda.
- `BCD.ψ` (def): `f z.1 + g z.2 + H z` became `f z.fst + g z.snd + H z`.
- `sub_prod` (private): `((x, y) : WithLp 2 (E × F)) - (x1, y1) = (x - x1, y - y1)` became `toLp 2 (x, y) - toLp 2 (x1, y1) = toLp 2 (x - x1, y - y1)`. It is still `rfl`.
- `BCD.A_k` (def): `(alg.A_kx k, alg.A_ky k)` became `WithLp.toLp 2 (alg.A_kx k, alg.A_ky k)`.
- `BCD.subdiff` (def): `gradient H (alg.x (k+1), alg.y (k+1))` became `gradient H (WithLp.toLp 2 (alg.x (k+1), alg.y (k+1)))`.

`comp_norm_le` is unchanged. It is about the plain `E × F` (sup norm), not `WithLp`.

## Proof changes

- `grad_fst_eq` / `grad_snd_eq`:
  - The old proof used `Filter.Eventually.curry_nhds`. That relied on `𝓝` on `WithLp` being the product filter on `E × F` by defeq, which no longer holds.
  - The new proof pulls the little-o bound back along the continuous map `x ↦ toLp 2 (x, z.snd)` (`Tendsto.eventually`). It then splits the inner product with `WithLp.prod_inner_apply`.
- `grad_eq_block_grad`: the proof now uses `WithLp.ext_iff` and `Prod.ext` instead of a `calc` that went through the pair defeq.
- `Proper_Prod`:
  - The new proof shows that the closed ball is contained in the `toLp`-image of a product of closed balls. That image is compact by `WithLp.prod_continuous_toLp`.
  - `Metric.isClosed_ball` became `Metric.isClosed_closedBall`.
- Renames:
  - `Differentiable.prod` became `Differentiable.prodMk`.
  - `differentiable_id'` became `differentiable_fun_id`.
  - `ContDiff.differentiable` now takes `n ≠ 0`, so `Preorder.le_refl 1` became `one_ne_zero`.

## Downstream

`Optlib/Algorithm/BCD/Convergence.lean` uses `alg.z`, `.1`/`.2` and pair casts into `WithLp`. It will need the same `.fst`/`.snd`/`toLp` treatment.


## Convex/BanachSubgradient.port.md

# Port note: Optlib.Convex.BanachSubgradient (v4.13 -> v4.33.1)

No declaration statement text changed. All defs/lemmas/theorems kept with the same names and statements.

## Imports
- `Mathlib.Analysis.NormedSpace.HahnBanach.Separation` -> `Mathlib.Analysis.LocallyConvex.Separation` (module moved).
- `Mathlib.LinearAlgebra.Dual` -> `Mathlib.LinearAlgebra.Dual.Lemmas` (module split; `Module.dualProdDualEquivDual` lives there).
- Added `Mathlib.Analysis.Normed.Operator.NormedSpace`: the operator norm `‖φ‖` on `StrongDual ℝ (E × ℝ)` is no longer pulled in transitively.

## Proof changes
- `ContinuousOn.prod` -> `ContinuousOn.prodMk` (rename; `.prod` now resolves to `Function.prod`).
- `Banach_SubderivWithinAt.Nonempty`: the operator-norm bound for `h` and `key1` were rewritten
  with explicit `calc`/linear arithmetic (via a helper `hgx : g.1 y = φ (y, 0)`), because
  `field_simp` no longer unfolds the `let`-bound `h`/`g` the way it did. `key2₀` limit proofs
  adjusted (explicit type args for `tendsto_one_div_add_atTop_nhds_zero_nat`, `rw` instead of `simp only`).
- Note: in Mathlib v4.33 the hypothesis `φ` from `geometric_hahn_banach_point_open` has type `StrongDual ℝ (E × ℝ)`
  (= `E × ℝ →L[ℝ] ℝ`), same meaning as before.


## Convex/ConvexFunction.port.md

# Port note: Optlib.Convex.ConvexFunction (v4.13 → v4.33.1)

## Statement text changes (meaning unchanged)

Mathlib's `inner` now takes the scalar field as an explicit argument (`inner 𝕜 x y`), so every
`inner (a) (b)` became `inner ℝ (a) (b)`. This affects these statements:

- `Convex_first_order_condition'`, `Convex_first_order_condition_inverse'`,
  `Convex_first_order_condition_iff'`: `inner (f' x) (y - x)` -> `inner ℝ (f' x) (y - x)`
- `Convex_monotone_gradient'`, `monotone_gradient_convex'`, `monotone_gradient_iff_convex'`:
  `inner (f' x - f' y) (x - y)` -> `inner ℝ (f' x - f' y) (x - y)`
- `monotone_gradient_strict_convex`, `strict_convex_monotone_gradient`,
  `strict_convex_iff_monotone_gradient`: the same change

No other statement changed.

## Proof changes

- `InnerProductSpace.toDual_apply` -> `InnerProductSpace.toDual_apply_apply` (renamed)
- `mul_le_mul_right` (the iff version) -> `mul_le_mul_iff_of_pos_right`
- `push_neg at` -> `push Not at` (`push_neg` is deprecated)
- `monotone_gradient_strict_convex`: rewrote the proof of `eq3` with `rw [eq2]` and
  `linear_combination` because the old `ring_nf` normal form changed; `zeq` now ends with `simp [z]`.

## Remaining warnings (not errors)

- `ContinuousLinearMap.coe_sub'` is deprecated (Mathlib suggests `FunLike.coe_sub`).
- A few unused simp arguments.


## Convex/StronglyConvex.port.md

# Port note: Optlib.Convex.StronglyConvex (v4.13 -> v4.33.1)

## Statement text changes (meaning unchanged)
- `Strong_Convex_lower`, `Lower_Strong_Convex`, `Strong_Convex_iff_lower`:
  `inner (f' x - f' y) (x - y)` -> `inner ℝ (f' x - f' y) (x - y)`.
- `Strong_Convex_second_lower`: `inner (f' x) (y - x)` -> `inner ℝ (f' x) (y - x)`.
  Why: Mathlib's `inner` now takes the scalar field `𝕜` as an explicit argument.

## Proof changes
- `stronglyConvexOn_def`: dropped a `simp at this` that no longer makes progress.
- `Strongly_Convex_Unique_Minima`: `push_neg` -> `push Not` (deprecated).
- `strongconvex_of_convex_add_sq`: `field_simp` now clears the `/ 2` itself, so
  `div_le_div_right` (removed) is no longer needed. The algebra in `eq2` is now closed by
  `subst b = 1 - a; ring`, and the last step by `linarith` from `eq4`.


## Convex/Subgradient.port.md

# Port note: Optlib.Convex.Subgradient (v4.13 → v4.33.1)

## Statements whose text changed
None. All declarations keep their names and statements. The edits are all in proofs.
The statements use the file's local `⟪x, y⟫` notation (`@inner ℝ _ _ x y`), which still works.

## Proof changes
- `inner` now takes the scalar field as an explicit argument. In proofs, bare `inner a b` became `inner ℝ a b`
  (`have`/`let`/`calc` terms, the `let S₁` set, and `congrArg (inner ℝ u)`).
- `not_le_of_lt` → `not_le_of_gt`; `nmem_singleton_empty` → `notMem_singleton_empty`.
- `le_of_le_of_eq'` (removed) → `Eq.trans_le (by …) h`.
- `(mul_le_mul_left hc).mpr h` → `mul_le_mul_of_nonneg_left h hc.le`;
  `(mul_lt_mul_right hpos).mpr h` → `mul_lt_mul_of_pos_right h hpos`;
  `mul_le_mul_right` (iff) → `mul_le_mul_iff_left₀`; `mem_setOf` → `mem_setOf_eq`.
- `SubderivWithinAt_eq_gradient`: `unfold HasFDerivAt; rw [hasFDerivAtFilter_iff_tendsto]` →
  `rw [hasFDerivAt_iff_tendsto]`, because the filter form changed to a product filter.
- On ℝ, `inner ℝ g (-x) = g * (-x)` no longer holds by `rfl`; it is now proved by `simp [mul_comm]`.
  `simp [f2]` became `simp [f2, mul_comm]` for the same reason (`RCLike.inner_apply` puts the factors in a different order).
- In `ceq0`, the `field_simp` sequence was rewritten as `have eq : b * (c / (2 * b)) = c / 2 := by field_simp [hb.ne]`.

## Notes
The build still prints deprecation and linter warnings, for example `push_neg`, `ContinuousLinearMap.coe_comp'`
and the unused `unfold` lines. None of them are errors.


## Differential/Calculation.port.md

# Port note: Optlib/Differential/Calculation.lean (v4.13.0 -> v4.33.1)

## Statement text changes
- `HasGradientAtFilter.sum`, `HasGradientWithinAt.sum`, `HasGradientAt.sum`, `gradient_sum`:
  `∑ i in u, ...` -> `∑ i ∈ u, ...` (the `in` big-operator syntax is deprecated). Meaning unchanged.

No other statement changed. All declarations kept with the same names.

## Proof changes
- `HasGradientAtFilter.comp`: `HasGradientAtFilter` now unfolds to `HasFDerivAtFilter … (L ×ˢ pure x)`, and
  `HasDerivAtFilter.comp_hasFDerivAtFilter` no longer takes the point `x` and needs
  `Tendsto (Prod.map f f) …`; this is given as `hL.prodMap (by simp)`.
- `HasGradientAtFilter.sum`: `HasFDerivAtFilter.sum` now concludes about `∑ i ∈ u, A i` (a sum of functions);
  rewritten to the pointwise form with `Finset.sum_fn`.
- `gradient_neg`: `fderiv_neg` is now stated for `-f`; the lambda form is `fderiv_fun_neg`.
- `equiv_lemma_mul`: `simp; congr <;> exact SemilinearMapClass.map_smul_inv …` replaced by
  `rw [map_add, map_smulₛₗ, map_smulₛₗ]; simp`.


## Differential/Lemmas.port.md

# Port note: Optlib.Differential.Lemmas (Mathlib v4.13.0 → v4.33.1)

`lake build Optlib.Differential.Lemmas` succeeds with no errors or warnings. The file has no `sorry`, `admit`, `axiom` or `native_decide`.

## Statements whose text changed (same meaning)

1. **`inner` now takes the scalar field explicitly.** In Mathlib, `inner x y` became `inner 𝕜 x y`. This applies to these statements:
   - `HasGradient_Convergence`, `Convergence_HasGradient`, `HasGradient_iff_Convergence_Point`, `HasGradient_iff_Convergence`
   - `gradient_of_inner_const`
   - `expansion`, `general_expansion`, `lagrange`

   In each one, `inner a b` is now `inner ℝ a b`. Before, the field was `ℝ` by elaboration, so the meaning is the same.
2. **`WithLp` is now a structure, not a type synonym.** In v4.13, `z.1` on `z : WithLp 2 (E × F)` meant the `E` part. In v4.33.1, `z.1` would be `WithLp.ofLp z : E × F`, which has a different norm. The new statements use Mathlib's `WithLp.fst` / `WithLp.snd`:
   - `fst_norm_le_prod_L2`: `‖z.1‖ ≤ ‖z‖` became `‖z.fst‖ ≤ ‖z‖`
   - `snd_norm_le_prod_L2`: `‖z.2‖ ≤ ‖z‖` became `‖z.snd‖ ≤ ‖z‖`
   - `prod_norm_le_block_sum_L2`: `‖z‖ ≤ ‖z.1‖ + ‖z.2‖` became `‖z‖ ≤ ‖z.fst‖ + ‖z.snd‖`
   - `norm_prod_right_zero`: the cast `((x, 0) : WithLp 2 (E × F))` became `WithLp.toLp 2 (x, 0)`
   - `norm_prod_left_zero`: `((0 : E), y)` became `WithLp.toLp 2 ((0 : E), y)`
3. **`instIsBoundedLinearMapL2equiv`:**
   - Old: `instance … : @IsBoundedLinearMap ℝ _ (E × F) _ _ (WithLp 2 (E × F)) _ _ id`
   - New: `theorem … : IsBoundedLinearMap ℝ (WithLp.toLp 2 : E × F → WithLp 2 (E × F))`

   There are two reasons:
   - `id` no longer has type `E × F → WithLp 2 (E × F)`. The canonical identity map is now `WithLp.toLp 2`.
   - `IsBoundedLinearMap` is now a plain `structure`, not a `class`, and Lean rejects `instance` for a non-class type.

   The name and the mathematical content are the same. Code that uses it as a term (e.g. `exact instIsBoundedLinearMapL2equiv` in `Optlib/Algorithm/BCD/Scheme.lean`) still works. Code that relied on instance search for it will not.

## Other changes (imports and proofs only)

- **Imports:**
  - `Mathlib.Topology.Semicontinuous` became `Mathlib.Topology.Semicontinuity.Basic`.
  - Added `Mathlib.Analysis.Calculus.Deriv.MeanValue`, which is where `exists_hasDerivAt_eq_slope` lives now.
- **Renamed or changed Mathlib names:**
  - `rw [LowerSemicontinuousOn]` / `[LowerSemicontinuousWithinAt]` became `lowerSemicontinuousOn_iff` / `lowerSemicontinuousWithinAt_iff`, because these are now abbrevs of `Semicontinuous`.
  - `HasFDerivAt` + `hasFDerivAtFilter_iff_isLittleO` became `hasFDerivAt_iff_isLittleO`. The filter is now `𝓝 x ×ˢ pure x`.
  - `norm_pos_iff'` became `norm_pos_iff`.
  - `div_le_div_right` became `div_le_div_iff_of_pos_right`.
  - `Set.mem_setOf` became `Set.mem_ofPred`.
  - `push_neg` became `push Not`.
- **Proofs rewritten:**
  - The `‖·‖²` gradient computations in `gradient_norm_sq_eq_two_self` and `gradient_of_sq`. The long `rw` chain no longer matched after `ring_nf`, so they now use `norm_sub_sq_real` + `ring`.
  - Small `simp` / `field_simp` fixes.

## Downstream impact

`Optlib/Algorithm/BCD/Scheme.lean` (not yet ported) uses `z.1` / `z.2` on `WithLp` and anonymous-constructor casts into `WithLp`. It will need the same `.fst` / `.snd` / `toLp` treatment.


## Differential/Subdifferential.port.md

# Port note: Optlib.Differential.Subdifferential (v4.13 -> v4.33.1)

## Statement text changes (meaning unchanged)
- Every `inner a b` -> `inner ℝ a b` (15 occurrences, including in
  `differential_fun`, `has_f_subdiff_iff` and other statements and proofs). Why: Mathlib's `inner` now
  takes the scalar field `𝕜` as an explicit argument.

## Other changes
- Import `Mathlib.Data.Real.EReal` -> `Mathlib.Data.EReal.Basic` (module moved).
- `lt_iff_not_le` -> `lt_iff_not_ge` (renamed).
- `f_subdiff_smul`: `(mul_le_mul_left cpos).mp` -> `(mul_le_mul_iff_right₀ cpos).mp`
  (`mul_le_mul_left` now names a different, ordered-monoid lemma).
- Line 244: a `simp` that now makes no progress (goal already closed earlier)
  became `try simp`.

Remaining warnings only (deprecated `Set.mem_setOf`, `push_neg`, unused section
variables); no `sorry`/`admit`/axioms.


## Function/KL.port.md

# Port note: Optlib.Function.KL (Mathlib v4.13.0 -> v4.33.1)

## Statement changes
None. Every def/lemma/theorem keeps its name and statement text.
`EMetric.infEdist` (now deprecated in favour of `Metric.infEDist`) is kept in statements;
it only produces deprecation warnings.

## Proof-only changes
- `Filter.Tendsto.prod_mk_nhds` -> `Filter.Tendsto.prodMk_nhds`.
- `mul_le_mul_left'` (removed) -> `by gcongr` in `const_mul_edist_ge_one`.
- `ENNReal.mul_le_mul_right` (removed) -> `ENNReal.mul_le_mul_iff_left` in `real_geq_ennreal_ofreal_geq`.
- `desingularizing_function_is_nonneg`, `const_mul_special_concave`: `field_simp`/`simp` now
  normalise differently; closing steps rewritten (`positivity`, `inv_pos`, `inv_ne_zero`,
  `simp only [desingularizing_function, mem_setOf_eq]` plus an explicit anonymous constructor).
- `edist_geq_const`: `rw [dist_zero_left] at hv` -> `simp only` (occurrence is under a binder).
- `uniformized_KL_property`:
  - dropped a `push_neg` that now makes no progress;
  - `simp` now turns the `tsum` over the finset subtype into a sum over `attach`, so a local
    `φ_sum_eq : φ_sum = fun c => ∑ x ∈ ht2.toFinset, φ x c` (via `tsum_fintype`,
    `Finset.sum_attach`) is used instead of `simp [φ_sum]`;
  - `deriv_sum` is now stated for `∑ i ∈ u, A i` (a sum of functions), so the lambda form is
    rewritten to that first;
  - `Finset.tsum_subtype'` step replaced with `Finset.mul_sum`.

## Notable
Builds with deprecation/linter warnings only (`push_neg`, `EMetric.infEdist`, `Set.mem_setOf_eq`).
The `sorry`s in the file are in a commented-out block carried over unchanged from the original.


## Function/Lsmooth.port.md

# Port note: Optlib.Function.Lsmooth (v4.13 → v4.33.1)

## Statement text changes (meaning unchanged)

- Every `inner a b` became `inner ℝ a b`. In current Mathlib `inner` takes the scalar
  field `𝕜` as an explicit argument. This touches the statements of:
  `lower_to_lipschitz`, `lipschitz_continuos_upper_bound'`, `convex_to_lower`,
  `lipschitz_to_lower`, `lower_iff_lipschitz`, `lower_iff_lnorm_sub_convex`
  (and inner products inside proofs). The mathematical content is the same real inner product.

No declaration was renamed, removed or weakened. Imports are unchanged.

## Proof fixes

- `InnerProductSpace.toDual_apply` → `InnerProductSpace.toDual_apply_apply`.
- `add_le_add_right` now has its arguments the other way round; that step is replaced by `linarith`.
- In several places `field_simp` / `simp` now closes the goal, or no longer makes progress.
  Leftover `ring_nf` / `left` / `simp` calls were removed or replaced with `rw`, `rfl` or `ring`.
- In `lipschitz_minima_lower_bound`, the last algebra step was re-proved by rewriting
  `y - x = -(1/l) • f' x` and then using `field_simp; ring`.
- In `lipschitz_continuous_upper_bound`, the bound `|g' t - g' 0| ≤ LL * t` is now
  shown by rewriting `glip t 0` directly instead of with `convert`.

Build: `lake build Optlib.Function.Lsmooth` succeeds. The only warnings are unused simp arguments.


## Function/MinimaClosedFunction.port.md

# Port note: Optlib.Function.MinimaClosedFunction (v4.13 -> v4.33.1)

## Statement text changes
- `strong_quasi` binder and the section `variable`: `[LinearOrderedRing 𝕜]` -> `[Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`.
  Why: Mathlib removed the bundled `LinearOrderedRing` class in favour of unbundled order mixins; same meaning.
  Affects `strong_quasi` and `isMinOn_unique` (statements otherwise unchanged).

## Other changes
- Import `Mathlib.Topology.Semicontinuous` -> `Mathlib.Topology.Semicontinuity.Basic` (module moved).
- `sInf_le_sInf_of_forall_exists_le` -> `sInf_le_sInf_of_isCoinitialFor`.
- `Filter.Tendsto.prod_mk_nhds` -> `Filter.Tendsto.prodMk_nhds`.
- `not_le_of_lt` -> `not_le_of_gt`.
- Proofs in `l0` (one step: rewrote the `y < f x` derivation) and `isMinOn_unique` (`Eq.trans_gt` step replaced by `lt_of_lt_of_eq`) adjusted.
- Build emits only a linter warning: unused section variable `[DenselyOrdered F]` in `IsMinOn.of_isCompact_preimage` (pre-existing; left as is to keep the statement unchanged).


## Function/Proximal.port.md

# Port notes: Optlib.Function.Proximal (v4.13 -> v4.33.1)

## Statement text changes
- `proximal_add_linear` (line ~480): `inner a x` -> `inner ℝ a x`.
  Why: in current Mathlib `inner` takes the scalar field explicitly. Same meaning (real inner product).

All other declarations keep their exact statements. The list of declarations is unchanged.

## Other changes
- Import `Mathlib.Topology.Semicontinuous` -> `Mathlib.Topology.Semicontinuity.Basic` (module moved).
- Renames: `continuous_iff_continuousOn_univ` -> `continuousOn_univ` (direction flipped),
  `div_le_div_right` -> `div_le_div_iff_of_pos_right`, `Tendsto.prod_mk_nhds` -> `Tendsto.prodMk_nhds`,
  `mul_le_mul_left` (iff form) -> `mul_le_mul_iff_right₀`.
- `inner a b` inside proofs -> `inner ℝ a b`.
- Proofs rewritten because `field_simp`/`simp` normal forms changed:
  `prox_set_compact_of_convex` (two bound computations), `convex_of_norm_sq` (new direct proof
  using `‖a•u+b•v‖² = a²‖u‖² + 2ab⟪u,v⟫ + b²‖v‖²` and `linear_combination`), `proximal_shift`,
  `proximal_scale` (`positivity`, `sq_abs`), `proximal_add_sq` (`aux` re-proved by expansion and
  `field_simp; ring`; both directions by scaling with `(l+1)⁻¹ > 0`), `prox_iff_subderiv`
  (continuity by `fun_prop`), `prox_iff_subderiv_smul` (reverse direction).
- Membership proofs `pnin` (the epigraph sequence) now use `show g (p c).1 ≤ (p c).2; exact le_rfl`.
- Remaining warnings only (deprecated `Set.mem_setOf`, unused simp args); no `sorry`/axioms.


## Optimality/OptimalityConditionOfUnconstrainedProblem.port.md

# Port note: Optlib.Optimality.OptimalityConditionOfUnconstrainedProblem (v4.13 -> v4.33.1)

## Statement text changes
- `DescentDirection` (def body) and the inner products inside proofs:
  `inner (f' x) d` -> `inner ℝ (f' x) d`.
  Why: Mathlib's `Inner.inner` now takes the scalar field 𝕜 as an explicit argument.
  Meaning unchanged (the real inner product, as before).
- `first_order_convex`, `optimal_no_descent_direction`, `first_order_unconstrained`,
  `first_order_convex_iff`: statements unchanged.

## Proof changes
- `optimal_no_descent_direction`: `simp [g]` before `apply ContinuousOn.inner` now rewrites
  `ContinuousOn _ univ` to `Continuous _`, so `ContinuousOn.inner` no longer applied. Replaced
  with `show ContinuousOn (fun r ↦ inner ℝ (f' (xm + r • d)) d) univ`.

No sorry/axiom/native_decide. Build: `lake build Optlib.Optimality.OptimalityConditionOfUnconstrainedProblem` succeeds (only warnings come from the dependency Optlib.Convex.ConvexFunction).


