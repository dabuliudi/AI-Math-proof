/-
Optlib (optsuite, https://github.com/optsuite/optlib, commit 5da27c5f95aa6a8a45b8c14b968ade4c13ff18c3),
the KL property and block coordinate descent (BCD) part, ported from Lean/Mathlib v4.13.0 to v4.33.1.
Copyright of the original files belongs to their authors; released under Apache 2.0 (see Optlib/LICENSE).
-/
import Optlib.Convex.BanachSubgradient
import Optlib.Differential.Calculation
import Optlib.Differential.Lemmas
import Optlib.Convex.ConvexFunction
import Optlib.Convex.Subgradient
import Optlib.Optimality.OptimalityConditionOfUnconstrainedProblem
import Optlib.Function.Lsmooth
import Optlib.Convex.StronglyConvex
import Optlib.Function.MinimaClosedFunction
import Optlib.Function.Proximal
import Optlib.Differential.Subdifferential
import Optlib.Function.KL
import Optlib.Algorithm.BCD.Scheme
import Optlib.Algorithm.BCD.Convergence
