import Mathlib.Data.Nat.Init
import Lean.Elab.Tactic.Omega

theorem demo_add_zero : ∀ n : Nat, n + 0 = n := by omega
theorem demo_double_zero : ∀ n : Nat, (n + 0) + 0 = n := by
  intro n
  simp only [demo_add_zero]
theorem demo_counterexample : ¬ (∀ n : Nat, n + 1 = n) := by
  intro h
  have h0 := h 0
  omega

#print axioms demo_add_zero
#print axioms demo_double_zero
#print axioms demo_counterexample
