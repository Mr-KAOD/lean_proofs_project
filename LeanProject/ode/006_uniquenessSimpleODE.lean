/-
 ===============================================================
    UNIQUENESS OF y(t) = e^{at}
 ===============================================================
-/

import Mathlib

theorem uniqueness_simple_ode (y : ℝ → ℝ) (a x₀ : ℝ):
-- ∀ has two sides: building it (proving a universal statement) and
-- destroying it (using one).
-- Use of the tactic for all (∀):
  -- Structure: ∀ x : T, P x
  -- it means that "for every x of type T, P x holds..."
   ∀ y, (∀ t, HasDerivAt y (a * y t) t ∧ y 0 = x₀) →
   (∀t, HasDerivAt y (Real.exp (a *  t) *x₀) t) := by
   sorry
