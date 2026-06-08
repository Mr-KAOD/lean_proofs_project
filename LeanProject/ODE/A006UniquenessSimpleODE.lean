/-
 ===============================================================
    UNIQUENESS OF y(t) = e^{at}
 ===============================================================
-/

import Mathlib
import LeanProject.ODE.A005ExistenceSimpleODE2

theorem uniqueness_simple_ode (a x₀ : ℝ):
-- ∀ has two sides: building it (proving a universal statement) and
-- destroying it (using one).
-- Use of the tactic for all (∀):
  -- Structure: ∀ x : T, P x
  -- it means that "for every x of type T, P x holds..."
   ∀(y : ℝ → ℝ),
      (∀t, HasDerivAt y (a * y t) t ∧ y 0 = x₀) →
      (∀t, y t = Real.exp (a * t) * x₀) := by

   intro y           -- Introduction of y because of ∀(y : ℝ → ℝ)
   intro hy          -- Introduction of hy because of →
   intro t           -- Introduction of t because of ∀t
   let f := Real.exp (a * t) * x₀
