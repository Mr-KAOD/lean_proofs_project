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

   -- We split the hypothesis in two to use them separately when needed
   have hy_deriv : HasDerivAt y (a * y t) t := (hy t).1
   have hy_zero : y 0 = x₀ := (hy t).2

   -- We are defining z as e^{-at}
   let z : ℝ → ℝ := fun s => Real.exp (-(a * s)) * y s

   -- We want to derive z using the product rule and prove it z' = 0

   -- Proof of the derive of the identity function
   have hident : HasDerivAt (fun x : ℝ => a * x) a t := by
      simpa using (hasDerivAt_id t).const_mul a

   -- Proof of the derive of the negative identity function
   have hneg :
      HasDerivAt (-(fun s : ℝ => a * s)) (-a) t := by
      exact hident.neg

   -- Proof of the e^{-at}
   have hexp :
      HasDerivAt
         (fun s : ℝ => Real.exp (-(a * s)))
         (Real.exp (-(a * t)) * (-a))
         t := by
         simpa [Pi.neg_apply] using hneg.exp          -- Pi.neg_apply :(-x) i = -x i

   -- Product rule
   have hprod :
      HasDerivAt
         ((fun s : ℝ => Real.exp (-(a * s))) * y)
         (Real.exp (-(a * t)) * (-a) * y t +
         Real.exp (-(a * t)) * (a * y t))
         t := by
         simpa [mul_assoc] using hexp.mul hy_deriv

   -- Unfolding y(t)
   have hzero :
      -(Real.exp (-(a * t)) * a * y t) +
      Real.exp (-(a * t)) * (a * y t) = 0 := by
      ring

   have hz :
      HasDerivAt
         ((fun s : ℝ => Real.exp (-(a * s))) * y)
         0
         t := by
         simpa [hzero] using hprod
