/-
 ===============================================================
    EXISTENCE OF y(t) = e^{at}
 ===============================================================
-/

import Mathlib

/-
We are proving the existance of the solution y(t) = e^{at} that satifies for all t that y'(t) = ay(t), when y(0) =x_0.
-/

theorem excistence_simple_ode (a x₀ : ℝ) :
-- Use of the tactic exists (∃):
  -- Structure: ∃ x : T, P x
  -- it means that "there exists some x of type T such that P x holds..."
  ∃ (y : ℝ → ℝ), (∀ t, HasDerivAt y (y (t) * a) t) ∧ (y (0) = x₀) := by

  -- Followed by this Lean uses two fields
    -- witness : T -> the actual x
    -- proof : P x -> evidence that P holds for that x
  -- In this case for ∃ (y : ℝ → ℝ) the witness is
  -- y = e^{at}x_0
  use fun t => Real.exp (a * t) * x₀ -- Here the goal changes and y is raplaced by this function
  -- GOAL:
  /-
     (∀ (t : ℝ), HasDerivAt (fun t => Real.exp (a * t) * x₀)
     ((fun t => Real.exp (a * t) * x₀) t * a) t) ∧
     (fun t => Real.exp (a * t) * x₀) 0 = x₀
  -/

  -- Now we need to prove each statement
    -- First: ∀ (t : ℝ), HasDerivAt (fun t => Real.exp (a * t) * x₀)
    -- (a * (fun t => Real.exp (a * t) * x₀) t) t)
  -- and
    --Second: fun t => Real.exp (a * t) * x₀) 0 = x₀
  -- To achieve this, we are using constructor tactic that splits the current goal into its components.
  constructor
  -- Since we are using ^, constructor splits the goal into the witness and the proof.
  · intro t
  -- GOAL 1:
  /-
    ∀ (t : ℝ), HasDerivAt (fun t => Real.exp (a * t) * x₀)
    (Real.exp (a * t) * x₀ * a) t
  -/
  -- Proof of the derivative of e^{at} using Chain Rule
    -- First: We are going to prove that for a function y = ax its derivate y'= a.
    -- For this we are defining the function and using simpa tactic to prove that the
    -- derivative of the identity function is 1 and .const_mul is a lemma that
    -- handles functions, derivatives, integrals, or algebraic structures being multiplied by a constant.
    have h1 : HasDerivAt (fun x : ℝ => a * x) a t := by
      simpa using (hasDerivAt_id t).const_mul a

    -- Second: We want to establish that the derivative of e^x is y' = e^x.
    -- Note that x = at
    have h2 : HasDerivAt Real.exp (Real.exp (a * t)) (a * t) := by
      simpa using Real.hasDerivAt_exp (a * t)

    -- Application of Chain Rule
    have h3 : HasDerivAt (fun x : ℝ => Real.exp (a * x)) (Real.exp (a * t) * a) t := by
      exact h2.comp t h1
      -- We are using HasDerivAt.comp where it is evaluating h1 in h2 at point t.

    -- We add x_0 to the expression
    have h4 : HasDerivAt (fun x : ℝ => Real.exp (a * x) * x₀) ((Real.exp (a * t) * a) * x₀) t := by
      simpa using h3.mul_const x₀

    simpa [mul_assoc, mul_left_comm, mul_comm] using h4
    -- Here GOAL 1 accomplished.

  · simp
  -- GOAL 2:
  /-
    Real.exp (a * 0) * x₀ = x₀
  -/
