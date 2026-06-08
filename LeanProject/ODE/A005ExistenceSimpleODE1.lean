/-
 ===============================================================
    EXISTENCE OF y(t) = e^{at} -- Version 1
 ===============================================================
-/
import Mathlib

-- EXISTENCE
theorem existence_simple_ode (a x0 : ℝ) :
  -- define a function x : ℝ → ℝ
    -- x(t) = e^(at) * x0
  let x : ℝ → ℝ := fun t => Real.exp (a * t) * x0

  -- Then x satisfies the differential equation x'(t) = a * x(t)
  -- for every t, and the initial condition x(0) = x0.
  (∀ t, HasDerivAt x (a * x t) t) ∧ x 0 = x0 := by

  -- Initial Goal:
    /-
    let x := fun t => Real.exp (a * t) * x0;
    (∀ (t : ℝ), HasDerivAt x (a * x t) t) ∧ x 0 = x0
    -/

  -- Replaces every instance of x in the goal with its definition
  dsimp
  -- New Goal:
    /-
    (∀ (t : ℝ),
      HasDerivAt (fun t => Real.exp (a * t) * x0)
        (a * (Real.exp (a * t) * x0)) t)
      ∧ Real.exp (a * 0) * x0 = x0
    -/
  --
  --

  -- Breaks down the conjunction into two separate goals
  constructor
  /-
  Goal 1:
    ∀ (t : ℝ),
      HasDerivAt (fun t => Real.exp (a * t) * x0)
        (a * (Real.exp (a * t) * x0)) t
  Goal 2:
    Real.exp (a * 0) * x0 = x0
  -/

  · intro t
    -- prove Goal 1
    -- x(t) has a derivative a*x(t) at t

    -- h1: derivative of a*t at t is a
    have h1 : HasDerivAt (fun t : ℝ => a * t) a t := by
      /-
      hasDerivAt_id t is a built in lemma:
        the derivative of the identity function (fun t => t)
        at t is 1.

      Since a * t is a constant multiple of the identity function,
      we use the fact that the derivative of a constant times a
      function is the constant times the derivative of the function.
      -/
      simpa using (hasDerivAt_id t).const_mul a
    -- GOAL: h1:
    /-
    HasDerivAt (fun t => a * t) a t
    -/

    -- h2: derivative of exp(a * t) is exp(a * t) * a
    -- obtained by applying the chain rule to exp(u),
    -- where u = a * t and u' = a
    have h2 := (Real.hasDerivAt_exp (a * t)).comp t h1
    -- GOAL: h2:
    /-
    HasDerivAt (Real.exp ∘ HMul.hMul a) (Real.exp (a * t) * a) t
    -/

    -- Take h2 and multiply both sides by constant x0 to get an expression
    -- for teh derivative of x(t) = exp(a * t) * x0
    have h3 := h2.mul_const x0
    -- GOAL: h3:
    /-
    HasDerivAt (fun y => (Real.exp ∘ HMul.hMul a) y * x0)
      (Real.exp (a * t) * a * x0)
      t
    -/

    -- Simplify h3 using
      -- the definition of function composition
      -- properties of multiplication
    simpa [Function.comp_def, mul_assoc, mul_left_comm, mul_comm] using h3

  ·
    -- prove Goal 2
    -- x 0 = x0

    -- Simplify a * 0 = 0, exp 0 = 1, and 1 * x0 = x0
    simp
    -- x0 = x0 so we are done.
