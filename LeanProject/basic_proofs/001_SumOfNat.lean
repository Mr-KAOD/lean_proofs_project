import Mathlib.Tactic

def sumTo (n : Nat) :=
  match n with
-- recursive definition of the sum of natural numbers
-- 0 + 1 + 2 + 3 + ... + n
  -- n = 0 (base)
    -- 0 = 0
  | 0 => 0
  -- Recursive
    -- (n + 1) = (0 + 1 + 2 + ... + n) + (n + 1)
  | k + 1 => (sumTo k) + (k + 1)

theorem sumNat (n : Nat) :
  -- We want to prove that sum of n natural numbers is n(n+1)/2
    -- which we will express as 2*sum = n(n+1)
  2 * (sumTo n) = n * (n + 1) := by
  -- we will perform induction on n
  induction n with
    -- Base case: zero
      -- WORD zero to respect the original definition of Nat
        -- zero is a Nat, succ k is a Nat
    | zero => rfl

    -- Inductive Step based on the recursive definition of Nat
      -- show that n = k + 1 holds assuming the
      -- induction hypothesis (ih) holds for n = k
        -- ih: 2 * (sumTo k) = k * (k + 1)
        -- Goal: 2 * (sumTo (k + 1)) = (k + 1) * ((k + 1) + 1)
    | succ k ih =>

      -- use the definition of sumTo to simplify the goal
      -- New Goal: 2 * (sumTo k + (k + 1)) = ...
      simp [sumTo]

      -- rewrite the left side using the distributive property
      -- New Goal: (2 * (sumTo k)) + 2 * (k + 1) = ...
      rw [Nat.left_distrib]

      -- Rewrite all instances of the inductive hypothesis in the current goal
      -- New Goal: (k * (k + 1)) + 2 * (k + 1) = ...
      rw [ih]

      -- algebraic simplification for both sides
      ring
