/-
 ===============================================================
    SUM OF NATURAL NUMBERS SQUARED
 ===============================================================
-/

import Mathlib

def sumSquares : Nat → Nat
  | 0 => 0
  | (n + 1) => sumSquares n + (n + 1) ^ 2

theorem sumOfNat (n : Nat) :
  6 * (sumSquares n) = n * (n + 1) * (2 * n + 1) := by

    induction n with
      | zero => rfl

      | succ k hyp =>
        simp[sumSquares]

        rw[Nat.left_distrib]
        rw[hyp]

        ring
