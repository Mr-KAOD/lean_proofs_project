import Mathlib.Tactic

def sumTo : Nat → Nat
  | 0 => 0
  | (n + 1) => sumTo n + (n + 1)

theorem sumOfNat (n : Nat) :
  2 * (sumTo n) = n * (n + 1) := by

    induction n with
      | zero => rfl

      | succ k hyp =>
        simp[sumTo]

        rw[Nat.left_distrib]
        rw[hyp]

        ring
