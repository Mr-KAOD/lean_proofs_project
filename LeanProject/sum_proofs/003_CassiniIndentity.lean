import Mathlib

def F : Nat → Nat
  | 0 => 0
  | 1 => 1
  | m + 2 => (F m) + (F (m + 1))

theorem Cassini (n : Nat) :
  (((F n) * (F (n + 2)) - (F (n + 1)) ^ 2) : Int ) = (-1) ^ (n + 1) := by

    -- Strong induction on n
    induction n using Nat.strong_induction_on with
    | h n ih =>

      -- Split special case n = 0
      by_cases h : n = 0



#eval F 0
#eval F 1
#eval F 2
#eval F 7
