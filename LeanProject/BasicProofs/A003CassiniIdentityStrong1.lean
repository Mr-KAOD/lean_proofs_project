/-
 ===============================================================
    CASSINI'S IDENTITY (STRONG INDUCTION) -- Version 1
 ===============================================================
-/
import Mathlib.Tactic

def F : Nat → Int
  | 0 => 0
  | 1 => 1
  | m + 2 => F (m + 1) + F (m)

lemma F_for_a_plus_b (a b : ℕ):
  F (a + (b + 2)) = (F (a + (b + 1)) + F (a + b)) := by
  simp [F, Nat.add_assoc]

theorem Cassini (n : Nat) :
  F (n + 2) * F (n) - F (n + 1) ^2 = (-1) ^(n + 1) := by

  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | k
    -- Base case: n=0
    . simp [F]
    -- Base case: n=1
    · simp [F]

    -- Induction Step
    -- Goal  => n = m+2
    ·
    -- Induction Hypotesis definition
      -- Definition of (k + 1) < (k + 2) --> k < n
      have ih_k_plus_1 := ih (k + 1) (by omega)

      -- Unfold over (k + 4)
      rw [F_for_a_plus_b k 2]


      have h1 : (F (k + 3) + F (k + 2)) * F (k + 2) - F (k + 3) ^ 2 = F (k + 2) ^ 2 - F (k + 3) * (F (k + 3) - F (k + 2)) := by ring

      have h2 : F (k + 3) - F (k + 2) = F (k + 1) := by
        -- To get the form of the induction hypotesis
        -- we rewrite F (k + 3) - F (k + 2) = F (k + 2) - F (k + 1)
        -- which gives us (F (k + 2) - F (k + 1)) - F (k + 2).
        rw [F]
        simp

      rw [h1, h2]

      have h3 : F (k + 2) ^ 2 - F (k + 3) * F (k + 1) = -(F (k + 3) * F (k + 1) - F (k + 2) ^ 2) := by ring

      rw [h3]

      rw [ih_k_plus_1]

      have h4 : -(-1) ^ (k + 2) = (-1) ^ (k + 3) := by
        ring

      rw [h4]
