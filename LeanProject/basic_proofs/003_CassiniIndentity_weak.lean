/-
 ===============================================================
    CASSINI'S IDENTITY
 ===============================================================
-/
import Mathlib.Tactic

def F : Nat → Int
-- We define Fibonacci numbers as F_0 = 0, n=0; F_1 = 1, n=1; and F_{n+1} = F_{n} + F{n-1}, n>1.
  | 0 => 0
  | 1 => 1
-- However, we are changing classic definition when n>1 from
  -- F_{n+1} = F_{n} + F{n-1}
-- to
  -- F_{n+2} = F_{n+1} + F{n}
-- This avoids circular argumets such as n = 1 is F_{2} = F_{1} + F{0} that gives us
-- F_{2} = 1 wich is true for the second case and third case.
  | m + 2 => F (m + 1) + F (m)

-- This lemma does what the definition does when n>1 but applied to F (k+3).
lemma F_for_k_plus_3 (k : Nat) : F (k + 3) = F (k + 2) + F (k + 1) := by rfl

theorem cassinis_identity (n : Nat) :
-- We want to prove Cassini's Indentity in which
  -- F_{n+1} * F_{n-1} - (F_{n+1})^2 = (-1)^n
-- but because Induction tactic first case only works with zero as its first case
-- we moved one position ahead for Cassini's Identity.
F (n + 2) * F (n) - F (n + 1) ^2 = (-1) ^(n + 1) := by
  induction n with
    /-
    -- Base case P(0)
    -/
    | zero => rfl
    /-
    -- Induction step
    -/
      -- ih => Induction Hypotesis
    | succ k ih =>
      -- This succesor theorem (Nat.succ_add_eq_add_succ) states that n.succ = n + 1
      -- We do this to be able to use arithmetic operations with (n + 1) instead of succ k
      rw [Nat.succ_add_eq_add_succ] at *

      -- We are unfolding
      -- F (k + 3) * F (k + 1) - F (k + 2) ^ 2 = (F (k + 2) + F (k + 1)) * F (k + 1) - F (k + 2) ^ 2
      -- using lemma F_for_k_plus_3.
      rw [F_for_k_plus_3]

      have h1 : (F (k + 2) + F (k + 1)) * F (k + 1) - F (k + 1 + 1) ^ 2 = F (k + 1) ^ 2 - F (k + 2) * (F (k + 2) - F (k + 1)) := by ring

      have h2 : F (k + 2) - F (k + 1) = F (k)  := by
        -- To get the form of the induction hypotesis
        -- we rewrite F (k + 2) - F (k + 1) = F (k + 1) - F (k)
        -- which gives us (F (k + 1) - F (k)) - F (k + 1).
        rw [F]
        omega

      rw [h1, h2]     -- We use h1 and h2 to adjust the current goal.

      have h3 : F (k + 1) ^2 - F (k + 2) * F (k) = - (F (k + 2) * F (k) - F (k + 1) ^2)  := by
        omega

      rw [h3]         -- We use h3 to adjust the current goal.
      -- Now we have - (F (k + 2) * F (k) - F (k + 1) ^2) that is -(ih).
      rw [ih]

      have h4 : -(-1) ^ (k + 1) = (-1) ^(k + 2) := by
        ring

      rw [h4]
-- ======================================================================================
/-
--> This is was the first attempt of the proof using tactics as conv_lhs trying to do
    all the algebra manually step-by-step. Even though the proof above was done manualy
    I akip several algebra steps.

    | succ k ih =>
      have h : F (k + 2) * F k - F (k + 1) ^ 2 = F k ^ 2 - F (k + 1) * (F (k + 1) - F k) := by
        simp [F]
        ring
      rw [ih] at h
      rw [F]
      ring_nf
      rw [ih]

    | succ k ih =>
      -- use conv_lhs to operate only in the left hand side of the equation
      conv_lhs =>
        -- congr creates as many targets as there are arguments
        congr
        -- Divides in two terms (branches) separated by the mean operation (subtraction)
        -- First branch: F (k + 2)*(F k)
        -- Second branch: (F (k + 1)) ^ 2
        · congr
          -- We want to separate the product F (k + 2)*(F k)
          -- First term: F (k + 2)
          -- Second term: (F k)
          · rw [F]
          · skip
        · skip
        conv_lhs =>
        -- We continue the process with the whole term resulting from previous congr
        -- (F (k + 1) + F (k)) * (F (k)) - (F (k + 1)) ^ 2
          congr
          · rw [mul_comm]
            simp [mul_add]
          · skip
        -- The expression so far is
        -- (F (k)) * (F (k + 1)) + F (k) * F (k) - (F (k + 1)) ^ 2

        have h : (F k) * (F (k+1)) + (F k) * (F k) - (F (k+1))^2 = (F k)^2 - (F (k+1)) * ((F (k+1)) - (F k)) := by ring_nf
        -- We already aprove the identity using ring tactic
        -- (F (k)) * (F (k + 1)) + (F (k)) * (F (k)) - (F (k + 1)) ^ 2
        rw [h]
-/
