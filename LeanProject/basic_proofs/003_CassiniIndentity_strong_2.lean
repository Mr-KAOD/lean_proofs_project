/-
 ===============================================================
    CASSINI'S IDENTITY (STRONG INDUCTION) -- Version 2
 ===============================================================
-/
import Mathlib.Tactic

def F : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | m + 2 => F (m + 1) + F (m)

theorem Cassini (n : ℕ) :
  F (n + 2) * F n - F (n + 1) ^ 2 = (-1) ^ (n + 1) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases n with _ | _ | k
      · -- Base case: n = 0
        norm_num [F]
      · -- Base case: n = 1
        norm_num [F]
      · -- Induction step: n = k + 2
        -- Completely unfold into F(1 + k) and F(k)
        simp [F]

        -- Algebraic simplification that results in the following
        -- F (1 + k) * F k - F (1 + k) ^ 2 + F k ^ 2 = -(-1) ^ k
        ring_nf

        -- Induction Hypothesis
        -- ih : ∀ m < k+2, Cassini(m)
        -- Define ihk as the induction hypothesis for m = k
          -- Then we can use it to rewrite the current goal
        have ihk := ih k (by omega)

        -- Completely unfold into F(1 + k) and F(k)
        simp [F] at ihk
        -- Algebraic simplification that results in the following
        -- F (1 + k) * F k - F (1 + k) ^ 2 + F k ^ 2 = -(-1) ^ k
        ring_nf at ihk

        -- The induction hypothesis and the current goal are the same
        -- so we can rewrite the current goal using the induction hypothesis
        exact ihk

        -- Done
