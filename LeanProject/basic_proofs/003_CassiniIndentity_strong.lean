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
        have ihk := ih k (by omega)

        simp [F] at ihk
        ring_nf at ihk

        simp [F]
        ring_nf

        exact ihk
