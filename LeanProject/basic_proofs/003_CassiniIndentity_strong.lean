import Mathlib.Tactic

def F : Nat → Int
  | 0 => 0
  | 1 => 1
  | m + 1 => (F (m - 1)) + (F m)

lemma unfold (k : Nat) (ok: k > 0):
  F (k + 1) = (F (k - 1) + F k) := by

  cases k with
  | zero =>
    contradiction
  | succ j =>
    simp [F]



lemma F_sub_mid (n : Nat) (ok : n >= 1) :
  F n = (F (n + 1)) - (F (n - 1)) := by
    cases n with
    | zero =>
      contradiction
    | succ k =>
      simp [F]

lemma F_sub_low (n : Nat) :
  (F (n - 1)) = (F (n + 1)) - (F n) := by sorry

lemma rearrange_sub (k : ℕ) (h : k ≥ 1) : (k - 1) + a = (k + a) - 1 := by
  rw [Nat.sub_add_comm h]

theorem Cassini (n : Nat) :
  ((F n) * (F (n + 2)) - (F (n + 1)) ^ 2) = (-1) ^ (n + 1) := by

    -- Strong induction on n
    induction n using Nat.strong_induction_on with
    | h n ih =>

      -- FRIST CASE:  n = 0
      by_cases h : n = 0
      ·
        -- Base Case: n = 0
        -- substitute n = 0 into the proposition
        subst n
        -- arithmetic verification
        norm_num [F]

      ·
        cases n with
        | zero => contradiction
        | succ k =>
        have ih1 := ih (k - 1) (by omega)
        rw [rearrange_sub k (by sorry)] at ih1
        rw [rearrange_sub k (by sorry)] at ih1
        norm_num at ih1

        have hk1 : k + 1 >= 1 := by
          omega
        have hk0' : k > 0 := by
          sorry
        have hk1' : k + 1 > 0 := by
          omega
        have hk2' : k + 2 > 0 := by
          omega

        change F (k + 1) * F (k + 3) - F (k + 2) ^ 2 = (-1) ^ (k + 2)
        -- Use the definition of F to simplify the goal
        rw [unfold k hk0']
        rw [unfold (k + 1) hk1']
        rw [unfold (k + 2) hk2']
        norm_num
        ring_nf
        rw [Nat.add_comm 1 k]
        rw [Nat.add_comm 2 k]

        nth_rewrite 2 [F_sub_mid (k + 1) hk1]

        simp only [Nat.add_assoc, Nat.add_sub_cancel]
        norm_num

        ring_nf
        rw [Nat.add_comm 1 k]
        rw [Nat.add_comm 2 k]

        rw [unfold (k + 1) hk1']
        norm_num
        nth_rewrite 2 [F_sub_low k]
        ring_nf

        rw [Nat.add_comm 1 k]

        rw [ih1]
