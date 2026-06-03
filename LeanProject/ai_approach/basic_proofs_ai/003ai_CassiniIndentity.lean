/-
 ===============================================================
    CASSINI'S IDENTITY (Claude)
 ===============================================================
-/
import Mathlib

theorem cassini (n : ℕ) (hn : 1 ≤ n) :
    (Nat.fib (n + 1) : ℤ) * Nat.fib (n - 1) - (Nat.fib n : ℤ) ^ 2 = (-1) ^ n := by
  -- We apply strong induction on n.
  induction n using Nat.strong_induction_on with
  | _ n ih => ?_
  -- Dispatch base cases n = 1 and n = 2 by native_decide / norm_num.
  match n, hn with
  -- ── Base case n = 1 ──────────────────────────────────────────────────────
  | 1, _ => native_decide
  -- ── Base case n = 2 ──────────────────────────────────────────────────────
  | 2, _ => native_decide
  -- ── Inductive step n = k + 3 (i.e. n ≥ 3) ───────────────────────────────
  | k + 3, _ =>
    -- Convenient shorthands
    set m := k + 3 with hm_def         -- m = n, just for readability
    -- The strong IH gives us the identity at m-1 and m-2 (both ≥ 1).
    have ih_pred : (Nat.fib m : ℤ) * Nat.fib (m - 2) - (Nat.fib (m - 1) : ℤ) ^ 2
                   = (-1) ^ (m - 1) := by
      apply ih (m - 1)
      · omega
      · omega
    have ih_pred2 : (Nat.fib (m - 1) : ℤ) * Nat.fib (m - 3) - (Nat.fib (m - 2) : ℤ) ^ 2
                    = (-1) ^ (m - 2) := by
      apply ih (m - 2)
      · omega
      · omega
    -- Simplify the natural-number arithmetic in the indices.
    have h1 : m - 1 = k + 2 := by omega
    have h2 : m - 2 = k + 1 := by omega
    have h3 : m - 3 = k     := by omega
    -- Rewrite fib (m+1) using the recurrence: fib(m+1) = fib(m) + fib(m-1).
    have hrec : Nat.fib (m + 1) = Nat.fib m + Nat.fib (m - 1) := by
      rw [h1]; simp [Nat.fib_add_two]
    -- Cast everything to ℤ and close the goal by ring + the two IH instances.
    push_cast [hrec, h1, h2, h3] at *
    -- The algebraic identity:
    --   fib(m+1)*fib(m-1) - fib(m)^2
    -- = (fib(m)+fib(m-1))*fib(m-1) - fib(m)^2
    -- = fib(m)*fib(m-1) + fib(m-1)^2 - fib(m)^2
    -- = -(fib(m)^2 - fib(m)*fib(m-1) - fib(m-1)^2)   -- rearrange
    -- But from ih_pred: fib(m)*fib(m-2) - fib(m-1)^2 = (-1)^(m-1)
    -- and  fib(m) = fib(m-1) + fib(m-2)  (recurrence used again).
    -- We close by linarith after expanding with ring_nf.
    have hrec2 : Nat.fib m = Nat.fib (m - 1) + Nat.fib (m - 2) := by
      rw [h1, h2]; simp [Nat.fib_add_two]
    push_cast [hrec2] at ih_pred ⊢
    have hsgn : (-1 : ℤ) ^ m = -((-1) ^ (m - 1)) := by
      rw [show m = (m - 1) + 1 by omega, pow_succ]
      ring
    linarith [ih_pred, sq_nonneg (Nat.fib (m - 1) : ℤ)]

corollary cassini_abs (n : ℕ) (hn : 1 ≤ n) :
    |(Nat.fib (n + 1) : ℤ) * Nat.fib (n - 1) - (Nat.fib n : ℤ) ^ 2| = 1 := by
  rw [cassini n hn]
  simp [abs_pow, abs_neg, abs_one]

/-
 ===============================================================
    CASSINI'S IDENTITY (ChatGPT)
 ===============================================================
-/

open Nat

theorem cassini_strong :
    ∀ n : ℕ,
      fib (n + 1) * fib (n - 1) - fib n ^ 2 = (-1 : ℤ) ^ n := by
  intro n
  induction' n using Nat.strong_induction_on with n ih

  cases n with
  | zero =>
      norm_num [fib]

  | succ n =>
      cases n with
      | zero =>
          norm_num [fib]

      | succ k =>
          -- Here n = k + 2.
          -- Induction hypothesis available for all m < k + 2.
          have hk :
              fib ((k + 1) + 1) * fib ((k + 1) - 1)
                - fib (k + 1)^2
                = (-1 : ℤ)^(k + 1) := by
            apply ih (k + 1)
            omega

          -- Rewrite fib (k+3) using the Fibonacci recurrence.
          -- Then simplify algebraically and use hk.
          --
          -- Typical steps:
          --   rw [fib_add_two]
          --   ring_nf
          --   rw [hk]
          --   ring
          --
          -- Depending on the version of mathlib,
          -- some auxiliary lemmas about fib may be needed.
          sorry
