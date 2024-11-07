import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int

def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

example (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  -- As on paper, we can prove this with simple induction
  simple_induction n with k IH
  . -- base case
    rw [B]
    ring
  . -- inductive step
    rw [B, IH]
    ring


def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)


example (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  simple_induction n with k IH
  . rw [S]; ring
  . rw [S, IH]; ring



def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

example (n : ℕ) : 0 < n ! := by
  simple_induction n with k IH
  . rw [factorial]; numbers
  . rw [factorial]; extra


example {n : ℕ} (hn : 2 ≤ n) : Nat.Even (n !) := by
  induction_from_starting_point n, hn with k hk IH
  . -- base case
    dsimp [factorial, Nat.Even]
    use 1
    ring
  . dsimp [Nat.Even] at *
    dsimp [factorial]
    obtain ⟨m, hm⟩ := IH
    rw [hm]
    use (k + 1) * m
    ring


def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) - q n + 6 * n + 6


example (n : ℕ) : q n = (n : ℤ) ^ 3 + 1 := by
  sorry


/- A much longer example! -/

def a : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => a (n + 1) + 2 * a n

