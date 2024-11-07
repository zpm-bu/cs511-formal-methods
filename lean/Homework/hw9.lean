import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int

--Exercise 6.2.7.1
def c : ℕ → ℤ
  | 0 => 7
  | n + 1 => 3 * c n - 10

example (n : ℕ) : Odd (c n) := by
  simple_induction n with k IH
  . rw [c]
    use 3
    ring
  . obtain ⟨n, hn⟩ := IH
    rw [c]
    use 3 * n - 4
    calc
      3 * c k - 10 = 3 * (2 * n + 1) - 10 := by rw [hn]
      _ = 2 * (3 * n - 4) + 1 := by ring

--Exercise 6.2.7.2
example (n : ℕ) : c n = 2 * 3 ^ n + 5 := by
  simple_induction n with k IH
  . rw [c]; numbers
  . rw [c, IH]
    ring

--Exercise 6.2.7.3
def y : ℕ → ℕ
  | 0 => 2
  | n + 1 => (y n) ^ 2

example (n : ℕ) : y n = 2 ^ (2 ^ n) := by
  two_step_induction n with k IH1 IH2
  -- base steps
  . rw [y]; numbers
  . rw [y]; rw [y]; numbers
  -- induction
  . rw [y]
    calc
      y (k + 1) ^ 2 = (2 ^ 2 ^ (k + 1)) ^ 2 := by rw [IH2]
      _ = 2 ^ 2 ^ (k + 1 + 1) := by ring


--# Exercise 4

--Exercise 6.3.6.1
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 5 * b (n + 1) - 6 * b n

example (n : ℕ) : b n = 3 ^ n - 2 ^ n := by
  two_step_induction n with k IH1 IH2
  -- base steps
  . rw [b]; ring;
  . rw[b]; ring;
  -- inductive step
  . rw [b]
    rw [IH1]
    rw [IH2]
    ring


--Exercise 6.3.6.2
def c' : ℕ → ℤ
  | 0 => 3
  | 1 => 2
  | n + 2 => 4 * c' n

example (n : ℕ) : c' n = 2 * 2 ^ n + (-2) ^ n := by
  two_step_induction n with k IH1 IH2
  -- base cases
  . rw [c']; ring;
  . rw [c']; ring;
  -- inductive step
  . rw [c']
    rw [IH1]
    ring

--Exercise 6.3.6.3
def t : ℕ → ℤ
  | 0 => 5
  | 1 => 7
  | n + 2 => 2 * t (n + 1) - t n

example (n : ℕ) : t n = 2 * n + 5 := by
  two_step_induction n with k IH1 IH2
  -- base cases
  . rw [t]; ring;
  . rw [t]; ring;
  -- inductive step
  . rw [t]
    rw [IH1]
    rw [IH2]
    ring

