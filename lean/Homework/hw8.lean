import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel
import Library.Tactic.ModEq
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

/-
# Exercise 3.1

Show that (∃x∀y (x ≈ y)) ⊢ (∀v∀w (v ≈ w)).
-/
example (h : ∃x : Type, ∀y : Type, (x = y)) : (∀v : Type, ∀w : Type, (v = w)) := by
  obtain ⟨x, hx⟩ := h
  intros v w
  have hv := hx v
  have hw := hx w
  calc
    v = x := by rw [hv]
    _ = w := by rw [hw]


/-
# Exercise 3.2

Show that ⊢ (∃x ∀y (x ≈ y) → (∀v∀w (v ≈ w)))
-/
example : (∃ x : Type, ∀ y : Type, (x = y)) → (∀ v : Type, ∀ w : Type, (v = w)) := by
  intros h
  obtain ⟨x, hx⟩ := h
  intros v w
  have hv := hx v
  have hw := hx w
  calc
    v = x := by rw [hv]
    _ = w := by rw [hw]


/-
# Exercise 5.3.6.9

Show that there does _not_ exist a real number $t$ such that $t ≤ 4$ and $t ≥ 5$.
-/
example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  intros t
  obtain ht | ht := lt_or_ge t 5
  . right
    apply ht
  . left
    calc
      4 < 5 := by numbers
      _ ≤ t := by rel [ht]


/-
# Exercise 6.1.2.

Let $n$ be a natural number. Then either $n$ is even or $n$ is odd.
-/

example (m : ℕ) : Even m ∨ Odd m := by
  simple_induction m with k IH
  . -- Base case
    left
    dsimp [Even]
    use 0
    numbers
  . -- Inductive step
    obtain ⟨x, hx⟩ | ⟨x, hx⟩ := IH
    . -- x is even
      right
      dsimp [Odd]
      use x
      calc
        k + 1 = (x + x) + 1 := by rw [hx]
        _ = 2 * x + 1 := by ring
    . -- x is odd
      left
      dsimp [Even]
      use x + 1
      calc
        k + 1 = (2 * x + 1) + 1 := by rw [hx]
        _ = (x + 1) + (x + 1) := by ring


/-
# Exercise 6.1.6

Show that for all sufficiently large natural numbers $n$, $2ⁿ ≥ n²$.
-/
example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  . -- base case n=4
    numbers
  . -- inductive step
    calc
      2 ^ (k + 1) = 2 * ( 2 ^ k ) := by ring
      _ ≥ 2 * (k ^ 2) := by rel [IH]
      _ = (k ^ 2) + (k * k) := by ring
      _ ≥ (k ^ 2) + (4 * k) := by rel [hk]
      _ = (k ^ 2) + (2 * k) + (2 * k) := by ring
      _ ≥ (k ^ 2) + (2 * k) + (2 * 4) := by rel [hk]
      _ = (k + 1) ^ 2 + 7 := by ring
      _ ≥ (k + 1) ^ 2 := by addarith []
