import Mathlib.Data.Real.Basic
import Library.Basic

/-
OR (premise): split a premise into cases
  obtain h1 | h2  := h
OR (conclusion): Split the premise into two separate premises
  use `left` or `right` to select which branch you want to prove

AND (preimse): Split the premise in two known truths
  obtain ⟨h1, h2⟩ := h

AND (conclusion): Prove both elements with the `constructor` method
  constructor
  p := by something
  q := by something
  => p ∧ q

IMPLICATION: If you have f : p → q
You can call it like a function.
  x : p
  f : p → q
  f x        <= this will get you q
-/

example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
      (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
      _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain h2 | h2 := h2
  · left
    addarith [h2]
  · right
    addarith [h2]



example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  obtain h | h := h
  · rw [h]; ring;
  · rw [h]; ring;


example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  left
  calc
    x < x + 1/2 := by extra
    _ = (2 * x + 1) / 2 := by ring
    _ = y / 2 := by rw [h]


example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by
  obtain ⟨h1, h2⟩ := H
  calc
    2 * r = (r + s) + (r - s) := by ring
    _ ≤ 1 + 5 := by rel [h1, h2]
    _ = 6 := by numbers
