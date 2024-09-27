import Mathlib.Data.Real.Basic
import Library.Basic

-- Example 1.4.3
-- Exercise: Type out the whole proof
example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : x + y < 2 :=
  calc
    x + y ≤ x + (x + 5) := by rel [h1]
    _ = 2 * x + 5 := by ring
    _ ≤ 2 * (-2) + 5 := by rel [h2]
    _ = 1 := by ring
    _ < 2 := by numbers

-- Eample 2.1.6
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 :=
  have h : x ≤ -1 := by addarith [hx]
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by rel [hy]
    _ ≥ 3 - 2 * (-1) := by rel [h]
    _ = 5 := by ring
    _ > 3 := by numbers

-- Example 2.2.2
example {y : ℝ} : y ^ 2 + 1 ≠ 0 := by
  apply ne_of_gt
  extra
