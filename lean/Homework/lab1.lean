import Mathlib.Data.Real.Basic
import Library.Basic

example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 :=
  calc
    y = 4 * x - 3 := by rw [h2]
    _ = 4 * 3 - 3 := by rw [h1]
    _ = 9 := by ring

example {a b : ℤ} (h : a - b = 0) : a = b :=
  calc
    a = (a - b) + b := by ring
    _ = 0 + b := by rw [h]
    _ = b := by ring

example {x y : ℤ} (h1 : x - 3 * y = 5) (h2 : y = 3) : x = 14 :=
  calc
    x = x - 3 * y + 3 * y := by ring
    _ = 5 + 3 * y := by rw [h1]
    _ = 5 + 3 * 3 := by rw [h2]
    _ = 14 := by ring
