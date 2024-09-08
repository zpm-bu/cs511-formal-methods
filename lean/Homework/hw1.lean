import Mathlib.Data.Real.Basic
import Library.Basic

/-
Exercise 1.3.4
Let $w$ be a rational number and suppose that $3w + 1 = 4$.
Show that $w = 1$.
-/
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 :=
  calc
    w = (3 * w + 1) / 3 - (1 / 3) := by ring
    _ = 4 / 3 - 1 / 3 := by rw [h1]
    _ = 1 := by ring


/-
Exercise 1.3.9
Let $a$ and $b$ be rational numbers and suppose that $a - 3 = 2b$.
Show that $a² - a + 3 = 4b² + 10b + 9$.
-/
example {a b : ℚ} (h1 : a - 3 = 2 * b) : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 :=
  calc
    a ^ 2 - a + 3 = ((a - 3) ^ 2 + 6 * a - 9) - a + 3 := by ring
    _ = (a - 3) ^ 2 + 5 * a - 6 := by ring
    _ = (a - 3) ^ 2 + 5 * ((a - 3) + 3) - 6 := by ring
    _ = (a - 3) ^ 2 + 5 * (a - 3) + 9 := by ring
    _ = (2 * b) ^ 2 + 5 * (2 * b) + 9 := by rw [h1]
    _ = 4 * b ^ 2 + 10 * b + 9 := by ring


/-
Exercise 1.3.11(7)
Let $a$, $b$, and $c$ be real numbers and suppose that $a + 2b + 3c = 7$,
$b + 2c = 3$, and $c = 1$. Show that $a = 2$.
-/
example {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3) (h3 : c = 1)
        : a = 2 :=
  calc
    a = a + 2 * b + 3 * c - 2 * b - 3 * c := by ring
    _ = 7 - 2 * b - 3 * c := by rw [h1]
    _ = 7 - 2 * b - 3 * 1 := by rw [h3]
    _ = 4 - 2 * b := by ring
    _ = 4 - 2 * b - 4 * c + 4 * c := by ring
    _ = 4 - 2 * b - 4 * c + 4 * 1 := by rw [h3]
    _ = 8 - 2 * b - 4 * c := by ring
    _ = 8 - 2 * (b + 2 * c) := by ring
    _ = 8 - 2 * 3 := by rw [h2]
    _ = 2 := by ring
