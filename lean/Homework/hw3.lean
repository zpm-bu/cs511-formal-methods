import Mathlib.Data.Real.Basic
import Library.Basic

/-
# Exercise 2.3.6.2

Let $x ∈ ℝ$ and suppose $x = 1$ or $x = 2$. Show that $x² - 3x + 2 = 0$.
-/
example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain h | h := h
  . calc
      x ^ 2 - 3 * x + 2 = 1 ^ 2 - 3 * 1 + 2 := by rw [h]
      _ = 0 := by ring
  . calc
      x ^ 2 - 3 * x + 2 = 2 ^ 2 - 3 * 2 + 2 := by rw [h]
      _ = 0 := by ring


/-
# Exercise 2.3.6.3

Let $t ∈ ℚ$ and suppose that $t = -2$ or $t = 3$. Show that $t² - t - 6 = 0$.
-/
example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  obtain h | h := h
  . calc
      t ^ 2 - t - 6 = (-2) ^ 2 - (-2) - 6 := by rw [h]
      _ = 0 := by ring
  . calc
      t ^ 2 - t - 6 = 3 ^ 2 - 3 - 6 := by rw [h]
      _ = 0 := by ring


/-
# Exercise 2.3.6.4

Let $x, y ∈ ℝ$ and suppose $x = 2$ or $y = -2$. Prove $x² + 2x = 2y + 4$.
-/
example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  obtain hx | hy := h
  . calc
      x * y + 2 * x = 2 * y + 2 * 2 := by rw [hx]
      _ = 2 * y + 4 := by ring
  . calc
      x * y + 2 * x = x * -2 + 2 * x := by rw [hy]
      _ = 0 := by ring
      _ = (2 * -2) + 4 := by ring
      _ = 2 * y + 4 := by rw [hy]


/-
# Exercise 2.3.6.12

Let $x$ be any integer. Show that $2x ≠ 3$.
-/
example {x : ℤ} : 2 * x ≠ 3 := by
  have hx := le_or_succ_le x 1
  obtain h_x_le_1 | h_x_ge_2 := hx
  . apply ne_of_lt
    calc
      2 * x ≤ 2 * 1 := by rel [h_x_le_1]
      _ = 2 := by ring
      _ < 3 := by numbers
  . apply ne_of_gt
    calc
      3 < 2 * 2 := by numbers
      _ ≤ 2 * x := by rel [h_x_ge_2]

/-
# Exercise 2.4.5.1

Let $a, b ∈ ℚ$ and suppose that $a ≤ 1$ and $a + b ≤ 3$. Show that
$2a + b ≤ 4$.
-/
example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨h1, h2⟩ := H
  calc
    2 * a + b = a + (a + b) := by ring
    _ ≤ 1 + 3 := by rel [h1, h2]
    _ = 4 := by ring

/-
# Exercise 2.4.5.6


Let $x, y ∈ ℚ$ and suppose that $x + y = 5$ and $x + 2y = 7$. Show that $x = 3$ and
$y = 2$.
-/
example {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨h1, h2⟩ := h
  have hy : y = 2 := by
    calc
      y = (x + y) + y - (x + y) := by ring
      _ = (x + 2 * y) - (x + y) := by ring
      _ = 7 - 5 := by rw [h1, h2]
      _ = 2 := by ring

  constructor
  . calc
    x = x + y - y := by ring
    _ = 5 - 2 := by rw [h1, hy]
    _ = 3 := by ring
  . apply hy


/-
# Exercise 2.3.6.10

Let $t ∈ ℝ$ for which $t³ = t²$. Show that either $t = 0$ or $t = 1$.
-/
example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have h' := by
    calc
      t * (t * t) = t ^ 3 := by ring
      _ = t ^ 2 := by rw [ht]
      _ = t * (t * 1) := by ring
  obtain h_t_ne_0 | h_t_eq_0 := ne_or_eq t 0

  . left
    cancel t at h'
    cancel t at h'

  . right
    apply h_t_eq_0


/-
# Exercise 2.3.6.14

Let $m ∈ ℕ$. Show that $m² + 4m ≠ 46$.
-/
example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  obtain h | h := le_or_succ_le m 5
  . apply ne_of_lt
    calc
      m ^ 2 + 4 * m ≤ 5 ^ 2 + 4 * 5 := by rel [h]
      _ < 46 := by numbers
  . apply ne_of_gt
    calc
      46 < 6 ^ 2 + 4 * 6 := by numbers
      _ ≤ m ^ 2 + 4 * m := by rel [h]


/-
# Exercise 2.4.5.7

Let $a, b ∈ ℝ$ and suppose that $ab = a = b$. Show that either $a = b = 0$ or
$a = b = 1$.
-/
example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b)
        : a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1
:= by
  obtain h_ab_ne_0 | h_ab_eq_0 := ne_or_eq (a * b) 0

  . right
    have h_a_neq_0 := by calc
      a = a * b := by rw [h1]
      _ ≠ 0 := by apply h_ab_ne_0
    have h_b_neq_0 := by calc
      b = a * b := by rw [h2]
      _ ≠ 0 := by apply h_ab_ne_0
    constructor
    . have h2' := by calc
        a * b = b := by rw [h2]
        _ = 1 * b := by ring
      cancel b at h2'
    . have h1' := by calc
        a * b = a := by rw [h1]
        _ = a * 1 := by ring
      cancel a at h1'

  . left
    constructor
    . calc
      a = a * b := by rw [h1]
      _ = 0 := by rw [h_ab_eq_0]
    . calc
      b = a * b := by rw [h2]
      _ = 0 := by rw [h_ab_eq_0]
