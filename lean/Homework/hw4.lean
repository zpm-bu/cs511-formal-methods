import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Library.Basic

/-
# Example 2.5.5

Show that there exist integers $m$ and $n$ such that $m² - n² = 11$.
-/
example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5
  numbers


/-
# Example 2.5.6

Let $a ∈ ℤ$. Show that there exists $m, n ∈ ℤ$ such that $m² - n² = 2a + 1$.
-/
example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1, a
  ring


/-
# Example 2.5.7

Let $p, q ∈ ℝ$ and $p < q$. Show that there exists $x ∈ ℝ$ such that $p < x < q$.
-/
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  constructor
  . calc
      p = (p + p) / 2 := by ring
      _ < (p + q) / 2 := by rel [h]
  . calc
      (p + q) / 2 < (q + q) / 2 := by rel [h]
      _ = q := by ring


/-
# Exercise 3.1.10.3

Let $m ∈ ℤ$ be odd and $n ∈ ℤ$ even. Prove that $n + m$ is odd.
-/
example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  dsimp [Odd, Even] at *
  obtain ⟨k, hk⟩ := hm
  obtain ⟨r, hr⟩ := hn
  use k + r
  calc
    n + m = (r + r) + (2 * k + 1) := by rw [hr, hk]
    _ = 2 * (k + r) + 1 := by ring


/-
# Exercise 4.1.10.1

Let $a ∈ ℚ$ be a rational number and suppose that for all rational numbers $b$,
$a ≥ -3 + 4b - b²$. Show that $a ≥ 1$.
-/
example {a : ℚ} (h : ∀ b : ℚ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 :=
  calc
    a ≥ -3 + 4 * 2 - 2 ^ 2 := by apply h
    _ = 1 := by ring


/-
# Example 4.1.3

Let $a, b ∈ ℝ$ and suppose that for every real number $x$, $x ≥ a$ or $x ≤ b$. Show
that $a ≤ b$.
-/
example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have h' : (a + b) / 2 ≥ a ∨ (a + b) / 2 ≤ b := by apply h
  obtain h' | h' := h'
  . calc
      b = 2 * ((a + b) / 2) - a := by ring
      _ ≥ 2 * a - a := by rel [h']
      _ = a := by ring
  . calc
      a = 2 * ((a + b) / 2) - b := by ring
      _ ≤ 2 * b - b := by rel [h']
      _ = b := by ring


/-
# Exercise 3.2.9.2

Show that $-10$ is not divisible by 3.
-/
example : ¬(3 : ℤ) ∣ -10 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use -4
  constructor
  . numbers
  . numbers


/-
# Exercise 3.2.9.5

Let $a, b ∈ ℤ$ and suppose that $a ∣ b$. Show that then
$a ∣ 2b³ - b² + 3b$.
-/
example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  dsimp [(.∣.)] at *
  obtain ⟨k, hk⟩ := hab
  use 2 * a ^ 2 * k ^ 3 - a * k ^ 2 + 3 * k
  calc
    2 * b ^ 3 - b ^ 2 + 3 * b = 2 * (a * k) ^ 3 - (a * k) ^ 2 + 3 * (a * k) := by rw [hk]
    _ = 2 * a ^ 3 * k ^ 3 - a ^ 2 * k ^ 2 + 3 * a * k := by ring
    _ = a * (2 * a ^ 2 * k ^ 3 - a * k ^ 2 + 3 * k) := by ring


/-
# Exercise 3.2.9.6

Let $k, l, m ∈ ℤ$ and suppose that $k ∣ l$ and $l³ ∣ m$. Show that $k³ ∣ m$.
-/
example {k l m : ℤ} (h1 : k ∣ l) (h2 : l ^ 3 ∣ m) : k ^ 3 ∣ m := by
  dsimp [(.∣.)] at *
  obtain ⟨n1, hn1⟩ := h1
  obtain ⟨n2, hn2⟩ := h2
  use n1 ^ 3 * n2
  calc
    m = l ^ 3 * n2 := by apply hn2
    _ = (k * n1) ^ 3 * n2 := by rw [hn1]
    _ = k ^ 3 * (n1 ^ 3 * n2) := by ring
