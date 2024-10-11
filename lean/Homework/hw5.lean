import Library.Basic
import Library.Theory.ModEq.Defs

/-
# Exercise 3.3.4

Let $a, b, c, d, n ∈ ℤ$ and suppose that $a ≡ b mod n$ and $c ≡ d mod n$. Then
$a - c ≡ b - d mod n$.
-/
theorem Int.ModEq.sub
  {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) : a - c ≡ b - d [ZMOD n]
:= by
  dsimp [Int.ModEq] at *
  dsimp [(.∣.)] at *
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x - y
  calc
    a - c - (b - d) = (a - b) - (c - d) := by ring
    _ = n * x - n * y := by rw [hx, hy]
    _ = n * (x - y) := by ring


/-
# Exercise 3.3.5

Let $a, b, n ∈ ℤ$ and suppose $a ≡ b mod n$. Then $-a ≡ -b mod n$.
-/
theorem Int.ModEq.neg {n a b : ℤ} (h1 : a ≡ b [ZMOD n]) : -a ≡ -b [ZMOD n] := by
  dsimp [Int.ModEq, (.∣.)] at *
  obtain ⟨k, hk⟩ := h1
  use -1 * k
  calc
    -a - -b = -1 * (a - b) := by ring
    _ = -1 * (n * k) := by rw [hk]
    _ = n * (-1 * k) := by ring


/-
# Example 3.3.12.2

Let $a, b, n ∈ ℤ$ and suppose $a ≡ b mod n$. Show that $b ≡ a mod n$.
-/
theorem Int.ModEq.symm (h : a ≡ b [ZMOD n]) : b ≡ a [ZMOD n] := by
  obtain ⟨k, hk⟩ := h
  use -1 * k
  calc
    b - a = -1 * (a - b) := by ring
    _ = -1 * (n * k) := by rw [hk]
    _ = n * (-1 * k) := by ring


/-
# Example 3.3.12.3

Let $a, b, c, n ∈ ℤ$ and suppose $a ≡ b mod n$ and $b ≡ c mod n$. Show that
$a ≡ c mod n$.
-/
theorem Int.ModEq.trans
  (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) : a ≡ c [ZMOD n]
:= by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x + y
  calc
    a - c = (a - b) + (b - c) := by ring
    _ = n * x + n * y := by rw [hx, hy]
    _ = n * (x + y) := by ring


/-
# Exercise 3.3.12.6

Let $a, b ∈ ℤ$ and $a ≡ b mod 5$. Show that $2a + 3 ≡ 2b + 3 mod 5$.
-/
example {a b : ℤ} (h : a ≡ b [ZMOD 5]) : 2 * a + 3 ≡ 2 * b + 3 [ZMOD 5] := by
  obtain ⟨k, hk⟩ := h
  use 2 * k
  calc
    2 * a + 3 - (2 * b + 3) = 2 * (a - b) := by ring
    _ = 2 * (5 * k) := by rw [hk]
    _ = 5 * (2 * k) := by ring


/-
# Example 4.3.5.2

Show that there exists a unique $n ∈ ℕ$ such that for all $a ∈ ℕ$, we have $n ≤ a$.
-/
example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  constructor
  . intros a
    extra
  . intros y hy
    apply Nat.le_zero.mp (hy 0)
