import Mathlib.Data.Real.Basic
import Library.Basic


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  numbers

example : ∃ m n : ℕ, m ^ 2 + n ^ 2 = 85 := by
  -- You can bind as many ∃ values as you want, using a comma
  use 6, 7
  numbers


example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -1/2
  constructor
  . numbers
  . numbers


example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  dsimp [Odd, Even] at *
  obtain ⟨x, hx⟩ := hp
  obtain ⟨y, hy⟩ := hq
  use x - y - 2
  rw [hx, hy]
  ring


example : ∃ n : ℕ, ∀ m : ℕ, n ≤ m := by
  use 0
  intros m
  extra


example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -4
  intros x y a
  have h1 : (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by extra
  have h2 : (x + y) ^ 2 + (x - y) ^ 2 = 2 * (x ^ 2 + y ^ 2) := by ring
  sorry


example : (11 : ℕ) ∣ 88 := by
  -- For simplifying a binary operation, you can use ``.R.``
  dsimp [(.∣.)]
  use 8
  numbers


example : (-2 : ℤ) ∣ 6 := by
  dsimp [(.∣.)]
  use -3
  numbers


example {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by
  sorry
