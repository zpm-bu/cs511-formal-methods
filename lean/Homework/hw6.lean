import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs
import Library.Tactic.ModEq
import Library.Theory.ParityModular
import Library.Theory.Parity
import AutograderLib

/-
# Exercise 3.4.5.6

Let $n$ be an integer. Show that $5n² + 3n + 7 ≡ 1 mod 2$.
-/

@[autograded 3]
example (n : ℤ) : 5 * n ^ 2 + 3 * n + 7 ≡ 1 [ZMOD 2] := by
  obtain he | ho := Int.even_or_odd n
  · obtain ⟨k, hk⟩ := he
    dsimp [Int.ModEq, (.∣.)]
    use 10 * k ^ 2 + 3 * k + 3
    calc
      5 * n ^ 2 + 3 * n + 7 - 1 = 5 * n ^ 2 + 3 * n + 6 := by ring
      _ = 5 * (2 * k) ^ 2 + 3 * (2 * k) + 6 := by rw [hk]
      _ = 20 * k ^ 2 + 6 * k + 6 := by ring
      _ = 2 * (10 * k ^ 2 + 3 * k + 3) := by ring
  · obtain ⟨k, hk⟩ := ho
    dsimp [Int.ModEq, (.∣.)]
    use 10 * k ^ 2 + 13 * k + 7
    calc
      5 * n ^ 2 + 3 * n + 7 - 1 = 5 * (2 * k + 1) ^ 2 + 3 * (2 * k + 1) + 7 - 1 := by rw [hk]
      _ = 20 * k ^ 2 + 26 * k + 14 := by ring
      _ = 2 * (10 * k ^ 2 + 13 * k + 7) := by ring


/-
# 3.4.5.7

Let $x ∈ ℤ$. Show that $x⁵ ≡ x (mod 5)$.
-/

@[autograded 3]
example {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
  dsimp [Int.ModEq] at *
  -- This is so gross, I'm sure there's a better way to do this
  mod_cases x % 5
  . dsimp [Int.ModEq, (.∣.)] at *
    obtain ⟨k, hk⟩ := H
    use (5 ^ 4) * k ^ 5 - k
    calc
      x ^ 5 - x = (x - 0) ^ 5 - (x - 0) := by ring
      _ = (5 * k) ^ 5 - (5 * k) := by rw [hk]
      _ = 5 * (5 ^ 4 * k ^ 5 - k) := by ring
  . dsimp [Int.ModEq, (.∣.)] at *
    obtain ⟨k, hk⟩ := H
    have hk' : x = 5 * k + 1 := by addarith [hk]
    use 5 ^ 4 * k ^ 5 + 5 ^ 4 * k ^ 4 + 2 * 5 ^ 3 * k ^ 3 + 2 * 5 ^ 2 * k ^ 2 + 4 * k
    calc
      x ^ 5 - x = (5 * k + 1) ^ 5 - (5 * k + 1) := by rw [hk']
      _ = 5 * ( 5 ^ 4 * k ^ 5 + 5 ^ 4 * k ^ 4 + 2 * 5 ^ 3 * k ^ 3 + 2 * 5 ^ 2 * k ^ 2 + 4 * k ) := by ring
  . dsimp [Int.ModEq, (.∣.)] at *
    obtain ⟨k, hk⟩ := H
    have hk' : x = 5 * k + 2 := by addarith [hk]
    use 5 ^ 4 * k ^ 5 + 2 * 5 ^ 4 * k ^ 4 + 2 ^ 3 * 5 ^ 3 * k ^ 3 + 2 ^ 4 * 5 ^ 2 * k ^ 2 + 79 * k + 6
    calc
      x ^ 5 - x = (5 * k + 2) ^ 5 - (5 * k + 2) := by rw [hk']
      _ = 5 * ( 5 ^ 4 * k ^ 5 + 2 * 5 ^ 4 * k ^ 4 + 2 ^ 3 * 5 ^ 3 * k ^ 3 + 2 ^ 4 * 5 ^ 2 * k ^ 2 + 79 * k + 6 ) := by ring
  . dsimp [Int.ModEq, (.∣.)] at *
    obtain ⟨k, hk⟩ := H
    have hk' : x = 5 * k + 3 := by addarith [hk]
    use 5 ^ 4 * k ^ 5 + 3 * 5 ^ 4 * k ^ 4 + 2 * 3 ^ 2 * 5 ^ 3 * k ^ 3 + 2 * 3 ^ 3 * 5 ^ 2 * k ^ 2 + 2^2 * 101 * k + 2 ^ 4 * 3
    calc
      x ^ 5 - x = (5 * k + 3) ^ 5 - (5 * k + 3) := by rw [hk']
      _ = 5 * ( 5 ^ 4 * k ^ 5 + 3 * 5 ^ 4 * k ^ 4 + 2 * 3 ^ 2 * 5 ^ 3 * k ^ 3 + 2 * 3 ^ 3 * 5 ^ 2 * k ^ 2 + 2^2 * 101 * k + 2 ^ 4 * 3 ) := by ring
  . dsimp [Int.ModEq, (.∣.)] at *
    obtain ⟨k, hk⟩ := H
    have hk' : x = 5 * k + 4 := by addarith [hk]
    use 5 ^ 4 * k ^ 5 + 2 ^ 2 * 5 ^ 4 * k ^ 4 + 2 ^ 5 * 5 ^ 3 * k ^ 3 + 2 ^ 7 * 5 ^ 2 * k ^ 2 + 1279 * k + 2 ^ 2 * 3 * 17
    calc
      x ^ 5 - x = (5 * k + 4) ^ 5 - (5 * k + 4) := by rw [hk']
      _ = 5 * ( 5 ^ 4 * k ^ 5 + 2 ^ 2 * 5 ^ 4 * k ^ 4 + 2 ^ 5 * 5 ^ 3 * k ^ 3 + 2 ^ 7 * 5 ^ 2 * k ^ 2 + 1279 * k + 2 ^ 2 * 3 * 17 ) := by ring
