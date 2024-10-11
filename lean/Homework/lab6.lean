example : ∃ k : ℤ, 5 * k ≡ 6 [ZMOD 8] := by
  use 6
  dsimp [Int.ModEq, (.∣.)]
  use 3
  ring


example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  sorry
