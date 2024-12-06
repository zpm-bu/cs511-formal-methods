def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n

theorem F_bound (n : ℕ) : F n ≤ 2 ^ n := by
  match n with
  | 0 =>
    calc
      F 0 = 1 := by rw [F]
      _ ≤ 2 ^ 0 := by numbers
  | 1 =>
    calc
      F 1 = 1 := by rw [F]
      _ ≤ 2 ^ 1 := by numbers
  | k + 2 =>
    have IH1 := F_bound k
    have IH2 := F_bound (k + 1)
    calc
      f (k + 2) = F (k + 1) + F k := by rw [F]
      _ ≤ 2 ^ (k + 1) + 2 ^ k := by rel [IH1, IH2]
      _ = 2 ^ (k + 1) + 2 ^ k + 2 ^ k := by extra
      _ = 2 ^ (k + 2) := by ring
