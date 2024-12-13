import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init

section
local infix:50 "∼" => fun (x y : ℤ) ↦ y ≡ x + 1 [ZMOD 5]

/- 10.1.5.4 -/
example : ¬ Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  push_neg
  use 2
  dsimp [Int.ModEq, (.∣.)]
  apply Int.not_dvd_of_exists_lt_and_lt
  use -1
  constructor <;> numbers


example : ¬ Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  push_neg
  use 1, 2
  constructor
  . dsimp [Int.ModEq, (.∣.)]; use 0; numbers;
  . apply Int.not_dvd_of_exists_lt_and_lt
    use -1
    constructor <;> numbers


example : AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  intros x y h1 h2
  dsimp [Int.ModEq] at *
  obtain ⟨c, hc⟩ := h1
  obtain ⟨d, hd⟩ := h2

  -- A chain of stupid conclusions
  have hc' : y = 5 * c + (x + 1) := by rw [← hc]; ring;
  have hd' : x = 5 * d + (y + 1) := by rw [← hd]; ring;
  have hz : 0 = 5 * d + 5 * c + 2 := by
    calc
      0 = x - x := by ring
      _ = 5 * d + (y + 1) - x := by rw [hd']
      _ = 5 * d + ((5 * c + (x + 1) + 1)) - x := by rw [hc']
      _ = 5 * d + 5 * c + 2 := by ring

  -- Now we can prove two contradictory statements!
  have ht : 5 ∣ -2 := by
    dsimp [(. ∣ .)]
    use d + c
    calc
      -2 = 0 - 2 := by ring
      _ = (5 * d + 5 * c + 2) - 2 := by rw [hz]
      _ = 5 * (d + c) := by ring

  have ht' : ¬ 5 ∣ -2 := by
    apply Int.not_dvd_of_exists_lt_and_lt
    use -1
    constructor <;> numbers

  -- Hooray, that's the dumbest proof I've ever written!
  contradiction


example : ¬ Transitive (. ∼ .) := by
  dsimp [Transitive]
  push_neg
  use 1, 2, 3

  -- Can you use 'constructor' for three statements?
  constructor
  . numbers
  . constructor
    . numbers
    . numbers

end -- section


/- 10.1.5.5 -/
section
local infix:50 "∼" => fun (x y : ℤ) ↦ x + y ≡ 0 [ZMOD 3]


example : ¬ Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  push_neg
  use 1
  dsimp [Int.ModEq, (. ∣ .)]
  apply Int.not_dvd_of_exists_lt_and_lt
  use 0
  constructor <;> numbers



example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intros x y h
  dsimp [Int.ModEq, (. ∣ .)] at *
  obtain ⟨c, h⟩ := h
  use c
  calc
    y + x - 0 = x + y - 0 := by ring
    _ = 3 * c := by rw [h]


example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  push_neg
  use 1, 2
  dsimp [Int.ModEq, (. ∣ .)]
  constructor
  . use 1; numbers;
  . constructor
    . use 1; numbers;
    . numbers;


example : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]
  push_neg
  use 1, 2, 4
  dsimp [Int.ModEq] at *
  constructor
  . use 1; numbers;
  . constructor
    . use 2; numbers;
    . apply Int.not_dvd_of_exists_lt_and_lt
      use 1
      constructor <;> numbers

end -- section
