import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.ModEq

math2001_init

theorem no_int_even_and_odd : ¬ ∃ x, Int.Even x ∧ Int.Odd x := by
  intros h
  obtain ⟨x, hEven, hOdd⟩ := h
  rw [Int.even_iff_modEq] at hEven
  rw [Int.odd_iff_modEq] at hOdd
  apply Int.ModEq.symm at hEven
  have contra : 0 ≡ 1 [ZMOD 2] := by apply Int.ModEq.trans hEven hOdd
  numbers at contra

example : ¬ Int.Even 7 := by
  intros hEven
  have hOdd : Int.Odd 7 := by
    rw [Int.odd_iff_modEq]
    use 3
    ring
  apply no_int_even_and_odd
  use 7
  constructor
  · apply hEven
  · apply hOdd
