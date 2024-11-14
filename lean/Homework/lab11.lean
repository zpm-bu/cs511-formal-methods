import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust

math2001_init

open Function

example : ¬ Injective (fun (x : ℝ) ↦ 3) := by
  dsimp [Injective]
  push_neg
  use 4, 5
  -- The syntax `<;>` is a shorthand for "use the same logic for all branches
  constructor <;> numbers

example : Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
  dsimp [Injective]
  intros a1 a2 ha
  have : 3 * a1 = 3 * a2 := by addarith [ha]
  cancel 3 at this

example (f : X → Y) : Injective f ↔ ∀ x1 x2 : X, x1 ≠ x2 → f x1 ≠ f x2 := by
  constructor
  . intros inj x1 x2 hx
    dsimp [Injective] at inj
    intro contra
    have this := inj contra
    contradiction
  . intros H
    dsimp [Injective] at *
    intros a1 a2 ha
    by_cases h : a1 = a2
    . apply h
    . have contra := H a1 a2 h
      contradiction

example : Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  constructor
  . -- Injective
    dsimp [Injective]
    intros a1 a2 ha
    have : 3 * a1 = 3 * a2 := by addarith [ha]
    cancel 3 at this
  . -- Surjective
    dsimp [Surjective]
    intros b
    use (4- b) / 3
    ring

example : ¬ Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by
  dsimp [Bijective]
  push_neg
  left
  dsimp [Injective]
  push_neg
  use -2, 0
  constructor
  . ring
  . numbers

inductive Element
  | fire
  | water
  | earth
  | air
  deriving DecidableEq

open Element

def e : Element → Element
  | fire => earth
  | water => air
  | earth => fire
  | air => water

example : Bijective e := by
  constructor
  . -- Injective
    dsimp [Injective]
    intros el1 el2 he
    -- `exhaust` is basically magic
    cases el1 <;> cases el2 <;> trivial
  . -- Surjective
    dsimp [Surjective]
    intros elem
    cases elem
    . use earth; rw [e]
    . use air; rw [e]
    . use fire; rw [e]
    . use water; rw [e]
