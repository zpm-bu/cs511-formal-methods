import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq
import Library.Theory.ParityModular

math2001_init
set_option pp.funBinderTypes true

open Function
namespace Int

/- # Exercise 3 -/

--Exercise 8.1.13.2

--# Prove one-------------------------------------------------------

example : ¬ Injective (fun (x : ℝ) ↦ 3) := by
  dsimp [Injective]
  push_neg
  use 4, 5
  constructor <;> numbers

--Exercise 8.1.13.3
--# Prove one-------------------------------------------------------

example : Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  dsimp [Injective]
  intros a₁ a₂ h
  have : 3 * a₁ = 3 * a₂ := by addarith [h]
  cancel 3 at this

--Exercise 8.1.13.5
--# Prove one-------------------------------------------------------

example : Surjective (fun (x : ℝ) ↦ 2 * x) := by
  dsimp [Surjective]
  intros b
  use (b / 2)
  ring

--# -----------------------------------------------------------------

/- # Exercise 4 -/

inductive Musketeer
  | athos
  | porthos
  | aramis
  deriving DecidableEq

open Musketeer

inductive White
  | meg
  | jack
  deriving DecidableEq

open White

def h : Musketeer → White
  | athos => jack
  | porthos => meg
  | aramis => jack

--Exercise 8.1.13.8
--# Prove one-------------------------------------------------------

example : ¬ Injective h := by
  dsimp [Injective]
  push_neg
  use athos, aramis
  constructor
  . rw [h]; rw [h];
  . trivial

--Exercise 8.1.13.9
--# Prove one-------------------------------------------------------

example : Surjective h := by
  dsimp [Surjective]
  intros b
  cases b
  . use Musketeer.porthos
    rw [h]
  . use Musketeer.aramis
    rw [h]


--# ----------------------------------------------------------------

def l : White → Musketeer
  | meg => aramis
  | jack => porthos

--Exercise 8.1.13.11
--# Prove one-------------------------------------------------------

example : ¬ Surjective l := by
  dsimp [Surjective]
  push_neg
  use athos
  intros w
  cases w
    <;> rw [l]
    <;> exhaust
