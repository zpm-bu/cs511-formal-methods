import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Theory.InjectiveSurjective
import Library.Tactic.ModEq

math2001_init
set_option pp.funBinderTypes true

open Function

/-# Exercise 3-/

--Exercise 8.3.10.2

def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := (x - 1) / 5

example : Inverse u v := by
  dsimp [Inverse]
  constructor
  . ext x
    calc
      (v ∘ u) x = v (u x) := by rfl
      _ = v (5 * x + 1) := by rw [u]
      _ = ((5 * x + 1) - 1) / 5 := by rw [v]
      _ = x := by ring
  . ext x
    calc
      (u ∘ v) x = u (v x) := by rfl
      _ = u ((x - 1) / 5) := by rw [v]
      _ = 5 * ((x - 1) / 5) + 1 := by rw [u]
      _ = x := by ring

--Exercise 8.3.10.3

example {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  dsimp [Injective]
  intros a1 a2 hgf
  apply hf
  apply hg
  trivial

--Exercise 8.3.10.4

example {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
  dsimp [Surjective] at *
  intros b
  obtain ⟨k₁, hk₁⟩ := hg b
  obtain ⟨k₂, hk₂⟩ := hf k₁
  use k₂
  exhaust

/-# Exercise 4-/

--Exercise 8.4.10.1

example : Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r - s)) := by
  rw [bijective_iff_exists_inverse]
  use fun (r, s) ↦ (r + s, r)
  constructor <;> ext ⟨a, b⟩ <;> dsimp <;> ring

--Exercise 8.4.10.2.1

example : ¬ Injective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp [Injective]
  push_neg
  use (3, 1), (5, 2)
  constructor
  . dsimp; ring;
  . trivial;

--Exercise 8.4.10.2.2

example : Surjective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp [Surjective]
  intros b
  use (b + 3, 1)
  dsimp
  ring
