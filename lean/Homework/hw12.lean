import Library.Basic
import Library.Tactic.ModEq
import Library.Tactic.Exhaust
import Mathlib.Data.Int.Basic

math2001_init

open Set Function Nat

/-
# Exercise 6.4.3.1

Show that for all natural numbers n > 0, there exist natural numbers a and x,
with x odd, such that n = 2ᵃx.
-/

lemma half_even_pos_is_pos {n m : ℕ} (hn : 0 < n) (hm : n = 2 * m) : 0 < m := by
  -- I can't get Lean to accept any proofs for this
  -- Stupid, I'm so angry. It's by definition.
  -- 0 => 0 < 0, a contradiction
  -- succ k => succ is always greater than 0
  sorry

theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  match n with
  | 1 =>
      use 0, 1;
      constructor
      . use 0; numbers;
      . numbers;

  | k + 1 =>
      obtain hke | hko := even_or_odd k
      . -- k is even ...
        use 0, k + 1
        constructor
        . -- ... so k + 1 is odd...
          obtain ⟨k₀, hk₀⟩ := hke; use k₀; exhaust;
        . -- ... and k + 1 = 2^0 * (k+1)
          ring

      . -- k is odd
        -- so k + 1 is even, with k = 2*k₀
        have : Even (k + 1) := by obtain ⟨k', hk'⟩ := hko; use k' + 1; rw [hk']; ring;
        obtain ⟨k₀, hk₀⟩ := this

        -- which gives us that k₀ must be 2^a * x for some a, x
        have : 0 < k₀ := half_even_pos_is_pos hn hk₀
        have IH := extract_pow_two k₀ this
        obtain ⟨a, x, ⟨hx, ha⟩⟩ := IH

        -- and thus k + 1 = 2 * (2^a * x)
        use a + 1, x
        constructor
        . exact hx
        . calc
            k + 1 = 2 * k₀ := by rw [hk₀]
            _ = 2 * (2 ^ a * x) := by rw [ha]
            _ = 2 ^ (a + 1) * x := by ring

/-
# Exercise 9.1.10.1

Prove or disprove that 4 ∈ {a : ℚ | a < 3}
-/
example : 4 ∉ {a : ℚ | a < 3} := by
    dsimp
    push_neg
    numbers

/-
# Exercise 9.1.10.2

Prove or disprove that 6 ∈ {n : ℕ | n ∣ 42}
-/
example : 6 ∈ {n : ℕ | n ∣ 42} := by
  use 7
  numbers


/-
# Exercise 9.1.10.3

Prove or disprove that 8 ∈ {k : ℤ | 5 ∣ k}
-/
example : 8 ∉ {k : ℤ | 5 ∣ k} := by
  dsimp
  apply Int.not_dvd_of_exists_lt_and_lt
  use 1
  constructor <;> trivial


/-
# 9.1.10.6

Prove or disprove that {a : ℕ | 20 ∣ a} ⊆ {x : ℕ | 5 ∣ x}
-/
example : {a : ℕ | 20 ∣ a} ⊆ {x : ℕ | 5 ∣ x} := by
  dsimp [Set.subset_def]
  intros a ha
  dsimp [(.∣.)] at *
  obtain ⟨c, hc⟩ := ha
  use 4 * c
  calc
    a = 20 * c := by rw [hc]
    _ = 5 * (4 * c) := by ring


/-
# 9.1.10.7

Prove or disprove that {a : ℕ | 5 ∣ a} ⊆ {x : ℕ | 20 ∣ x}
-/
example : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
  dsimp [Set.subset_def]
  push_neg
  use 5
  constructor
  . use 1; numbers;
  . exact of_decide_eq_false rfl


/-
# Exercise 9.2.8.5

Prove that {r : ℤ | r ≡ 7 mod 10} ⊆ {s : ℤ | s ≡ 1 mod 2} ∩ {t : ℤ | t ≡ 2 mod 5}
-/
example : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  dsimp [Set.subset_def]
  intros x hx
  dsimp [Int.ModEq, (.∣.)] at *
  obtain ⟨c, hc⟩ := hx
  constructor
  . use 5 * c + 3
    calc
      x - 1 = (x - 7) + 6 := by ring
      _ = 10 * c + 6 := by rw [hc]
      _ = 2 * (5 * c + 3) := by ring
  . use 2 * c + 1
    calc
      x - 2 = (x - 7) + 5 := by ring
      _ = 10 * c + 5 := by rw [hc]
      _ = 5 * (2 * c + 1) := by ring
