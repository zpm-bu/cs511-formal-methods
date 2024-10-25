import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

--Exercise 5.1.7.6

@[autograded 2]
example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  obtain ⟨h_if_p_then_q, h_if_q_then_p⟩ := h
  constructor
  . intro p_and_r
    obtain ⟨p, r⟩ := p_and_r
    constructor
    . apply h_if_p_then_q p
    . apply r
  . intro q_and_r
    obtain ⟨q, r⟩ := q_and_r
    constructor
    . apply h_if_q_then_p q
    . apply r

--Exercise 5.1.7.8

@[autograded 2]
example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  . intro p_or_q
    obtain p | q := p_or_q
    . right
      apply p
    . left
      apply q
  . intro q_or_p
    obtain q | p := q_or_p
    . right
      apply q
    . left
      apply p

--Exercise 5.1.7.9

@[autograded 2]
example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  . intro not_p_or_q
    constructor
    . intro p
      have p_or_q : P ∨ Q := by
        left
        apply p
      contradiction
    . intro q
      have p_or_q : P ∨ Q := by
        right
        apply q
      contradiction
  . intro not_p_and_not_q
    intro p_or_q
    obtain ⟨not_p, not_q⟩ := not_p_and_not_q
    obtain p | q := p_or_q
    . contradiction
    . contradiction


--Exercise 5.1.7.11

@[autograded 2]
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  . intro hx
    obtain ⟨x, hx⟩ := hx
    have hpq := h x
    obtain ⟨hpq, hqp⟩ := hpq
    use x
    apply hpq
    apply hx
  . intro hx
    obtain ⟨x, hx⟩ := hx
    have hpq := h x
    obtain ⟨hpq, hqp⟩ := hpq
    use x
    apply hqp
    apply hx

--Exercise 5.1.7.12

@[autograded 2]
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  . intro h
    obtain ⟨x, y, h⟩ := h
    use y, x
    apply h
  . intro h
    obtain ⟨y, x, h⟩ := h
    use x, y
    apply h

--Exercise 5.1.7.13

@[autograded 2]
example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  . intros h
    intros y x
    apply h
  . intros h
    intros x y
    apply h
