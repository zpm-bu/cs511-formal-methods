/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Prod.Basic
import Mathlib.Tactic.Replace

open Lean


theorem Prod.inj {a1 a2 : A} {b1 b2 : B} (h : (a1, b1) = (a2, b2)) : a1 = a2 ∧ b1 = b2 :=
  Iff.mp Prod.mk.inj_iff h

theorem Prod.inj2 {a1 a2 : A} {b1 b2 : B} {c1 c2 : C} (h : (a1, b1, c1) = (a2, b2, c2)) :
    a1 = a2 ∧ b1 = b2 ∧ c1 = c2 :=
  let h' := Prod.inj h
  ⟨h'.1, Prod.inj h'.2⟩

macro_rules
| `(tactic| obtain $pat? $[ :  $ty]? := $val) =>
  if Syntax.isIdent val then
    let h := val.raw.getId
    `(tactic|
      replace $(mkIdent h):ident := Prod.inj $(mkIdent h):ident ;
      obtain $pat? $[ :  $ty]? := $val)
  else
    `(tactic| have h := Prod.inj $val ; obtain $pat? $[ :  $ty]? := h)

macro_rules
| `(tactic| obtain $pat? $[ :  $ty]? := $val) =>
  if Syntax.isIdent val then
    let h := val.raw.getId
    `(tactic|
      replace $(mkIdent h):ident := Prod.inj2 $(mkIdent h):ident ;
      obtain $pat? $[ :  $ty]? := $val)
  else
    `(tactic| have h := Prod.inj2 $val ; obtain $pat? $[ :  $ty]? := h)
