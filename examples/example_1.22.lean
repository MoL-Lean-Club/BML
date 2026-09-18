/-
Copyright (c) 2026 MoL Lean Club. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: see COLLABORATORS.md

This file contains example 1.22 (i) from BdRV.

## References

* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]
-/


import BML.Def
open BML


/-- Defines the worlds {w1, w2, w3, w4, w5} -/
abbrev World := Fin 5
def w1 : World := 0
def w2 : World := 1
def w3 : World := 2
def w4 : World := 3
def w5 : World := 4

/-- Defines the atomic propositions {p, q, r} -/
def p : Proposition String := Proposition.atom "p"
def q : Proposition String := Proposition.atom "q"
def r : Proposition String := Proposition.atom "r"

/-- Defines the model -/
def model : Model World String := {
  r := fun v w => w.val = v.val + 1,
  v := fun w p => match p with
    | "p" => w.val ∈ ({1, 2} : Set Nat)
    | "q" => True
    | _ => False
}

/- L1: w1 ⊩ □ ◇ p-/
lemma L1 :  Proposition.eval
    model
    w1
    (Proposition.box (Proposition.diamond p) : Proposition String)
  := by
  simp only [Proposition.eval_box]
  intro x hx
  /- We derive that the only accessible world from w1 is w2 -/
  have x_val : x = w2 := by
    apply Fin.ext /- this extracts the value of the Fin type -/
    simp only [model, w1, w2] at hx ⊢
    exact hx
  rw [x_val]
  use w3
  tauto


/- L2: w1 ⊮ □ ◇ p → p-/


/- L3: w2 ⊩ ◇ (p ∧ ¬ r)-/
lemma L3 : Proposition.eval
    model
    w2
    (Proposition.diamond (p.and (r.not)) : Proposition String)
  := by
  simp only [Proposition.eval]
  use w3
  tauto

/- L4: w1 ⊩ q ∧ ◇(q ∧ ◇(q ∧ ◇ (q ∧ ◇ q)))-/
lemma L4 : Proposition.eval
    model
    w1
    (q.and
      (Proposition.diamond (q.and
        (Proposition.diamond (q.and
          (Proposition.diamond (q.and
            (Proposition.diamond q))))))) : Proposition String)
  := by
  simp only [Proposition.eval, model, q, true_and, and_true]
  use w2
  constructor
  · tauto
  use w3
  constructor
  · tauto
  use w4
  constructor
  · tauto
  use w5
  tauto

/- L5: ⊩ □ q -/
lemma L5 : ∀ w, Proposition.eval model w (Proposition.box q : Proposition String) := by
  intro w
  simp only [Proposition.eval_box]
  intro x hx
  simp only [Proposition.eval, model, q]
