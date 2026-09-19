/-
Copyright (c) 2026 MoL Lean Club. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: see COLLABORATORS.md
-/
import BML.Def

/-!
This file contains example 1.22 (i) from BdRV.
This model is
w1 → w2 → w3 → w4 → w5

with the following valuation:
w1: q
w2: p, q
w3: p, q
w4: q
w5: q


## References

* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]
-/

open BML
namespace BdRV

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
  v := fun w p => match w, p with
    | 1, "p" => True
    | 2, "p" => True
    | _, "q" => True
    | _, _ => False
}

/- Helper lemmas-/
lemma w2_only_successor_of_w1 : ∀ x, model.r w1 x → x = w2 := by
  intro x hx
  apply Fin.ext
  simp only [model, w1, w2] at hx ⊢
  exact hx

/- L1: w1 ⊩ □ ◇ p-/
lemma L1 :  Proposition.eval
    model
    w1
    (Proposition.box (Proposition.diamond p) : Proposition String)
  := by
  simp only [Proposition.eval_box]
  intro x hx
  rw [w2_only_successor_of_w1 x hx]
  use w3
  tauto

/- L2: w1 ⊮ □ ◇ p → p-/
lemma L2 : ¬ Proposition.eval
    model
    w1
    ((Proposition.box (Proposition.diamond p)).imply p : Proposition String)
  := by
  simp only [Proposition.eval_imply, Proposition.eval_box, Proposition.eval]
  intro h
  /- Antecedent is true at w1 -/
  have h1 : ∀ x, model.r w1 x → ∃ y, model.r x y ∧ Proposition.eval model y p := by
    intro x hx
    rw [w2_only_successor_of_w1 x hx]
    use w3
    tauto
  /- Consequent is false at w1 -/
  have h2 : ¬ Proposition.eval model w1 p := by
    simp only [Proposition.eval, model, w1, p]
    tauto
  tauto

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

end BdRV
