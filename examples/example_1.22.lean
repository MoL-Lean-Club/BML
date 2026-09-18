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
def World : Type :=
  { n : Nat // n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 }

def w1 : World := (⟨1, by simp⟩ : World)
def w2 : World := (⟨2, by simp⟩ : World)
def w3 : World := (⟨3, by simp⟩ : World)
def w4 : World := (⟨4, by simp⟩ : World)
def w5 : World := (⟨5, by simp⟩ : World)


/-- Defines the atomic propositions {p, q} -/
def Atom : Type :=
  { atom : String // atom = "p" ∨ atom = "q"}
def p : Proposition Atom := (Proposition.atom (⟨"p", by simp⟩ : Atom) : Proposition Atom)
def q : Proposition Atom := (Proposition.atom (⟨"q", by simp⟩ : Atom) : Proposition Atom)

/-- Defines the model -/
def model : Model World Atom := {
  r := fun v w => w.1 = v.1 + 1,
  v := fun w p => match p.1 with
    | "p" => w.1 ∈ ({2, 3} : Set Nat)
    | "q" => w.1 ∈ ({1, 2, 3, 4, 5} : Set Nat)
    | _ => False
}

/- L1: w1 ⊩ □ ◇ p-/
lemma L1 :  Proposition.eval
    model
    w1
    (Proposition.box (Proposition.diamond p) : Proposition Atom)
  := by
  simp only [Proposition.eval_box]
  intro x hx
  /- We derive that the only accessible world from w1 is w2 -/
  have x_val : x = w2 := by
    simp only [model] at hx
    apply Subtype.ext
    exact hx
  rw [x_val]
  use w3
  tauto

/- L2: w1 ⊮ □ ◇ p → p-/

/- L3: w2 ⊩ ◇ (p ∧ ¬ r)-/

/- L4: w1 ⊩ q ∧ ◇(q ∧ ◇(p ∧ ◇ (q ∧ ◇ q)))-/

/- L5: ⊩ □ q -/
