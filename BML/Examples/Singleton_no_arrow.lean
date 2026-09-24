/-
Copyright (c) 2026 MoL Lean Club. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: see COLLABORATORS.md
-/

import BML.Def

/-! A simple model with a single world and no arrow. -/

open BML

namespace SingletonWithNoArrow

/-- The only world is called `w`. -/
abbrev World := Fin 1
def w : World := 0

/-- Defines the atomic propositions {p, q, r} -/
def p : Proposition String := Proposition.atom "p"
def q : Proposition String := Proposition.atom "q"

/-- M, w ⊧ p and M, w ⊭ q -/
def M : Model World String := {
  r := fun _ _ => False,
  v := fun w p => match w, p with
    | 0, "p" => True
    | 0, "q" => False
    | _, _ => False
}

lemma w_only_world : ∀ w', w = w' := by
  simp [w]

lemma w_no_successor : ¬∃ w', M.r w w' := by
  simp [w, M]

lemma w_sat_p : Proposition.eval M w p := by
  simp only [w, p, Proposition.eval, M]

theorem w_sat_not_q : Proposition.eval M w q.not := by
  simp only [w, q, Proposition.eval, M, not_false_eq_true]

theorem w_sat_box_phi (φ : Proposition String) : Proposition.eval M w φ.box := by
  simp [M]

theorem box_phi_valid (φ : Proposition String) : Proposition.eval_global M φ.box := by
  simp [Proposition.eval_global, M]

theorem w_sat_not_diam_phi (φ : Proposition String) : Proposition.eval M w φ.diamond.not := by
  simp only [Proposition.eval, not_exists, not_and]
  intro x h
  exfalso
  apply w_no_successor
  use x

end SingletonWithNoArrow
