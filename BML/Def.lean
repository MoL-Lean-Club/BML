/-
Copyright (c) 2026 MoL Lean Club. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: see COLLABORATORS.md
-/

import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Tauto

/-!
We start from the basic definitions of modal logic from
`CSLib.Logic.Modal`.
-/

/-! # Modal Logic

Modal logic is a logic for reasoning about relational structures, studying statements about
necessity (`□φ`) and possibility (`◇φ`).

## References

* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]
-/

namespace BML

/-- A model consists of a relation between worlds `r` and a valuation `v`. -/
structure Model (World : Type) (Atom : Type) where
  /-- World accessibility relation. -/
  r : World → World → Prop
  /-- Valuation of atoms at a world. -/
  v : World → Atom → Prop

/-- Propositions. -/
inductive Proposition (Atom : Type) : Type where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Negation. -/
  | not (φ : Proposition Atom)
  /-- Conjunction. -/
  | and (φ₁ φ₂ : Proposition Atom)
  /-- Possibility. -/
  | diamond (φ : Proposition Atom)

/-- M,w ⊨ φ -/
def eval {World Atom} (M : Model World Atom) (w : World) : Proposition Atom → Prop
  | .atom p => M.v w p
  | .not φ => ¬ eval M w φ
  | .and φ1 φ2 => eval M w φ1 ∧ eval M w φ2
  | .diamond φ => ∃ x : World, M.r w x ∧ eval M x φ

/-- M ⊨ φ -/
def model_eval {World Atom} (M : Model World Atom) : Proposition Atom → Prop
  | φ => ∀ w : World, eval M w φ

/-- M ⊨ φ iff for all world w: M ⊨ φ -/
lemma model_true {World Atom} (M : Model World Atom) (φ : Proposition Atom) : model_eval M φ ↔ ∀w : World, eval M w φ := by
  trivial

def Proposition.or : Proposition A → Proposition A → Proposition A
  | φ1, φ2 => (φ1.not.and φ2.not).not

lemma eval_or : eval M w (φ1.or φ2) ↔ eval M w φ1 ∨ eval M w φ2 := by
  unfold Proposition.or
  simp only [eval, not_and, not_not]
  tauto

end BML
