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

namespace Proposition

variable {World : Type}
variable {Atom : Type}
variable {M : Model World Atom}
variable {w : World}
variable {φ₁ φ₂ : Proposition Atom}

/-- M,w ⊨ φ -/
def eval {World : Type} {Atom : Type} (M : Model World Atom) (w : World) : Proposition Atom → Prop
  | .atom p => M.v w p
  | .not φ => ¬ eval M w φ
  | .and φ₁ φ₂ => eval M w φ₁ ∧ eval M w φ₂
  | .diamond φ => ∃ x : World, M.r w x ∧ eval M x φ

def or : Proposition Atom → Proposition Atom → Proposition Atom
  | φ₁, φ₂ => (φ₁.not.and φ₂.not).not

@[simp]
lemma eval_or : eval M w (φ₁.or φ₂) ↔ eval M w φ₁ ∨ eval M w φ₂ := by
  unfold Proposition.or
  simp only [eval, not_and, not_not]
  tauto

def imply : Proposition Atom → Proposition Atom → Proposition Atom
  | φ₁, φ₂ => (φ₁.and φ₂.not).not

@[simp]
lemma eval_imply : eval M w (φ₁.imply φ₂) ↔ (eval M w φ₁ -> eval M w φ₂) := by
  unfold Proposition.imply
  simp only [eval, not_and, not_not]


def box : Proposition A → Proposition A
  | φ => φ.not.diamond.not

@[simp]
lemma eval_box : eval M w φ.box ↔ ∀ x, M.r w x → eval M x φ := by
  unfold Proposition.box
  simp only [eval, not_exists, not_and, not_not]


end Proposition

end BML
