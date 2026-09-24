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

/-- A Frame is a relation on a set of worlds -/
def Frame (World : Type) := World → World → Prop
/--
A valuation is a function that assigns
truth values to atomic propositions at each world
-/
def Valuation (World Atom : Type) := World → Atom → Prop

def Frame.reflexive {World : Type} (F : Frame World) : Prop :=
  ∀ w : World, F w w

structure Model (World Atom : Type) where
  r : Frame World
  v : Valuation World Atom

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
def eval (M : Model World Atom) (w : World) : Proposition Atom → Prop
  | .atom p => M.v w p
  | .not φ => ¬ eval M w φ
  | .and φ₁ φ₂ => eval M w φ₁ ∧ eval M w φ₂
  | .diamond φ => ∃ x : World, M.r w x ∧ eval M x φ

/--
  Notation for the satisfaction relation.
  we add prop:50 to make sure this notation doesn't
  eat lower-precedence operators to the right of it.
-/
notation "(" model ", " world ")" " ⊨ " prop:50 => eval model world prop

/-- M ⊨ φ -/
def model_valid (M : Model World Atom) (φ : Proposition Atom) : Prop
  := ∀ w : World, (M, w) ⊨ φ

notation model " ⊨ " prop:50 => model_valid model prop

/-- 𝔽 ⊨ φ -/
def frame_valid (F : Frame World) (φ : Proposition Atom) : Prop
  := ∀ V : Valuation World Atom, ∀ w : World, (⟨F, V⟩, w) ⊨ φ

notation frame " ⊨ " prop:50 => frame_valid frame prop

/-- ⊨ φ -/
def valid (φ : Proposition Atom) : Prop
  := ∀ M : Model World Atom, ∀ world : World, (M, world) ⊨ φ

notation " ⊨ " prop:50 => valid prop

def or : Proposition Atom → Proposition Atom → Proposition Atom
  | φ₁, φ₂ => (φ₁.not.and φ₂.not).not

def imply : Proposition Atom → Proposition Atom → Proposition Atom
  | φ₁, φ₂ => (φ₁.and φ₂.not).not

def iff (φ₁ φ₂ : Proposition Atom) :=
  (φ₁.imply φ₂).and (φ₂.imply φ₁)

def box : Proposition A → Proposition A
  | φ => φ.not.diamond.not

@[simp]
lemma eval_atom
  : (M, w) ⊨ (atom p)
  ↔ M.v w p
  := by
  unfold eval
  simp

@[simp]
lemma eval_or
  : (M, w) ⊨ (φ₁.or φ₂)
  ↔ (M, w) ⊨ φ₁ ∨ (M, w) ⊨ φ₂
  := by
  unfold Proposition.or
  simp only [eval, not_and, not_not]
  tauto

@[simp]
lemma eval_imply
  : (M, w) ⊨ φ₁.imply φ₂
  ↔ (M, w) ⊨ φ₁ → (M, w) ⊨ φ₂
  := by
  unfold Proposition.imply
  simp only [eval, not_and, not_not]

@[simp]
lemma eval_diamond
  : (M, w) ⊨ Proposition.diamond φ₁
  ↔ ∃ x, M.r w x ∧ (M, x) ⊨ φ₁
  := by
  simp only [eval]

@[simp]
lemma eval_box
  : (M, w) ⊨ φ.box
  ↔ ∀ x, M.r w x → (M, x) ⊨ φ
  := by
  unfold Proposition.box
  simp only [eval, not_exists, not_and, not_not]

@[simp]
lemma eval_not
  : (M, w) ⊨ φ.not
  ↔ ¬ (M, w) ⊨ φ
  := by
  rfl

@[simp]
lemma eval_and
  : (M, w) ⊨ φ₁.and φ₂
  ↔ (M, w) ⊨ φ₁ ∧ (M, w) ⊨ φ₂
  := by
  rfl

end Proposition

end BML
