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
def eval (M : Model World Atom) (w : World) : Proposition Atom → Prop
  | .atom p => M.v w p
  | .not φ => ¬ eval M w φ
  | .and φ₁ φ₂ => eval M w φ₁ ∧ eval M w φ₂
  | .diamond φ => ∃ x : World, M.r w x ∧ eval M x φ

/-- M ⊨ φ -/
def eval_global (M : Model World Atom) : Proposition Atom → Prop
  | φ => ∀ w : World, eval M w φ

def or : Proposition Atom → Proposition Atom → Proposition Atom
  | φ₁, φ₂ => (φ₁.not.and φ₂.not).not

@[simp]
lemma eval_or : eval M w (φ₁.or φ₂) ↔ eval M w φ₁ ∨ eval M w φ₂ := by
  unfold Proposition.or
  simp only [eval, not_and, not_not]
  tauto

@[simp]
lemma eval_diamond :
    eval M w (.diamond φ) ↔ ∃ x : World, M.r w x ∧ eval M x φ := by
  simp [eval]

def imply : Proposition Atom → Proposition Atom → Proposition Atom
  | φ₁, φ₂ => (φ₁.and φ₂.not).not

@[simp]
lemma eval_imply : eval M w (φ₁.imply φ₂) ↔ (eval M w φ₁ -> eval M w φ₂) := by
  unfold Proposition.imply
  simp only [eval, not_and, not_not]

def box : Proposition A → Proposition A
  | φ => φ.not.diamond.not

lemma eval_box : eval M w φ.box ↔ ∀ x, M.r w x → eval M x φ := by
  unfold Proposition.box
  simp only [eval, not_exists, not_and, not_not]

@[simp]
lemma eval_not : eval M w φ.not ↔ ¬ (eval M w φ) := by
  rfl

@[simp]
lemma eval_and : eval M w (φ₁.and φ₂) ↔ eval M w φ₁ ∧ eval M w φ₂ := by
  rfl

end Proposition



/-- Definition 2.16 -/
class Bisimulation {World1 World2 : Type} {Atom : Type}
  (M1 : Model World1 Atom) (M2 : Model World2 Atom) where

  /-- Relation between worlds of the two models. -/
  Z : World1 → World2 → Prop

  /- Z is non-empty -/
  nonempty : ∃ w1 w2, Z w1 w2

  /- Related world have the same proposition letters -/
  same_atoms : ∀ w1 w2, Z w1 w2 → ∀ p, M1.v w1 p ↔ M2.v w2 p

  /- Forth condition -/
  forth : ∀ w1 w2 v1, Z w1 w2 → M1.r w1 v1 → ∃ v2, M2.r w2 v2 ∧ Z v1 v2

  /- Back condition -/
  back : ∀ w1 w2 v2, Z w1 w2 → M2.r w2 v2 → ∃ v1, M1.r w1 v1 ∧ Z v1 v2


/-- Theorem 2.20: Bisimilar worlds are modally equivalent -/
theorem bisimular_worlds_are_modally_equivalent {World1 World2 : Type} {Atom : Type}
  {M1 : Model World1 Atom} {M2 : Model World2 Atom}
  (B : Bisimulation M1 M2) (w1 : World1) (w2 : World2) (h : B.Z w1 w2) :
  ∀ φ, Proposition.eval M1 w1 φ ↔ Proposition.eval M2 w2 φ := by
  intro φ
  induction φ generalizing w1 w2 h with
  | atom p =>
    exact B.same_atoms w1 w2 h p
  | not ψ ih =>
    simp only [Proposition.eval]
    rw [ih]
    exact h
  | and ψ₁ ψ₂ ih₁ ih₂ =>
    simp only [Proposition.eval]
    rw [(ih₁ w1 w2 h), (ih₂ w1 w2 h)]
  | diamond ψ ih =>
    simp only [Proposition.eval]
    constructor
    · intro ltr
      obtain ⟨v1, hr, hψ⟩ := ltr
      obtain ⟨v2, hr', hZ⟩ := B.forth w1 w2 v1 h hr
      use v2
      constructor
      · exact hr'
      · exact (ih v1 v2 hZ).mp hψ
    · intro rtl
      obtain ⟨v2, hr, hψ⟩ := rtl
      obtain ⟨v1, hr', hZ⟩ := B.back w1 w2 v2 h hr
      use v1
      constructor
      · exact hr'
      · exact (ih v1 v2 hZ).mpr hψ

end BML
