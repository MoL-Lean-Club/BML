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

namespace Frame

def reflexive {World : Type} (F : Frame World) : Prop :=
  ∀ w : World, F w w

def antisymmetric {World : Type} (F : Frame World) : Prop :=
  ∀ v w : World, F v w -> F w v -> w = v

def transitive {World : Type} (F : Frame World) : Prop :=
  ∀ u v w : World, F u v -> F v w -> F u w

end Frame

structure Model (World Atom : Type) where
  r : Frame World
  v : Valuation World Atom

/-- Propositions. -/
inductive Proposition (Atom : Type) : Type where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Bot -/
  | bot : Proposition Atom
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
  | .bot => False
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

def top : Proposition Atom := .not .bot

def or : Proposition Atom → Proposition Atom → Proposition Atom
  | φ₁, φ₂ => (φ₁.not.and φ₂.not).not

def imply : Proposition Atom → Proposition Atom → Proposition Atom
  | φ₁, φ₂ => (φ₁.and φ₂.not).not

def iff (φ₁ φ₂ : Proposition Atom) :=
  (φ₁.imply φ₂).and (φ₂.imply φ₁)

def box : Proposition A → Proposition A
  | φ => φ.not.diamond.not


@[simp]
lemma eval_bot
  : (M, w) ⊨ .bot
  ↔ False
  := by
  tauto

@[simp]
lemma eval_top
  : (M, w) ⊨ .top
  ↔ True
  := by
  tauto

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

def disjoint_union : Model World Atom → Model World Atom → Model (Sum World World) Atom
  | M₁, M₂ => {
    r := fun w₁ w₂ => match w₁, w₂ with
      | .inl x, .inl y => M₁.r x y
      | .inr x, .inr y => M₂.r x y
      | _, _ => False
    v := fun w p => match w with
      | .inl x => M₁.v x p
      | .inr x => M₂.v x p
  }
example {M₁ M₂ : Model World Atom} {x y : World} :
    M₁.r x y → (disjoint_union M₁ M₂).r (.inl x) (.inl y) := by
  intro h
  simpa [disjoint_union] using h





end Proposition



/-- Definition 2.16 -/
structure Bisimulation {World1 World2 : Type} {Atom : Type}
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
theorem bisimilar_worlds_are_modally_equivalent {World1 World2 : Type} {Atom : Type}
  {M1 : Model World1 Atom} {M2 : Model World2 Atom}
  (B : Bisimulation M1 M2) (w1 : World1) (w2 : World2) (h : B.Z w1 w2) :
  ∀ φ, Proposition.eval M1 w1 φ ↔ Proposition.eval M2 w2 φ := by
  intro φ
  induction φ generalizing w1 w2 h with
  | atom p =>
    exact B.same_atoms w1 w2 h p
  | bot =>
    simp [Proposition.eval]
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
