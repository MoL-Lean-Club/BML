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

/-- M ⊨ φ -/
def eval_global (M : Model World Atom) (φ : Proposition Atom) : Prop
  := ∀ w : World, eval M w φ

/-- 𝔽 ⊨ φ -/
def frame_valid (F : Frame World) (φ : Proposition Atom) : Prop
  := ∀ V : Valuation World Atom, eval_global ⟨F, V⟩ φ

def or : Proposition Atom → Proposition Atom → Proposition Atom
  | φ₁, φ₂ => (φ₁.not.and φ₂.not).not

def imply : Proposition Atom → Proposition Atom → Proposition Atom
  | φ₁, φ₂ => (φ₁.and φ₂.not).not

def iff (φ₁ φ₂ : Proposition Atom) :=
  (φ₁.imply φ₂).and (φ₂.imply φ₁)

def box : Proposition A → Proposition A
  | φ => φ.not.diamond.not

@[simp]
lemma eval_atom : eval M w (atom p) ↔ M.v w p := by
  unfold eval
  simp

@[simp]
lemma eval_or : eval M w (φ₁.or φ₂) ↔ eval M w φ₁ ∨ eval M w φ₂ := by
  unfold Proposition.or
  simp only [eval, not_and, not_not]
  tauto

@[simp]
lemma eval_imply : eval M w (φ₁.imply φ₂) ↔ (eval M w φ₁ -> eval M w φ₂) := by
  unfold Proposition.imply
  simp only [eval, not_and, not_not]

@[simp]
lemma eval_diamond : eval M w (Proposition.diamond φ₁) ↔ ∃ x, M.r w x ∧ eval M x φ₁ := by
  simp only [eval]

@[simp]
lemma eval_box : eval M w φ.box ↔ ∀ x, M.r w x → eval M x φ := by
  unfold Proposition.box
  simp only [eval, not_exists, not_and, not_not]

@[simp]
lemma eval_not : eval M w φ.not ↔ ¬ (eval M w φ) := by
  rfl

@[simp]
lemma eval_and : eval M w (φ₁.and φ₂) ↔ eval M w φ₁ ∧ eval M w φ₂ := by
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

section

variable {World1 World2 Atom : Type}
variable {M1 : Model World1 Atom} {M2 : Model World2 Atom}


/-- Definition 2.10 -/
class BoundedMorphism (f : World1 → World2) where
  /- w and f(w) satisfy the same proposition letters -/
  same_prop : ∀ w p, M1.v w p ↔ M2.v (f w) p

  /- homomorphism -/
  hom : ∀ w v, M1.r w v → M2.r (f w) (f v)

  /- back condition -/
  back : ∀ w v', M2.r (f w) v' → ∃ v, M1.r w v ∧ f v = v'


/-- Proposition 2.14 -/
lemma model_satisfaction_invariance_under_bounded_morphism
  {f : World1 → World2}
  (hf : BoundedMorphism (M1 := M1) (M2 := M2) f)
  (w : World1)
  (φ : Proposition Atom) :
  Proposition.eval M1 w φ ↔ Proposition.eval M2 (f w) φ := by
  induction φ generalizing w with
  | atom p => exact hf.same_prop w p
  | not φ ih => simp [Proposition.eval, ih]
  | and φ₁ φ₂ ih₁ ih₂ => simp [Proposition.eval, ih₁, ih₂]
  | diamond φ ih =>
      constructor
      · intro h
        simp only [Proposition.eval, ih] at h
        rcases h with ⟨v, hv, hφ⟩
        have h' : M2.r (f w) (f v) := hf.hom w v hv
        simp only [Proposition.eval]
        use f v
      · intro h
        simp only [Proposition.eval] at h
        rcases h with ⟨v', hv', hφ⟩
        obtain ⟨v, hv, h_eq⟩ := hf.back w v' hv'
        simp only [Proposition.eval]
        use v
        constructor
        · exact hv
        · specialize ih v
          rw [← h_eq] at hφ
          exact ih.mpr hφ

end

end BML
