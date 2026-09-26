/-
Copyright (c) 2026 MoL Lean Club. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: see COLLABORATORS.md
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
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
  /-- Bottom element. -/
  | bot
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

def top : Proposition Atom := Proposition.bot.not

@[simp]
lemma eval_top : eval M w Proposition.top := by
  unfold Proposition.top
  tauto

end Proposition



/-- Definition 2.16 -/
class Bisimulation {World1 World2 : Type} {Atom : Type}
  (M1 : Model World1 Atom) (M2 : Model World2 Atom) where

  /-- Relation between worlds of the two models. -/
  Z : World1 → World2 → Prop

  /- Z is non-empty -/
  -- nonempty : ∃ w1 w2, Z w1 w2

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
  | bot =>
    simp only [Proposition.eval]
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


/- Image-finite definition for model with 1 relation-/
def image_finite {World Atom : Type} (M : Model World Atom) : Prop :=
  ∀ w, Set.Finite {v | M.r w v}


/-- Theorem 2.24: Hennessey-Milner -/
theorem hennessey_milner
  {World1 World2 Atom : Type}
  {M1 : Model World1 Atom}
  {M2 : Model World2 Atom}
  (h1 : image_finite M1)
  (h2 : image_finite M2)
  (w1 : World1) (w2 : World2) :
  (∃ B : Bisimulation M1 M2, B.Z w1 w2) ↔
  (∀ φ, Proposition.eval M1 w1 φ ↔ Proposition.eval M2 w2 φ) := by
  constructor
  /- This is theorem 2.20 -/
  · intro h
    obtain ⟨B, hZ⟩ := h
    exact bisimular_worlds_are_modally_equivalent B w1 w2 hZ
  /- Prove that modal equivalence is a bisimulation -/
  · intro h
    let Z : World1 → World2 → Prop :=
      fun w1 w2 => ∀ φ, Proposition.eval M1 w1 φ ↔ Proposition.eval M2 w2 φ
    /- Same atoms -/
    have same_atoms : ∀ w1 w2, Z w1 w2 → ∀ p, (M1.v w1 p ↔ M2.v w2 p) := by
      intro w1 w2 hZ p
      specialize hZ (Proposition.atom p)
      exact hZ
    /- Forth condition -/
    have forth : ∀ w1 w2 v1, Z w1 w2 → M1.r w1 v1 → ∃ v2, M2.r w2 v2 ∧ Z v1 v2 := by
      intro w1 w2 v1 hZ hr
      classical
      by_contra
      /- Define S' -/
      let S' : Set World2 := {v2 | M2.r w2 v2}
      /- Show that S' is non-empty -/
      have hS' : ∃ v2, M2.r w2 v2 := by
        by_contra hhS'
        /- M2, w2 ⊩ □ ⊥ -/
        have boxBot : Proposition.eval M2 w2 (Proposition.bot.box) := by
          unfold Proposition.box
          simp only [Proposition.eval, not_exists, not_and, not_not]
          intro v2 hr
          exact hhS' ⟨v2, hr⟩
        /- M1, w1 ⊩ ◇ ⊤ -/
        have diamondTop : Proposition.eval M1 w1 (Proposition.top.diamond) := by
          use v1
          constructor
          · exact hr
          · exact False.elim
        /- M2, w2 ⊩ ◇ ⊤ -/
        have diamondTop' : Proposition.eval M2 w2 (Proposition.top.diamond) := by
          specialize hZ (Proposition.top.diamond)
          exact hZ.mp diamondTop
        /- Now derive the contradiction -/
        unfold Proposition.eval at diamondTop'
        simp only [Proposition.eval_top] at diamondTop'
        rw [Proposition.eval_box] at boxBot
        unfold Proposition.eval at boxBot
        rcases diamondTop' with ⟨v2, hr', h⟩
        specialize boxBot v2 hr'
        exact boxBot
      /- We now proceed to build the described conjuction and disjunction -/
      /- First prove that for each w' ∈ S', the ψ in the book exists -/
      have phi_exists_for_each_member_of_S :
        ∀ w' ∈ S', ∃ ψ , Proposition.eval M1 v1 ψ ∧ ¬ Proposition.eval M2 w' ψ := by
        intro w' hw'
        /- w' is neighbor of w2 -/
        have hr' : M2.r w2 w' := hw'
        push Not at this
        specialize this w' hr'
        unfold Z at this
        push Not at this
        rcases this with ⟨ψ, hψ⟩
        rcases hψ with ⟨hψ1, hψ2⟩
        · use ψ
        · use ψ.not
          simp only [Proposition.eval, not_not]
          tauto
      /- Show that S' is finite by image-finiteness -/
      have hS'finite : Set.Finite S' := by apply h2 w2
      let S := (hS'finite).toFinset
      /- Now, construct the finite conjunction of these formulas -/
      choose ψ hψ1 hψ2 using phi_exists_for_each_member_of_S
      /- With attach we create a list of pairs (world, proof) that we need to extract ψ -/
      let enumerated_S := S.attach.toList
      /- φ = ⋄ ( ψ1 ∧ … ∧ ψn )-/
      let φ := Proposition.diamond ((enumerated_S.map (fun w' => ψ w'.1 (
          hS'finite.mem_toFinset.mp w'.2
        ))).foldr (fun formula acc => Proposition.and formula acc) Proposition.top)
      /- Now, we show that M1, v1 ⊩ ◇ φ -/
      have phi_at_v1 :
        Proposition.eval M1 w1 φ
        := by
        --
        unfold φ
        simp only [Proposition.eval_diamond]
        use v1
        constructor
        · exact hr
        · induction enumerated_S with
          | nil => tauto
          | cons w' ws ih =>
            simp only [List.map, List.foldr]
            have hψ := hψ1 w'.1 (hS'finite.mem_toFinset.mp w'.2)
            simp only [Proposition.eval_and]
            constructor
            · exact hψ
            · exact ih
      /- Now, we show that M2, w2  ⊩ ¬φ -/





      /- We now have a contradiction -/
      specialize hZ φ
      sorry

    /- Back condition -/
    have back : ∀ w1 w2 v2, Z w1 w2 → M2.r w2 v2 → ∃ v1, M1.r w1 v1 ∧ Z v1 v2 := by
      sorry

    /- Construct the bisimulation -/
    use { Z := Z, same_atoms := same_atoms, forth := forth, back := back }
    tauto








end BML
