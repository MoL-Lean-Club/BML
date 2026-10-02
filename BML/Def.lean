/-
Copyright (c) 2026 MoL Lean Club. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: see COLLABORATORS.md
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
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

def or : Proposition Atom → Proposition Atom → Proposition Atom
  | φ₁, φ₂ => (φ₁.not.and φ₂.not).not

def imply : Proposition Atom → Proposition Atom → Proposition Atom
  | φ₁, φ₂ => (φ₁.and φ₂.not).not

def iff (φ₁ φ₂ : Proposition Atom) :=
  (φ₁.imply φ₂).and (φ₂.imply φ₁)

def box : Proposition A → Proposition A
  | φ => φ.not.diamond.not

def top : Proposition Atom := Proposition.not Proposition.bot

@[simp]
lemma eval_top : (M, w) ⊨ Proposition.top := by
  unfold Proposition.top
  simp only [Proposition.eval, not_false_iff]

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


def satisfiable (φ : Proposition Atom) : Prop :=
  ∃ M : Model World Atom, ∃ w : World, (M, w) ⊨ φ

/-- Satisfiable in a set X ⊆ World if there exists a world in X that satisfies the proposition. -/
def satisfiable_in (M : Model World Atom) (X : Set World) (S : Set (Proposition Atom)) : Prop :=
  ∃ w : World, w ∈ X ∧ ∀ φ ∈ S, (M, w) ⊨ φ

def finitely_satisfiable_in
  (M : Model World Atom)
  (X : Set World)
  (S : Set (Proposition Atom))
  : Prop :=
  ∀ S' : Finset (Proposition Atom), (↑S' ⊆ S) → satisfiable_in M X S'

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
  ∀ φ, (M1, w1) ⊨ φ ↔ (M2, w2) ⊨ φ := by
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



section

def m_saturated {World Atom : Type} (M : Model World Atom) : Prop :=
  let successors (w : World) : Set World := { v | M.r w v }
  ∀ (w : World) (S : Set (Proposition Atom)),
    Proposition.finitely_satisfiable_in M (successors w) S
    → Proposition.satisfiable_in M (successors w) S



def has_hennessey_milner_property {World Atom : Type} (M : Model World Atom) : Prop :=
  ∀ w1 w2, (∀ φ, Proposition.eval M w1 φ ↔ Proposition.eval M w2 φ)
  → ∃ B : Bisimulation M M, B.Z w1 w2





def list_and {Atom : Type} : List (Proposition Atom) → Proposition Atom
  | [] => Proposition.top
  | φ :: φs => φ.and (list_and φs)

lemma list_equiv_to_modal_formula
    {World Atom : Type} {M : Model World Atom} {w : World}
    (L : List (Proposition Atom)) :
    (∀ φ ∈ L, (M, w) ⊨ φ) ↔ (M, w) ⊨ list_and L := by
  induction L with
  | nil =>
      simp [list_and, Proposition.top]
      tauto
  | cons φ L ih =>
      simp [list_and, ih]

lemma finset_equiv_to_modal_formula
    {World Atom : Type} {M : Model World Atom} {w : World}
    (S : Finset (Proposition Atom)) :
    (∀ φ ∈ S, (M, w) ⊨ φ) ↔ (M, w) ⊨ list_and S.toList := by
  classical
  rw [← list_equiv_to_modal_formula S.toList]
  simp


theorem m_saturated_imp_hennessey_milner_property
  {World1 World2 Atom : Type}
  {M1 : Model World1 Atom}
  {M2 : Model World2 Atom}
  (h1 : m_saturated M1)
  (h2 : m_saturated M2)
  (w1 : World1) (w2 : World2) :
  (∀ φ, (M1, w1) ⊨ φ ↔ (M2, w2) ⊨ φ)
  ↔ ∃ B : Bisimulation M1 M2, B.Z w1 w2 := by
  constructor
  · intro h
    /- The bisimulation is defined by the equivalence of modal formulas -/
    let Z : World1 → World2 → Prop := fun v1 v2 =>
      ∀ φ, (M1, v1) ⊨ φ ↔ (M2, v2) ⊨ φ
    /- Z is non-empty -/
    have hZ_nonempty : ∃ v1 v2, Z v1 v2 := by
      use w1, w2
    have hZ_same_atoms : ∀ v1 v2, Z v1 v2 → ∀ p, M1.v v1 p ↔ M2.v v2 p := by
      intro v1 v2 hZ p
      specialize hZ (Proposition.atom p)
      exact hZ
    /- Forth condition -/
    have hZ_forth : ∀ w w' v, Z w w' → M1.r w v → ∃ v', M2.r w' v' ∧ Z v v' := by
      intro w w' v hZ hr
      /- We show that the set of formulas satisfied by v1 is the same as the set of formulas
      satisfied by v2 -/
      let S := { φ | (M1, v) ⊨ φ }
      have S_finitely_satisfiable : Proposition.finitely_satisfiable_in M2 { v | M2.r w' v } S := by
        unfold Proposition.finitely_satisfiable_in
        intro S' hS'
        unfold Proposition.satisfiable_in
        /- φ = φ1 ∧ φ2 ∧ ... ∧ φn-/
        let φ := list_and S'.toList
        /- v ⊨ φ -/
        have φ_satisfiable_at_v : (M1, v) ⊨ φ := by
          /- S' satisfiable at v, since S' is a finite subset of S -/
          have S'_satisfiable_at_v : ∀ φ ∈ S', (M1, v) ⊨ φ := by
            intro φ hφ
            exact hS' hφ
          exact (finset_equiv_to_modal_formula S').mp S'_satisfiable_at_v
        /- w ⊨ ⋄ φ -/
        have diamond_φ_satisfiable_at_w : (M1, w) ⊨ φ.diamond := by
          unfold Proposition.eval
          use v
        /- Carry to w' using modal equivalence -/
        have diamond_φ_satisfiable_at_w' : (M2, w') ⊨ φ.diamond := by
          specialize hZ φ.diamond
          exact hZ.mp diamond_φ_satisfiable_at_w
        /- Obtain witness and proof for v' ⊨ φ-/
        obtain ⟨v', hr', φ_satisfiable_at_v'⟩ := diamond_φ_satisfiable_at_w'
        use v'
        constructor
        · exact hr'
        · exact (finset_equiv_to_modal_formula S').mpr φ_satisfiable_at_v'
      /- m-saturation gives us the witness and a proof for v_satisfiable_imp_v'_satisfiable -/
      obtain ⟨v', htemp⟩ := h2 w' S S_finitely_satisfiable
      have v_satisfiable_imp_v'_satisfiable : ∀ φ, (M1, v) ⊨ φ → (M2, v') ⊨ φ := by
        intro φ hφ
        exact htemp.2 φ hφ
      use v'
      apply And.intro
      · exact htemp.1
      · have v'_satisfiable_imp_v_satisfiable : ∀ φ, (M2, v') ⊨ φ → (M1, v) ⊨ φ := by
          classical
          by_contra h
          push Not at h
          obtain ⟨φ, hφ⟩ := h
          obtain ⟨hφ_v', hφ2⟩ := hφ
          have hnotφ_v : (M1, v) ⊨ φ.not := by
            rw [Proposition.eval_not]
            exact hφ2
          /- ¬ φ must be true at v' -/
          specialize v_satisfiable_imp_v'_satisfiable φ.not hnotφ_v
          /- This is a contradiction -/
          tauto
        /- Now derive Z v v' -/
        simp only [Z]
        intro φ
        constructor
        · exact v_satisfiable_imp_v'_satisfiable φ
        · exact v'_satisfiable_imp_v_satisfiable φ
    /- Back condition -/
    have hZ_back : ∀ v1 v2 v2', Z v1 v2 → M2.r v2 v2' → ∃ v1', M1.r v1 v1' ∧ Z v1' v2' := by
      intro v1 v2 v2' hZ hr
      /- We show that the set of formulas satisfied by v1 is the same as the set of formulas
      satisfied by v2 -/
      let S := { φ | (M2, v2') ⊨ φ }
      have S_finitely_satisfiable : Proposition.finitely_satisfiable_in M1 { v | M1.r v1 v } S := by
        unfold Proposition.finitely_satisfiable_in
        intro S' hS'
        unfold Proposition.satisfiable_in
        /- φ = φ1 ∧ φ2 ∧ ... ∧ φn-/
        let φ := list_and S'.toList
        /- v' ⊨ φ -/
        have φ_satisfiable_at_v' : (M2, v2') ⊨ φ := by
          /- S' satisfiable at v', since S' is a finite subset of S -/
          have S'_satisfiable_at_v' : ∀ φ ∈ S', (M2, v2') ⊨ φ := by
            intro φ hφ
            exact hS' hφ
          exact (finset_equiv_to_modal_formula S').mp S'_satisfiable_at_v'
        /- w' ⊨ ⋄ φ -/
        have diamond_φ_satisfiable_at_w' : (M2, v2) ⊨ φ.diamond := by
          unfold Proposition.eval
          use v2'
        /- Carry to w using modal equivalence -/
        have diamond_φ_satisfiable_at_w : (M1, v1) ⊨ φ.diamond := by
          specialize hZ φ.diamond
          exact hZ.mpr diamond_φ_satisfiable_at_w'
        /- Obtain witness and proof for v ⊨ φ-/
        obtain ⟨v1', hr', φ_satisfiable_at_v1'⟩ := diamond_φ_satisfiable_at_w
        use v1'
        constructor
        · exact hr'
        · exact (finset_equiv_to_modal_formula S').mpr φ_satisfiable_at_v1'
      obtain ⟨v1', htemp⟩ := h1 v1 S S_finitely_satisfiable
      have v'_satisfiable_imp_v1_satisfiable : ∀ φ, (M2, v2') ⊨ φ → (M1, v1') ⊨ φ := by
        intro φ hφ
        exact htemp.2 φ hφ
      use v1'
      apply And.intro
      · exact htemp.1
      · have v1_satisfiable_imp_v'_satisfiable : ∀ φ, (M1, v1') ⊨ φ → (M2, v2') ⊨ φ := by
          classical
          by_contra h
          push Not at h
          obtain ⟨φ, hφ⟩ := h
          obtain ⟨hφ_v1', hφ2⟩ := hφ
          have hnotφ_v2' : (M2, v2') ⊨ φ.not := by
            rw [Proposition.eval_not]
            exact hφ2
          /- ¬ φ must be true at v1' -/
          specialize v'_satisfiable_imp_v1_satisfiable φ.not hnotφ_v2'
          /- This is a contradiction -/
          tauto
        /- Now derive Z v1' v2' -/
        simp only [Z]
        intro φ
        constructor
        · exact v1_satisfiable_imp_v'_satisfiable φ
        · exact v'_satisfiable_imp_v1_satisfiable φ
    use {
        Z := Z,
        nonempty := hZ_nonempty,
        same_atoms := hZ_same_atoms,
        forth := hZ_forth,
        back := hZ_back
    }
  /- Converse is Theorem 2.20 -/
  · intro h
    obtain ⟨B, hZ⟩ := h
    exact bisimilar_worlds_are_modally_equivalent B w1 w2 hZ



end


end BML
