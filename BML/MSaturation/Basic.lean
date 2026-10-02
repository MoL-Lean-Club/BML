/-
Copyright (c) 2026 MoL Lean Club. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: see COLLABORATORS.md
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Tauto

import BML.Def

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

open BML


namespace MSaturation

def m_saturated {World Atom : Type} (M : Model World Atom) : Prop :=
  let successors (w : World) : Set World := { v | M.r w v }
  ∀ (w : World) (S : Set (Proposition Atom)),
    finitely_satisfiable_in M (successors w) S
    → satisfiable_in M (successors w) S

def has_hennessey_milner_property {World Atom : Type} (M : Model World Atom) : Prop :=
  ∀ w1 w2, (∀ φ, Proposition.eval M w1 φ ↔ Proposition.eval M w2 φ)
  → ∃ B : Bisimulation M M, B.Z w1 w2

/- Helper functions to build a conjunction from a finite set of propositions -/
/-- Convert a list of propositions to a single proposition using conjunction. -/
def list_and {Atom : Type} : List (Proposition Atom) → Proposition Atom
  | [] => Proposition.top
  | φ :: φs => φ.and (list_and φs)

/-- Satisfying the list of propositions is equivalent to satisfying the conjunction of the list. -/
lemma list_equiv_to_modal_formula
    {World Atom : Type} {M : Model World Atom} {w : World}
    (L : List (Proposition Atom)) :
    (∀ φ ∈ L, (M, w) ⊨ φ) ↔ (M, w) ⊨ list_and L := by
  induction L with
  | nil =>
      simp [list_and, Proposition.top]
  | cons φ L ih =>
      simp [list_and, ih]

/-- Satisfying the finite set of propositions is equivalent to satisfying the conjunction of
the set. -/
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
      have S_finitely_satisfiable : finitely_satisfiable_in M2 { v | M2.r w' v } S := by
        unfold finitely_satisfiable_in
        intro S' hS'
        unfold satisfiable_in
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
      have S_finitely_satisfiable : finitely_satisfiable_in M1 { v | M1.r v1 v } S := by
        unfold finitely_satisfiable_in
        intro S' hS'
        unfold satisfiable_in
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



end MSaturation
