/-
Copyright (c) 2026 MoL Lean Club. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: see COLLABORATORS.md
-/

import Mathlib.Data.Set.Basic
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

section

variable {World1 World2 Atom : Type}
variable {M1 : Model World1 Atom} {M2 : Model World2 Atom}


/-- Definition 2.10 -/
structure BoundedMorphism (f : World1 → World2) where
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
