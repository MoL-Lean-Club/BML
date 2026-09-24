import BML.Def

open BML
open BML.Proposition
namespace Lemmas

variable {World Atom : Type}

lemma disjoint_union_invariance {M₁ M₂ : Model World Atom} {w : World}
    (φ : Proposition Atom) :
    eval (disjoint_union M₁ M₂) (.inl w) φ ↔ eval M₁ w φ := by
  induction φ generalizing w with
  | atom p => rfl
  | not φ ih => simp [eval, ih]
  | and φ₁ φ₂ ih₁ ih₂ => simp [eval, ih₁, ih₂]
  | diamond φ ih =>
      constructor
      · rintro ⟨z, hz, hφ⟩
        cases z with
        | inl z => exact ⟨z, hz, ih.mp hφ⟩
        | inr z => exact False.elim hz
      · rintro ⟨z, hz, hφ⟩
        exact ⟨.inl z, hz, ih.mpr hφ⟩

end Lemmas
