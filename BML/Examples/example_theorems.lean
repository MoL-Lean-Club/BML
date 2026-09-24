import BML.Def
import Mathlib.Logic.Relation

open BML Proposition

theorem p_implies_diamond_p_frame_refl
  {World Atom : Type}
  (F : Frame World)
  (p : Atom)
  : frame_valid F (imply (atom p) (diamond (atom p)))
  <-> F.reflexive :=
  by
    classical
    constructor
    /-
      Forward direction: if F ⊧ p → ◇p,
      then it is reflexive
    -/
    · intro f_valid w
      /-
        Pick a convenient valuation V that
        makes p true at w and false in all other worlds.
      -/
      let V : Valuation World Atom :=
        fun w' p' ↦ w' = w ∧ p' = p
      /-
        By frame validity, this valuation
        V must satisfy p → ◇p at w.
      -/
      have sat := f_valid V w
      /-
        Simplify using the semantics
      -/
      simp only [eval_imply, eval_diamond, eval_atom] at sat
      /-
        By definition of our valuation,
        the antecedent is true at w,
        so use that to obtain the consequent.
      -/
      have vwp : V w p := by simp [V]
      have dp := sat vwp
      /-
        Take a witness x of ◇p, which
        is a world x such that w R x and F, V, x ⊨ p.
        In a single step we unfold our
        valuation function to see that x must be equal to w.
        Why? Because the only world where p is true is w itself.
      -/
      rcases dp with ⟨x, left, xw, pp⟩
      /-
        Substitute out x everywhere
      -/
      subst x
      trivial
    /-
      Backward direction: if F is reflexive,
      then F ⊧ p → ◇p
    -/
    · intro f_refl
      simp only [frame_valid]
      intro V
      simp only [eval_global, eval_imply, eval_atom, eval_diamond]
      intro w h'
      have h2 := f_refl w -- specialise reflexivity to w
      use w
