import BML.Def

open BML
open Proposition

namespace BML
namespace Frame

variable {World : Type}
variable {Atom : Type}
variable {𝔽 : Frame World}
variable {w : World}
variable {p : Atom}



lemma frame_eval_diamondp_implies_diamonddiamondp_implies_relation_is_transitive :
  frame_valid 𝔽 (
    (diamond (diamond (atom p))).imply (diamond (atom p))
  ) ->
  transitive 𝔽 := by

  unfold transitive
  unfold frame_valid

  intro h_frame_valid
  intro u v w uRv vRw

  let V : Valuation World Atom :=
    fun w' p' ↦ w' = w ∧ p' = p

  have h_frame_valid_w := h_frame_valid V u

  have u_diamond_diamond_p : eval ⟨𝔽, V⟩ u (diamond (diamond (atom p))) := by
    simp only [eval_diamond, eval_atom]
    use v
    constructor
    · assumption
    · use w

  have u_diamond_p : eval ⟨𝔽, V⟩ u (diamond (atom p)) := by
    rw [eval_imply] at h_frame_valid_w
    apply h_frame_valid_w u_diamond_diamond_p

  rcases u_diamond_p with ⟨w₀, ⟨uRw₀, Vw₀⟩⟩

  have hw₀ : w₀ = w := by
    unfold V at Vw₀
    simp only [eval_atom, and_true] at Vw₀
    exact Vw₀

  rw [hw₀] at uRw₀
  exact uRw₀



lemma relation_transitive_implies_frame_eval_diamondp_implies_diamonddiamondp :
  transitive 𝔽 ->
  frame_valid 𝔽 (
    (diamond (diamond (atom p))).imply (diamond ((atom p)))
  ) := by

  unfold transitive
  unfold frame_valid

  intro htrans
  intro V

  intro u
  rw[eval_imply]
  intro hu
  rw[eval_diamond] at hu

  rcases hu with ⟨v, ⟨huv, ⟨w, ⟨hvw, hw⟩⟩⟩⟩

  have huw : 𝔽 u w := by
    exact htrans u v w huv hvw

  rw[eval_diamond]
  use w




theorem frame_eval_diamonddiamondp_implies_diamondp_iff_relation_is_transitive :
  frame_valid 𝔽 (
    (diamond (diamond (atom p))).imply (diamond (atom p))
  ) ↔
  transitive 𝔽 := by
  constructor
  · exact frame_eval_diamondp_implies_diamonddiamondp_implies_relation_is_transitive
  · exact relation_transitive_implies_frame_eval_diamondp_implies_diamonddiamondp



end Frame
end BML
