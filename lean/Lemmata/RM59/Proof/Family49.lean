module

public import Lemmata.RM59.Proof.FlagTriples
public import Lemmata.RM59.Proof.FlagNine

@[expose] public section

namespace Lemmata.RM59.Family49

open Lemmata.RM59.FlagActions
open scoped symmDiff

theorem completion_nine (P : Finset (Point 9))
    (hp : AffineIndependent Field ((↑) : P → Point 9)) (hcard : P.card = 9) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G seed ∧ (G ∆ P).card ≤ 31 := by
  classical
  let e : P ≃ Fin 9 := Fintype.equivFinOfCardEq (by
    simpa only [Fintype.card_coe] using hcard)
  let p : Fin 9 → Point 9 := fun i => (e.symm i).val
  have hpi : Function.Injective p := Subtype.val_injective.comp e.symm.injective
  have hpa : AffineIndependent Field p := hp.comp_embedding e.symm.toEmbedding
  obtain ⟨G, hG, hc, q, hq, hm⟩ := FlagNine.cover_nine p hpa
  have hi : Function.Injective (p ∘ q) := hpi.comp hq
  have hs : Finset.univ.image (p ∘ q) ⊆ G ∩ P := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_inter.mpr ⟨hm i, (e.symm (q i)).property⟩
  have hn : 4 ≤ (G ∩ P).card := by
    have hh := Finset.card_le_card hs
    simpa only [Finset.card_image_of_injective _ hi, Finset.card_univ,
      Fintype.card_fin] using hh
  refine ⟨G, hG, ?_⟩
  apply symmDiff_card_le_of_intersection
  omega

theorem completion (P : Finset (Point 9))
    (hp : AffineIndependent Field ((↑) : P → Point 9))
    (hcard : P.card ∈ ({1, 3, 5, 7, 9} : Finset Nat)) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G seed ∧ (G ∆ P).card ≤ 31 := by
  have hcases : P.card = 1 ∨ P.card = 3 ∨ P.card = 5 ∨ P.card = 7 ∨ P.card = 9 := by
    simpa using hcard
  rcases hcases with h1 | h3 | h5 | h7 | h9
  · exact FlagTriples.completion_small P (by simp [h1])
  · exact FlagTriples.completion_small P (by simp [h3])
  · exact FlagTriples.completion_small P (by simp [h5])
  · exact FlagTriples.completion_small P (by simp [h7])
  · exact completion_nine P hp h9

end Lemmata.RM59.Family49
