module

public import Lemmata.RM59.Proof.FlagWitnessChecks
public import Lemmata.RM59.Proof.FlagGeometry

@[expose] public section

namespace Lemmata.RM59.FlagWitnessSound

open Lemmata.RM59.Packed Lemmata.RM59.FlagActions Lemmata.RM59.FlagWitnessChecks Lemmata.RM59.SupportForms

def canonical (which : Fin 2) (a b : Point 9) : Finset (Point 9) :=
  {0, a, b, a + b + decodePoint (basePoint which)}

theorem decoded_canonical (which : Fin 2) (a b : PackedPoint) :
    (canonicalQuad which a b).image decodePoint = canonical which (decodePoint a) (decodePoint b) := by
  simp only [canonicalQuad, canonical, Finset.image_insert, Finset.image_singleton,
    decodePoint_zero, decodePoint_xorPoint]

theorem vector_member (codes : Vector PackedPoint 4)
    (hcodes : ∀ i : Fin 4, codes.get i ∈ Certificate.seed 49) (x : PackedPoint)
    (hx : x ∈ codes.toList) : x ∈ Certificate.seed 49 := by
  obtain ⟨i, hi, he⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hx)
  have hm := hcodes ⟨i, hi⟩
  change codes[i] ∈ Certificate.seed 49 at hm
  simpa only [he] using hm

theorem canonical_available (which : Fin 2) (a b : PackedPoint)
    (hab : allowed which a b = true) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G seed ∧ G.card = 30 ∧
      canonical which (decodePoint a) (decodePoint b) ⊆ G := by
  obtain ⟨w, hw, he⟩ := witness_exists which a b hab
  let P := seed.image (wordLinear w.word)
  let G := translateSupport P (decodePoint w.shift)
  have hP : MatchSupportMoments 3 P seed := wordLinear_moments w.word
  have hlow : LowerZero P := by
    intro s hs
    rw [hP s (hs.trans (by decide : 2 ≤ 3)), seed_lowerZero s hs]
  refine ⟨G, (matchSupportMoments_translate P hlow _).trans hP, ?_, ?_⟩
  · change (translateSupport (seed.image (wordLinear w.word)) (decodePoint w.shift)).card = 30
    rw [translateSupport,
      Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h),
      Finset.card_image_of_injective _ (wordLinear_injective w.word), seed_card]
  · intro x hx
    rw [← decoded_canonical] at hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    rw [← he] at hz
    simp only [shiftedImages, images, List.mem_toFinset, List.mem_map] at hz
    obtain ⟨y, ⟨c, hc, rfl⟩, rfl⟩ := hz
    have hseed : decodePoint c ∈ seed := List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨c, vector_member w.codes hw c hc, rfl⟩)
    rw [decodePoint_xorPoint, decode_wordPacked]
    exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hseed)

theorem normalizing_word (which : Fin 2) (x : Point 9)
    (hx : pointAllowed which (encodePoint x) = true) :
    ∃ word : Word, wordLinear word x = decodePoint (basePoint which) := by
  obtain ⟨word, hw⟩ := point_word_exists which (encodePoint x) hx
  refine ⟨word, ?_⟩
  simpa only [decode_wordPacked, decodePoint_encodePoint] using congrArg decodePoint hw

end Lemmata.RM59.FlagWitnessSound
