module

public import Lemmata.RM59.Proof.FlagNormalizing

@[expose] public section

namespace Lemmata.RM59.FlagCover

open Lemmata.RM59.Packed Lemmata.RM59.FlagActions Lemmata.RM59.FlagGeometry Lemmata.RM59.FlagNormalizing
open Lemmata.RM59.BinaryQuadGeometry Lemmata.RM59.SupportForms

theorem translate_moments (G : Finset (Point 9)) (hG : MatchSupportMoments 3 G seed)
    (t : Point 9) : MatchSupportMoments 3 (translateSupport G t) seed := by
  have hl : LowerZero G := by
    intro s hs
    rw [hG s (hs.trans (by decide : 2 ≤ 3)), seed_lowerZero s hs]
  exact (matchSupportMoments_translate G hl t).trans hG

theorem align_cleared (which : Fin 2) (p : Fin 4 → Point 9)
    (ht : sumFour p = base which) (G : Finset (Point 9))
    (hG : MatchSupportMoments 3 G seed) (hcard : G.card = 30)
    (hquad : quad (clearLinear which (p 0 + p 1)) (clearLinear which (p 0 + p 2))
      (base which) ⊆ G) :
    ∃ G' : Finset (Point 9), MatchSupportMoments 3 G' seed ∧ G'.card = 30 ∧ ∀ i, p i ∈ G' := by
  let a := p 0 + p 1
  let b := p 0 + p 2
  let α := a (baseIndex which)
  let β := b (baseIndex which)
  let s := β • a + α • b + (α * β) • base which
  have he : quad (clearLinear which a) (clearLinear which b) (base which) =
      (quad a b (base which)).image (fun x => x + s) :=
    clear_translation a b (base which) α β
  let G' := translateSupport G (p 0 + s)
  refine ⟨G', translate_moments G hG _, ?_, ?_⟩
  · change (translateSupport G (p 0 + s)).card = 30
    rw [translateSupport,
      Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h), hcard]
  · intro i
    have hp : p i ∈ (quad a b (base which)).image (fun x => x + p 0) := by
      have hi : p i ∈ Finset.univ.image p := Finset.mem_image_of_mem _ (Finset.mem_univ i)
      rw [quadruple_translate p] at hi
      simpa only [ht, a, b] using hi
    obtain ⟨x, hx, hxi⟩ := Finset.mem_image.mp hp
    have hxG : x + s ∈ G := by
      apply hquad
      change x + s ∈ quad (clearLinear which a) (clearLinear which b) (base which)
      rw [he]
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨x + s, hxG, ?_⟩
    calc
      (x + s) + (p 0 + s) = (x + p 0) + (s + s) := by ac_rfl
      _ = p i := by rw [point_add_self, add_zero, hxi]

theorem pullback_cover (word : Word) (p : Fin 4 → Point 9) (G : Finset (Point 9))
    (hG : MatchSupportMoments 3 G seed) (hcard : G.card = 30)
    (hp : ∀ i, wordLinear word (p i) ∈ G) :
    ∃ G' : Finset (Point 9), MatchSupportMoments 3 G' seed ∧ G'.card = 30 ∧ ∀ i, p i ∈ G' := by
  let e := wordEquiv word
  refine ⟨G.image e.symm,
    (matchSupportMoments_image hG e.symm.toLinearMap e.symm.injective).trans
      (inverse_moments word), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ e.symm.injective, hcard]
  · intro i
    refine Finset.mem_image.mpr ⟨wordLinear word (p i), hp i, ?_⟩
    exact e.symm_apply_apply (p i)

theorem sumFour_map (g : Point 9 →ₗ[Field] Point 9) (p : Fin 4 → Point 9) :
    sumFour (fun i => g (p i)) = g (sumFour p) := by
  simp only [sumFour, map_add]

theorem cover_A (p : Fin 4 → Point 9) (hp : AffineIndependent Field p)
    (ht : sumFour p ∉ space 2) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G seed ∧ G.card = 30 ∧ ∀ i, p i ∈ G := by
  have hallowed : FlagWitnessChecks.pointAllowed 0 (encodePoint (sumFour p)) = true := by
    apply (point_allowed_checked _ _).2
    simpa only [if_pos (show (0 : Fin 2).val = 0 from rfl), decodePoint_encodePoint] using ht
  obtain ⟨word, hw⟩ := FlagWitnessSound.normalizing_word 0 (sumFour p) hallowed
  let q : Fin 4 → Point 9 := fun i => wordLinear word (p i)
  have hq : AffineIndependent Field q := hp.map' (wordLinear word).toAffineMap
    (wordLinear_injective word)
  have hsum : sumFour q = base 0 := by
    rw [sumFour_map]
    exact hw
  have hLI := independent_sum_directions q hq
  rw [hsum] at hLI
  obtain ⟨G, hG, hn, hm⟩ := domain_available 0 _ _ (clear_domain_A _ _ hLI)
  obtain ⟨G', hG', hn', hm'⟩ := align_cleared 0 q hsum G hG hn hm
  exact pullback_cover word p G' hG' hn' hm'

theorem cover_B (p : Fin 4 → Point 9) (hp : AffineIndependent Field p)
    (E : Submodule Field (Point 9)) (ha : p 0 + p 1 ∈ E) (hb : p 0 + p 2 ∈ E)
    (htE : sumFour p ∈ E) (hH : E ≤ space 2) (hU : Disjoint E (space 0))
    (ht : sumFour p ∉ space 1) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G seed ∧ G.card = 30 ∧ ∀ i, p i ∈ G := by
  have hallowed : FlagWitnessChecks.pointAllowed 1 (encodePoint (sumFour p)) = true := by
    apply (point_allowed_checked _ _).2
    simpa only [if_neg (show (1 : Fin 2).val ≠ 0 by decide), decodePoint_encodePoint] using
      And.intro (hH htE) ht
  obtain ⟨word, hw⟩ := FlagWitnessSound.normalizing_word 1 (sumFour p) hallowed
  let g := wordLinear word
  let q : Fin 4 → Point 9 := fun i => g (p i)
  let F := E.map g
  have hq : AffineIndependent Field q := hp.map' g.toAffineMap (wordLinear_injective word)
  have hsum : sumFour q = base 1 := by rw [sumFour_map]; exact hw
  have hLI := independent_sum_directions q hq
  rw [hsum] at hLI
  have hFH : F ≤ space 2 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact (word_preserves word 2 y).2 (hH hy)
  have hFU : Disjoint F (space 0) := by
    apply Submodule.disjoint_def.2
    intro x hx hu
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    have hyU := (word_preserves word 0 y).1 hu
    rw [(Submodule.disjoint_def.1 hU) y hy hyU, map_zero]
  have haF : q 0 + q 1 ∈ F := Submodule.mem_map.mpr
    ⟨p 0 + p 1, ha, by rw [map_add] <;> rfl⟩
  have hbF : q 0 + q 2 ∈ F := Submodule.mem_map.mpr
    ⟨p 0 + p 2, hb, by rw [map_add] <;> rfl⟩
  have htF : base 1 ∈ F := Submodule.mem_map.mpr ⟨sumFour p, htE, hw⟩
  obtain ⟨G, hG, hn, hm⟩ := domain_available 1 _ _
    (clear_domain_B _ _ F hLI haF hbF htF hFH hFU)
  obtain ⟨G', hG', hn', hm'⟩ := align_cleared 1 q hsum G hG hn hm
  exact pullback_cover word p G' hG' hn' hm'

end Lemmata.RM59.FlagCover
