module

public import Lemmata.RM59.Proof.CatalogComplete
public import Lemmata.RM59.Proof.CatalogCompletion
public import Lemmata.RM59.Proof.SimplexSearchCheckCore
public import Lemmata.RM59.Proof.HeavyFamilies
public import Lemmata.RM59.Proof.Intersections
public import Lemmata.RM59.Proof.Family35
public import Lemmata.RM59.Proof.Family49
public import Lemmata.RM59.Proof.Family53Selection

@[expose] public section

namespace Lemmata.RM59.SimplexRepresentativeCompletion

open scoped symmDiff
open Packed SupportForms CatalogCompletion

theorem onepoint_completion (Q P : Finset (Point 9)) (hQ : LowerZero Q)
    (hQnonempty : Q.Nonempty) (hPnonempty : P.Nonempty) (hsize : Q.card + P.card ≤ 33) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G Q ∧ (G ∆ P).card ≤ 31 := by
  classical
  obtain ⟨q, hq⟩ := hQnonempty
  obtain ⟨p, hp⟩ := hPnonempty
  let G := translateSupport Q (p - q)
  have hGcard : G.card = Q.card :=
    Finset.card_image_of_injective Q (fun _ _ h => add_right_cancel h)
  have hpG : p ∈ G := by
    apply Finset.mem_image.mpr
    refine ⟨q, hq, ?_⟩
    simp [sub_eq_add_neg, add_comm, add_left_comm]
  have hintersection : 0 < (G ∩ P).card :=
    Finset.card_pos.mpr ⟨p, Finset.mem_inter.mpr ⟨hpG, hp⟩⟩
  refine ⟨G, translateSupport_sameMoments Q hQ _, ?_⟩
  apply symmDiff_card_le_of_intersection
  omega

private theorem seed_onepoint_completion (i : Fin 348) (P : Finset (Point 9))
    (hPnonempty : P.Nonempty) (hsize : (Certificate.seed (i.val + 1)).length + P.card ≤ 33) :
    ∃ G : Finset (Point 9),
      MatchSupportMoments 3 G (decodeWord (Certificate.seed (i.val + 1))) ∧
        (G ∆ P).card ≤ 31 := by
  have hnodup := (Certificate.supplied_families_checked i).2.1
  have hQnonempty : (decodeWord (Certificate.seed (i.val + 1))).Nonempty := by
    apply Finset.card_pos.mp
    rw [decodeWord_card _ hnodup]
    exact (Certificate.supplied_families_checked i).1
  apply onepoint_completion _ P (Certificate.seed_support_properties i).2.2.1 hQnonempty hPnonempty
  simpa only [decodeWord_card _ hnodup] using hsize

private theorem family35_completion (i : Fin 348) (hi : i.val + 1 = 35) :
    SupportCompletion (decodeWord (Certificate.seed (i.val + 1))) := by
  intro P hAI hcard
  simpa only [hi, HeavyFamilies.decoded_seed35_eq_support35, Family35.seed] using
    Family35.completion P hAI hcard

private theorem family53_completion (i : Fin 348) (hi : i.val + 1 = 53) :
    SupportCompletion (decodeWord (Certificate.seed (i.val + 1))) := by
  intro P hAI hcard
  simpa only [hi, HeavyFamilies.decoded_seed53_eq_support53, Family53Five.seed] using
    Family53Selection.completion P hAI hcard

theorem all_representatives_complete
    (hchunks : ∀ chunk : Fin 4, SimplexSearchChecks.chunkCheck chunk.val = true) :
    ∀ i : Fin 348, SupportCompletion (decodeWord (Certificate.seed (i.val + 1))) := by
  intro i P hAI hcard
  have hcards : P.card = 1 ∨ P.card = 3 ∨ P.card = 5 ∨ P.card = 7 ∨ P.card = 9 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hcard
  by_cases hsmall : (Certificate.seed (i.val + 1)).length + P.card ≤ 33
  · exact seed_onepoint_completion i P (Finset.card_pos.mp (by omega)) hsmall
  · have hbound := (Certificate.supplied_families_checked i).2.2.1
    have heven := (Certificate.supplied_families_checked i).2.2.2.1
    have hweights : (Certificate.seed (i.val + 1)).length = 26 ∨
        (Certificate.seed (i.val + 1)).length = 28 ∨
        (Certificate.seed (i.val + 1)).length = 30 ∨
        (Certificate.seed (i.val + 1)).length = 32 := by omega
    rcases hweights with h26 | h28 | h30 | h32
    · exact SimplexSearchChecks.weight26_completion hchunks i h26 P hAI (by omega)
    · have hlarge : P.card = 7 ∨ P.card = 9 := by omega
      rcases hlarge with h7 | h9
      · exact SimplexSearchChecks.weight28_seven_completion hchunks i h28 P hAI h7
      · exact SimplexSearchChecks.weight28_nine_completion hchunks i h28 P hAI h9
    · rcases HeavyFamilies.weight30_family i h30 with h35 | h49
      · exact family35_completion i h35 P hAI hcard
      · have hseed : decodeWord (Certificate.seed (i.val + 1)) = FlagActions.seed := by
          rw [h49]
          rfl
        simpa only [hseed] using Family49.completion P hAI hcard
    · exact family53_completion i (HeavyFamilies.weight32_family i h32) P hAI hcard

theorem geometric_completion
    (hchunks : ∀ chunk : Fin 4, SimplexSearchChecks.chunkCheck chunk.val = true) :
    GeometricCompletion :=
  CatalogCompletion.geometricCompletion_of_catalog CatalogUniform.catalog_cover
    (all_representatives_complete hchunks)

theorem covering_radius_upper_bound
    (hchunks : ∀ chunk : Fin 4, SimplexSearchChecks.chunkCheck chunk.val = true) : FullBound 32 :=
  fullBound_of_geometricCompletion (geometric_completion hchunks)

end Lemmata.RM59.SimplexRepresentativeCompletion
