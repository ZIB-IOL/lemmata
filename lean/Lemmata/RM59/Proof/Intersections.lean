module

public import Lemmata.RM59.Proof.SupportForms

@[expose] public section

namespace Lemmata.RM59

open scoped symmDiff
open SupportForms

theorem translateSupport_sameMoments (Q : Finset (Point 9)) (hQ : LowerZero Q)
    (t : Point 9) : MatchSupportMoments 3 (translateSupport Q t) Q := by
  classical
  apply matchSupportMoments_of_supportForm_eq (supportForm_translate Q hQ t)
  rw [supportMoment_empty_index, supportMoment_empty_index]
  congr 1
  exact Finset.card_image_of_injective Q (fun _ _ h => add_right_cancel h)

theorem symmDiff_card_le_of_intersection {α : Type*} [DecidableEq α]
    (Q P : Finset α) (B : Nat)
    (h : Q.card + P.card ≤ B + 2 * (Q ∩ P).card) : (Q ∆ P).card ≤ B := by
  have hd : Disjoint (Q \ P) (P \ Q) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hd]
  have hQ := Finset.card_sdiff_add_card_inter Q P
  have hP := Finset.card_sdiff_add_card_inter P Q
  rw [Finset.inter_comm P Q] at hP
  omega

theorem small_support_completion (Q P : Finset (Point 9)) (hQ : LowerZero Q)
    (hQnonempty : Q.Nonempty) (hPnonempty : P.Nonempty)
    (hQcard : Q.card ≤ 24) (hPcard : P.card ≤ 9) :
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

end Lemmata.RM59
