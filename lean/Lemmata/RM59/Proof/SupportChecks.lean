module

public import Lemmata.RM59.Proof.Packed
public meta import Lemmata.RM59.Proof.Packed
public import Lemmata.RM59.Proof.CertificateData
public meta import Lemmata.RM59.Proof.CertificateData

@[expose] public section

namespace Lemmata.RM59.Certificate

open Lemmata.RM59.Packed

def familyWords (family : Nat) : List (List PackedPoint) :=
  (supports.toList.filter fun row => row.1 == family).map Prod.snd

def seed (family : Nat) : List PackedPoint :=
  (familyWords family).headD []

def FamilyCertificate (family : Nat) : Prop :=
  0 < (seed family).length ∧
  (seed family).Nodup ∧
  (seed family).length ≤ 32 ∧
  (seed family).length % 2 = 0 ∧
  (∀ mask : PackedPoint, bitCount mask.val ≤ 2 →
    packedMoment (seed family) mask.val = false) ∧
  (∃ mask : PackedPoint, bitCount mask.val = 3 ∧
    packedMoment (seed family) mask.val = true) ∧
  (∀ word ∈ familyWords family, word.Nodup ∧
    word.length = (seed family).length ∧
    ∀ mask : PackedPoint, bitCount mask.val ≤ 3 →
      packedMoment word mask.val = packedMoment (seed family) mask.val)

instance (family : Nat) : Decidable (FamilyCertificate family) := by
  unfold FamilyCertificate
  infer_instance

theorem supplied_families_checked : ∀ i : Fin 348, FamilyCertificate (i.val + 1) := by
  native_decide

theorem seed_support_properties (i : Fin 348) :
    (decodeWord (seed (i.val + 1))).card ≤ 32 ∧
    (decodeWord (seed (i.val + 1))).card % 2 = 0 ∧
    (∀ s, s.card ≤ 2 → supportMoment (decodeWord (seed (i.val + 1))) s = 0) ∧
    (∃ s, s.card = 3 ∧
      supportMoment (decodeWord (seed (i.val + 1))) s = 1) := by
  obtain ⟨_, hnodup, hbound, heven, hzero, ⟨mask, hdegree, hnonzero⟩, _⟩ :=
    supplied_families_checked i
  refine ⟨?_, ?_, zero_supportMoments_of_packedMoments _ hnodup hzero, ?_⟩
  · exact (decodeWord_card _ hnodup).le.trans hbound
  · exact (congrArg (fun n : Nat => n % 2) (decodeWord_card _ hnodup)).trans heven
  · refine ⟨decodeMask mask, ?_, ?_⟩
    · exact (decodeMask_card mask).trans hdegree
    · rw [← packedMoment_decodeWord _ hnodup, hnonzero, bitField_true]

theorem family_word_same_moments (i : Fin 348) (word : List PackedPoint)
    (hword : word ∈ familyWords (i.val + 1)) :
    MatchSupportMoments 3 (decodeWord word) (decodeWord (seed (i.val + 1))) := by
  obtain ⟨_, hseed, _, _, _, _, hwords⟩ := supplied_families_checked i
  obtain ⟨hnodup, _, hsame⟩ := hwords word hword
  exact matchSupportMoments_of_packedMoments _ _ hnodup hseed hsame

end Lemmata.RM59.Certificate
