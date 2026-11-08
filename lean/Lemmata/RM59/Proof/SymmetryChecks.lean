module

public import Lemmata.RM59.Proof.PackedLinear
public import Lemmata.RM59.Proof.SupportChecks
public meta import Lemmata.RM59.Proof.PackedLinear
public meta import Lemmata.RM59.Proof.SupportChecks

@[expose] public section

namespace Lemmata.RM59.Certificate

open Lemmata.RM59.Packed

def symmetryColumns (row : List PackedPoint) : Columns :=
  fun i => row[i.val]?.getD 0

def symmetryWord (family : Nat) (row : List PackedPoint) : List PackedPoint :=
  (seed family).map (evalColumns (symmetryColumns row))

def SymmetryCertificate (family : Nat) (row : List PackedPoint) : Prop :=
  row.length = 9 ∧ KernelZero (symmetryColumns row) ∧
  (symmetryWord family row).Nodup ∧
  ∀ mask : PackedPoint, bitCount mask.val ≤ 3 →
    packedMoment (symmetryWord family row) mask.val = packedMoment (seed family) mask.val

instance (family : Nat) (row : List PackedPoint) :
    Decidable (SymmetryCertificate family row) := by
  unfold SymmetryCertificate KernelZero
  infer_instance

theorem supplied_symmetries_checked : ∀ entry ∈ symmetries.toList,
    1 ≤ entry.1 ∧ entry.1 ≤ 348 ∧ SymmetryCertificate entry.1 entry.2 := by
  native_decide

theorem decodeWord_map_columns (word : List PackedPoint) (columns : Columns) :
    decodeWord (word.map (evalColumns columns)) =
      (decodeWord word).image (columnMap columns) := by
  classical
  ext y
  simp only [decodeWord, List.mem_toFinset, List.mem_map, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨decodePoint x, ⟨x, hx, rfl⟩, (decodePoint_evalColumns columns x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨evalColumns columns x, ⟨x, hx, rfl⟩, decodePoint_evalColumns columns x⟩

theorem supplied_symmetry_sound (entry : Nat × List PackedPoint)
    (hentry : entry ∈ symmetries.toList) :
    Function.Injective (columnMap (symmetryColumns entry.2)) ∧
    MatchSupportMoments 3
      ((decodeWord (seed entry.1)).image (columnMap (symmetryColumns entry.2)))
      (decodeWord (seed entry.1)) := by
  obtain ⟨hlo, hhi, _, hkernel, hnodup, hsame⟩ := supplied_symmetries_checked entry hentry
  let i : Fin 348 := ⟨entry.1 - 1, by omega⟩
  have hi : i.val + 1 = entry.1 := by dsimp [i]; omega
  have hseed := (supplied_families_checked i).2.1
  rw [hi] at hseed
  refine ⟨columnMap_injective_of_kernelZero _ hkernel, ?_⟩
  rw [← decodeWord_map_columns]
  exact matchSupportMoments_of_packedMoments _ _ hnodup hseed hsame

end Lemmata.RM59.Certificate
