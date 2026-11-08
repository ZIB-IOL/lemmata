module

public import Lemmata.RM59.Proof.SymmetryChecks
public import Lemmata.RM59.Proof.PullbackEquiv
public meta import Lemmata.RM59.Proof.SymmetryChecks
public meta import Lemmata.RM59.Proof.PackedLinear

@[expose] public section

namespace Lemmata.RM59.FlagActions

open Lemmata.RM59.Packed Lemmata.RM59.SupportForms

def baseRows : List (List PackedPoint) :=
  ((Certificate.symmetries.toList.filter fun entry => entry.1 == 49).map Prod.snd) ++
    (Certificate.flagMaps.toList.map Prod.snd)

def inverseRow (row : List PackedPoint) : List PackedPoint :=
  (List.finRange 9).map fun i =>
    ((List.finRange 512).find? fun x =>
      evalColumns (Certificate.symmetryColumns row) x == encodePoint (Pi.single i 1)).getD 0

def rows : List (List PackedPoint) := baseRows ++ baseRows.map inverseRow

def row (i : Fin 12) : List PackedPoint := rows[i.val]?.getD []

def columns (i : Fin 12) : Columns := Certificate.symmetryColumns (row i)

def linear (i : Fin 12) : Point 9 →ₗ[Field] Point 9 := columnMap (columns i)

def packedTable : Vector (Vector PackedPoint 512) 12 :=
  Vector.ofFn fun i => Vector.ofFn (evalColumns (columns i))

def packed (i : Fin 12) (x : PackedPoint) : PackedPoint := (packedTable.get i).get x

def seed : Finset (Point 9) := decodeWord (Certificate.seed 49)

theorem baseRows_length : baseRows.length = 6 := by native_decide

theorem alphabet_checked : ∀ i : Fin 12, Certificate.SymmetryCertificate 49 (row i) := by
  native_decide

theorem packed_eq_evalColumns : ∀ (i : Fin 12) (x : PackedPoint),
    packed i x = evalColumns (columns i) x := by native_decide

theorem seed_card : seed.card = 30 := by native_decide

theorem seed_lowerZero : LowerZero seed :=
  (Certificate.seed_support_properties ⟨48, by decide⟩).2.2.1

theorem generator_sound (i : Fin 12) : Function.Injective (linear i) ∧
    MatchSupportMoments 3 (seed.image (linear i)) seed := by
  obtain ⟨_, hkernel, hnodup, hsame⟩ := alphabet_checked i
  have hseed := (Certificate.supplied_families_checked ⟨48, by decide⟩).2.1
  refine ⟨columnMap_injective_of_kernelZero _ hkernel, ?_⟩
  change MatchSupportMoments 3
    ((decodeWord (Certificate.seed 49)).image (columnMap (Certificate.symmetryColumns (row i))))
    (decodeWord (Certificate.seed 49))
  rw [← Certificate.decodeWord_map_columns]
  exact matchSupportMoments_of_packedMoments _ _ hnodup hseed hsame

abbrev Word := List (Fin 12)

def wordPacked : Word → PackedPoint → PackedPoint
  | [], x => x
  | i :: word, x => packed i (wordPacked word x)

def wordLinear : Word → Point 9 →ₗ[Field] Point 9
  | [] => LinearMap.id
  | i :: word => (linear i).comp (wordLinear word)

theorem decode_wordPacked (word : Word) (x : PackedPoint) :
    decodePoint (wordPacked word x) = wordLinear word (decodePoint x) := by
  induction word with
  | nil => rfl
  | cons i word ih =>
    change decodePoint (packed i (wordPacked word x)) = _
    rw [packed_eq_evalColumns, decodePoint_evalColumns, ih]
    rfl

theorem wordLinear_injective (word : Word) : Function.Injective (wordLinear word) := by
  induction word with
  | nil => exact Function.injective_id
  | cons i word ih => exact (generator_sound i).1.comp ih

theorem wordLinear_moments (word : Word) :
    MatchSupportMoments 3 (seed.image (wordLinear word)) seed := by
  induction word with
  | nil =>
    change MatchSupportMoments 3 (seed.image id) seed
    rw [Finset.image_id]
    exact MatchSupportMoments.refl _ _
  | cons i word ih =>
    have hm := (matchSupportMoments_image ih (linear i) (generator_sound i).1).trans
      (generator_sound i).2
    simpa only [wordLinear, Finset.image_image, Function.comp_def, LinearMap.coe_comp] using hm

noncomputable def wordEquiv (word : Word) : Point 9 ≃ₗ[Field] Point 9 :=
  LinearEquiv.ofBijective (wordLinear word)
    ⟨wordLinear_injective word, Finite.surjective_of_injective (wordLinear_injective word)⟩

theorem inverse_moments (word : Word) :
    MatchSupportMoments 3 (seed.image (wordEquiv word).symm) seed := by
  let e := wordEquiv word
  have hm := matchSupportMoments_image (wordLinear_moments word)
    e.symm.toLinearMap e.symm.injective
  change MatchSupportMoments 3 ((seed.image e).image e.symm) (seed.image e.symm) at hm
  have he : (seed.image e).image e.symm = seed := by
    rw [Finset.image_image]
    change seed.image (fun x => e.symm (e x)) = seed
    have hh : (fun x : Point 9 => e.symm (e x)) = id := by
      funext x
      exact e.symm_apply_apply x
    rw [hh, Finset.image_id]
  rw [he] at hm
  exact hm.symm

end Lemmata.RM59.FlagActions
