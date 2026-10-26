module

public import Lemmata.CocubicCovering.Proof.Symmetry
public meta import Lemmata.CocubicCovering.Proof.Symmetry
public import Lemmata.CocubicCovering.Proof.PackedAction
public meta import Lemmata.CocubicCovering.Proof.PackedAction

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringWord

open CoveringSymmetry CoveringLocal CoveringAffine CoveringBits CoveringPackedAction
open CoveringWitness

def move : List (Fin 8) → Vector 127 → Vector 127
  | [] => id
  | step :: rest => fun v => move rest (unitMove step v)

def action : List (Fin 8) → Vector 12 →ₗ[Field] Vector 12
  | [] => LinearMap.id
  | step :: rest => (action rest).comp (unitAction step)

def applyMask (steps : List (Fin 8)) (mask : ℕ) : ℕ :=
  steps.foldl (fun value step => composeRow value (unitCoreColumns step)) mask

theorem action_decodeMask (steps : List (Fin 8)) (mask : ℕ) :
    action steps (decodeMask mask) = (decodeMask (applyMask steps mask) : Vector 12) := by
  induction steps generalizing mask with
  | nil => rfl
  | cons step rest ih =>
      change action rest (unitAction step (decodeMask mask)) = _
      rw [unitAction_decodeMask, ih]
      rfl

theorem action_columns (steps : List (Fin 8)) (columns : Fin 12 → ℕ)
    (hcolumns : ∀ i, columns i = applyMask steps (2 ^ i.val)) (mask : ℕ) :
    action steps (decodeMask mask) = (decodeMask (composeRow mask columns) : Vector 12) := by
  have hlinear : action steps = familyLinear (fun i => (decodeMask (columns i) : Vector 12)) := by
    apply (Pi.basisFun Field (Fin 12)).ext
    intro i
    have hsingle : (decodeMask (2 ^ i.val) : Vector 12) = Pi.single i 1 := by
      funext j
      by_cases hij : i = j
      · subst j
        simp [decodeMask, Nat.testBit_two_pow, Pi.single_apply]
      · have hval : i.val ≠ j.val := fun he => hij (Fin.ext he)
        simp [decodeMask, Nat.testBit_two_pow, Pi.single_apply,
          hij, Ne.symm hij, hval, Ne.symm hval]
    simp only [Pi.basisFun_apply, familyLinear,
      Fintype.linearCombination_apply_single, one_smul]
    rw [← hsingle, action_decodeMask, ← hcolumns i]
  rw [hlinear, ← decodeMask_composeRow_familyLinear]

theorem move_last (steps : List (Fin 8)) (v : Vector 127) :
    move steps v (Fin.last 126) = v (Fin.last 126) := by
  induction steps generalizing v with
  | nil => rfl
  | cons step rest ih => exact (ih _).trans (unitMove_last step v)

theorem move_rank (steps : List (Fin 8)) (v : Vector 127) :
    Module.finrank Field (LinearMap.range (fullForm (move steps v))) =
      Module.finrank Field (LinearMap.range (fullForm v)) := by
  induction steps generalizing v with
  | nil => rfl
  | cons step rest ih => exact (ih _).trans (fullRank_unitMove step v)

theorem move_zero_projection (steps : List (Fin 8)) (v : Vector 127)
    (hv : localParameterProjection v = 0) : localParameterProjection (move steps v) = 0 := by
  induction steps generalizing v with
  | nil => exact hv
  | cons step rest ih => exact ih _ (unitMove_preserves_zero_projection step v hv)

theorem kernel_transport (steps : List (Fin 8)) (p : Vector 127) :
    (fullKernel (fullForm p)).map (action steps) ≤ fullKernel (fullForm (move steps p)) := by
  induction steps generalizing p with
  | nil => simpa [move, action]
  | cons step rest ih =>
      rintro _ ⟨v, hv, rfl⟩
      apply ih (unitMove step p)
      refine ⟨unitAction step v, ?_, rfl⟩
      exact fullKernel_unitMove step p ⟨v, hv, rfl⟩

def allowed (root : ℕ) (v : Vector 127) : Prop :=
  v (Fin.last 126) = 1 ∧ localParameterProjection v = decodeMask root ∧
    Module.finrank Field (LinearMap.range (fullForm v)) ≤ 9

theorem allowed_move (steps : List (Fin 8)) (root : ℕ)
    (guard : root = 0 ∨ steps = []) (v : Vector 127) :
    allowed root v → allowed root (move steps v) := by
  rintro ⟨hpoint, hroot, hrank⟩
  refine ⟨(move_last steps v).trans hpoint, ?_, ?_⟩
  · rcases guard with rfl | rfl
    · rw [decodeMask_zero] at hroot ⊢
      exact move_zero_projection steps v hroot
    · exact hroot
  · rw [move_rank]
    exact hrank

end Lemmata.CocubicCovering.CoveringWord
