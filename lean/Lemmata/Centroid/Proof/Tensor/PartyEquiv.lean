module

public import Lemmata.Centroid.Proof.Tensor.Support

@[expose] public section

open Classical

noncomputable section

namespace Lemmata.Centroid.Tensor

variable {F ι κ : Type*} [Field F] {V : ι → Type*}

local instance sourcePartyDecidableEq : DecidableEq ι := Classical.decEq _
local instance targetPartyDecidableEq : DecidableEq κ := Classical.decEq _

def reorder (e : ι ≃ κ) : Tensor F ι V ≃ₗ[F] Tensor F κ (fun j => V (e.symm j)) :=
  LinearEquiv.funCongrLeft F F (Equiv.piCongrLeft' V e).symm

@[simp] theorem reorder_apply (e : ι ≃ κ) (T : Tensor F ι V) (x : ∀ j, V (e.symm j)) :
    reorder e T x = T ((Equiv.piCongrLeft' V e).symm x) := rfl

theorem oneSlice_reorder (e : ι ≃ κ) (j : κ) (x : ∀ j, V (e.symm j)) :
    (oneSlice (F := F) j x).comp (reorder e).toLinearMap =
      oneSlice (e.symm j) ((Equiv.piCongrLeft' V e).symm x) := by
  apply LinearMap.ext
  intro T
  funext a
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, oneSlice_apply, reorder_apply,
    Function.piCongrLeft'_symm_update]

theorem oppositeSlice_reorder (e : ι ≃ κ) (j : κ) (a : V (e.symm j)) :
    (oppositeSlice (F := F) j a).comp (reorder e).toLinearMap =
      (reorder e).toLinearMap.comp (oppositeSlice (e.symm j) a) := by
  apply LinearMap.ext
  intro T
  funext x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, oppositeSlice_apply, reorder_apply,
    Function.piCongrLeft'_symm_update]

theorem oneSupportAt_reorder (e : ι ≃ κ) (S : Submodule F (Tensor F ι V)) (j : κ) :
    oneSupportAt (S.map (reorder e).toLinearMap) j = oneSupportAt S (e.symm j) := by
  simp only [oneSupportAt, ← Submodule.map_comp, oneSlice_reorder]
  apply le_antisymm
  · apply iSup_le
    intro x
    exact le_iSup_of_le ((Equiv.piCongrLeft' V e).symm x) le_rfl
  · apply iSup_le
    intro x
    apply le_iSup_of_le (Equiv.piCongrLeft' V e x)
    simp only [Equiv.symm_apply_apply]
    exact le_rfl

theorem oppositeSupportAt_reorder (e : ι ≃ κ) (S : Submodule F (Tensor F ι V)) (j : κ) :
    oppositeSupportAt (S.map (reorder e).toLinearMap) j =
      (oppositeSupportAt S (e.symm j)).map (reorder e).toLinearMap := by
  simp only [oppositeSupportAt, Submodule.map_iSup, ← Submodule.map_comp, oppositeSlice_reorder]

theorem finrank_oppositeSupportAt_reorder (e : ι ≃ κ) (S : Submodule F (Tensor F ι V)) (j : κ) :
    Module.finrank F (oppositeSupportAt (S.map (reorder e).toLinearMap) j) =
      Module.finrank F (oppositeSupportAt S (e.symm j)) := by
  rw [oppositeSupportAt_reorder, (reorder e).finrank_map_eq]

end Lemmata.Centroid.Tensor
