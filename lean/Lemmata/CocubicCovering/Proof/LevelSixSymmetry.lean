module

public import Lemmata.CocubicCovering.Proof.LevelSixCovariance
public meta import Lemmata.CocubicCovering.Proof.LevelSixCovariance
public import Lemmata.CocubicCovering.Proof.LevelSixReduction
public meta import Lemmata.CocubicCovering.Proof.LevelSixReduction

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringLevelSixSymmetry

open CoveringAffine CoveringBits CoveringCongruence CoveringEncoding CoveringPackedAction
open CoveringSymmetry CoveringLevelSixReduction

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def unitMove (step : Fin 8) : Vector 127 →ₗ[Field] Vector 127 :=
  rowMap (CoveringLevelSixCovariance.parameterRows (unitDirection step) (unitGenerator step))

theorem unitMove_last (step : Fin 8) (v : Vector 127) :
    unitMove step v (Fin.last 126) = v (Fin.last 126) := by
  change evalRow (CoveringLevelSixCovariance.parameterRows
    (unitDirection step) (unitGenerator step) (Fin.last 126)) v = _
  rw [CoveringLevelSixCovariance.parameter_last]
  exact evalRow_two_pow (Fin.last 126) v

def projection_rows_decision (step : Fin 8) : Decidable (∀ i : Fin 15, composeRow (projectionRows i)
      (CoveringLevelSixCovariance.parameterRows (unitDirection step) (unitGenerator step)) =
        composeRow (unitLocalRows step i) projectionRows) :=
  inferInstance

@[noinline, never_extract]
def projection_rows_check (step : Fin 8) : Bool :=
  @decide (∀ i : Fin 15, composeRow (projectionRows i)
      (CoveringLevelSixCovariance.parameterRows (unitDirection step) (unitGenerator step)) =
        composeRow (unitLocalRows step i) projectionRows) (projection_rows_decision step)

theorem projection_rows_check_sound (step : Fin 8) (computed : projection_rows_check step = true) :
    ∀ i : Fin 15, composeRow (projectionRows i)
      (CoveringLevelSixCovariance.parameterRows (unitDirection step) (unitGenerator step)) =
        composeRow (unitLocalRows step i) projectionRows := by
  unfold projection_rows_check at computed
  exact @of_decide_eq_true (∀ i : Fin 15, composeRow (projectionRows i)
      (CoveringLevelSixCovariance.parameterRows (unitDirection step) (unitGenerator step)) =
        composeRow (unitLocalRows step i) projectionRows) (projection_rows_decision step) computed

theorem projection_rows (step : Fin 8) :
    ∀ i : Fin 15, composeRow (projectionRows i)
      (CoveringLevelSixCovariance.parameterRows (unitDirection step) (unitGenerator step)) =
        composeRow (unitLocalRows step i) projectionRows := by
  have computed : ∀ (step : Fin 8), projection_rows_check step = true := by native_decide
  exact projection_rows_check_sound step (computed step)

theorem localParameterProjection_unitMove (step : Fin 8) (v : Vector 127) :
    localParameterProjection (unitMove step v) =
      rowMap (unitLocalRows step) (localParameterProjection v) := by
  funext i
  change evalRow (projectionRows i)
      (rowMap (CoveringLevelSixCovariance.parameterRows (unitDirection step) (unitGenerator step)) v) =
    evalRow (unitLocalRows step i) (rowMap projectionRows v)
  rw [← evalRow_composeRow, ← evalRow_composeRow, projection_rows]

def unit_intertwines_basis_decision (step : Fin 8) : Decidable (∀ i : Fin 12,
      CoveringLevelSixReduction.localEmbedding (unitAction step (Pi.single i 1)) =
        rowMap (CoveringLevelSixCovariance.inverseCoordinateRows
          (unitDirection step) (unitGenerator step))
            (CoveringLevelSixReduction.localEmbedding (Pi.single i 1))) :=
  inferInstance

@[noinline, never_extract]
def unit_intertwines_basis_check (step : Fin 8) : Bool :=
  @decide (∀ i : Fin 12,
      CoveringLevelSixReduction.localEmbedding (unitAction step (Pi.single i 1)) =
        rowMap (CoveringLevelSixCovariance.inverseCoordinateRows
          (unitDirection step) (unitGenerator step))
            (CoveringLevelSixReduction.localEmbedding (Pi.single i 1))) (unit_intertwines_basis_decision step)

theorem unit_intertwines_basis_check_sound (step : Fin 8) (computed : unit_intertwines_basis_check step = true) :
    ∀ i : Fin 12,
      CoveringLevelSixReduction.localEmbedding (unitAction step (Pi.single i 1)) =
        rowMap (CoveringLevelSixCovariance.inverseCoordinateRows
          (unitDirection step) (unitGenerator step))
            (CoveringLevelSixReduction.localEmbedding (Pi.single i 1)) := by
  unfold unit_intertwines_basis_check at computed
  exact @of_decide_eq_true (∀ i : Fin 12,
      CoveringLevelSixReduction.localEmbedding (unitAction step (Pi.single i 1)) =
        rowMap (CoveringLevelSixCovariance.inverseCoordinateRows
          (unitDirection step) (unitGenerator step))
            (CoveringLevelSixReduction.localEmbedding (Pi.single i 1))) (unit_intertwines_basis_decision step) computed

theorem unit_intertwines_basis (step : Fin 8) :
    ∀ i : Fin 12,
      CoveringLevelSixReduction.localEmbedding (unitAction step (Pi.single i 1)) =
        rowMap (CoveringLevelSixCovariance.inverseCoordinateRows
          (unitDirection step) (unitGenerator step))
            (CoveringLevelSixReduction.localEmbedding (Pi.single i 1)) := by
  have computed : ∀ (step : Fin 8), unit_intertwines_basis_check step = true := by native_decide
  exact unit_intertwines_basis_check_sound step (computed step)

theorem coordinateEquiv_symm_toLinearMap (direction : Fin 2) (g : Fin 4) :
    (CoveringLevelSixCovariance.coordinateEquiv direction g).symm.toLinearMap =
      rowMap (CoveringLevelSixCovariance.inverseCoordinateRows direction g) := rfl

theorem unit_intertwines (step : Fin 8) :
    CoveringLevelSixReduction.localEmbedding.comp (unitAction step) =
      (CoveringLevelSixCovariance.coordinateEquiv
        (unitDirection step) (unitGenerator step)).symm.toLinearMap.comp
          CoveringLevelSixReduction.localEmbedding := by
  rw [coordinateEquiv_symm_toLinearMap]
  apply (Pi.basisFun Field (Fin 12)).ext
  intro i
  simpa only [Pi.basisFun_apply, LinearMap.comp_apply] using unit_intertwines_basis step i

theorem fullForm_unitMove (step : Fin 8) (v : Vector 127) :
    CoveringLevelSixReduction.fullForm (unitMove step v) =
      Covering.gram (CoveringLevelSixReduction.fullForm v)
        (CoveringLevelSixCovariance.coordinateEquiv
          (unitDirection step) (unitGenerator step)).toLinearMap := by
  unfold CoveringLevelSixReduction.fullForm unitMove
  rw [bilinear_covariance_of_rows _ _ _
    (CoveringLevelSixCovariance.coefficientIdentities (unitDirection step) (unitGenerator step)),
    ← CoveringLevelSixCovariance.coordinateEquiv_toLinearMap]

theorem kernel_transport (step : Fin 8) (v : Vector 127) :
    (CoveringLevelSixReduction.fullKernel v).map (unitAction step) ≤
      CoveringLevelSixReduction.fullKernel (unitMove step v) := by
  rintro _ ⟨w, hw, rfl⟩
  change CoveringLevelSixReduction.fullForm v
    (CoveringLevelSixReduction.localEmbedding w) = 0 at hw
  change CoveringLevelSixReduction.fullForm (unitMove step v)
    (CoveringLevelSixReduction.localEmbedding (unitAction step w)) = 0
  rw [fullForm_unitMove]
  apply LinearMap.ext
  intro z
  have he := LinearMap.congr_fun (unit_intertwines step) w
  change CoveringLevelSixReduction.localEmbedding (unitAction step w) =
    (CoveringLevelSixCovariance.coordinateEquiv
      (unitDirection step) (unitGenerator step)).symm
        (CoveringLevelSixReduction.localEmbedding w) at he
  change CoveringLevelSixReduction.fullForm v
    ((CoveringLevelSixCovariance.coordinateEquiv (unitDirection step) (unitGenerator step))
      (CoveringLevelSixReduction.localEmbedding (unitAction step w)))
    ((CoveringLevelSixCovariance.coordinateEquiv (unitDirection step) (unitGenerator step)) z) = 0
  rw [he, LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun hw _

theorem kernel_map (step : Fin 8) (v : Vector 127) :
    (CoveringLevelSixReduction.fullKernel v).map (unitAction step) =
      CoveringLevelSixReduction.fullKernel (unitMove step v) := by
  apply le_antisymm (kernel_transport step v)
  intro w hw
  obtain ⟨u, rfl⟩ := LinearMap.surjective_of_injective (unitAction_injective step) w
  refine ⟨u, ?_, rfl⟩
  change CoveringLevelSixReduction.fullForm v
    (CoveringLevelSixReduction.localEmbedding u) = 0
  apply LinearMap.ext
  intro z
  let e := CoveringLevelSixCovariance.coordinateEquiv (unitDirection step) (unitGenerator step)
  obtain ⟨z, rfl⟩ := e.surjective z
  change CoveringLevelSixReduction.fullForm (unitMove step v)
    (CoveringLevelSixReduction.localEmbedding (unitAction step u)) = 0 at hw
  have hzero := LinearMap.congr_fun hw z
  change CoveringLevelSixReduction.fullForm (unitMove step v)
    (CoveringLevelSixReduction.localEmbedding (unitAction step u)) z = 0 at hzero
  rw [fullForm_unitMove] at hzero
  change CoveringLevelSixReduction.fullForm v
    (e (CoveringLevelSixReduction.localEmbedding (unitAction step u))) (e z) = 0 at hzero
  have he := LinearMap.congr_fun (unit_intertwines step) u
  change CoveringLevelSixReduction.localEmbedding (unitAction step u) =
    e.symm (CoveringLevelSixReduction.localEmbedding u) at he
  rw [he, LinearEquiv.apply_symm_apply] at hzero
  exact hzero

theorem kernel_finrank_unitMove (step : Fin 8) (v : Vector 127) :
    Module.finrank Field (CoveringLevelSixReduction.fullKernel (unitMove step v)) =
      Module.finrank Field (CoveringLevelSixReduction.fullKernel v) := by
  rw [← kernel_map]
  exact (Submodule.equivMapOfInjective (unitAction step) (unitAction_injective step)
    (CoveringLevelSixReduction.fullKernel v)).finrank_eq.symm

theorem rank_unitMove (step : Fin 8) (v : Vector 127) :
    Module.finrank Field (LinearMap.range (CoveringLevelSixReduction.fullForm (unitMove step v))) =
      Module.finrank Field (LinearMap.range (CoveringLevelSixReduction.fullForm v)) :=
  CoveringLevelSixCovariance.rank_covariance (unitDirection step) (unitGenerator step) v

def move : List (Fin 8) → Vector 127 → Vector 127
  | [] => id
  | step :: rest => fun v => move rest (unitMove step v)

theorem move_last (steps : List (Fin 8)) (v : Vector 127) :
    move steps v (Fin.last 126) = v (Fin.last 126) := by
  induction steps generalizing v with
  | nil => rfl
  | cons step rest ih => exact (ih _).trans (unitMove_last step v)

theorem move_rank (steps : List (Fin 8)) (v : Vector 127) :
    Module.finrank Field (LinearMap.range (CoveringLevelSixReduction.fullForm (move steps v))) =
      Module.finrank Field (LinearMap.range (CoveringLevelSixReduction.fullForm v)) := by
  induction steps generalizing v with
  | nil => rfl
  | cons step rest ih => exact (ih _).trans (rank_unitMove step v)

theorem move_kernel_finrank (steps : List (Fin 8)) (v : Vector 127) :
    Module.finrank Field (CoveringLevelSixReduction.fullKernel (move steps v)) =
      Module.finrank Field (CoveringLevelSixReduction.fullKernel v) := by
  induction steps generalizing v with
  | nil => rfl
  | cons step rest ih => exact (ih _).trans (kernel_finrank_unitMove step v)

theorem word_kernel_transport (steps : List (Fin 8)) (v : Vector 127) :
    (CoveringLevelSixReduction.fullKernel v).map (CoveringWord.action steps) ≤
      CoveringLevelSixReduction.fullKernel (move steps v) := by
  induction steps generalizing v with
  | nil => simpa [move, CoveringWord.action]
  | cons step rest ih =>
      rintro _ ⟨w, hw, rfl⟩
      apply ih (unitMove step v)
      refine ⟨unitAction step w, ?_, rfl⟩
      exact kernel_transport step v ⟨w, hw, rfl⟩

def forwardMove (g : Fin 4) : Vector 127 →ₗ[Field] Vector 127 :=
  unitMove ⟨g.val, by omega⟩

theorem forward_last (g : Fin 4) (v : Vector 127) :
    forwardMove g v (Fin.last 126) = v (Fin.last 126) :=
  unitMove_last _ v

theorem forward_rank (g : Fin 4) (v : Vector 127) :
    Module.finrank Field (LinearMap.range (CoveringLevelSixReduction.fullForm (forwardMove g v))) =
      Module.finrank Field (LinearMap.range (CoveringLevelSixReduction.fullForm v)) :=
  rank_unitMove _ v

def forward_localRows_decision (g : Fin 4) : Decidable (unitLocalRows ⟨g.val, by omega⟩ = localRows g) :=
  inferInstance

@[noinline, never_extract]
def forward_localRows_check (g : Fin 4) : Bool :=
  @decide (unitLocalRows ⟨g.val, by omega⟩ = localRows g) (forward_localRows_decision g)

theorem forward_localRows_check_sound (g : Fin 4) (computed : forward_localRows_check g = true) :
    unitLocalRows ⟨g.val, by omega⟩ = localRows g := by
  unfold forward_localRows_check at computed
  exact @of_decide_eq_true (unitLocalRows ⟨g.val, by omega⟩ = localRows g) (forward_localRows_decision g) computed

theorem forward_localRows (g : Fin 4) :
    unitLocalRows ⟨g.val, by omega⟩ = localRows g := by
  have computed : ∀ (g : Fin 4), forward_localRows_check g = true := by native_decide
  exact forward_localRows_check_sound g (computed g)

theorem localParameterProjection_forwardMove (g : Fin 4) (v : Vector 127) :
    localParameterProjection (forwardMove g v) =
      rowMap (localRows g) (localParameterProjection v) := by
  rw [forwardMove, localParameterProjection_unitMove, forward_localRows]

attribute [local irreducible] encodeVector decodeMask localParameterProjection

theorem projection_forwardMove (g : Fin 4) (v : Vector 127) :
    CoveringSymmetry.projection (forwardMove g v) =
      localStep g (CoveringSymmetry.projection v) := by
  have h := rowMap_decodeMask (localRows g) (localColumns g)
    (localRows_transpose g) (encodeVector (localParameterProjection v))
  rw [decodeMask_encodeVector] at h
  apply Fin.ext
  simp only [CoveringSymmetry.projection, localStep, Fin.val_ofNat]
  rw [localParameterProjection_forwardMove, h, CoveringBits.encodeVector_decodeMask_mod]
  norm_num

end Lemmata.CocubicCovering.CoveringLevelSixSymmetry
