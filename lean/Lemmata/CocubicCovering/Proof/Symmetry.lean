module

public import Lemmata.CocubicCovering.Proof.Local
public meta import Lemmata.CocubicCovering.Proof.Local
public import Lemmata.CocubicCovering.Proof.CovarianceData
public meta import Lemmata.CocubicCovering.Proof.CovarianceData
public import Lemmata.CocubicCovering.Proof.PackedAction
public meta import Lemmata.CocubicCovering.Proof.PackedAction

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringSymmetry

open CoveringAffine CoveringBits CoveringCongruence CoveringCovarianceData
open CoveringLocal CoveringPackedAction

def localRowData : List (List Nat) := [
  [0x3, 0x4, 0x1, 0x30, 0x8, 0x10, 0x180, 0x40, 0x80, 0x200, 0x1800, 0x400, 0x800, 0x2000, 0x4000],
  [0x200, 0x2000, 0x4000, 0x8, 0x40, 0x400, 0x10, 0x80, 0x800, 0x1, 0x20, 0x100, 0x1000, 0x2, 0x4],
  [0x251, 0x2422, 0x4904, 0x8, 0x210, 0x2020, 0x240, 0x80, 0x4100, 0x200, 0x2400, 0x4800, 0x1000, 0x2000, 0x4000],
  [0x6, 0x4, 0x3, 0x1000, 0x1c00, 0x1800, 0x1120, 0x1df8, 0x19b0, 0x6000, 0x1100, 0x1dc0, 0x1980, 0x4000, 0x2200]
]

def coreRowData : List (List Nat) := [
  [0x3, 0x4, 0x1, 0xb0, 0x108, 0x150, 0x8, 0x10, 0x20, 0x200, 0x400, 0x800],
  [0x200, 0x400, 0x800, 0x108, 0x10, 0x80, 0x150, 0x20, 0x100, 0x1, 0x2, 0x4],
  [0x301, 0x512, 0x8a4, 0x208, 0x10, 0x820, 0x440, 0x880, 0x100, 0x200, 0x400, 0x800],
  [0x6, 0x4, 0x3, 0x70, 0x110, 0x1e8, 0x120, 0x1f8, 0x1b0, 0xc00, 0x800, 0x600]
]

def localColumnData : List (List Nat) := [
  [0x5, 0x1, 0x2, 0x10, 0x28, 0x8, 0x80, 0x140, 0x40, 0x200, 0x800, 0x1400, 0x400, 0x2000, 0x4000],
  [0x200, 0x2000, 0x4000, 0x8, 0x40, 0x400, 0x10, 0x80, 0x800, 0x1, 0x20, 0x100, 0x1000, 0x2, 0x4],
  [0x1, 0x2, 0x4, 0x8, 0x11, 0x22, 0x41, 0x80, 0x104, 0x251, 0x402, 0x804, 0x1000, 0x2422, 0x4904],
  [0x4, 0x5, 0x3, 0x80, 0x180, 0x1c0, 0x880, 0x1980, 0x1dc0, 0x4000, 0x890, 0x19b0, 0x1df8, 0x4200, 0x2200]
]

def localColumns (g : Fin 4) (i : Fin 15) : Nat :=
  ((localColumnData[g.val]?.getD [])[i.val]?).getD 0

def localStep (g : Fin 4) (i : Fin 32768) : Fin 32768 :=
  Fin.ofNat 32768 (composeRow i.val (localColumns g))

def localRows (g : Fin 4) (i : Fin 15) : Nat :=
  ((localRowData[g.val]?.getD [])[i.val]?).getD 0

def coreRows (g : Fin 4) (i : Fin 12) : Nat :=
  ((coreRowData[g.val]?.getD [])[i.val]?).getD 0

def projectionRows (i : Fin 15) : Nat := 2 ^ (111 + i.val)

def localParameterProjection : Vector 127 →ₗ[Field] Vector 15 := rowMap projectionRows

def projection (v : Vector 127) : Fin 32768 :=
  ⟨encodeVector (localParameterProjection v), encodeVector_lt _⟩

def move (g : Fin 4) : Vector 127 →ₗ[Field] Vector 127 := rowMap (parameterRows 1 g)

def coreAction (g : Fin 4) : Vector 12 →ₗ[Field] Vector 12 := rowMap (coreRows g)

def fullForm (v : Vector 127) := Matrix.toBilin' (coefficientMatrix matrixRows v)

theorem projection_coefficient_identity (g : Fin 4) :
    ∀ i : Fin 15, composeRow (projectionRows i) (parameterRows 1 g) =
      composeRow (localRows g i) projectionRows := by
  fin_cases g <;> native_decide

theorem localRows_transpose (g : Fin 4) :
    ∀ i j : Fin 15, (localRows g i).testBit j.val =
      (localColumns g j).testBit i.val := by
  fin_cases g <;> native_decide

theorem move_last_coefficient (g : Fin 4) : parameterRows 1 g (Fin.last 126) = 2 ^ 126 := by
  fin_cases g <;> native_decide

theorem move_last (g : Fin 4) (v : Vector 127) : move g v (Fin.last 126) = v (Fin.last 126) := by
  change evalRow (parameterRows 1 g (Fin.last 126)) v = _
  rw [move_last_coefficient]
  exact CoveringEncoding.evalRow_two_pow (Fin.last 126) v

theorem localParameterProjection_move (g : Fin 4) (v : Vector 127) :
    localParameterProjection (move g v) = rowMap (localRows g) (localParameterProjection v) := by
  funext i
  change evalRow (projectionRows i) (rowMap (parameterRows 1 g) v) =
    evalRow (localRows g i) (rowMap projectionRows v)
  rw [← evalRow_composeRow, ← evalRow_composeRow, projection_coefficient_identity]

theorem decodeMask_mod (mask : Nat) (n : Nat) :
    (decodeMask (mask % 2 ^ n) : Vector n) = decodeMask mask := by
  funext i
  simp only [decodeMask, Nat.testBit_mod_two_pow]
  simp [i.isLt]

theorem encodeVector_decodeMask_mod (mask : Nat) (n : Nat) :
    encodeVector (decodeMask mask : Vector n) = mask % 2 ^ n := by
  rw [← decodeMask_mod mask n]
  exact encodeVector_decodeMask (Nat.mod_lt _ (by positivity))

set_option maxRecDepth 8192 in
theorem projection_move (g : Fin 4) (v : Vector 127) :
    projection (move g v) = localStep g (projection v) := by
  have h := rowMap_decodeMask (localRows g) (localColumns g)
    (localRows_transpose g) (encodeVector (localParameterProjection v))
  rw [decodeMask_encodeVector] at h
  apply Fin.ext
  simp only [projection, localStep, Fin.val_ofNat]
  rw [localParameterProjection_move, h, encodeVector_decodeMask_mod]
  norm_num

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem core_intertwines_basis (g : Fin 4) :
    ∀ i : Fin 12, localEmbedding (coreAction g (Pi.single i 1)) =
      rowMap (inverseCoordinateRows 1 g) (Pi.single (CoveringMatrix.localInclusion i) 1) := by
  fin_cases g <;> native_decide

theorem coordinateEquiv_symm_apply (direction : Fin 2) (g : Fin 4) (v : Vector 24) :
    (coordinateEquiv direction g).symm v = rowMap (inverseCoordinateRows direction g) v := rfl

theorem coordinateEquiv_symm_toLinearMap (direction : Fin 2) (g : Fin 4) :
    (coordinateEquiv direction g).symm.toLinearMap =
      rowMap (inverseCoordinateRows direction g) := rfl

theorem core_intertwines (g : Fin 4) :
    localEmbedding.comp (coreAction g) =
      (coordinateEquiv 1 g).symm.toLinearMap.comp localEmbedding := by
  rw [coordinateEquiv_symm_toLinearMap]
  apply (Pi.basisFun Field (Fin 12)).ext
  intro i
  simpa only [Pi.basisFun_apply, LinearMap.comp_apply, localEmbedding_basis] using
    core_intertwines_basis g i

theorem coreAction_injective (g : Fin 4) : Function.Injective (coreAction g) := by
  intro a b hab
  apply localEmbedding_injective
  apply (coordinateEquiv 1 g).symm.injective
  have h := congrArg localEmbedding hab
  have heq := core_intertwines g
  change (localEmbedding.comp (coreAction g)) a = (localEmbedding.comp (coreAction g)) b at h
  rw [heq] at h
  exact h

theorem fullForm_move (g : Fin 4) (v : Vector 127) :
    fullForm (move g v) = Covering.gram (fullForm v) (coordinateEquiv 1 g).toLinearMap := by
  unfold fullForm move
  rw [CoveringCongruence.bilinear_covariance_of_rows _ _ _ (coefficientIdentities 1 g),
    ← coordinateEquiv_toLinearMap]

theorem fullKernel_move (g : Fin 4) (v : Vector 127) :
    (fullKernel (fullForm v)).map (coreAction g) ≤ fullKernel (fullForm (move g v)) := by
  rw [fullForm_move]
  exact fullKernel_transport _ _ _ (core_intertwines g)

theorem fullRank_move (g : Fin 4) (v : Vector 127) :
    Module.finrank Field (LinearMap.range (fullForm (move g v))) =
      Module.finrank Field (LinearMap.range (fullForm v)) :=
  rank_covariance 1 g v

def inverseCoreRowData : List (List Nat) := [
  [0x4, 0x5, 0x2, 0x40, 0x80, 0x100, 0xf0, 0x188, 0x50, 0x200, 0x400, 0x800],
  [0x200, 0x400, 0x800, 0x108, 0x10, 0x80, 0x150, 0x20, 0x100, 0x1, 0x2, 0x4],
  [0x301, 0x512, 0x8a4, 0x208, 0x10, 0x820, 0x440, 0x880, 0x100, 0x200, 0x400, 0x800],
  [0x7, 0x3, 0x2, 0x1d8, 0xa0, 0xf0, 0x58, 0x1e0, 0xb0, 0xe00, 0x600, 0x400]
]

def unitDirection (step : Fin 8) : Fin 2 := if step.val < 4 then 1 else 0

def unitGenerator (step : Fin 8) : Fin 4 := Fin.ofNat 4 step.val

def unitCoreRows (step : Fin 8) (i : Fin 12) : Nat :=
  if step.val < 4 then coreRows (unitGenerator step) i else
    ((inverseCoreRowData[(unitGenerator step).val]?.getD [])[i.val]?).getD 0

def unitMove (step : Fin 8) : Vector 127 →ₗ[Field] Vector 127 :=
  rowMap (parameterRows (unitDirection step) (unitGenerator step))

def unitAction (step : Fin 8) : Vector 12 →ₗ[Field] Vector 12 := rowMap (unitCoreRows step)

theorem unit_last_coefficient (step : Fin 8) :
    parameterRows (unitDirection step) (unitGenerator step) (Fin.last 126) = 2 ^ 126 := by
  fin_cases step <;> native_decide

theorem unitMove_last (step : Fin 8) (v : Vector 127) :
    unitMove step v (Fin.last 126) = v (Fin.last 126) := by
  change evalRow (parameterRows (unitDirection step) (unitGenerator step) (Fin.last 126)) v = _
  rw [unit_last_coefficient]
  exact CoveringEncoding.evalRow_two_pow (Fin.last 126) v

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem unit_intertwines_basis (step : Fin 8) :
    ∀ i : Fin 12, localEmbedding (unitAction step (Pi.single i 1)) =
      rowMap (inverseCoordinateRows (unitDirection step) (unitGenerator step))
        (Pi.single (CoveringMatrix.localInclusion i) 1) := by
  fin_cases step <;> native_decide

theorem unit_intertwines (step : Fin 8) :
    localEmbedding.comp (unitAction step) =
      (coordinateEquiv (unitDirection step) (unitGenerator step)).symm.toLinearMap.comp
        localEmbedding := by
  rw [coordinateEquiv_symm_toLinearMap]
  apply (Pi.basisFun Field (Fin 12)).ext
  intro i
  simpa only [Pi.basisFun_apply, LinearMap.comp_apply, localEmbedding_basis] using
    unit_intertwines_basis step i

theorem unitAction_injective (step : Fin 8) : Function.Injective (unitAction step) := by
  intro a b hab
  apply localEmbedding_injective
  apply (coordinateEquiv (unitDirection step) (unitGenerator step)).symm.injective
  have h := congrArg localEmbedding hab
  change (localEmbedding.comp (unitAction step)) a =
    (localEmbedding.comp (unitAction step)) b at h
  rw [unit_intertwines] at h
  exact h

theorem fullForm_unitMove (step : Fin 8) (v : Vector 127) :
    fullForm (unitMove step v) = Covering.gram (fullForm v)
      (coordinateEquiv (unitDirection step) (unitGenerator step)).toLinearMap := by
  unfold fullForm unitMove
  rw [CoveringCongruence.bilinear_covariance_of_rows _ _ _
      (coefficientIdentities (unitDirection step) (unitGenerator step)),
    ← coordinateEquiv_toLinearMap]

theorem fullKernel_unitMove (step : Fin 8) (v : Vector 127) :
    (fullKernel (fullForm v)).map (unitAction step) ≤ fullKernel (fullForm (unitMove step v)) := by
  rw [fullForm_unitMove]
  exact fullKernel_transport _ _ _ (unit_intertwines step)

theorem fullRank_unitMove (step : Fin 8) (v : Vector 127) :
    Module.finrank Field (LinearMap.range (fullForm (unitMove step v))) =
      Module.finrank Field (LinearMap.range (fullForm v)) :=
  rank_covariance (unitDirection step) (unitGenerator step) v

def unitCoreColumnData : List (List Nat) := [
  [0x5, 0x1, 0x2, 0x50, 0xa8, 0x108, 0x20, 0x8, 0x30, 0x200, 0x400, 0x800],
  [0x200, 0x400, 0x800, 0x8, 0x50, 0x80, 0x40, 0x20, 0x148, 0x1, 0x2, 0x4],
  [0x1, 0x2, 0x4, 0x8, 0x12, 0x24, 0x40, 0x84, 0x103, 0x209, 0x442, 0x8a4],
  [0x4, 0x5, 0x3, 0xa0, 0x198, 0x1e8, 0xa8, 0x1a0, 0x1f0, 0x800, 0xa00, 0x600],
  [0x2, 0x4, 0x3, 0x80, 0x140, 0x40, 0x148, 0xd0, 0xa0, 0x200, 0x400, 0x800],
  [0x200, 0x400, 0x800, 0x8, 0x50, 0x80, 0x40, 0x20, 0x148, 0x1, 0x2, 0x4],
  [0x1, 0x2, 0x4, 0x8, 0x12, 0x24, 0x40, 0x84, 0x103, 0x209, 0x442, 0x8a4],
  [0x3, 0x7, 0x1, 0x48, 0x168, 0x1b0, 0xe8, 0x1b8, 0x88, 0x600, 0xe00, 0x200]
]

def unitLocalRowData : List (List Nat) := [
  [0x3, 0x4, 0x1, 0x30, 0x8, 0x10, 0x180, 0x40, 0x80, 0x200, 0x1800, 0x400, 0x800, 0x2000, 0x4000],
  [0x200, 0x2000, 0x4000, 0x8, 0x40, 0x400, 0x10, 0x80, 0x800, 0x1, 0x20, 0x100, 0x1000, 0x2, 0x4],
  [0x251, 0x2422, 0x4904, 0x8, 0x210, 0x2020, 0x240, 0x80, 0x4100, 0x200, 0x2400, 0x4800, 0x1000, 0x2000, 0x4000],
  [0x6, 0x4, 0x3, 0x1000, 0x1c00, 0x1800, 0x1120, 0x1df8, 0x19b0, 0x6000, 0x1100, 0x1dc0, 0x1980, 0x4000, 0x2200],
  [0x4, 0x5, 0x2, 0x10, 0x20, 0x28, 0x80, 0x100, 0x140, 0x200, 0x800, 0x1000, 0x1400, 0x2000, 0x4000],
  [0x200, 0x2000, 0x4000, 0x8, 0x40, 0x400, 0x10, 0x80, 0x800, 0x1, 0x20, 0x100, 0x1000, 0x2, 0x4],
  [0x251, 0x2422, 0x4904, 0x8, 0x210, 0x2020, 0x240, 0x80, 0x4100, 0x200, 0x2400, 0x4800, 0x1000, 0x2000, 0x4000],
  [0x7, 0x3, 0x2, 0x1980, 0x1540, 0x440, 0x1830, 0x1428, 0x408, 0x6200, 0x30, 0x28, 0x8, 0x2200, 0x2000]
]

def unitCoreColumns (step : Fin 8) (i : Fin 12) : Nat :=
  ((unitCoreColumnData[step.val]?.getD [])[i.val]?).getD 0

def unitLocalRows (step : Fin 8) (i : Fin 15) : Nat :=
  ((unitLocalRowData[step.val]?.getD [])[i.val]?).getD 0

theorem unitCoreRows_transpose (step : Fin 8) :
    ∀ i j : Fin 12, (unitCoreRows step i).testBit j.val =
      (unitCoreColumns step j).testBit i.val := by
  fin_cases step <;> native_decide

theorem unitAction_decodeMask (step : Fin 8) (mask : Nat) :
    unitAction step (decodeMask mask) =
      (decodeMask (composeRow mask (unitCoreColumns step)) : Vector 12) :=
  rowMap_decodeMask _ _ (unitCoreRows_transpose step) mask

theorem unit_projection_coefficient_identity (step : Fin 8) :
    ∀ i : Fin 15, composeRow (projectionRows i)
      (parameterRows (unitDirection step) (unitGenerator step)) =
        composeRow (unitLocalRows step i) projectionRows := by
  fin_cases step <;> native_decide

theorem localParameterProjection_unitMove (step : Fin 8) (v : Vector 127) :
    localParameterProjection (unitMove step v) =
      rowMap (unitLocalRows step) (localParameterProjection v) := by
  funext i
  change evalRow (projectionRows i)
      (rowMap (parameterRows (unitDirection step) (unitGenerator step)) v) =
    evalRow (unitLocalRows step i) (rowMap projectionRows v)
  rw [← evalRow_composeRow, ← evalRow_composeRow, unit_projection_coefficient_identity]

theorem unitMove_preserves_zero_projection (step : Fin 8) (v : Vector 127)
    (hv : localParameterProjection v = 0) :
    localParameterProjection (unitMove step v) = 0 := by
  rw [localParameterProjection_unitMove, hv, map_zero]

end Lemmata.CocubicCovering.CoveringSymmetry
