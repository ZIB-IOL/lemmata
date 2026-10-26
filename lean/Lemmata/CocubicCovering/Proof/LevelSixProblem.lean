module

public import Lemmata.CocubicCovering.Proof.LevelSixCoreData
public meta import Lemmata.CocubicCovering.Proof.LevelSixCoreData
public import Lemmata.CocubicCovering.Proof.LevelSixSymmetry
public meta import Lemmata.CocubicCovering.Proof.LevelSixSymmetry

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringLevelSixProblem

open Module CoveringAffine CoveringBits CoveringPolynomial CoveringEncoding
open CoveringSymmetry
open CoveringPackedAction CoveringWitness

set_option maxRecDepth 32768

private theorem elementary_columns : ∀ step i,
    CoveringLevelSixCoreData.elementaryColumns step i = unitCoreColumns step i := by
  native_decide

private theorem elementary_local_transpose : ∀ (step : Fin 8) (i j : Fin 15),
    (unitLocalRows step i).testBit j.val =
      (CoveringLevelSixCoreData.elementaryLocalColumns step j).testBit i.val := by
  native_decide

theorem applyWord_eq (steps : List (Fin 8)) (mask : ℕ) :
    CoveringLevelSixCoreData.applyWord steps mask = CoveringWord.applyMask steps mask := by
  have he : CoveringLevelSixCoreData.elementaryColumns = unitCoreColumns := by
    funext step i
    exact elementary_columns step i
  unfold CoveringLevelSixCoreData.applyWord CoveringWord.applyMask
  rw [he]

def localAction : List (Fin 8) → Vector 15 →ₗ[Field] Vector 15
  | [] => LinearMap.id
  | step :: rest => (localAction rest).comp (rowMap (unitLocalRows step))

theorem localAction_decodeMask (steps : List (Fin 8)) (mask : ℕ) :
    localAction steps (decodeMask mask) =
      (decodeMask (CoveringLevelSixCoreData.applyLocalWord steps mask) : Vector 15) := by
  induction steps generalizing mask with
  | nil => rfl
  | cons step rest ih =>
      change localAction rest (rowMap (unitLocalRows step) (decodeMask mask)) = _
      rw [rowMap_decodeMask _ _ (elementary_local_transpose step), ih]
      rfl

theorem projection_move (steps : List (Fin 8)) (v : Vector 127) :
    localParameterProjection (CoveringLevelSixSymmetry.move steps v) =
      localAction steps (localParameterProjection v) := by
  induction steps generalizing v with
  | nil => rfl
  | cons step rest ih =>
      change localParameterProjection
          (CoveringLevelSixSymmetry.move rest (CoveringLevelSixSymmetry.unitMove step v)) = _
      rw [ih, CoveringLevelSixSymmetry.localParameterProjection_unitMove]
      rfl

theorem localAction_columns (steps : List (Fin 8)) (columns : Fin 15 → ℕ)
    (hcolumns : ∀ i, columns i = CoveringLevelSixCoreData.applyLocalWord steps (2 ^ i.val))
    (mask : ℕ) : localAction steps (decodeMask mask) =
      (decodeMask (composeRow mask columns) : Vector 15) := by
  have hlinear : localAction steps =
      familyLinear (fun i => (decodeMask (columns i) : Vector 15)) := by
    apply (Pi.basisFun Field (Fin 15)).ext
    intro i
    have hsingle : (decodeMask (2 ^ i.val) : Vector 15) = Pi.single i 1 := by
      funext j
      by_cases hij : i = j
      · subst j
        simp [decodeMask, Nat.testBit_two_pow, Pi.single_apply]
      · have hval : i.val ≠ j.val := fun he => hij (Fin.ext he)
        simp [decodeMask, Nat.testBit_two_pow, Pi.single_apply,
          hij, Ne.symm hij, hval, Ne.symm hval]
    simp only [Pi.basisFun_apply, familyLinear,
      Fintype.linearCombination_apply_single, one_smul]
    rw [← hsingle, localAction_decodeMask, ← hcolumns i]
  rw [hlinear, ← decodeMask_composeRow_familyLinear]

def allowed (root : Fin 30) (v : Vector 127) : Prop :=
  v (Fin.last 126) = 1 ∧
    localParameterProjection v = decodeMask (CoveringLevelSixCoreData.roots root).assignment ∧
    finrank Field (CoveringLevelSixReduction.fullKernel v) =
      (CoveringLevelSixCoreData.roots root).required ∧
    finrank Field (LinearMap.range (CoveringLevelSixReduction.fullForm v)) ≤ 10

theorem allowed_coordinates (root : Fin 30) (v : Vector 127) (hv : allowed root v)
    (i : Fin 15) : v ⟨111 + i.val, by omega⟩ =
      ofBool ((CoveringLevelSixCoreData.roots root).assignment.testBit i.val) := by
  have he := congrFun hv.2.1 i
  have hp : localParameterProjection v i = v ⟨111 + i.val, by omega⟩ :=
    evalRow_two_pow ⟨111 + i.val, by omega⟩ v
  rw [hp] at he
  exact he

attribute [local irreducible] encodeVector decodeMask localParameterProjection

theorem allowed_transform (steps : List (Fin 8)) (source target : Fin 30)
    (hassignment : composeRow (CoveringLevelSixCoreData.roots source).assignment
      (fun i : Fin 15 => CoveringLevelSixCoreData.applyLocalWord steps (2 ^ i.val)) =
        (CoveringLevelSixCoreData.roots target).assignment)
    (hdimension : (CoveringLevelSixCoreData.roots source).required =
      (CoveringLevelSixCoreData.roots target).required)
    (v : Vector 127) (hv : allowed source v) :
    allowed target (CoveringLevelSixSymmetry.move steps v) := by
  refine ⟨(CoveringLevelSixSymmetry.move_last _ v).trans hv.1, ?_, ?_, ?_⟩
  · rw [projection_move, hv.2.1, localAction_columns _ _ (fun _ => rfl), hassignment]
  · rw [CoveringLevelSixSymmetry.move_kernel_finrank, hv.2.2.1, hdimension]
  · rw [CoveringLevelSixSymmetry.move_rank]
    exact hv.2.2.2

end Lemmata.CocubicCovering.CoveringLevelSixProblem
