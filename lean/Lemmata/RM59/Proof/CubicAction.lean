module

public import Lemmata.RM59.Proof.CubicForms
public import Lemmata.RM59.Proof.CatalogInvariant
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Lemmata.RM59

open scoped BigOperators

abbrev CoordinateGroup (m : ℕ) := Point m ≃ₗ[Field] Point m

def coordinateGroupMatrixEquiv (m : ℕ) :
    Matrix.GeneralLinearGroup (Fin m) Field ≃* CoordinateGroup m :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv Field (Point m))

instance coordinateGroupFinite (m : ℕ) : Finite (CoordinateGroup m) :=
  Finite.of_equiv (Matrix.GeneralLinearGroup (Fin m) Field)
    (coordinateGroupMatrixEquiv m).toEquiv

noncomputable instance coordinateGroupFintype (m : ℕ) : Fintype (CoordinateGroup m) :=
  Fintype.ofFinite _

def binaryGeneralLinearOrder (m : ℕ) : ℕ := ∏ i : Fin m, (2 ^ m - 2 ^ i.val)

theorem coordinateGroup_card (m : ℕ) : Nat.card (CoordinateGroup m) = binaryGeneralLinearOrder m := by
  calc
    Nat.card (CoordinateGroup m) = Nat.card (Matrix.GeneralLinearGroup (Fin m) Field) :=
      (Nat.card_congr (coordinateGroupMatrixEquiv m).toEquiv).symm
    _ = ∏ i : Fin m, (Fintype.card Field ^ m - Fintype.card Field ^ i.val) :=
      Matrix.card_GL_field m
    _ = binaryGeneralLinearOrder m := by simp [binaryGeneralLinearOrder, Field]

instance cubicFormMulAction : MulAction (CoordinateGroup 9) CubicForm where
  smul g T := T.compLinearMap g.symm.toLinearMap
  one_smul T := by
    apply AlternatingMap.ext
    intro v
    rfl
  mul_smul g h T := by
    apply AlternatingMap.ext
    intro v
    rfl

theorem cubicForm_smul_apply (g : CoordinateGroup 9) (T : CubicForm)
    (v : Fin 3 → Point 9) :
    (g • T) v = T (fun i => g.symm (v i)) := rfl

theorem cubicForm_smul_on_images (g : CoordinateGroup 9) (T : CubicForm)
    (v : Fin 3 → Point 9) : (g • T) (fun i => g (v i)) = T v := by
  change T (fun i => g.symm (g (v i))) = T v
  simp only [LinearEquiv.symm_apply_apply]

@[simp] theorem cubicForm_smul_zero (g : CoordinateGroup 9) : g • (0 : CubicForm) = 0 := by
  apply AlternatingMap.ext
  intro v
  rfl

theorem mem_cubicForm_stabilizer_iff (g : CoordinateGroup 9) (T : CubicForm) :
    g ∈ MulAction.stabilizer (CoordinateGroup 9) T ↔
      ∀ v : Fin 3 → Point 9, T (fun i => g (v i)) = T v := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h v
    have hp := congrArg (fun F : CubicForm => F (fun i => g (v i))) h
    change T (fun i => g.symm (g (v i))) = T (fun i => g (v i)) at hp
    simpa only [LinearEquiv.symm_apply_apply] using hp.symm
  · intro h
    apply AlternatingMap.ext
    intro v
    have hp := h (fun i => g.symm (v i))
    change T (fun i => g.symm (v i)) = T v
    simpa only [LinearEquiv.apply_symm_apply] using hp.symm

def cubicFormValue (T : CubicForm) (v w u : Point 9) : Field := T ![v, w, u]

theorem cubicFormValue_smul_on_images (g : CoordinateGroup 9) (T : CubicForm)
    (v w u : Point 9) : cubicFormValue (g • T) (g v) (g w) (g u) = cubicFormValue T v w u := by
  have htuple : (fun i => g (![v, w, u] i)) = ![g v, g w, g u] := by
    funext i
    fin_cases i <;> rfl
  unfold cubicFormValue
  rw [← htuple]
  exact cubicForm_smul_on_images g T ![v, w, u]

def cubicFormInvariant (T : CubicForm) : List CatalogInvariant.VertexFeature :=
  CatalogInvariant.contractionInvariant (cubicFormValue T)

theorem cubicFormInvariant_smul (g : CoordinateGroup 9) (T : CubicForm) :
    cubicFormInvariant (g • T) = cubicFormInvariant T := by
  exact (CatalogInvariant.contractionInvariant_equiv (cubicFormValue T)
    (cubicFormValue (g • T)) g.toEquiv g.map_zero
    (cubicFormValue_smul_on_images g T)).symm

end Lemmata.RM59
