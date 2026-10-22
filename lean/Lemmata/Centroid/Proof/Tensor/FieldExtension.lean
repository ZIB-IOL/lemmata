module

public import Lemmata.Centroid.Proof.Centroid
public import Lemmata.Centroid.Proof.Symmetric.Basic
public import Lemmata.Centroid.Proof.Linear.FieldExtension
public import Mathlib.FieldTheory.RatFunc.Basic

@[expose] public section

open scoped BigOperators Matrix
open Classical

noncomputable section

namespace Lemmata.Centroid.Tensor

variable {F K I : Type*} [Field F] [Field K] [Fintype I]

def centroidCoordinates :
    (Fin 3 × I × I → F) ≃ₗ[F] (Fin 3 → Matrix I I F) where
  toFun q i a b := q (i, a, b)
  invFun A p := A p.1 p.2.1 p.2.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype I] in
@[simp] theorem centroidCoordinates_apply (q : Fin 3 × I × I → F) (i : Fin 3) (a b : I) :
    centroidCoordinates q i a b = q (i, a, b) := rfl

def centroidEquations (T : Cubic F I) :
    (Fin 3 × I × I → F) →ₗ[F] (Fin 3 × Fin 3 × (Fin 3 → I) → F) where
  toFun q r := legAction T r.1 (centroidCoordinates q r.1) r.2.2 -
    legAction T r.2.1 (centroidCoordinates q r.2.1) r.2.2
  map_add' q p := by
    funext r
    simp only [map_add, Pi.add_apply]
    ring
  map_smul' t q := by
    funext r
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_sub]

@[simp] theorem centroidEquations_apply (T : Cubic F I) (q : Fin 3 × I × I → F)
    (r : Fin 3 × Fin 3 × (Fin 3 → I)) :
    centroidEquations T q r = legAction T r.1 (centroidCoordinates q r.1) r.2.2 -
      legAction T r.2.1 (centroidCoordinates q r.2.1) r.2.2 := rfl

def centroidEquationsEquiv (T : Cubic F I) :
    (centroidEquations T).ker ≃ₗ[F] centroid T where
  toFun q := ⟨centroidCoordinates q.val, by
    intro i j
    funext x
    have h := congrFun q.property (i, j, x)
    exact sub_eq_zero.mp h⟩
  invFun A := ⟨centroidCoordinates.symm A.val, by
    funext r
    change legAction T r.1 (A.val r.1) r.2.2 -
      legAction T r.2.1 (A.val r.2.1) r.2.2 = 0
    exact sub_eq_zero.mpr (congrFun (A.property r.1 r.2.1) r.2.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def centroidMatrix (T : Cubic F I) :
    Matrix (Fin 3 × Fin 3 × (Fin 3 → I)) (Fin 3 × I × I) F :=
  LinearMap.toMatrix' (centroidEquations T)

theorem centroidMatrix_mulVecLin (T : Cubic F I) :
    (centroidMatrix T).mulVecLin = centroidEquations T :=
  Matrix.toLin'_toMatrix' _

theorem centroidEquations_map (φ : F →+* K) (T : Cubic F I)
    (q : Fin 3 × I × I → F) (r : Fin 3 × Fin 3 × (Fin 3 → I)) :
    centroidEquations (φ ∘ T) (φ ∘ q) r = φ (centroidEquations T q r) := by
  simp only [centroidEquations_apply, legAction_apply, centroidCoordinates_apply,
    Function.comp_apply, map_sub, map_sum, map_mul]

theorem centroidMatrix_map (φ : F →+* K) (T : Cubic F I) :
    centroidMatrix (φ ∘ T) = (centroidMatrix T).map φ := by
  ext r p
  change centroidEquations (φ ∘ T) (Pi.single p 1) r =
    φ (centroidEquations T (Pi.single p 1) r)
  have h : (Pi.single p (1 : K)) = φ ∘ Pi.single p (1 : F) := by
    funext a
    by_cases h : a = p <;> simp [h]
  rw [h, centroidEquations_map]

theorem finrank_centroid_map (φ : F →+* K) (T : Cubic F I) :
    Module.finrank K (centroid (φ ∘ T)) = Module.finrank F (centroid T) := by
  rw [← (centroidEquationsEquiv (φ ∘ T)).finrank_eq,
    ← (centroidEquationsEquiv T).finrank_eq,
    ← centroidMatrix_mulVecLin, ← centroidMatrix_mulVecLin, centroidMatrix_map]
  exact Linear.matrix_kernel_finrank_map φ _

def contractionMatrix (T : Cubic F I) (i : Fin 3) : Matrix (Fin 3 → I) I F :=
  fun x a => T (@Function.update (Fin 3) (fun _ => I) (Classical.decEq _) x i a)

theorem contractionMatrix_mulVecLin (T : Cubic F I) (i : Fin 3) :
    (contractionMatrix T i).mulVecLin = contraction T i := by
  apply LinearMap.ext
  intro u
  funext x
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    contractionMatrix, contraction_apply, mul_comm]

theorem Concise.map {T : Cubic F I} (hT : Concise T) (φ : F →+* K) :
    Concise (φ ∘ T) := by
  intro i
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  rw [← contractionMatrix_mulVecLin]
  have heq : contractionMatrix (φ ∘ T) i = (contractionMatrix T i).map φ := rfl
  rw [heq, Linear.matrix_kernel_finrank_map, contractionMatrix_mulVecLin,
    LinearMap.ker_eq_bot.mpr (hT i)]
  simp

end Lemmata.Centroid.Tensor
