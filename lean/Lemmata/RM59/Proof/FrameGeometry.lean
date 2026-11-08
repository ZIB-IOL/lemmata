module

public import Lemmata.RM59.Proof.TraceGeometry
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Tactic.Abel

@[expose] public section

namespace Lemmata.RM59.FrameGeometry

open scoped Matrix

abbrev FieldPoint := TraceGeometry.FieldPoint
abbrev FieldMatrix := TraceGeometry.FieldMatrix

def fullFrameMap (U V : FieldMatrix) : FieldMatrix := V * (U.det⁻¹ • U.adjugate)

theorem fullFrameMap_eq (U V : FieldMatrix) : fullFrameMap U V = V * U⁻¹ := by
  rw [fullFrameMap, Matrix.inv_def, Ring.inverse_eq_inv]

theorem fullFrameMap_mul (U V : FieldMatrix) (hU : U.det ≠ 0) :
    fullFrameMap U V * U = V := by
  rw [fullFrameMap_eq, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul U (isUnit_iff_ne_zero.mpr hU), Matrix.mul_one]

theorem fullFrameMap_det_one (U V : FieldMatrix) (hU : U.det ≠ 0)
    (hdet : V.det = U.det) : (fullFrameMap U V).det = 1 := by
  rw [fullFrameMap_eq, Matrix.det_mul, hdet, mul_comm]
  exact Matrix.det_nonsing_inv_mul_det U (isUnit_iff_ne_zero.mpr hU)

theorem fullFrameMap_column (U V : FieldMatrix) (hU : U.det ≠ 0) (j : Fin 3) :
    fullFrameMap U V *ᵥ U.col j = V.col j := by
  exact congrArg (fun M : FieldMatrix => M.col j) (fullFrameMap_mul U V hU)

def differenceMatrix (p : Fin 4 → FieldPoint) : FieldMatrix :=
  Matrix.of fun i j => p j.succ i - p 0 i

def frameDeterminant (p : Fin 4 → FieldPoint) : F8Scalar := (differenceMatrix p).det

theorem centered_frame_match (p q : Fin 4 → FieldPoint)
    (hp : frameDeterminant p ≠ 0) (i : Fin 4) :
    q 0 + fullFrameMap (differenceMatrix p) (differenceMatrix q) *ᵥ (p i - p 0) = q i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · have h := fullFrameMap_column (differenceMatrix p) (differenceMatrix q) hp j
    change fullFrameMap (differenceMatrix p) (differenceMatrix q) *ᵥ
      (p j.succ - p 0) = q j.succ - q 0 at h
    rw [h]
    abel

theorem exists_affine_det_one_frame_map (p q : Fin 4 → FieldPoint)
    (hp : frameDeterminant p ≠ 0) (hdet : frameDeterminant q = frameDeterminant p) :
    ∃ A : FieldMatrix, ∃ b : FieldPoint, A.det = 1 ∧ ∀ i, A *ᵥ p i + b = q i := by
  let A := fullFrameMap (differenceMatrix p) (differenceMatrix q)
  refine ⟨A, q 0 - A *ᵥ p 0, fullFrameMap_det_one _ _ hp hdet, ?_⟩
  intro i
  calc
    A *ᵥ p i + (q 0 - A *ᵥ p 0) = q 0 + A *ᵥ (p i - p 0) := by
      rw [Matrix.mulVec_sub]
      abel
    _ = q i := centered_frame_match p q hp i

theorem det_rows_eq_cross_dot (u v w : FieldPoint) :
    Matrix.det (Matrix.of ![u, v, w]) = (u ⨯₃ v) ⬝ᵥ w := by
  calc
    Matrix.det (Matrix.of ![u, v, w]) = u ⬝ᵥ (v ⨯₃ w) :=
      (triple_product_eq_det u v w).symm
    _ = w ⬝ᵥ (u ⨯₃ v) := (triple_product_permutation w u v).symm
    _ = (u ⨯₃ v) ⬝ᵥ w := dotProduct_comm _ _

theorem exists_coordinate_ne_zero (v : FieldPoint) (hv : v ≠ 0) : ∃ i, v i ≠ 0 := by
  classical
  by_cases h : ∃ i, v i ≠ 0
  · exact h
  · exfalso
    apply hv
    funext i
    by_contra hi
    exact h ⟨i, hi⟩

theorem extend_independent_vectors (u v : FieldPoint)
    (h : LinearIndependent F8Scalar ![u, v]) (δ : F8Scalar) :
    ∃ w : FieldPoint, Matrix.det (Matrix.of ![u, v, w]) = δ := by
  have hc : u ⨯₃ v ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.mpr h
  obtain ⟨i, hi⟩ := exists_coordinate_ne_zero (u ⨯₃ v) hc
  refine ⟨Pi.single i (δ / (u ⨯₃ v) i), ?_⟩
  rw [det_rows_eq_cross_dot, dotProduct_single, div_eq_mul_inv]
  calc
    (u ⨯₃ v) i * (δ * ((u ⨯₃ v) i)⁻¹) =
        δ * ((u ⨯₃ v) i * ((u ⨯₃ v) i)⁻¹) := by ring
    _ = δ := by rw [mul_inv_cancel₀ hi, mul_one]

theorem exists_independent_partner (v : FieldPoint) (hv : v ≠ 0) :
    ∃ u : FieldPoint, LinearIndependent F8Scalar ![v, u] := by
  obtain ⟨i, hi⟩ := exists_coordinate_ne_zero v hv
  fin_cases i
  · refine ⟨![0, 1, 0], crossProduct_ne_zero_iff_linearIndependent.mp ?_⟩
    intro h
    apply hi
    simpa [cross_apply] using congrFun h 2
  · refine ⟨![0, 0, 1], crossProduct_ne_zero_iff_linearIndependent.mp ?_⟩
    intro h
    apply hi
    simpa [cross_apply] using congrFun h 0
  · refine ⟨![1, 0, 0], crossProduct_ne_zero_iff_linearIndependent.mp ?_⟩
    intro h
    apply hi
    simpa [cross_apply] using congrFun h 1

theorem extend_independent_triple (a b c : FieldPoint)
    (h : LinearIndependent F8Scalar ![b - a, c - a]) (δ : F8Scalar) :
    ∃ d : FieldPoint, frameDeterminant ![a, b, c, d] = δ := by
  obtain ⟨w, hw⟩ := extend_independent_vectors (b - a) (c - a) h δ
  refine ⟨a + w, ?_⟩
  have hm : differenceMatrix ![a, b, c, a + w] =
      (Matrix.of ![b - a, c - a, w])ᵀ := by
    ext i j
    fin_cases j <;> simp [differenceMatrix, Matrix.transpose_apply]
  change (differenceMatrix ![a, b, c, a + w]).det = δ
  rw [hm, Matrix.det_transpose]
  exact hw

theorem extend_distinct_pair (a b : FieldPoint) (h : a ≠ b) (δ : F8Scalar) :
    ∃ c d : FieldPoint, frameDeterminant ![a, b, c, d] = δ := by
  have hv : b - a ≠ 0 := sub_ne_zero.mpr h.symm
  obtain ⟨u, hu⟩ := exists_independent_partner (b - a) hv
  have htriple : LinearIndependent F8Scalar ![b - a, (a + u) - a] := by
    simpa only [add_sub_cancel_left] using hu
  obtain ⟨d, hd⟩ := extend_independent_triple a b (a + u) htriple δ
  exact ⟨a + u, d, hd⟩

end Lemmata.RM59.FrameGeometry
