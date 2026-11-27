module

public import Lemmata.RM59.Proof.FieldCoordinates
public import Lemmata.RM59.Proof.SupportForms
public import Mathlib.LinearAlgebra.StdBasis
public meta import Lemmata.RM59.Proof.TraceGeometry
public meta import Lemmata.RM59.Proof.FieldData
public meta import Lemmata.RM59.Proof.Packed

@[expose] public section

namespace Lemmata.RM59.TraceData

open scoped BigOperators Matrix
open Lemmata.RM59.SupportForms

def traceForm : MultilinearMap Field (fun _ : Fin 3 => Point 9) Field :=
  TraceGeometry.tau.toMultilinearMap.compLinearMap fun _ => FieldCoordinates.covectorLinear

/-- Ordered triples include repetitions, so the encoded mask uses a set. -/
theorem ordered_coefficients : ∀ i j k : Fin 9,
    Packed.bitField (FieldData.packedMoment FieldData.support35
      (Packed.encodeMask {i, j, k}).val) =
    TraceGeometry.traceToField (FieldData.determinant (FieldData.basisCovector i)
      (FieldData.basisCovector j) (FieldData.basisCovector k)) := by native_decide

theorem data_determinant (u v w : TraceGeometry.FieldPoint) :
    FieldData.determinant u v w = Matrix.det (Matrix.of ![u, v, w]) := by
  rw [Matrix.det_fin_three]
  simp [FieldData.determinant] <;> ring

theorem traceForm_basis (v : Fin 3 → Fin 9) :
    traceForm (fun r => Pi.single (v r) 1) =
      TraceGeometry.traceToField (FieldData.determinant (FieldData.basisCovector (v 0))
        (FieldData.basisCovector (v 1)) (FieldData.basisCovector (v 2))) := by
  change TraceGeometry.traceToField (Matrix.det
    (Matrix.of fun r => FieldCoordinates.covectorLinear (Pi.single (v r) 1))) = _
  simp_rw [FieldCoordinates.covector_basis]
  have h : Matrix.of (fun r => FieldData.basisCovector (v r)) =
      Matrix.of ![FieldData.basisCovector (v 0), FieldData.basisCovector (v 1),
        FieldData.basisCovector (v 2)] := by
    ext r s
    fin_cases r <;> rfl
  rw [h, ← data_determinant]

theorem support35_form_eq_traceForm :
    supportForm (Packed.decodeWord FieldData.support35) = traceForm := by
  apply Module.Basis.ext_multilinear (fun _ => Pi.basisFun Field (Fin 9))
  intro v
  simp only [Pi.basisFun_apply]
  rw [packed_supportForm_basis _ FieldData.support35_data.2, traceForm_basis]
  exact ordered_coefficients (v 0) (v 1) (v 2)

theorem triple_mask_degree : ∀ i j k : Fin 9,
    FieldData.bitCount (Packed.encodeMask {i, j, k}).val ≤ 3 := by native_decide

theorem support53_form_eq_sum :
    supportForm (Packed.decodeWord FieldData.support53) =
      supportForm (Packed.decodeWord FieldData.support35) +
      supportForm (Packed.decodeWord FieldData.verticalFlat) := by
  apply Module.Basis.ext_multilinear (fun _ => Pi.basisFun Field (Fin 9))
  intro v
  simp only [Pi.basisFun_apply]
  change supportForm (Packed.decodeWord FieldData.support53) (fun r => Pi.single (v r) 1) =
    supportForm (Packed.decodeWord FieldData.support35) (fun r => Pi.single (v r) 1) +
    supportForm (Packed.decodeWord FieldData.verticalFlat) (fun r => Pi.single (v r) 1)
  rw [packed_supportForm_basis _ FieldData.support53_data.2,
    packed_supportForm_basis _ FieldData.support35_data.2,
    packed_supportForm_basis _ FieldData.verticalFlat_data.2]
  have h := congrArg Packed.bitField (FieldData.syndrome53_eq_35_xor_vertical
    (Packed.encodeMask {v 0, v 1, v 2}) (triple_mask_degree (v 0) (v 1) (v 2)))
  simpa only [Packed.bitField_xor, FieldData.packedMoment, Packed.packedMoment] using h

theorem support53_form_eq_traceForm_add_vertical :
    supportForm (Packed.decodeWord FieldData.support53) =
      traceForm + supportForm (Packed.decodeWord FieldData.verticalFlat) := by
  rw [support53_form_eq_sum, support35_form_eq_traceForm]

end Lemmata.RM59.TraceData
