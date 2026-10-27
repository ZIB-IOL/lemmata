module

public import Lemmata.CocubicCovering.Proof.Pairing
public meta import Lemmata.CocubicCovering.Proof.Pairing
public import Lemmata.CocubicCovering.Proof.CovarianceData
public meta import Lemmata.CocubicCovering.Proof.CovarianceData

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringRealization

open Covering CoveringPolynomial CoveringEmbedding CoveringPairing
open CoveringEncoding CoveringCongruence CoveringCovarianceData

theorem exists_pointed_realization (h : BooleanFunction 9) (hh : h ∈ reedMuller 9 5) :
    ∃ v : Vector 127, v (Fin.last 126) = 1 ∧
      supportGram (Covering.eval form9 + h) multiplierLinear =
        Matrix.toBilin' (coefficientMatrix matrixRows v) := by
  obtain ⟨assignment, hentries⟩ := exists_parameter_assignment h hh
  let fieldAssignment : ℕ → Field := fun n => ofBool (assignment n)
  let v := pointedVector parameterMasks fieldAssignment
  refine ⟨v, ?_, ?_⟩
  · change Fin.lastCases (motive := fun _ : Fin 127 => Field) (1 : Field)
      (fun i : Fin 126 => fieldAssignment (parameterMasks i))
      (Fin.last 126) = 1
    rw [Fin.lastCases_last]
  · have hmatrix : ∀ i j : Fin 24,
        supportGram (Covering.eval form9 + h) multiplierLinear (Pi.single i 1) (Pi.single j 1) =
          coefficientMatrix matrixRows v i j := by
      intro i j
      calc
        _ = ofBool (CoveringMatrix.matrix assignment i j) := hentries i j
        _ = evalField fieldAssignment
            (CoveringMatrix.equation (CoveringMatrix.multiplier i) (CoveringMatrix.multiplier j)) :=
          (evalField_ofBool assignment _).symm
        _ = coefficientMatrix matrixRows v i j :=
          congrFun (congrFun (matrix_equations fieldAssignment) i) j
    apply (Pi.basisFun Field (Fin 24)).ext
    intro i
    apply (Pi.basisFun Field (Fin 24)).ext
    intro j
    simpa only [Pi.basisFun_apply, Matrix.toBilin'_single] using hmatrix i j

theorem form9_packed_weight_reduction (h : BooleanFunction 9) (hh : h ∈ reedMuller 9 5) :
    ∃ v : Vector 127, v (Fin.last 126) = 1 ∧
      20 + Module.finrank Field
        (LinearMap.range (Matrix.toBilin' (coefficientMatrix matrixRows v))) ≤
          weight (Covering.eval form9 + h) := by
  obtain ⟨v, hv, hgram⟩ := exists_pointed_realization h hh
  refine ⟨v, hv, ?_⟩
  have hweight := form9_weight_lower h hh
  rw [hgram] at hweight
  exact hweight

end Lemmata.CocubicCovering.CoveringRealization
