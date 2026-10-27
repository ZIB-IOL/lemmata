module

public import Lemmata.CocubicCovering.Proof.LevelSixSystems
public meta import Lemmata.CocubicCovering.Proof.LevelSixSystems

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringSystemSemantics

open scoped BigOperators
open CoveringAffine CoveringBits CoveringCongruence CoveringPolynomial
open CoveringPackedPair CoveringQuotient CoveringCoordinates CoveringSymplectic
open CoveringLevelSixReconstruction CoveringLevelSixSystems

def fullMatrix (v : Vector 127) : Matrix (Fin 27) (Fin 27) Field :=
  coefficientMatrix CoveringLevelSix.matrixRows v

def crossParameters (s : Fin 13) (v : Vector 127) (i : Fin (crossCount s)) : Field :=
  evalRow (crossCoefficients s i) v

def outsideParameters (s : Fin 13) (v : Vector 127) (i : Fin (outsideCount s)) : Field :=
  evalRow (outsideCoefficients s i) v

def actualCross (s : Fin 13) (v : Vector 127)
    (i : Fin (localRank s + crossRank s)) (j : Fin 15) : Field :=
  Matrix.toBilin' (fullMatrix v) (decodeMask (crossBasis s i)) (decodeMask (outsideBasis s j))

def actualOutside (s : Fin 13) (v : Vector 127) : Matrix (Fin 15) (Fin 15) Field :=
  fun i j => Matrix.toBilin' (fullMatrix v)
    (decodeMask (outsideBasis s i)) (decodeMask (outsideBasis s j))

def outsideRemainder (s : Fin 13) (v : Vector 127) : Matrix (Fin 15) (Fin 15) Field :=
  fun i j => ∑ k, outsideParameters s v k * Matrix.toBilin' (bitMatrix (outside s k))
    (decodeMask (outsideBasis s i)) (decodeMask (outsideBasis s j))

theorem reconstruction_matrix (s : Fin 13) (v : Vector 127)
    (hpoint : v (Fin.last 126) = 1)
    (hconstraints : ∀ k, evalRow (constraints s k) v = 0) :
    fullMatrix v = bitMatrix (base s) +
      (∑ k, crossParameters s v k • bitMatrix (cross s k)) +
      ∑ k, outsideParameters s v k • bitMatrix (outside s k) := by
  ext i j
  simpa only [fullMatrix, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, bitMatrix, crossParameters, outsideParameters, mul_comm] using
    CoveringLevelSixReconstruction.realization s v hpoint hconstraints i j

theorem reconstruction_pairing (s : Fin 13) (v : Vector 127)
    (hpoint : v (Fin.last 126) = 1)
    (hconstraints : ∀ k, evalRow (constraints s k) v = 0) (x y : Vector 27) :
    Matrix.toBilin' (fullMatrix v) x y = Matrix.toBilin' (bitMatrix (base s)) x y +
      (∑ k, crossParameters s v k * Matrix.toBilin' (bitMatrix (cross s k)) x y) +
      ∑ k, outsideParameters s v k * Matrix.toBilin' (bitMatrix (outside s k)) x y := by
  rw [reconstruction_matrix s v hpoint hconstraints]
  simp only [map_add, map_sum, map_smul, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

theorem cross_evaluation (s : Fin 13) (v : Vector 127)
    (hpoint : v (Fin.last 126) = 1)
    (hconstraints : ∀ k, evalRow (constraints s k) v = 0)
    (assignment : ℕ → Field)
    (hparameters : ∀ i : Fin (crossCount s), assignment i.val = crossParameters s v i)
    (i : Fin (localRank s + crossRank s)) (j : Fin 15) :
    CoveringIdeal.eval assignment (crossPolynomial s i j) = actualCross s v i j := by
  rw [crossPolynomial, eval_affinePolynomial]
  rw [(affineChecked s).1 i j]
  simp_rw [(affineChecked s).2.1 i j, hparameters, ofBool_pairBit]
  unfold actualCross
  rw [reconstruction_pairing s v hpoint hconstraints]
  have hzero : (∑ k, outsideParameters s v k * Matrix.toBilin' (bitMatrix (outside s k))
      (decodeMask (crossBasis s i)) (decodeMask (outsideBasis s j))) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [← ofBool_pairBit, (outsideChecked s).1 k i j, ofBool_false, mul_zero]
  rw [hzero, add_zero]
  simp only [mul_comm]

theorem outside_evaluation (s : Fin 13) (v : Vector 127)
    (hpoint : v (Fin.last 126) = 1)
    (hconstraints : ∀ k, evalRow (constraints s k) v = 0)
    (assignment : ℕ → Field)
    (hparameters : ∀ i : Fin (crossCount s), assignment i.val = crossParameters s v i)
    (i j : Fin 15) :
    actualOutside s v i j = CoveringIdeal.eval assignment (outsidePolynomial s i j) +
      outsideRemainder s v i j := by
  rw [outsidePolynomial, eval_affinePolynomial]
  rw [(affineChecked s).2.2.1 i j]
  simp_rw [(affineChecked s).2.2.2 i j, hparameters, ofBool_pairBit]
  unfold actualOutside outsideRemainder
  rw [reconstruction_pairing s v hpoint hconstraints]
  simp only [mul_comm]

theorem exists_input_solution_of_gram (s : Fin 13) (v : Vector 127)
    (hpoint : v (Fin.last 126) = 1)
    (hconstraints : ∀ k, evalRow (constraints s k) v = 0)
    (points : Fin 15 → Standard Field (pairs s))
    (hforced : ∀ (i : Fin (crossRank s)) (column : Fin 15),
      (points column).2 (Fin.castLE (crossRank_le_pairs s) i) =
        actualCross s v (Fin.natAdd (localRank s) i) column)
    (hgram : ∀ i j : Fin 15, standardBilin (pairs s) (points i) (points j) =
      CoveringSchur.schur (fun i j => ofBool (inverse s i j))
        (fun i => actualCross s v (Fin.castAdd (crossRank s) i))
        (Matrix.transpose (fun i => actualCross s v (Fin.castAdd (crossRank s) i)))
        (actualOutside s v) i j) :
    ∃ assignment : ℕ → Field, ∀ row : Fin 87,
      CoveringIdeal.eval assignment (input s row) = 0 := by
  obtain ⟨assignment, hparameters, hz⟩ := exists_coordinate_assignment
    (crossRank_le_pairs s) (crossParameters s v) points
  have hx : ∀ (column : Fin 15) (i : Fin (pairs s)),
      CoveringIdeal.eval assignment (nativeX s column i) = (points column).1 i :=
    eval_xPolynomial (crossRank_le_pairs s) assignment points hz
  have hy : ∀ (column : Fin 15) (i : Fin (pairs s)),
      CoveringIdeal.eval assignment (nativeY s column i) = (points column).2 i := by
    apply eval_yPolynomial (crossRank_le_pairs s) assignment points _ _ hz
    intro i column
    exact (cross_evaluation s v hpoint hconstraints assignment hparameters _ _).trans
      (hforced i column).symm
  have hc : ∀ (i : Fin (localRank s + crossRank s)) (j : Fin 15),
      CoveringIdeal.eval assignment (crossPolynomial s i j) = actualCross s v i j :=
    cross_evaluation s v hpoint hconstraints assignment hparameters
  have hraw : ∀ pair : Fin 105, CoveringIdeal.eval assignment (raw s pair) =
      ∑ k, outsideParameters s v k * Matrix.toBilin' (bitMatrix (outside s k))
        (decodeMask (outsideBasis s (pairFirst pair)))
        (decodeMask (outsideBasis s (pairSecond pair))) := by
    intro pair
    apply eval_rawPolynomial_of_gram assignment _ _ _ _ _
      (actualOutside s v) (outsideRemainder s v)
      (outside_evaluation s v hpoint hconstraints assignment hparameters)
    intro i j
    simpa only [hx, hy, hc] using hgram i j
  refine ⟨assignment, input_vanishes s assignment ?_⟩
  intro target
  exact quotientPolynomial_vanishes assignment (keep s) (raw s)
    (fun k pair => Matrix.toBilin' (bitMatrix (outside s k))
      (decodeMask (outsideBasis s (pairFirst pair)))
      (decodeMask (outsideBasis s (pairSecond pair))))
    (outsideParameters s v) hraw (fun target k => outside_annihilate s k target) target

end Lemmata.CocubicCovering.CoveringSystemSemantics
