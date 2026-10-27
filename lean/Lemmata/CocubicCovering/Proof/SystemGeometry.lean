module

public import Lemmata.CocubicCovering.Proof.Geometry
public meta import Lemmata.CocubicCovering.Proof.Geometry
public import Lemmata.CocubicCovering.Proof.SystemGeometryData
public meta import Lemmata.CocubicCovering.Proof.SystemGeometryData
public import Lemmata.CocubicCovering.Proof.SystemSemantics
public meta import Lemmata.CocubicCovering.Proof.SystemSemantics

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringSystemGeometry

open Module Covering CoveringWitness CoveringGeometry CoveringSymplectic
open CoveringLevelSixSystems CoveringSystemGeometryData CoveringSystemSemantics
open LinearMap (BilinForm)
open scoped BigOperators

abbrev ResidualIndex (s : Fin 13) := Fin (crossRank s) ⊕ Fin 15

def C (s : Fin 13) (v : Vector 127) : Matrix (Fin (localRank s)) (Fin 15) Field :=
  fun i => actualCross s v (Fin.castAdd (crossRank s) i)

def Z (s : Fin 13) (v : Vector 127) : Matrix (Fin (crossRank s)) (Fin 15) Field :=
  fun i => actualCross s v (Fin.natAdd (localRank s) i)

def X (s : Fin 13) (v : Vector 127) : Matrix (Fin (localRank s)) (ResidualIndex s) Field :=
  fun i => Sum.elim 0 (C s v i)

def D (s : Fin 13) (v : Vector 127) : Matrix (ResidualIndex s) (ResidualIndex s) Field :=
  Matrix.fromBlocks 0 (Z s v) (Matrix.transpose (Z s v)) (actualOutside s v)

def residualMatrix (s : Fin 13) (v : Vector 127) :
    Matrix (ResidualIndex s) (ResidualIndex s) Field :=
  Matrix.fromBlocks 0 (Z s v) (Matrix.transpose (Z s v))
    (CoveringSchur.schur (inverseMatrix s) (C s v) (Matrix.transpose (C s v)) (actualOutside s v))

def residualForm (s : Fin 13) (v : Vector 127) : BilinForm Field (ResidualIndex s → Field) :=
  Matrix.toBilin' (residualMatrix s v)

def residualFrame (s : Fin 13) (i : Fin (crossRank s)) : ResidualIndex s → Field :=
  Pi.single (Sum.inl i) 1

def residualOutside (s : Fin 13) (i : Fin 15) : ResidualIndex s → Field :=
  Pi.single (Sum.inr i) 1

def fullVectors (s : Fin 13) : Fin (localRank s) ⊕ ResidualIndex s → Vector 27 :=
  Sum.elim (nondegenerateVector s) (Sum.elim (complementVector s) (outsideVector s))

def pullback (s : Fin 13) : (Fin (localRank s) ⊕ ResidualIndex s → Field) →ₗ[Field] Vector 27 :=
  Fintype.linearCombination Field (fullVectors s)

theorem fullForm_symmetric (v : Vector 127) (x y : Vector 27) :
    CoveringLevelSixReduction.fullForm v x y = CoveringLevelSixReduction.fullForm v y x := by
  simpa only [CharTwo.neg_eq] using (CoveringLevelSixReduction.fullForm_isAlt v).neg_eq x y

theorem pullback_block (s : Fin 13) (v : Vector 127)
    (hlocal : ∀ i : Fin 15, v ⟨111 + i.val, by omega⟩ =
      CoveringPolynomial.ofBool ((CoveringLevelSixReconstruction.restriction s).testBit i.val)) :
    gram (CoveringLevelSixReduction.fullForm v) (pullback s) =
      Matrix.toBilin' (Matrix.fromBlocks (localBlock s) (X s v) (Matrix.transpose (X s v)) (D s v)) := by
  apply (Pi.basisFun Field (Fin (localRank s) ⊕ ResidualIndex s)).ext
  intro i
  apply (Pi.basisFun Field (Fin (localRank s) ⊕ ResidualIndex s)).ext
  intro j
  simp only [Pi.basisFun_apply, gram_apply, pullback,
    Fintype.linearCombination_apply_single, one_smul, Matrix.toBilin'_single]
  cases i with
  | inl i =>
    cases j with
    | inl j => exact actual_localBlock s v hlocal i j
    | inr j =>
      cases j with
      | inl j =>
        change CoveringLevelSixReduction.fullForm v (nondegenerateVector s i) (complementVector s j) = 0
        rw [fullForm_symmetric]
        exact complement_orthogonal_W s v hlocal j _ (embed_mem_W _)
      | inr j =>
        change CoveringLevelSixReduction.fullForm v (nondegenerateVector s i) (outsideVector s j) =
          actualCross s v (Fin.castAdd (crossRank s) i) j
        rw [← native_nondegenerate]
        rfl
  | inr i =>
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change CoveringLevelSixReduction.fullForm v (complementVector s i) (nondegenerateVector s j) = 0
        exact complement_orthogonal_W s v hlocal i _ (embed_mem_W _)
      | inr j =>
        cases j with
        | inl j =>
          change CoveringLevelSixReduction.fullForm v (complementVector s i) (complementVector s j) = 0
          exact complement_orthogonal_W s v hlocal i _ (complement_mem_W s j)
        | inr j =>
          change CoveringLevelSixReduction.fullForm v (complementVector s i) (outsideVector s j) =
            actualCross s v (Fin.natAdd (localRank s) i) j
          rw [← native_complement]
          rfl
    | inr i =>
      cases j with
      | inl j =>
        change CoveringLevelSixReduction.fullForm v (outsideVector s i) (nondegenerateVector s j) =
          actualCross s v (Fin.castAdd (crossRank s) j) i
        rw [fullForm_symmetric, ← native_nondegenerate]
        rfl
      | inr j =>
        cases j with
        | inl j =>
          change CoveringLevelSixReduction.fullForm v (outsideVector s i) (complementVector s j) =
            actualCross s v (Fin.natAdd (localRank s) j) i
          rw [fullForm_symmetric, ← native_complement]
          rfl
        | inr j => rfl

theorem schur_matrix (s : Fin 13) (v : Vector 127) :
    CoveringSchur.schur (inverseMatrix s) (X s v) (Matrix.transpose (X s v)) (D s v) =
      residualMatrix s v := by
  ext i j
  cases i <;> cases j <;>
    simp [CoveringSchur.schur, residualMatrix, X, D, Matrix.mul_apply,
      Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.transpose_apply]

def rank_budget_decision (s : Fin 13) : Decidable (localRank s + 2 * pairs s = 10) :=
  inferInstance

@[noinline, never_extract]
def rank_budget_check (s : Fin 13) : Bool :=
  @decide (localRank s + 2 * pairs s = 10) (rank_budget_decision s)

theorem rank_budget_check_sound (s : Fin 13) (computed : rank_budget_check s = true) :
    localRank s + 2 * pairs s = 10 := by
  unfold rank_budget_check at computed
  exact @of_decide_eq_true (localRank s + 2 * pairs s = 10) (rank_budget_decision s) computed

theorem rank_budget (s : Fin 13) : localRank s + 2 * pairs s = 10 := by
  have computed : ∀ (s : Fin 13), rank_budget_check s = true := by native_decide
  exact rank_budget_check_sound s (computed s)

theorem residual_rank (s : Fin 13) (v : Vector 127)
    (hlocal : ∀ i : Fin 15, v ⟨111 + i.val, by omega⟩ =
      CoveringPolynomial.ofBool ((CoveringLevelSixReconstruction.restriction s).testBit i.val))
    (hrank : finrank Field (LinearMap.range (CoveringLevelSixReduction.fullForm v)) ≤ 10) :
    finrank Field (LinearMap.range (residualForm s v)) ≤ 2 * pairs s := by
  have h := schur_rank_bound (CoveringLevelSixReduction.fullForm v) (pullback s)
    (localBlock s) (inverseMatrix s) (X s v) (Matrix.transpose (X s v)) (D s v)
    (pullback_block s v hlocal) (inverse_left s) (inverse_right s)
  rw [schur_matrix, Fintype.card_fin] at h
  have hbudget := rank_budget s
  rw [residualForm, matrix_bilinear_rank]
  omega

theorem residual_isAlt (s : Fin 13) (v : Vector 127)
    (hlocal : ∀ i : Fin 15, v ⟨111 + i.val, by omega⟩ =
      CoveringPolynomial.ofBool ((CoveringLevelSixReconstruction.restriction s).testBit i.val)) :
    (residualForm s v).IsAlt := by
  have hfull := gram_isAlt (CoveringLevelSixReduction.fullForm v)
    (CoveringLevelSixReduction.fullForm_isAlt v) (pullback s)
  rw [pullback_block s v hlocal] at hfull
  have h := schur_isAlt (localBlock s) (inverseMatrix s) (X s v)
    (Matrix.transpose (X s v)) (D s v) (inverse_right s) hfull
  rwa [schur_matrix] at h

theorem residual_frame_isotropic (s : Fin 13) (v : Vector 127)
    (i j : Fin (crossRank s)) : residualForm s v (residualFrame s i) (residualFrame s j) = 0 := by
  simp [residualForm, residualFrame, residualMatrix, Matrix.fromBlocks]

theorem residual_pairing (s : Fin 13) (v : Vector 127)
    (i : Fin (crossRank s)) (j : Fin 15) :
    residualForm s v (residualFrame s i) (residualOutside s j) =
      CoveringLevelSixReduction.fullForm v (complementVector s i) (outsideVector s j) := by
  simp only [residualForm, residualFrame, residualOutside, Matrix.toBilin'_single]
  change actualCross s v (Fin.natAdd (localRank s) i) j = _
  rw [← native_complement]
  rfl

theorem residual_frame_injective (s : Fin 13) (v : Vector 127)
    (hlocal : ∀ i : Fin 15, v ⟨111 + i.val, by omega⟩ =
      CoveringPolynomial.ofBool ((CoveringLevelSixReconstruction.restriction s).testBit i.val))
    (hcore : W ⊓ LinearMap.ker (CoveringLevelSixReduction.fullForm v) = coreSpace s) :
    Function.Injective (LinearMap.comp (residualForm s v)
      (Fintype.linearCombination Field (residualFrame s))) := by
  have hinjective := frame_functionals_injective (CoveringLevelSixReduction.fullForm v)
    W (coreSpace s) (complementVector s) (complement_mem_W s) hcore
    (complement_disjoint_core s) (complement_injective s)
  have hcross := crossPairing_injective (CoveringLevelSixReduction.fullForm v) W
    (complementVector s) (outsideVector s) (W_outside_spanning s)
    (complement_orthogonal_W s v hlocal) hinjective
  apply frame_functionals_injective_of_cross (residualForm s v)
    (residualFrame s) (residualOutside s)
  rwa [crossPairing_eq_of_pairings (CoveringLevelSixReduction.fullForm v) (residualForm s v)
    (complementVector s) (residualFrame s) (outsideVector s) (residualOutside s)
    (residual_pairing s v)]

theorem exists_gram_points (s : Fin 13) (v : Vector 127)
    (hlocal : ∀ i : Fin 15, v ⟨111 + i.val, by omega⟩ =
      CoveringPolynomial.ofBool ((CoveringLevelSixReconstruction.restriction s).testBit i.val))
    (hcore : W ⊓ LinearMap.ker (CoveringLevelSixReduction.fullForm v) = coreSpace s)
    (hrank : finrank Field (LinearMap.range (CoveringLevelSixReduction.fullForm v)) ≤ 10) :
    ∃ points : Fin 15 → Standard Field (pairs s),
      (∀ (i : Fin (crossRank s)) (j : Fin 15),
        (points j).2 (Fin.castLE (crossRank_le_pairs s) i) =
          actualCross s v (Fin.natAdd (localRank s) i) j) ∧
      ∀ i j : Fin 15, standardBilin (pairs s) (points i) (points j) =
        CoveringSchur.schur (inverseMatrix s) (C s v) (Matrix.transpose (C s v)) (actualOutside s v) i j := by
  obtain ⟨L, hgram, hframe⟩ := exists_gram_map_with_frame (pairs s) (residualForm s v)
    (residual_isAlt s v hlocal) (residual_rank s v hlocal hrank) (residualFrame s)
    (residual_frame_isotropic s v) (residual_frame_injective s v hlocal hcore) (crossRank_le_pairs s)
  refine ⟨fun j => L (residualOutside s j), ?_, ?_⟩
  · intro i j
    rw [gram_map_frame_coordinate (residualForm s v) L (residualFrame s)
      hgram hframe (crossRank_le_pairs s) i, residual_pairing]
    rw [← native_complement]
    rfl
  · intro i j
    rw [hgram]
    simp [residualForm, residualOutside, residualMatrix, Matrix.fromBlocks]

theorem constraints_of_core (s : Fin 13) (v : Vector 127)
    (hpoint : v (Fin.last 126) = 1)
    (hlocal : ∀ i : Fin 15, v ⟨111 + i.val, by omega⟩ =
      CoveringPolynomial.ofBool ((CoveringLevelSixReconstruction.restriction s).testBit i.val))
    (hcore : W ⊓ LinearMap.ker (CoveringLevelSixReduction.fullForm v) = coreSpace s) :
    ∀ k, CoveringAffine.evalRow (CoveringLevelSixReconstruction.constraints s k) v = 0 := by
  apply CoveringLevelSixReconstruction.constraints_vanish_of_local_and_kernel s v hpoint hlocal
  intro q hq
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hq
  rw [← hi]
  change CoveringLevelSixReduction.fullForm v (coreVector s i) = 0
  have hmem : coreVector s i ∈ coreSpace s := Submodule.subset_span ⟨i, rfl⟩
  rw [← hcore] at hmem
  exact hmem.2

theorem exists_input_solution (s : Fin 13) (v : Vector 127)
    (hpoint : v (Fin.last 126) = 1)
    (hlocal : ∀ i : Fin 15, v ⟨111 + i.val, by omega⟩ =
      CoveringPolynomial.ofBool ((CoveringLevelSixReconstruction.restriction s).testBit i.val))
    (hcore : W ⊓ LinearMap.ker (CoveringLevelSixReduction.fullForm v) = coreSpace s)
    (hrank : finrank Field (LinearMap.range (CoveringLevelSixReduction.fullForm v)) ≤ 10) :
    ∃ assignment : ℕ → Field, ∀ row : Fin 87,
      CoveringIdeal.eval assignment (input s row) = 0 := by
  obtain ⟨points, hforced, hgram⟩ := exists_gram_points s v hlocal hcore hrank
  exact exists_input_solution_of_gram s v hpoint (constraints_of_core s v hpoint hlocal hcore)
    points hforced hgram

end Lemmata.CocubicCovering.CoveringSystemGeometry
