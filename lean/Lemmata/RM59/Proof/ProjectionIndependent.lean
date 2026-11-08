module

public import Lemmata.RM59.Proof.ProjectionRref

@[expose] public section

namespace Lemmata.RM59.ProjectionIndependent

open scoped Matrix
open Lemmata.RM59.ProjectionGeometry Lemmata.RM59.ProjectionTupleChecks

abbrev F8Row := ProjectionChecks.Row
abbrev FieldPoint := TraceGeometry.FieldPoint

theorem horizontal_cross (a b : F8Row) (i j : Fin 4) :
    column a b 0 i ⨯₃ column a b 0 j = ![0, 0, pivotMinor a b i j] := by
  ext k
  fin_cases k <;> simp [column, cross_apply, pivotMinor, mul_comm]

theorem exists_nonzero_minor (a b : F8Row)
    (h : LinearIndependent Field (column a b 0)) :
    ∃ i j, pivotMinor a b i j ≠ 0 := by
  obtain ⟨f, hf⟩ := FieldRank.exists_field_independent_subfamily (column a b 0) h 2 (by decide)
  have hp : LinearIndependent F8Scalar ![column a b 0 (f 0), column a b 0 (f 1)] := by
    have he : (fun j : Fin 2 => column a b 0 (f j)) =
        ![column a b 0 (f 0), column a b 0 (f 1)] := by
      funext j
      fin_cases j <;> rfl
    rwa [he] at hf
  refine ⟨f 0, f 1, ?_⟩
  intro hz
  apply (crossProduct_ne_zero_iff_linearIndependent.mpr hp)
  rw [horizontal_cross, hz]
  ext k
  fin_cases k <;> rfl

theorem minor_plucker_a (a b : F8Row) (i j : Fin 4) :
    a 0 * pivotMinor a b i j =
      a i * pivotMinor a b 0 j - a j * pivotMinor a b 0 i := by
  unfold pivotMinor
  ring

theorem minor_plucker_b (a b : F8Row) (i j : Fin 4) :
    b 0 * pivotMinor a b i j =
      b i * pivotMinor a b 0 j - b j * pivotMinor a b 0 i := by
  unfold pivotMinor
  ring

theorem first_nonzero (a b : F8Row) (h : LinearIndependent Field (column a b 0)) :
    a 0 ≠ 0 ∨ b 0 ≠ 0 := by
  by_contra hz
  push_neg at hz
  apply h.ne_zero 0
  ext k
  fin_cases k <;> simp [column, hz.1, hz.2]

theorem exists_first_minor (a b : F8Row) (h : LinearIndependent Field (column a b 0)) :
    ∃ j, 0 < j ∧ pivotMinor a b 0 j ≠ 0 := by
  obtain ⟨i, j, hij⟩ := exists_nonzero_minor a b h
  have hex : ∃ k, pivotMinor a b 0 k ≠ 0 := by
    by_contra hn
    push_neg at hn
    rcases first_nonzero a b h with ha | hb
    · have he := minor_plucker_a a b i j
      rw [hn j, hn i, mul_zero, mul_zero, sub_self] at he
      exact hij ((mul_eq_zero.mp he).resolve_left ha)
    · have he := minor_plucker_b a b i j
      rw [hn j, hn i, mul_zero, mul_zero, sub_self] at he
      exact hij ((mul_eq_zero.mp he).resolve_left hb)
  obtain ⟨k, hk⟩ := hex
  refine ⟨k, ?_, hk⟩
  have hk0 : k ≠ 0 := by
    intro he
    subst k
    exact hk (by simp [pivotMinor])
  exact (Fin.pos_iff_ne_zero' k).mpr hk0

theorem normalization_exists (a b c : F8Row)
    (h : LinearIndependent Field (column a b 0)) :
    ∃ normal, normalizeRows a b c = some normal := by
  have hp : (List.finRange 4).find? (fun j => a j != 0 || b j != 0) = some 0 := by
    apply (ProjectionRref.find_fin4_spec _ 0).2
    refine ⟨?_, ?_⟩
    · simpa using first_nonzero a b h
    · intro j hj
      omega
  obtain ⟨j, hj, hd⟩ := exists_first_minor a b h
  obtain ⟨q, hq⟩ := ProjectionRref.find_fin4_complete
    (fun j => 0 < j && pivotMinor a b 0 j != 0) ⟨j, by simpa using And.intro hj hd⟩
  exact ⟨ProjectionTupleSound.atPivots a b c 0 q,
    ProjectionTupleSound.normalizeRows_eq_atPivots a b c 0 q hp hq⟩

def projectionMatrix (a b : F8Row) (p q : Fin 4) : TraceGeometry.FieldMatrix :=
  TraceGeometry.blockMatrix (reducer a b p q) 0

theorem projectionMatrix_det (a b : F8Row) (p q : Fin 4) (hd : pivotMinor a b p q ≠ 0) :
    (projectionMatrix a b p q).det = 1 := by
  apply TraceGeometry.blockMatrix_det_one
  rw [reducer_det a b p q hd]
  exact inv_ne_zero hd

theorem projectionMatrix_apply (a b : F8Row) (p q j : Fin 4) :
    projectionMatrix a b p q *ᵥ column a b 0 j =
      column (topRows a b p q 0) (topRows a b p q 1) 0 j := by
  ext i
  fin_cases i <;>
    simp [projectionMatrix, TraceGeometry.blockMatrix, column, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, topRows]

theorem projectionMatrix_injective (a b : F8Row) (p q : Fin 4)
    (hd : pivotMinor a b p q ≠ 0) :
    Function.Injective (TraceActions.matrixLinear (projectionMatrix a b p q)) := by
  intro x y hxy
  have hdet : (projectionMatrix a b p q).det ≠ 0 := by
    rw [projectionMatrix_det a b p q hd]
    exact one_ne_zero
  have hi := congrArg (fun z : FieldPoint => (projectionMatrix a b p q)⁻¹ *ᵥ z) hxy
  change (projectionMatrix a b p q)⁻¹ *ᵥ ((projectionMatrix a b p q) *ᵥ x) =
    (projectionMatrix a b p q)⁻¹ *ᵥ ((projectionMatrix a b p q) *ᵥ y) at hi
  simpa only [Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec] using hi

theorem normalization_independent (a b c : F8Row) (normal : NormalForm)
    (h : normalizeRows a b c = some normal)
    (hi : LinearIndependent Field (column a b 0)) :
    LinearIndependent Field (ProjectionTupleSound.projectionColumns normal.projection) := by
  obtain ⟨p, q, _, _, hd, rfl⟩ := ProjectionTupleSound.normalizeRows_sound a b c normal h
  have hm := hi.map' (TraceActions.matrixLinear (projectionMatrix a b p q))
    (LinearMap.ker_eq_bot.mpr (projectionMatrix_injective a b p q hd))
  have he : TraceActions.matrixLinear (projectionMatrix a b p q) ∘ column a b 0 =
      ProjectionTupleSound.projectionColumns
        (ProjectionTupleSound.atPivots a b c p q).projection := by
    funext j
    change projectionMatrix a b p q *ᵥ column a b 0 j = _
    rw [projectionMatrix_apply]
    simp only [ProjectionTupleSound.projectionColumns, ProjectionTupleSound.atPivots,
      projectionFromRows, Vector.getElem_ofFn, column] <;> rfl
  rwa [he] at hm

theorem normalization_covered (a b c : F8Row)
    (hi : LinearIndependent Field (column a b 0)) :
    ∃ normal, normalizeRows a b c = some normal ∧ normal.projection ∈ coveredProjections := by
  obtain ⟨normal, hn⟩ := normalization_exists a b c hi
  exact ⟨normal, hn, ProjectionTupleSound.projection_covered normal.projection
    (ProjectionRref.normalization_projection_mem a b c normal hn)
    (normalization_independent a b c normal hn hi)⟩

end Lemmata.RM59.ProjectionIndependent
