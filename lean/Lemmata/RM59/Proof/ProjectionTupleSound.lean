module

public import Lemmata.RM59.Proof.ProjectionTupleChecks
public import Lemmata.RM59.Proof.ProjectionEquivalence
public meta import Lemmata.RM59.Proof.ProjectionTupleChecks
public meta import Lemmata.RM59.Proof.Model
public meta import Lemmata.RM59.Proof.F8

@[expose] public section

namespace Lemmata.RM59.ProjectionTupleSound

open scoped BigOperators Matrix
open Lemmata.RM59.ProjectionGeometry
open Lemmata.RM59.ProjectionTupleChecks

abbrev F8Row := ProjectionChecks.Row
abbrev FieldPoint := TraceGeometry.FieldPoint

def atPivots (a b c : F8Row) (p q : Fin 4) : NormalForm := {
  projection := projectionFromRows p q
    (Vector.ofFn (topRows a b p q 0)) (Vector.ofFn (topRows a b p q 1))
  lift := (residual a b c p q (freeColumn p q 0), residual a b c p q (freeColumn p q 1)) }

theorem normalizeRows_eq_atPivots (a b c : F8Row) (p q : Fin 4)
    (hp : (List.finRange 4).find? (fun j => a j != 0 || b j != 0) = some p)
    (hq : (List.finRange 4).find? (fun j => p < j && pivotMinor a b p j != 0) = some q) :
    normalizeRows a b c = some (atPivots a b c p q) := by
  simp [normalizeRows, hp, hq, atPivots, topRows, residual] <;> rfl

theorem normalizeRows_sound (a b c : F8Row) (normal : NormalForm)
    (h : normalizeRows a b c = some normal) :
    ∃ p q : Fin 4,
      (List.finRange 4).find? (fun j => a j != 0 || b j != 0) = some p ∧
      (List.finRange 4).find? (fun j => p < j && pivotMinor a b p j != 0) = some q ∧
      pivotMinor a b p q ≠ 0 ∧ normal = atPivots a b c p q := by
  cases hp : (List.finRange 4).find? (fun j => a j != 0 || b j != 0) with
  | none => simp [normalizeRows, hp] at h
  | some p =>
    cases hq : (List.finRange 4).find?
        (fun j => p < j && pivotMinor a b p j != 0) with
    | none => simp [normalizeRows, hp, hq] at h
    | some q =>
      have hpred : p < q ∧ pivotMinor a b p q ≠ 0 := by
        simpa using List.find?_some hq
      refine ⟨p, q, rfl, hq, hpred.2, ?_⟩
      exact Option.some.inj (h.symm.trans (normalizeRows_eq_atPivots a b c p q hp hq))

theorem freeColumn_cover : ∀ p q j : Fin 4, p ≠ q →
    j = p ∨ j = q ∨ j = freeColumn p q 0 ∨ j = freeColumn p q 1 := by decide

theorem equal_atPivots (a b c a' b' c' : F8Row) (p q p' q' : Fin 4)
    (hd : pivotMinor a b p q ≠ 0) (hd' : pivotMinor a' b' p' q' ≠ 0)
    (he : atPivots a b c p q = atPivots a' b' c' p' q') :
    ProjectionEquivalence.normalizedColumns a b c p q =
      ProjectionEquivalence.normalizedColumns a' b' c' p' q' := by
  have hpp : p = p' := congrArg (fun n : NormalForm => n.projection.pivot0) he
  have hqq : q = q' := congrArg (fun n : NormalForm => n.projection.pivot1) he
  subst p'
  subst q'
  have hv0 : Vector.ofFn (topRows a b p q 0) = Vector.ofFn (topRows a' b' p q 0) :=
    congrArg (fun n : NormalForm => n.projection.row0) he
  have hv1 : Vector.ofFn (topRows a b p q 1) = Vector.ofFn (topRows a' b' p q 1) :=
    congrArg (fun n : NormalForm => n.projection.row1) he
  have h0 (j : Fin 4) : topRows a b p q 0 j = topRows a' b' p q 0 j := by
    simpa only [Vector.getElem_ofFn] using
      congrArg (fun r : StoredRow => r[j.val]) hv0
  have h1 (j : Fin 4) : topRows a b p q 1 j = topRows a' b' p q 1 j := by
    simpa only [Vector.getElem_ofFn] using
      congrArg (fun r : StoredRow => r[j.val]) hv1
  have hz0 : residual a b c p q (freeColumn p q 0) =
      residual a' b' c' p q (freeColumn p q 0) := congrArg (fun n : NormalForm => n.lift.1) he
  have hz1 : residual a b c p q (freeColumn p q 1) =
      residual a' b' c' p q (freeColumn p q 1) := congrArg (fun n : NormalForm => n.lift.2) he
  have hpq : p ≠ q := by
    intro hpq
    subst q
    exact hd (by simp [pivotMinor])
  have hz (j : Fin 4) : residual a b c p q j = residual a' b' c' p q j := by
    obtain ⟨hzp, hzq⟩ := residual_pivots a b c p q hd
    obtain ⟨hzp', hzq'⟩ := residual_pivots a' b' c' p q hd'
    rcases freeColumn_cover p q j hpq with rfl | rfl | rfl | rfl
    · rw [hzp, hzp']
    · rw [hzq, hzq']
    · exact hz0
    · exact hz1
  funext j
  simp only [ProjectionEquivalence.normalizedColumns, column, h0 j, h1 j, hz j]

theorem same_result_equivalence (a b c a' b' c' : F8Row) (normal : NormalForm)
    (h : normalizeRows a b c = some normal) (h' : normalizeRows a' b' c' = some normal) :
    ∃ A : TraceGeometry.FieldMatrix, A.det = 1 ∧
      (fun x => A *ᵥ x) '' TraceGeometry.verticalSpace = TraceGeometry.verticalSpace ∧
      ∀ j, A *ᵥ column a b c j = column a' b' c' j := by
  obtain ⟨p, q, _, _, hd, he⟩ := normalizeRows_sound a b c normal h
  obtain ⟨p', q', _, _, hd', he'⟩ := normalizeRows_sound a' b' c' normal h'
  exact ProjectionEquivalence.equal_normalized_columns a b c a' b' c' p q p' q' hd hd'
    (equal_atPivots a b c a' b' c' p q p' q' hd hd' (he.symm.trans he'))

def projectionColumns (p : Projection) : Fin 4 → FieldPoint :=
  fun j => ![p.row0[j.val], p.row1[j.val], 0]

def linearTest (p : Projection) : Bool :=
  decide (∀ c : Fin 4 → Field,
    (∑ i, if c i = 1 then projectionColumns p i else 0) = 0 → ∀ i, c i = 0)

theorem scalar_smul (r : Field) (x : FieldPoint) : r • x = if r = 1 then x else 0 := by
  rcases field_eq_zero_or_one r with rfl | rfl <;> simp

theorem linearTest_iff (p : Projection) :
    linearTest p = true ↔ LinearIndependent Field (projectionColumns p) := by
  simp only [linearTest, decide_eq_true_eq, Fintype.linearIndependent_iff, scalar_smul]

theorem linear_independence_checked : ∀ p ∈ allReducedProjections,
    independentProjection p = linearTest p := by native_decide

theorem independentProjection_iff_of_mem (p : Projection) (hp : p ∈ allReducedProjections) :
    independentProjection p = true ↔ LinearIndependent Field (projectionColumns p) := by
  rw [linear_independence_checked p hp]
  exact linearTest_iff p

theorem contains_iff_mem {α : Type*} [DecidableEq α] (values : List α) (value : α) :
    contains values value = true ↔ value ∈ values := by
  simp [contains]

theorem projection_covered (p : Projection) (hp : p ∈ allReducedProjections)
    (hindependent : LinearIndependent Field (projectionColumns p)) : p ∈ coveredProjections := by
  have hi := (independentProjection_iff_of_mem p hp).2 hindependent
  have hc := List.all_eq_true.mp projection_coverage_checked p hp
  apply (contains_iff_mem _ _).1
  simpa only [hi, Bool.not_true, Bool.false_or] using hc

end Lemmata.RM59.ProjectionTupleSound
