module

public import Lemmata.RM59.Proof.ProjectionGeometry
public meta import Lemmata.RM59.Proof.ProjectionGeometry
public meta import Lemmata.RM59.Proof.ProjectionChecks
public meta import Lemmata.RM59.Proof.CertificateData
public meta import Lemmata.RM59.Proof.F8

@[expose] public section

namespace Lemmata.RM59.ProjectionTupleChecks

abbrev Row := ProjectionChecks.Row
abbrev StoredRow := Vector F8Scalar 4
abbrev Lift := F8Scalar × F8Scalar

/-- The fingerprint accelerates equality; the stored rows are also compared. -/
structure Projection where
  fingerprint : Nat
  pivot0 : Fin 4
  pivot1 : Fin 4
  row0 : StoredRow
  row1 : StoredRow
  deriving DecidableEq, Repr

structure NormalForm where
  projection : Projection
  lift : Lift
  deriving DecidableEq, Repr

def rowFunction (row : StoredRow) : Row := fun i => row[i.val]

def projectionFromRows (p q : Fin 4) (r0 r1 : StoredRow) : Projection := {
  fingerprint := ProjectionChecks.rowKey (rowFunction r0) (rowFunction r1)
  pivot0 := p
  pivot1 := q
  row0 := r0
  row1 := r1 }

def contains {α : Type*} [DecidableEq α] (values : List α) (value : α) : Bool :=
  values.any fun x => decide (x = value)

def freeColumns (p q : Fin 4) : List (Fin 4) :=
  (List.finRange 4).filter fun j => j != p && j != q

def freeColumn (p q : Fin 4) (i : Fin 2) : Fin 4 := (freeColumns p q)[i.val]?.getD 0

def normalizeRows (a b c : Row) : Option NormalForm := do
  let p ← (List.finRange 4).find? fun j => a j != 0 || b j != 0
  let q ← (List.finRange 4).find? fun j =>
    p < j && ProjectionGeometry.pivotMinor a b p j != 0
  let delta := ProjectionGeometry.pivotMinor a b p q
  let D := ProjectionGeometry.reducer a b p q
  let r0 := Vector.ofFn fun j : Fin 4 => D 0 0 * a j + D 0 1 * b j
  let r1 := Vector.ofFn fun j : Fin 4 => D 1 0 * a j + D 1 1 * b j
  let z := fun j => delta * c j - delta * c p * r0[j.val] - delta * c q * r1[j.val]
  let projection := projectionFromRows p q r0 r1
  return ⟨projection, (z (freeColumn p q 0), z (freeColumn p q 1))⟩

def normalizeFive (points : List (Fin 512)) : Option NormalForm :=
  let center := points.foldl ProjectionChecks.xorPoint 0
  let rows : Fin 3 → Row := fun i j =>
    FieldData.coordinates
      (ProjectionChecks.xorPoint (points[j.val]?.getD 0) center) i
  normalizeRows (rows 0) (rows 1) (rows 2)

def representativeProjection (entry : List (Fin 8) × List (Fin 8)) : Option Projection :=
  let (a, b) := ProjectionChecks.projectionRows entry
  (normalizeRows a b 0).map NormalForm.projection

def coveredProjections : List Projection :=
  Certificate.projections.toList.flatMap fun entry =>
    (List.finRange 5).permutations.flatMap fun order =>
      (List.range 3).filterMap fun power =>
        (normalizeFive (order.map fun j => ProjectionChecks.frobeniusPoint
          ((ProjectionChecks.projectionPoints entry)[j.val]?.getD 0) power)).map
            NormalForm.projection

def elements : List F8Scalar := (List.finRange 8).map fun a => ⟨a⟩

def scalarPairs : List Lift :=
  elements.flatMap fun a => elements.map fun b => (a, b)

def scalarTriples : List (F8Scalar × F8Scalar × F8Scalar) :=
  elements.flatMap fun a => scalarPairs.map fun bc => (a, bc)

def scalarQuadruples : List (Lift × Lift) :=
  scalarPairs.flatMap fun ab => scalarPairs.map fun cd => (ab, cd)

def allReducedProjections : List Projection :=
  (scalarQuadruples.map fun x =>
    projectionFromRows 0 1 #v[1, 0, x.1.1, x.1.2] #v[0, 1, x.2.1, x.2.2]) ++
  (scalarTriples.map fun x =>
    projectionFromRows 0 2 #v[1, x.1, 0, x.2.1] #v[0, 0, 1, x.2.2]) ++
  (scalarPairs.map fun x =>
    projectionFromRows 0 3 #v[1, x.1, x.2, 0] #v[0, 0, 0, 1]) ++
  (scalarPairs.map fun x =>
    projectionFromRows 1 2 #v[0, 1, 0, x.1] #v[0, 0, 1, x.2]) ++
  (elements.map fun x =>
    projectionFromRows 1 3 #v[0, 1, x, 0] #v[0, 0, 0, 1]) ++
  [projectionFromRows 2 3 #v[0, 0, 1, 0] #v[0, 0, 0, 1]]

def independentProjection (p : Projection) : Bool :=
  ProjectionChecks.independentFour (rowFunction p.row0) (rowFunction p.row1)

def projectionCoverage : Bool :=
  let covered := coveredProjections
  allReducedProjections.all fun p => !independentProjection p || contains covered p

def allLifts : List Lift := scalarPairs

def liftImages (projection : Nat) : List (Option NormalForm) :=
  (Certificate.lifts.toList.filter fun entry => entry.1 == projection).flatMap fun entry =>
    (List.range 32).map fun mask => normalizeFive (ProjectionChecks.liftPoints entry.2 mask)

def liftCoverage : Bool :=
  Certificate.projections.toList.zipIdx |>.all fun entry =>
    match representativeProjection entry.1 with
    | none => false
    | some projection =>
      let values := liftImages entry.2
      values.all (fun value => match value with
        | none => false
        | some normal => decide (normal.projection = projection)) &&
        allLifts.all (fun lift => contains values (some ⟨projection, lift⟩))

theorem reduced_rows_count : allReducedProjections.length = 4745 := by native_decide

theorem admissible_rows_count :
    (allReducedProjections.filter independentProjection).length = 3720 := by native_decide

theorem projection_coverage_checked : projectionCoverage = true := by native_decide

theorem allLifts_count : allLifts.length = 64 := by decide

theorem elements_complete : ∀ a : F8Scalar, a ∈ elements := by decide

theorem scalarPairs_complete (x : Lift) : x ∈ scalarPairs := by
  rcases x with ⟨a, b⟩
  exact List.mem_flatMap.mpr ⟨a, elements_complete a,
    List.mem_map.mpr ⟨b, elements_complete b, rfl⟩⟩

theorem scalarTriples_complete (x : F8Scalar × F8Scalar × F8Scalar) : x ∈ scalarTriples := by
  rcases x with ⟨a, bc⟩
  exact List.mem_flatMap.mpr ⟨a, elements_complete a,
    List.mem_map.mpr ⟨bc, scalarPairs_complete bc, rfl⟩⟩

theorem scalarQuadruples_complete (x : Lift × Lift) : x ∈ scalarQuadruples := by
  rcases x with ⟨ab, cd⟩
  exact List.mem_flatMap.mpr ⟨ab, scalarPairs_complete ab,
    List.mem_map.mpr ⟨cd, scalarPairs_complete cd, rfl⟩⟩

theorem allLifts_complete (lift : Lift) : lift ∈ allLifts := scalarPairs_complete lift

theorem lift_coverage_checked : liftCoverage = true := by native_decide

end Lemmata.RM59.ProjectionTupleChecks
