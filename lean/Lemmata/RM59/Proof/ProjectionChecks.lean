module

public import Lemmata.RM59.Proof.FieldData
public import Lemmata.RM59.Proof.CertificateData
public meta import Lemmata.RM59.Proof.FieldData
public meta import Lemmata.RM59.Proof.CertificateData

@[expose] public section

namespace Lemmata.RM59.ProjectionChecks

abbrev Row := Fin 4 → F8Scalar

def rowKey (a b : Row) : Nat :=
  (List.finRange 4).foldl (fun key j =>
    key + (a j).code.val * 8 ^ j.val + (b j).code.val * 8 ^ (4 + j.val)) 0

def normalizeRows (a b c : Row) : Option (Nat × Nat) := do
  let p ← (List.finRange 4).find? fun j => a j != 0 || b j != 0
  let q ← (List.finRange 4).find? fun j =>
    p < j && a p * b j - a j * b p != 0
  let delta := a p * b q - a q * b p
  let r0 : Row := fun j => delta⁻¹ * (b q * a j - a q * b j)
  let r1 : Row := fun j => delta⁻¹ * (b p * a j - a p * b j)
  let scaled : Row := fun j => delta * c j
  let free := (List.finRange 4).filter fun j => j != p && j != q
  let lift := (free.zipIdx).foldl (fun key ji =>
    key + (scaled ji.1 - scaled p * r0 ji.1 - scaled q * r1 ji.1).code.val *
      8 ^ ji.2) 0
  return (rowKey r0 r1, lift)

def packPoint (a b c : F8Scalar) : Fin 512 :=
  ⟨(a.code.val + 8 * b.code.val + 64 * c.code.val) % 512,
    Nat.mod_lt _ (by decide)⟩

def xorPoint (x y : Fin 512) : Fin 512 :=
  ⟨(Nat.xor x.val y.val) % 512, Nat.mod_lt _ (by decide)⟩

def frobeniusPoint (x : Fin 512) (power : Nat) : Fin 512 :=
  let v := FieldData.coordinates x
  packPoint (v 0 ^ (2 ^ power)) (v 1 ^ (2 ^ power)) (v 2 ^ (2 ^ power))

def normalizeFive (points : List (Fin 512)) : Option (Nat × Nat) :=
  let center := points.foldl xorPoint 0
  let rows : Fin 3 → Row := fun i j =>
    FieldData.coordinates (xorPoint (points[j.val]?.getD 0) center) i
  normalizeRows (rows 0) (rows 1) (rows 2)

def projectionRows (entry : List (Fin 8) × List (Fin 8)) : Row × Row :=
  (fun j => ⟨entry.1[j.val]?.getD 0⟩,
   fun j => ⟨entry.2[j.val]?.getD 0⟩)

def projectionKey (entry : List (Fin 8) × List (Fin 8)) : Option Nat :=
  let (a, b) := projectionRows entry
  (normalizeRows a b 0).map Prod.fst

def projectionPoints (entry : List (Fin 8) × List (Fin 8)) : List (Fin 512) :=
  let (a, b) := projectionRows entry
  let points := (List.finRange 4).map fun j => packPoint (a j) (b j) 0
  points ++ [points.foldl xorPoint 0]

def coveredProjections : List Nat :=
  Certificate.projections.toList.flatMap fun entry =>
    (List.finRange 5).permutations.flatMap fun order =>
      (List.range 3).filterMap fun power =>
        (normalizeFive (order.map fun j =>
          frobeniusPoint ((projectionPoints entry)[j.val]?.getD 0) power)).map Prod.fst

def independentFour (a b : Row) : Bool :=
  (List.range 16).all fun mask =>
    mask == 0 ||
      ((List.finRange 4).foldl (fun v j =>
        if mask.testBit j.val then xorPoint v (packPoint (a j) (b j) 0) else v) 0 != 0)

def freeEntries (p q : Fin 4) : List (Fin 2 × Fin 4) :=
  ((List.finRange 4).filterMap fun j => if p < j && j != q then some (0, j) else none) ++
  ((List.finRange 4).filterMap fun j => if q < j then some (1, j) else none)

def reducedRows (p q : Fin 4) (code : Nat) : Row × Row :=
  let entries := freeEntries p q
  let matrix : Fin 2 → Row := fun i j =>
    if i = 0 && j = p || i = 1 && j = q then 1 else
      (entries.zipIdx).foldl (fun value cell =>
        if cell.1 = (i, j) then F8Scalar.ofNat (code / 8 ^ cell.2) else value) 0
  (matrix 0, matrix 1)

def allReducedRows : List (Row × Row) :=
  (List.finRange 4).flatMap fun p =>
    ((List.finRange 4).filter fun q => p < q).flatMap fun q =>
      (List.range (8 ^ (freeEntries p q).length)).map fun code => reducedRows p q code

def projectionCoverage : Bool :=
  let covered := coveredProjections
  allReducedRows.all fun rows =>
    !independentFour rows.1 rows.2 ||
      match normalizeRows rows.1 rows.2 0 with
      | none => false
      | some normal => covered.contains normal.1

def fibers : List (List (Fin 512)) :=
  let sorted := FieldData.support53.mergeSort (fun x y => x.val ≤ y.val)
  ((List.range 64).filterMap fun ab =>
    let points := sorted.filter fun x => 8 * (x.val % 8) + (x.val / 8) % 8 == ab
    if points.isEmpty then none else some points)

def liftPoints (certificate : List Nat) (mask : Nat) : List (Fin 512) :=
  (List.range 5).map fun j =>
    let fiber := fibers[certificate[j + 1]?.getD 0]?.getD []
    frobeniusPoint (fiber[if mask.testBit j then 1 else 0]?.getD 0)
      (certificate[0]?.getD 0)

def liftImages (projection : Nat) : List (Option (Nat × Nat)) :=
  (Certificate.lifts.toList.filter fun entry => entry.1 == projection).flatMap fun entry =>
    (List.range 32).map fun mask => normalizeFive (liftPoints entry.2 mask)

def liftCoverage : Bool :=
  Certificate.projections.toList.zipIdx |>.all fun entry =>
    match projectionKey entry.1 with
    | none => false
    | some key =>
      let values := liftImages entry.2
      values.all (fun value => match value with
        | none => false
        | some result => result.1 == key && result.2 < 64) &&
      (List.range 64).all (fun value => values.contains (some (key, value)))

theorem reduced_rows_count : allReducedRows.length = 4745 := by native_decide

theorem admissible_rows_count :
    (allReducedRows.filter fun rows => independentFour rows.1 rows.2).length = 3720 := by
  native_decide

theorem projection_coverage_checked : projectionCoverage = true := by native_decide

theorem fibers_checked : fibers.length = 16 ∧ ∀ fiber ∈ fibers, fiber.length = 2 := by
  native_decide

theorem lift_certificates_checked : ∀ entry ∈ Certificate.lifts.toList,
    entry.1 < 15 ∧ entry.2.length = 6 ∧ entry.2[0]?.getD 0 < 3 ∧
    (entry.2.drop 1).Nodup ∧ ∀ i ∈ entry.2.drop 1, i < 16 := by native_decide

theorem lift_coverage_checked : liftCoverage = true := by native_decide

end Lemmata.RM59.ProjectionChecks
