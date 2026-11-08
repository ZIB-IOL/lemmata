module

public import Lemmata.RM59.Proof.ProjectionTupleChecks
public import Std.Data.HashMap
public meta import Lemmata.RM59.Proof.ProjectionTupleChecks
public meta import Std.Data.HashMap

@[expose] public section

namespace Lemmata.RM59.ProjectionWitnessChecks

open Lemmata.RM59.ProjectionTupleChecks

structure Witness where
  codes : Vector (Fin 512) 5
  power : Fin 3
  deriving DecidableEq

def witnessNormal (w : Witness) : Option NormalForm :=
  normalizeFive (w.codes.toList.map fun x => ProjectionChecks.frobeniusPoint x w.power.val)

def validWitness (normal : NormalForm) (w : Witness) : Bool :=
  decide ((∀ i : Fin 5, w.codes.get i ∈ FieldData.support53) ∧ witnessNormal w = some normal)

instance : BEq NormalForm := ⟨fun x y => decide (x = y)⟩

instance : Hashable NormalForm where
  hash n := hash (n.projection.fingerprint, n.projection.pivot0.val,
    n.projection.pivot1.val, n.lift.1.code.val, n.lift.2.code.val)

def rawLiftCodes (certificate : List Nat) (mask : Nat) : Vector (Fin 512) 5 :=
  Vector.ofFn fun j =>
    let fiber := ProjectionChecks.fibers[certificate[j.val + 1]?.getD 0]?.getD []
    fiber[if mask.testBit j.val then 1 else 0]?.getD 0

/-- Search uses hashes; every returned value is checked independently below. -/
def witnessIndex : Std.HashMap NormalForm Witness := Id.run do
  let orders := (List.finRange 5).permutations
  let mut index : Std.HashMap NormalForm Witness := {}
  for entry in Certificate.lifts.toList do
    for mask in List.range 32 do
      let codes := rawLiftCodes entry.2 mask
      for order in orders do
        let ordered := Vector.ofFn fun j : Fin 5 => codes.get (order[j.val]?.getD 0)
        for power in List.finRange 3 do
          let witness : Witness := ⟨ordered, power⟩
          match witnessNormal witness with
          | none => pure ()
          | some normal => index := index.insert normal witness
  return index

def coverage : Bool :=
  let index := witnessIndex
  allReducedProjections.all fun p => !independentProjection p ||
    allLifts.all fun lift =>
      match index.get? ⟨p, lift⟩ with
      | none => false
      | some witness => validWitness ⟨p, lift⟩ witness

theorem coverage_checked : coverage = true := by native_decide

theorem witness_exists (p : Projection) (hp : p ∈ allReducedProjections)
    (hi : independentProjection p = true) (lift : Lift) :
    ∃ w : Witness, (∀ i : Fin 5, w.codes.get i ∈ FieldData.support53) ∧
      witnessNormal w = some ⟨p, lift⟩ := by
  have hc := List.all_eq_true.mp coverage_checked p hp
  simp only [hi, Bool.not_true, Bool.false_or] at hc
  have hl := List.all_eq_true.mp hc lift (allLifts_complete lift)
  cases hw : witnessIndex.get? ⟨p, lift⟩ with
  | none => simp only [hw, Bool.false_eq_true] at hl
  | some w =>
    refine ⟨w, ?_⟩
    simpa only [hw, validWitness, decide_eq_true_eq] using hl

end Lemmata.RM59.ProjectionWitnessChecks
