module

public import Lemmata.RM59.Proof.FlagActions
public import Std.Data.HashMap
public meta import Lemmata.RM59.Proof.FlagActions
public meta import Std.Data.HashMap

@[expose] public section

namespace Lemmata.RM59.FlagWitnessChecks

open Lemmata.RM59.Packed Lemmata.RM59.FlagActions

def basePoint (which : Fin 2) : PackedPoint := if which.val = 0 then 2 else 16

def pointAllowed (which : Fin 2) (x : PackedPoint) : Bool :=
  if which.val = 0 then x.val.testBit 1 else
    !x.val.testBit 1 && Nat.land x.val 338 != 0

def inverseIndex (i : Fin 12) : Fin 12 :=
  ⟨(i.val + 6) % 12, Nat.mod_lt _ (by decide)⟩

def inverseWord (word : Word) : Word := word.reverse.map inverseIndex

def findPointWords (which : Fin 2) : Array (Option Word) := Id.run do
  let start := basePoint which
  let mut words : Array (Option Word) := (Array.replicate 512 none).set! start.val (some [])
  let mut queue := #[start]
  for pos in List.range 512 do
    if let some x := queue[pos]? then
      let word := (words[x.val]?.getD none).getD []
      for i in [0, 1, 2] do
        let y := packed i x
        if (words[y.val]?.getD none).isNone then
          words := words.set! y.val (some (i :: word))
          queue := queue.push y
  return words

def pointTables : Vector (Array (Option Word)) 2 := Vector.ofFn findPointWords

def pointWord (which : Fin 2) (x : PackedPoint) : Option Word :=
  ((pointTables.get which)[x.val]?.getD none).map inverseWord

def pointCheck (which : Fin 2) (x : PackedPoint) : Bool :=
  match pointWord which x with
  | none => false
  | some word => wordPacked word x == basePoint which

theorem point_coverage_checked : ∀ (which : Fin 2) (x : PackedPoint),
    pointAllowed which x = true → pointCheck which x = true := by native_decide

def clear (which : Fin 2) (x : PackedPoint) : PackedPoint :=
  ⟨Nat.land x.val (if which.val = 0 then 509 else 495) % 512,
    Nat.mod_lt _ (by decide)⟩

def allowed (which : Fin 2) (a b : PackedPoint) : Bool :=
  a != 0 && b != 0 && a != b &&
    Nat.land (Nat.lor a.val b.val) (basePoint which).val == 0 &&
    Nat.land (Nat.lor a.val b.val) 2 == 0 &&
    (which.val == 0 ||
      (Nat.land a.val 506 != 0 && Nat.land b.val 506 != 0 &&
        Nat.land (xorPoint a b).val 506 != 0))

abbrev PlaneKey := PackedPoint × PackedPoint

def planeKey (a b : PackedPoint) : PlaneKey :=
  let c := xorPoint a b
  let first := min a (min b c)
  let second := if first = a then min b c else if first = b then min a c else min a b
  (first, second)

def canonicalQuad (which : Fin 2) (a b : PackedPoint) : Finset PackedPoint :=
  {0, a, b, xorPoint (xorPoint a b) (basePoint which)}

structure Witness where
  codes : Vector PackedPoint 4
  word : Word
  shift : PackedPoint

def images (codes : Vector PackedPoint 4) (word : Word) : List PackedPoint :=
  codes.toList.map (wordPacked word)

def shiftedImages (w : Witness) : Finset PackedPoint :=
  ((images w.codes w.word).map fun x => xorPoint x w.shift).toFinset

def findShift (which : Fin 2) (a b : PackedPoint) (codes : Vector PackedPoint 4)
    (word : Word) : PackedPoint :=
  let points := images codes word
  let target := canonicalQuad which a b
  (points.find? fun shift => decide
    ((points.map fun x => xorPoint x shift).toFinset = target)).getD 0

def makeWitness (which : Fin 2) (a b : PackedPoint) (codes : Vector PackedPoint 4)
    (word : Word) : Witness := ⟨codes, word, findShift which a b codes word⟩

def validWitness (which : Fin 2) (a b : PackedPoint) (w : Witness) : Bool :=
  decide ((∀ i : Fin 4, w.codes.get i ∈ Certificate.seed 49) ∧
    shiftedImages w = canonicalQuad which a b)

def sourceQuads : List (Vector PackedPoint 4) :=
  (List.range 30).flatMap fun i => (List.range i).flatMap fun j =>
    (List.range j).flatMap fun k => (List.range k).map fun l =>
      #v[(Certificate.seed 49)[i]?.getD 0, (Certificate.seed 49)[j]?.getD 0,
        (Certificate.seed 49)[k]?.getD 0, (Certificate.seed 49)[l]?.getD 0]

def planeMoves (which : Fin 2) : List (Fin 12) :=
  if which.val = 0 then [3, 4] else [5]

/-- The index is untrusted; coverage checks the complete returned witness. -/
def findPlaneIndex (which : Fin 2) : Std.HashMap PlaneKey Witness := Id.run do
  let mut index : Std.HashMap PlaneKey Witness := {}
  let mut queue : Array PlaneKey := #[]
  for codes in sourceQuads do
    let t := codes.toList.foldl xorPoint 0
    if let some word := pointWord which t then
      let a := clear which (xorPoint (wordPacked word (codes.get 0))
        (wordPacked word (codes.get 1)))
      let b := clear which (xorPoint (wordPacked word (codes.get 0))
        (wordPacked word (codes.get 2)))
      if allowed which a b then
        let key := planeKey a b
        if !(index.contains key) then
          index := index.insert key (makeWitness which key.1 key.2 codes word)
          queue := queue.push key
  for pos in List.range 16384 do
    if let some key := queue[pos]? then
      if let some old := index.get? key then
        for i in planeMoves which do
          let next := planeKey (clear which (packed i key.1))
            (clear which (packed i key.2))
          if !(index.contains next) then
            let witness := makeWitness which next.1 next.2 old.codes (i :: old.word)
            index := index.insert next witness
            queue := queue.push next
  return index

def planeTables : Vector (Std.HashMap PlaneKey Witness) 2 := Vector.ofFn findPlaneIndex

def findWitness (which : Fin 2) (a b : PackedPoint) : Option Witness :=
  ((planeTables.get which).get? (planeKey a b)).map fun w =>
    makeWitness which a b w.codes w.word

def quadCheck (which : Fin 2) (a b : PackedPoint) : Bool :=
  match findWitness which a b with
  | none => false
  | some w => validWitness which a b w

theorem plane_domain_counts :
    ((List.finRange 512).flatMap fun a => (List.finRange 512).filterMap fun b =>
      if a < b && b < xorPoint a b && allowed 0 a b then some (a, b) else none).length = 10795 ∧
    ((List.finRange 512).flatMap fun a => (List.finRange 512).filterMap fun b =>
      if a < b && b < xorPoint a b && allowed 1 a b then some (a, b) else none).length = 2480 := by
  native_decide

theorem quad_coverage_checked : ∀ (which : Fin 2) (a b : PackedPoint),
    allowed which a b = true → quadCheck which a b = true := by native_decide

theorem point_word_exists (which : Fin 2) (x : PackedPoint)
    (hx : pointAllowed which x = true) :
    ∃ word : Word, wordPacked word x = basePoint which := by
  have hc := point_coverage_checked which x hx
  cases hw : pointWord which x with
  | none => simp only [pointCheck, hw, Bool.false_eq_true] at hc
  | some word =>
    refine ⟨word, ?_⟩
    simpa only [pointCheck, hw, beq_iff_eq] using hc

theorem witness_exists (which : Fin 2) (a b : PackedPoint)
    (hab : allowed which a b = true) :
    ∃ w : Witness, (∀ i : Fin 4, w.codes.get i ∈ Certificate.seed 49) ∧
      shiftedImages w = canonicalQuad which a b := by
  have hc := quad_coverage_checked which a b hab
  cases hw : findWitness which a b with
  | none => simp only [quadCheck, hw, Bool.false_eq_true] at hc
  | some w =>
    refine ⟨w, ?_⟩
    simpa only [quadCheck, hw, validWitness, decide_eq_true_eq] using hc

end Lemmata.RM59.FlagWitnessChecks
