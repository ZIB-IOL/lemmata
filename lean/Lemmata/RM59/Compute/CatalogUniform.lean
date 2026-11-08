module

public import Std
public import Init.Data.Vector.Lemmas
public import Init.Data.Vector.OfFn
public import Init.Data.Array.OfFn
public import Std.Data.TreeMap.Basic

@[expose] public section

namespace Lemmata.RM59.CatalogUniform

def exactColors (keys : Array (List Nat)) : Array Nat := Id.run do
  let mut dictionary : Std.TreeMap (List Nat) Nat := {}
  for key in keys do
    dictionary := dictionary.insert key 0
  let mut labels : Std.TreeMap (List Nat) Nat := {}
  for entry in dictionary.toList.zipIdx do
    labels := labels.insert entry.1.1 entry.2
  return keys.map fun key => labels.getD key 0

def classCount (color : Array Nat) : Nat :=
  if color.isEmpty then 0 else color.foldl max 0 + 1

def classSize (color : Array Nat) (anchor : Nat) : Nat :=
  color.foldl (fun size c => size + if c = color[anchor]?.getD 0 then 1 else 0) 0

structure Geometry where
  values : Array (Array Nat)
  neighbors : Array (List Nat)
  vertexKeys : Array (List Nat)

def Geometry.count (_g : Geometry) : Nat := 512

def additionColors (g : Geometry) (color : Array Nat) : Array Nat :=
  let vertices := List.range g.count
  exactColors (Array.ofFn fun v : Fin g.count =>
    let terms := vertices.map fun w =>
      let a := color[w]?.getD 0
      let b := color[Nat.xor w v.val]?.getD 0
      min a b * 1024 + max a b
    color[v.val]?.getD 0 :: terms.mergeSort (· ≤ ·))

def ordinaryColors (g : Geometry) (anchors : List Nat) (color : Array Nat) : Array Nat :=
  exactColors (Array.ofFn fun v : Fin g.count =>
    [color[v.val]?.getD 0] ++
      anchors.map (fun a => color[Nat.xor v.val a]?.getD 0) ++
      (((g.neighbors[v.val]?.getD []).map fun w => color[w]?.getD 0).mergeSort (· ≤ ·)))

def shiftColors (g : Geometry) (anchors : List Nat) (color : Array Nat) : Array Nat :=
  exactColors (Array.ofFn fun v : Fin g.count =>
    color[v.val]?.getD 0 :: anchors.map fun a => color[Nat.xor v.val a]?.getD 0)

def parity (value : Nat) : Bool :=
  ((List.range 9).countP fun i => value.testBit i) % 2 == 1

def functionalColors (g : Geometry) (color : Array Nat) : Array Nat :=
  let classes := classCount color
  let vertices := List.range g.count
  let keys := Array.ofFn fun f : Fin g.count => Id.run do
    let mut histogram := Array.replicate classes 0
    for w in vertices do
      if parity (Nat.land f.val w) then
        histogram := histogram.modify (color[w]?.getD 0) (· + 1)
    return histogram.toList
  exactColors keys

def bilinearColors (g : Geometry) (anchors : List Nat) (color : Array Nat) : Array Nat :=
  let profile := functionalColors g color
  exactColors (Array.ofFn fun v : Fin g.count =>
    color[v.val]?.getD 0 :: anchors.map fun a =>
      profile[(g.values[a]?.getD #[])[v.val]?.getD 0]?.getD 0)

def stabilize (g : Geometry) (anchors : List Nat) (anchor : Nat) : Nat → Array Nat → Array Nat
  | 0, color => color
  | fuel + 1, color =>
    if classSize color anchor = 1 then color else
      let ordinary := ordinaryColors g anchors color
      let refined := if classCount ordinary = classCount color && !anchors.isEmpty then
        bilinearColors g anchors ordinary else ordinary
      if classCount refined = classCount color then refined
      else stabilize g anchors anchor fuel refined

def terminalColors (g : Geometry) (anchors : List Nat) : Nat → Array Nat → Array Nat
  | 0, color => color
  | fuel + 1, color =>
    if classCount color = g.count then color
    else terminalColors g anchors fuel (shiftColors g anchors color)

structure Result where
  invariant : List (List Nat)
  anchors : List Nat
  stages : Array (Array Nat)
  factors : Array Nat
  terminal : Array Nat

def Result.valid (result : Result) : Bool :=
  let count := 512
  result.anchors.length == 9 && result.anchors.all (· < count) &&
    result.stages.size == 9 && result.factors.size == 9 &&
    result.stages.all (fun color => color.size == count) &&
    result.factors.all (· > 0) && result.terminal.size == count &&
    result.terminal.toList.Nodup

def Result.bound (result : Result) : Nat := result.factors.foldl (· * ·) 1

def generalLinearOrder (n : Nat) : Nat :=
  (List.range n).foldl (fun value j => value * (2 ^ n - 2 ^ j)) 1

end Lemmata.RM59.CatalogUniform
