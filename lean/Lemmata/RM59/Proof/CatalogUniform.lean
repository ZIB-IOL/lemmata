module

public import Lemmata.RM59.Compute.CatalogUniform
public meta import Lemmata.RM59.Compute.CatalogUniform
public import Lemmata.RM59.Proof.CatalogCompute
public import Lemmata.RM59.Proof.BinaryValues
public import Lemmata.RM59.Proof.GraphCache
public import Std.Data.TreeMap.Basic
public meta import Lemmata.RM59.Proof.CatalogCompute
public meta import Lemmata.RM59.Proof.BinaryValues
public meta import Lemmata.RM59.Proof.GraphCache
public meta import Std.Data.TreeMap.Basic

@[expose] public section

namespace Lemmata.RM59.CatalogUniform

open Lemmata.RM59.CatalogCompute

def geometry (family : Nat) : Geometry :=
  let coeff := coefficients family
  let n := 9
  let count := 512
  let vertices := List.finRange count
  let values := BinaryValues.fastPairValues (contractions (coordinateContractions coeff) n)
  let neighbors : Vector (List (Fin count)) count := Vector.ofFn fun v =>
    vertices.filter fun w => v.val != 0 && w.val != 0 && v != w &&
      (values[v.val]?.getD #[])[w.val]?.getD 0 == 0
  let getNeighbors := fun v => neighbors.get v
  let counts := GraphCache.countTable getNeighbors
  let vertexKeys := Array.ofFn fun v : Fin count =>
    let f := GraphCache.cachedVertexFeature getNeighbors counts
      (fun w => if w.val = 0 then 1 else 0) v
    let rest := ofLex (ofLex f).2
    let last := ofLex rest.2
    [(ofLex f).1, rest.1, last.1, last.2]
  ⟨values, neighbors.toArray.map (fun row => row.map Fin.val), vertexKeys⟩

def standardAnchors : List Nat := (List.range 9).map (2 ^ ·)

def fixedAnchors : List Nat := [5, 6, 0, 7, 4, 1, 3, 2, 8].map (2 ^ ·)

def individualize (g : Geometry) (color : Array Nat) (anchor : Nat) : Array Nat :=
  exactColors (Array.ofFn fun v : Fin g.count =>
    [color[v.val]?.getD 0, if v.val = anchor then 1 else 0])

structure AnchorState where
  colors : Array Nat
  fixed : List Nat
  stages : Array (Array Nat)
  factors : Array Nat

def anchorStep (g : Geometry) (state : AnchorState) (anchor : Nat) : AnchorState :=
  let colors := stabilize g state.fixed anchor g.count state.colors
  ⟨individualize g colors anchor, state.fixed ++ [anchor],
    state.stages.push colors, state.factors.push (classSize colors anchor)⟩

def anchorLoop (g : Geometry) (anchors : List Nat) (state : AnchorState) : AnchorState := Id.run do
  let mut colors := state.colors
  let mut fixed := state.fixed
  let mut stages := state.stages
  let mut factors := state.factors
  for anchor in anchors do
    colors := stabilize g fixed anchor g.count colors
    stages := stages.push colors
    factors := factors.push (classSize colors anchor)
    fixed := fixed ++ [anchor]
    colors := individualize g colors anchor
  return ⟨colors, fixed, stages, factors⟩

def initialState (g : Geometry) : AnchorState :=
  ⟨additionColors g (exactColors g.vertexKeys), [], #[], #[]⟩

def runResult (g : Geometry) (anchors : List Nat) : Result :=
  let state := anchorLoop g anchors (initialState g)
  ⟨g.vertexKeys.toList.mergeSort (fun a b => compare a b != .gt), anchors,
    state.stages, state.factors, terminalColors g anchors 9 state.colors⟩

def run (family : Nat) : Result :=
  let g := geometry family
  let first := runResult g standardAnchors
  let second := runResult g fixedAnchors
  let selected := if first.bound ≤ second.bound then first else second
  {selected with invariant := g.vertexKeys.toList.mergeSort (fun a b => compare a b != .gt)}

def catalogCheck : Bool :=
  let results := Array.ofFn fun i : Fin 348 => run (i.val + 1)
  let gl := generalLinearOrder 9
  results.all (fun result => result.valid && result.bound > 0 && gl % result.bound == 0) &&
    results.foldl (fun mass result => mass + gl / result.bound) 1 == 2 ^ 84 &&
    (results.toList.map Result.invariant).Nodup

theorem pilot_results_valid : ∀ family ∈ ([1, 49, 348] : List Nat), (run family).valid = true := by
  native_decide

end Lemmata.RM59.CatalogUniform
