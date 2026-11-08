module

public import Std
public import Init.Data.Vector.Lemmas
public import Init.Data.Vector.OfFn
public import Init.Data.Array.OfFn

@[expose] public section

namespace Lemmata.RM59.GraphCache

variable {n : Nat}

def bump (row : Vector Nat n) (v : Fin n) : Vector Nat n :=
  row.set v.val (row.get v + 1) v.isLt

def addNeighbors (row : Vector Nat n) (vertices : List (Fin n)) : Vector Nat n :=
  vertices.foldl bump row

def addWalks (neighbors : Fin n → List (Fin n)) (row : Vector Nat n)
    (vertices : List (Fin n)) : Vector Nat n :=
  vertices.foldl (fun row u => addNeighbors row (neighbors u)) row

def commonRow (neighbors : Fin n → List (Fin n)) (v : Fin n) : Vector Nat n :=
  addWalks neighbors (Vector.replicate n 0) (neighbors v)

def countTable (neighbors : Fin n → List (Fin n)) : Vector (Vector Nat n) n :=
  Vector.ofFn fun v => commonRow neighbors v

def neighborWeightedSum (row : Vector Nat n) (vertices : List (Fin n)) (w : Fin n) : Nat :=
  let cw := row.get w
  if cw = 0 then 0 else vertices.foldl (fun acc z => acc + cw * row.get z) 0

end Lemmata.RM59.GraphCache
