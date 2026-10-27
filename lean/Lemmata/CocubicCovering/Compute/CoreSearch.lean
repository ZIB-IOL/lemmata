module

public import Std.Data.HashMap
public import Lemmata.CocubicCovering.Certificate.CoreCertificate
public meta import Lemmata.CocubicCovering.Certificate.CoreCertificate

@[expose] public section

namespace Lemmata.CocubicCovering.Compute.CoreSearch

structure State where
  root : Nat
  core : List Nat
  deriving BEq, Hashable, DecidableEq

structure Root where
  assignment : Nat
  radical : List Nat
  required : Nat

def combine (columns : List Nat) (coefficients : Nat) : Nat :=
  Lemmata.CocubicCovering.Certificate.CoreCertificate.composeRow coefficients columns.get

def reducePair : Nat → Array (Nat × Nat) → Nat × Nat → Nat × Nat
  | 0, _, row => row
  | fuel + 1, basis, row =>
      if row.1 == 0 then row
      else
        let previous := basis[row.1.log2]?.getD (0, 0)
        if previous.1 == 0 then row
        else reducePair fuel basis (row.1 ^^^ previous.1, row.2 ^^^ previous.2)

def elimination (columns : List Nat) : Array (Nat × Nat) := Id.run do
  let dimension := columns.foldl (fun size row => max size (row.log2 + 1)) 1
  let mut basis := Array.replicate dimension (0, 0)
  for (column, i) in columns.zipIdx do
    let row := reducePair dimension basis (column, 2 ^ i)
    if row.1 != 0 then basis := basis.set! row.1.log2 row
  return basis

def solve (columns : List Nat) (target : Nat) : Option Nat :=
  let result := reducePair (target.log2 + 1) (elimination columns) (target, 0)
  if result.1 == 0 then some result.2 else none

def reduceVector : Nat → Array Nat → Nat → Nat
  | 0, _, row => row
  | fuel + 1, basis, row =>
      if row == 0 then 0
      else
        let previous := basis[row.log2]?.getD 0
        if previous == 0 then row else reduceVector fuel basis (row ^^^ previous)

def canonical (columns : List Nat) : List Nat := Id.run do
  let dimension := columns.foldl (fun size row => max size (row.log2 + 1)) 1
  let mut basis := Array.replicate dimension 0
  for column in columns do
    let row := reduceVector dimension basis column
    if row != 0 then basis := basis.set! row.log2 row
  for pivot in [:basis.size] do
    let row := basis[pivot]?.getD 0
    if row != 0 then
      for higher in [pivot + 1:basis.size] do
        let value := basis[higher]?.getD 0
        if value.testBit pivot then basis := basis.set! higher (value ^^^ row)
  return (basis.toList.filter (· != 0)).reverse

def coefficients (source target : List Nat) : Option (List Nat) :=
  source.mapM (solve target)

def transpose (dimension : Nat) (columns : List Nat) : List Nat :=
  (List.range dimension).map fun bit =>
    (columns.zipIdx).foldl (fun row (column, i) =>
      if column.testBit bit then row ||| 2 ^ i else row) 0

def dual (dimension : Nat) (columns : List Nat) : Option (List Nat) :=
  (List.range columns.length).mapM fun i => solve (transpose dimension columns) (2 ^ i)

def fresh (radical core : List Nat) (count : Nat) : List Nat := Id.run do
  let mut span := canonical core
  let mut result := []
  for vector in radical do
    if result.length == count then break
    if (solve span vector).isNone then
      result := result ++ [vector]
      span := canonical (span ++ [vector])
  return result

structure Branch where
  fresh : List Nat
  inRadical : List Nat
  dual : List Nat

def branch (root : Root) (state : State) : Option Branch := do
  let count := root.radical.length + 1 - root.required
  let vectors := fresh root.radical state.core count
  if vectors.length != count then return ← none
  let inclusion ← coefficients vectors root.radical
  let dualRows ← dual 12 (state.core ++ vectors)
  return ⟨vectors, inclusion, dualRows⟩

def children (state : State) (data : Branch) : List State :=
  (List.range (2 ^ data.fresh.length - 1)).map fun i =>
    ⟨state.root, state.core ++ [combine data.fresh (i + 1)]⟩

end Lemmata.CocubicCovering.Compute.CoreSearch
