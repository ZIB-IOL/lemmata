module

public import Lemmata.RM59.Proof.SupportChecks
public meta import Lemmata.RM59.Proof.SupportChecks

@[expose] public section

namespace Lemmata.RM59.CatalogCompute

open Lemmata.RM59.Packed Lemmata.RM59.Certificate

def coefficients (family : Nat) : Array Bool :=
  Array.ofFn fun mask : Fin 512 =>
    bitCount mask.val == 3 && packedMoment (seed family) mask.val

def usedCoordinates (coeff : Array Bool) : Nat :=
  (List.range 512).foldl (fun used mask =>
    if coeff[mask]?.getD false then Nat.lor used mask else used) 0

def quotientDimension (coeff : Array Bool) : Nat :=
  (usedCoordinates coeff).log2 + 1

def coordinateContractions (coeff : Array Bool) : Array (Array Nat) :=
  Array.ofFn fun i : Fin 9 => Array.ofFn fun j : Fin 9 =>
    (List.finRange 9).foldl (fun value k =>
      if i != j && i != k && j != k &&
          coeff[2 ^ i.val + 2 ^ j.val + 2 ^ k.val]?.getD false then
        Nat.lor value (2 ^ k.val)
      else value) 0

def contractions (basis : Array (Array Nat)) (n : Nat) : Array (Array Nat) :=
  Array.ofFn fun v : Fin (2 ^ n) => Array.ofFn fun j : Fin n =>
    (List.range n).foldl (fun value i =>
      if v.val.testBit i then Nat.xor value ((basis[i]?.getD #[])[j.val]?.getD 0)
      else value) 0

def contractPair (row : Array Nat) (w : Nat) : Nat :=
  (List.range row.size).foldl (fun value j =>
    if w.testBit j then Nat.xor value (row[j]?.getD 0) else value) 0

def pairValues (table : Array (Array Nat)) : Array (Array Nat) :=
  table.map fun row => Array.ofFn fun w : Fin table.size => contractPair row w.val

def neighborLists (values : Array (Array Nat)) : Array (List Nat) :=
  Array.ofFn fun v : Fin values.size =>
    (List.range values.size).filter fun w =>
      v.val != 0 && w != 0 && v.val != w && (values[v.val]?.getD #[])[w]?.getD 0 == 0

def quotientCheck (coeff : Array Bool) : Bool :=
  let n := quotientDimension coeff
  let table := contractions (coordinateContractions coeff) n
  3 ≤ n && n ≤ 9 && usedCoordinates coeff < 2 ^ n &&
    (List.range (2 ^ n)).all (fun v =>
      v == 0 || (table[v]?.getD #[]).any (fun value => value != 0))

theorem quotient_coordinates_checked :
    ∀ family : Fin 348, quotientCheck (coefficients (family.val + 1)) = true := by
  native_decide

end Lemmata.RM59.CatalogCompute
