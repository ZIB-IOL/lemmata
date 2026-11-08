module

public import Std
public import Init.Data.Vector.Lemmas
public import Init.Data.Vector.OfFn
public import Init.Data.Array.OfFn
public meta import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Lemmata.RM59.BinaryValues

def xorValue : List Nat → Nat → Nat
  | [], _ => 0
  | c :: columns, w =>
    let tail := xorValue columns (w / 2)
    if w.testBit 0 then Nat.xor tail c else tail

def slowList (columns : List Nat) (w start : Nat) : Nat :=
  (List.range columns.length).foldl (fun acc j =>
    if w.testBit j then Nat.xor acc (columns[j]?.getD 0) else acc) start

def values : List Nat → Array Nat
  | [] => #[0]
  | c :: columns =>
    let previous := values columns
    Array.ofFn fun w : Fin (2 * previous.size) =>
      let tail := previous[w.val / 2]'(by have := w.isLt; omega)
      if w.val.testBit 0 then Nat.xor tail c else tail

def fastPairValues (table : Array (Array Nat)) : Array (Array Nat) :=
  table.map fun row => values row.toList

end Lemmata.RM59.BinaryValues
