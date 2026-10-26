module

public import Init.Data.Nat.Bitwise.Basic

@[expose] public section

namespace Lemmata.CocubicCovering.Compute.Encoding

def encodeIndices (indices : List Nat) : Nat :=
  indices.foldr (fun i mask => (2 ^ i) ^^^ mask) 0

def rowCheck (dictionary : Nat → Nat) (size : Nat) (row indices : List Nat)
    (bits : Nat) : Bool :=
  indices.all (fun i => decide (i < size)) &&
    decide (indices.map dictionary = row) && decide (encodeIndices indices = bits)

def mapCheck (dictionary : Nat → Nat) (size coefficient : Nat)
    (pairs : List (Nat × Nat)) : Bool :=
  pairs.all fun pair => decide (pair.1 < size ∧ pair.2 < size ∧
    dictionary pair.2 = dictionary pair.1 ||| coefficient)

def mapAcc (word : Nat) : List (Nat × Nat) → Nat → Nat
  | [], result => result
  | (source, target) :: pairs, result =>
      mapAcc word pairs (if word.testBit source then result ^^^ 2 ^ target else result)

def mapped (pairs : List (Nat × Nat)) (word : Nat) : Nat := mapAcc word pairs 0

inductive Derives (dictionary : Nat → Nat) (size : Nat) (inputs : List Nat → Prop) : Nat → Prop
  | input {row indices bits}
      (encoded : rowCheck dictionary size row indices bits = true)
      (premise : inputs row) : Derives dictionary size inputs bits
  | mappedProduct {coefficient pairs domain source}
      (calibrated : mapCheck dictionary size coefficient pairs = true)
      (encoded : domain = encodeIndices (pairs.map Prod.fst))
      (contained : source &&& domain = source)
      (previous : Derives dictionary size inputs source) :
      Derives dictionary size inputs (mapped pairs source)
  | xor {left right} (a : Derives dictionary size inputs left)
      (b : Derives dictionary size inputs right) : Derives dictionary size inputs (left ^^^ right)
  | cast {left right} (equal : left = right) (previous : Derives dictionary size inputs left) :
      Derives dictionary size inputs right

end Lemmata.CocubicCovering.Compute.Encoding
