module

public import Lemmata.CocubicCovering.Compute.Encoding
public meta import Lemmata.CocubicCovering.Compute.Encoding
public import Std.Data.HashMap

@[expose] public section

namespace Lemmata.CocubicCovering.Compute.Polynomial


abbrev Inputs := List (List Nat)

structure Row (dictionary : Nat → Nat) (size : Nat) (inputs : Inputs) where
  bits : Nat
  valid : Encoding.Derives dictionary size (fun row => row ∈ inputs) bits

def Row.xor {dictionary : Nat → Nat} {size : Nat} {inputs : Inputs}
    (a b : Row dictionary size inputs) : Row dictionary size inputs :=
  ⟨a.bits ^^^ b.bits, .xor a.valid b.valid⟩

structure Multiplier (dictionary : Nat → Nat) (size : Nat) (inputs : Inputs) where
  pairs : List (Nat × Nat)
  domain : Nat
  valid : ∀ bits, bits &&& domain = bits →
    Encoding.Derives dictionary size (fun row => row ∈ inputs) bits →
    Encoding.Derives dictionary size (fun row => row ∈ inputs)
      (Encoding.mapped pairs bits)

def calibrate (dictionary : Nat → Nat) (size : Nat) (inputs : Inputs)
    (coefficient : Nat) (pairs : List (Nat × Nat)) :
    Option (Multiplier dictionary size inputs) :=
  if h : Encoding.mapCheck dictionary size coefficient pairs = true then
    some ⟨pairs, Encoding.encodeIndices (pairs.map Prod.fst),
      fun _ contained previous => .mappedProduct h rfl contained previous⟩
  else none

def Multiplier.apply {dictionary : Nat → Nat} {size : Nat} {inputs : Inputs}
    (multiplier : Multiplier dictionary size inputs) (row : Row dictionary size inputs) :
    Option (Row dictionary size inputs) :=
  if h : row.bits &&& multiplier.domain = row.bits then
    some ⟨Encoding.mapped multiplier.pairs row.bits, multiplier.valid row.bits h row.valid⟩
  else none

def monomials (variables : Nat) : Array Nat := Id.run do
  let mut result := #[0]
  for i in [:variables] do
    result := result.push (2 ^ i)
  for i in [:variables] do
    for j in [i + 1: variables] do
      result := result.push (2 ^ i ||| 2 ^ j)
  for i in [:variables] do
    for j in [i + 1: variables] do
      for k in [j + 1: variables] do
        result := result.push (2 ^ i ||| 2 ^ j ||| 2 ^ k)
  return result

def dictionary (table : Array Nat) (i : Nat) : Nat := table[i]?.getD 0

def positions (table : Array Nat) : Std.HashMap Nat Nat := Id.run do
  let mut result := Std.HashMap.emptyWithCapacity table.size
  for i in [:table.size] do
    result := result.insert (dictionary table i) i
  return result

def initialRows (table : Array Nat) (inputs : Inputs) (index : Std.HashMap Nat Nat) :
    Option (Array (Row (dictionary table) table.size inputs)) := do
  let mut result := #[]
  for input in inputs.attach do
    let indices := input.val.map fun monomial => index[monomial]?.getD table.size
    let bits := Encoding.encodeIndices indices
    if h : Encoding.rowCheck (dictionary table) table.size input.val indices bits = true then
      result := result.push ⟨bits, .input h input.property⟩
    else return ← none
  return result

def multipliers (variables retained : Nat) (table : Array Nat) (inputs : Inputs)
    (index : Std.HashMap Nat Nat) : Option (Array (Multiplier (dictionary table) table.size inputs)) := do
  let mut result := #[]
  for v in [:variables] do
    let coefficient := 2 ^ v
    let mut pairs := #[]
    for source in [:retained] do
      let target := index[dictionary table source ||| coefficient]?.getD table.size
      pairs := pairs.push (source, target)
    let checked ← calibrate (dictionary table) table.size inputs coefficient pairs.toList
    result := result.push checked
  return result

abbrev Basis (dictionary : Nat → Nat) (size : Nat) (inputs : Inputs) :=
  Array (Option (Row dictionary size inputs))

def insert {dictionary : Nat → Nat} {size : Nat} {inputs : Inputs} :
    Nat → Basis dictionary size inputs → Row dictionary size inputs →
      Basis dictionary size inputs × Option (Row dictionary size inputs)
  | 0, basis, _ => (basis, none)
  | fuel + 1, basis, row =>
      if row.bits == 0 then (basis, none)
      else if row.bits == 1 then (basis, some row)
      else
        let pivot := row.bits.log2
        match basis[pivot]?.getD none with
        | none => (basis.set! pivot (some row), none)
        | some previous => insert fuel basis (row.xor previous)

def lowRows {dictionary : Nat → Nat} {size : Nat} {inputs : Inputs}
    (retained : Nat) (basis : Basis dictionary size inputs) : Array (Row dictionary size inputs) := Id.run do
  let mut basis := basis
  let mut indices := #[]
  for i in [1:retained] do
    if (basis[i]?.getD none).isSome then indices := indices.push i
  for pivot in indices do
    if let some row := basis[pivot]?.getD none then
      for other in indices do
        if pivot < other then
          if let some value := basis[other]?.getD none then
            if value.bits.testBit pivot then
              basis := basis.set! other (some (value.xor row))
  let mut result := #[]
  for i in indices do
    if let some row := basis[i]?.getD none then result := result.push row
  return result

def round {dictionary : Nat → Nat} {size : Nat} {inputs : Inputs}
    (rows : Array (Row dictionary size inputs))
    (actions : Array (Multiplier dictionary size inputs)) :
    Basis dictionary size inputs × Option (Row dictionary size inputs) := Id.run do
  let mut basis := Array.replicate size none
  for row in rows do
    let (next, found) := insert size basis row
    if found.isSome then return (next, found)
    basis := next
    for action in actions do
      if let some product := action.apply row then
        let (next, found) := insert size basis product
        if found.isSome then return (next, found)
        basis := next
  return (basis, none)

def iterate {dictionary : Nat → Nat} {size : Nat} {inputs : Inputs}
    (retained : Nat) (actions : Array (Multiplier dictionary size inputs)) :
    Nat → Array (Row dictionary size inputs) → Option (Row dictionary size inputs)
  | 0, _ => none
  | fuel + 1, rows =>
      let (basis, found) := round rows actions
      match found with
      | some row => some row
      | none => iterate retained actions fuel (lowRows retained basis)

def solve (variables rounds : Nat) (inputs : Inputs) :
    Option (Row (dictionary (monomials variables)) (monomials variables).size inputs) := do
  let table := monomials variables
  let index := positions table
  let retained := 1 + variables + variables * (variables - 1) / 2
  let rows ← initialRows table inputs index
  let actions ← multipliers variables retained table inputs index
  iterate retained actions rounds rows

def refutes (variables rounds : Nat) (inputs : Inputs) : Bool :=
  let table := monomials variables
  decide (0 < table.size ∧ dictionary table 0 = 0) &&
    (solve variables rounds inputs).any fun row => row.bits == 1

end Lemmata.CocubicCovering.Compute.Polynomial
