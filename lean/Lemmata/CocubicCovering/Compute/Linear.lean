module

public import Init

@[expose] public section

namespace Lemmata.CocubicCovering.Compute.Linear

structure Row where
  bits : Nat
  coefficients : Nat
  deriving Inhabited

abbrev Echelon := Array (Option Row)

def reduce (width : Nat) (basis : Echelon) : Nat → Row → Row
  | 0, row => row
  | fuel + 1, row =>
      let active := row.bits &&& (2 ^ width - 1)
      if active == 0 then row
      else
        match basis[active.log2]?.getD none with
        | none => row
        | some previous => reduce width basis fuel
            ⟨row.bits ^^^ previous.bits, row.coefficients ^^^ previous.coefficients⟩

def build (width : Nat) (rows : Array Nat) : Echelon := Id.run do
  let mut basis := Array.replicate width none
  for i in [:rows.size] do
    let row := reduce width basis width ⟨rows[i]?.getD 0, 2 ^ i⟩
    let active := row.bits &&& (2 ^ width - 1)
    if active != 0 then basis := basis.set! active.log2 (some row)
  return basis

def basis (width : Nat) (rows : Array Nat) : Array Nat :=
  ((build width rows).filterMap id).map Row.bits

def orderedBasis (width : Nat) (rows : Array Nat) : Array Nat := Id.run do
  let mut echelon := Array.replicate width none
  let mut result := #[]
  for bits in rows do
    let row := reduce width echelon width ⟨bits, 0⟩
    let active := row.bits &&& (2 ^ width - 1)
    if active != 0 then
      echelon := echelon.set! active.log2 (some row)
      result := result.push row.bits
  return result

def solve (width : Nat) (basis : Echelon) (bits : Nat) : Row :=
  reduce width basis width ⟨bits, 0⟩

def normalForm (width : Nat) (basis : Echelon) (bits : Nat) : Nat := Id.run do
  let mut result := bits
  for offset in [:width] do
    let pivot := width - 1 - offset
    if result.testBit pivot then
      if let some row := basis[pivot]?.getD none then result := result ^^^ row.bits
  return result

def parity (bits : Nat) : Bool :=
  (List.range (bits.log2 + 1)).foldl (fun value i => Bool.xor value (bits.testBit i)) false

def nullspace (width : Nat) (rows : Array Nat) : Array Nat := Id.run do
  let echelon := build width rows
  let mut result := #[]
  for free in [:width] do
    if (echelon[free]?.getD none).isNone then
      let mut vector := 2 ^ free
      for pivot in [:width] do
        if let some row := echelon[pivot]?.getD none then
          if parity (row.bits &&& vector) then vector := vector ^^^ 2 ^ pivot
      result := result.push vector
  return result

end Lemmata.CocubicCovering.Compute.Linear
