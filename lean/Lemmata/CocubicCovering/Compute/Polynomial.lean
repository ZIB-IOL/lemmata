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

def monomials (variableCount : Nat) : Array Nat := Id.run do
  let mut result := #[0]
  for i in [:variableCount] do
    result := result.push (2 ^ i)
  for i in [:variableCount] do
    for j in [i + 1: variableCount] do
      result := result.push (2 ^ i ||| 2 ^ j)
  for i in [:variableCount] do
    for j in [i + 1: variableCount] do
      for k in [j + 1: variableCount] do
        result := result.push (2 ^ i ||| 2 ^ j ||| 2 ^ k)
  return result

def dictionary (table : Array Nat) (i : Nat) : Nat := table[i]?.getD 0

structure MonomialKey where
  value : Nat
  deriving BEq

instance : Hashable MonomialKey where
  hash key := mixHash (UInt64.ofNat key.value) (UInt64.ofNat (key.value >>> 64))

abbrev Index := Std.HashMap MonomialKey Nat

def positions (table : Array Nat) : Index := Id.run do
  let mut result := Std.HashMap.emptyWithCapacity table.size
  for i in [:table.size] do
    result := result.insert ⟨dictionary table i⟩ i
  return result

def initialRows (table : Array Nat) (inputs : Inputs) (index : Nat → Option Nat) :
    Option (Array (Row (dictionary table) table.size inputs)) := do
  let mut result := #[]
  for input in inputs.attach do
    let indices := input.val.map fun monomial => (index monomial).getD table.size
    let bits := Encoding.encodeIndices indices
    if h : Encoding.rowCheck (dictionary table) table.size input.val indices bits = true then
      result := result.push ⟨bits, .input h input.property⟩
    else return ← none
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

def selectedSourcesAux : Nat → Nat → List Nat → List Nat
  | 0, _, result => result
  | fuel + 1, bits, result =>
      if bits == 0 then result
      else
        let pivot := bits.log2
        selectedSourcesAux fuel (bits ^^^ 2 ^ pivot) (pivot :: result)

def selectedSources (bits : Nat) : List Nat :=
  selectedSourcesAux (bits.log2 + 1) bits []

structure Entry (dictionary : Nat → Nat) (size coefficient : Nat) where
  source : Nat
  target : Nat
  calibrated : source < size ∧ target < size ∧
    dictionary target = dictionary source ||| coefficient

def Entry.pair {dictionary : Nat → Nat} {size coefficient : Nat}
    (entry : Entry dictionary size coefficient) : Nat × Nat :=
  (entry.source, entry.target)

structure Action (dictionary : Nat → Nat) (size retained : Nat) where
  coefficient : Nat
  entries : Array (Entry dictionary size coefficient)
  size_eq : entries.size = retained
  aligned : ∀ source : Fin entries.size, (entries[source.val]'source.isLt).source = source.val

def Action.get {dictionary : Nat → Nat} {size retained : Nat}
    (action : Action dictionary size retained) (source : Fin retained) :
    Entry dictionary size action.coefficient :=
  action.entries[source.val]'(by simpa only [action.size_eq] using source.isLt)

theorem Action.get_source {dictionary : Nat → Nat} {size retained : Nat}
    (action : Action dictionary size retained) (source : Fin retained) :
    (action.get source).source = source.val :=
  action.aligned ⟨source.val, by simpa only [action.size_eq] using source.isLt⟩

def actions (variableCount retained : Nat) (table : Array Nat)
    (index : Nat → Option Nat) :
    Option (Array (Action (dictionary table) table.size retained)) := do
  let mut result := #[]
  for v in [:variableCount] do
    let coefficient := 2 ^ v
    let mut entries := #[]
    for source in [:retained] do
      let target := (index (dictionary table source ||| coefficient)).getD table.size
      if h : source < table.size ∧ target < table.size ∧
          dictionary table target = dictionary table source ||| coefficient then
        entries := entries.push ⟨source, target, h⟩
      else return ← none
    if hsize : entries.size = retained then
      if haligned : ∀ source : Fin entries.size,
          (entries[source.val]'source.isLt).source = source.val then
        result := result.push ⟨coefficient, entries, hsize, haligned⟩
      else return ← none
    else return ← none
  return result

theorem entries_checked {dictionary : Nat → Nat} {size coefficient : Nat}
    (entries : List (Entry dictionary size coefficient)) :
    Encoding.mapCheck dictionary size coefficient (entries.map Entry.pair) = true := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      change decide (entry.source < size ∧ entry.target < size ∧
        dictionary entry.target = dictionary entry.source ||| coefficient) &&
          Encoding.mapCheck dictionary size coefficient (entries.map Entry.pair) = true
      exact Bool.and_eq_true_iff.mpr ⟨by simpa only [decide_eq_true_eq] using entry.calibrated, ih⟩

def boundedSources (retained : Nat) : List Nat → Option (List (Fin retained))
  | [] => some []
  | source :: sources =>
      if h : source < retained then do
        let rest ← boundedSources retained sources
        return ⟨source, h⟩ :: rest
      else none

structure Support (retained bits : Nat) where
  sources : List (Fin retained)
  domain : Nat
  encoded : domain = Encoding.encodeIndices (sources.map Fin.val)
  contained : bits &&& domain = bits
  present : ∀ source ∈ sources, bits.testBit source.val = true

def support (retained bits : Nat) : Option (Support retained bits) := do
  let sources ← boundedSources retained (selectedSources bits)
  let domain := Encoding.encodeIndices (sources.map Fin.val)
  if present : sources.all (fun source => bits.testBit source.val) = true then
    if contained : bits &&& domain = bits then
      some ⟨sources, domain, rfl, contained, List.all_eq_true.mp present⟩
    else none
  else none

def applySources {dictionary : Nat → Nat} {size retained : Nat}
    (action : Action dictionary size retained) : List (Fin retained) → Nat → Nat
  | [], bits => bits
  | source :: sources, bits =>
      applySources action sources (bits ^^^ (2 ^ (action.get source).target))

theorem applySources_eq {dictionary : Nat → Nat} {size retained : Nat}
    (action : Action dictionary size retained) (word : Nat) :
    ∀ (sources : List (Fin retained)) (bits : Nat),
      (∀ source ∈ sources, word.testBit source.val = true) →
      applySources action sources bits =
        Encoding.mapAcc word ((sources.map action.get).map Entry.pair) bits := by
  intro sources
  induction sources with
  | nil => intro bits present; rfl
  | cons source sources ih =>
      intro bits present
      have hsource := present source (by simp)
      have hrest : ∀ source ∈ sources, word.testBit source.val = true :=
        fun source h => present source (by simp [h])
      rw [applySources, ih _ hrest]
      simp [Encoding.mapAcc, Entry.pair, Action.get_source, hsource]

def Action.apply {dictionary : Nat → Nat} {size retained : Nat} {inputs : Inputs}
    (action : Action dictionary size retained) (row : Row dictionary size inputs)
    (support : Support retained row.bits) : Row dictionary size inputs :=
  let selected := support.sources.map action.get
  let bits := applySources action support.sources 0
  have domain : support.domain = Encoding.encodeIndices ((selected.map Entry.pair).map Prod.fst) := by
    have sourceIndices : (selected.map Entry.pair).map Prod.fst = support.sources.map Fin.val := by
      simp only [selected, List.map_map]
      apply List.map_congr_left
      intro source _
      exact action.get_source source
    rw [sourceIndices]
    exact support.encoded
  have output : Encoding.mapped (selected.map Entry.pair) row.bits = bits :=
    (applySources_eq action row.bits support.sources 0 support.present).symm
  ⟨bits, .cast output (.mappedProduct (entries_checked selected) domain support.contained row.valid)⟩

def round {dictionary : Nat → Nat} {size retained : Nat} {inputs : Inputs}
    (rows : Array (Row dictionary size inputs)) (actions : Array (Action dictionary size retained)) :
    Basis dictionary size inputs × Option (Row dictionary size inputs) := Id.run do
  let mut basis := Array.replicate size none
  for row in rows do
    if row.bits != 0 then
      let (next, found) := insert size basis row
      if found.isSome then return (next, found)
      basis := next
      if let some support := support retained row.bits then
        for action in actions do
          let product := action.apply row support
          let (next, found) := insert size basis product
          if found.isSome then return (next, found)
          basis := next
  return (basis, none)

def iterate {dictionary : Nat → Nat} {size : Nat} {inputs : Inputs}
    (retained : Nat) (actions : Array (Action dictionary size retained)) :
    Nat → Array (Row dictionary size inputs) → Option (Row dictionary size inputs)
  | 0, _ => none
  | fuel + 1, rows =>
      let (basis, found) := round rows actions
      match found with
      | some row => some row
      | none => iterate retained actions fuel (lowRows retained basis)

def solve (variableCount rounds : Nat) (inputs : Inputs) :
    Option (Row (dictionary (monomials variableCount)) (monomials variableCount).size inputs) := do
  let table := monomials variableCount
  let index := positions table
  let retained := 1 + variableCount + variableCount * (variableCount - 1) / 2
  let rows ← initialRows table inputs (fun monomial => index[(⟨monomial⟩ : MonomialKey)]?)
  let calibrated ← actions variableCount retained table (fun monomial => index[(⟨monomial⟩ : MonomialKey)]?)
  iterate retained calibrated rounds rows

def refutes (variableCount rounds : Nat) (inputs : Inputs) : Bool :=
  let table := monomials variableCount
  decide (0 < table.size ∧ dictionary table 0 = 0) &&
    (solve variableCount rounds inputs).any fun row => row.bits == 1

end Lemmata.CocubicCovering.Compute.Polynomial
