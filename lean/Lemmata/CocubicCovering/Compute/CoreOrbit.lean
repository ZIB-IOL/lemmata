module

public import Lemmata.CocubicCovering.Compute.CoreSearch
public meta import Lemmata.CocubicCovering.Compute.CoreSearch

@[expose] public section

namespace Lemmata.CocubicCovering.Compute.CoreSearch

@[noinline, never_extract]
def force {α : Type} (value : Thunk α) : α := value.get

structure Generators where
  coreColumns : Fin 8 → Fin 12 → Nat
  localColumns : Fin 8 → Fin 15 → Nat

structure Action where
  word : List (Fin 8)
  coreColumns : List Nat
  localColumns : List Nat

def fastCombine : List Nat → Nat → Nat
  | [], _ => 0
  | column :: columns, mask =>
      if mask == 0 then 0
      else (if mask.testBit 0 then column else 0) ^^^ fastCombine columns (mask / 2)

def inverseWord (word : List (Fin 8)) : List (Fin 8) :=
  word.reverse.map fun generator => Fin.ofNat 8 (generator.val + 4)

def Action.coreColumn (action : Action) (i : Fin 12) : Nat :=
  action.coreColumns[i.val]?.getD 0

def Action.localColumn (action : Action) (i : Fin 15) : Nat :=
  action.localColumns[i.val]?.getD 0

def Action.identity : Action :=
  ⟨[], (List.range 12).map (2 ^ ·), (List.range 15).map (2 ^ ·)⟩

def Action.nextColumns (action : Action) (generator : Fin 8) (core localColumns : List Nat) : Action :=
  ⟨action.word ++ [generator], action.coreColumns.map (fastCombine core),
    action.localColumns.map (fastCombine localColumns)⟩

def Action.next (generators : Generators) (action : Action) (generator : Fin 8) : Action :=
  action.nextColumns generator (List.ofFn (generators.coreColumns generator))
    (List.ofFn (generators.localColumns generator))

def Action.key (action : Action) : List Nat × List Nat := (action.coreColumns, action.localColumns)

@[noinline, never_extract]
def group (generators : Generators) (limit : Nat) : Array Action := Id.run do
  let core := Array.ofFn fun generator : Fin 8 => List.ofFn (generators.coreColumns generator)
  let localColumns := Array.ofFn fun generator : Fin 8 => List.ofFn (generators.localColumns generator)
  let mut result := #[Action.identity]
  let mut known : Std.HashMap (List Nat × List Nat) Unit := ∅
  known := known.insert Action.identity.key ()
  for position in [:limit] do
    if position >= result.size then break
    let previous := result[position]?.getD Action.identity
    for generator in List.finRange 8 do
      let image := previous.nextColumns generator (core[generator.val]?.getD [])
        (localColumns[generator.val]?.getD [])
      if !known.contains image.key then
        known := known.insert image.key ()
        result := result.push image
  return result

def stabilizer (actions : Array Action) (assignment : Nat) : Array Action :=
  actions.filter fun action => fastCombine action.localColumns assignment == assignment

structure OrbitImage where
  core : List Nat
  action : Action

def canonicalOrbit (actions : Array Action) (core : List Nat) : OrbitImage := Id.run do
  let mut result := { core := canonical core, action := Action.identity }
  for action in actions do
    let image := canonical (core.map fun vector => fastCombine action.coreColumns vector)
    if compare image result.core == Ordering.lt then
      result := ⟨image, action⟩
  return result

structure PreparedAction where
  action : Action
  low : Array Nat
  high : Array Nat

def prepareAction (action : Action) : PreparedAction :=
  ⟨action, Array.ofFn (fun i : Fin 64 => fastCombine action.coreColumns i.val),
    Array.ofFn (fun i : Fin 64 => fastCombine action.coreColumns (64 * i.val))⟩

def PreparedAction.apply (action : PreparedAction) (vector : Nat) : Nat :=
  (action.low[vector % 64]?.getD 0) ^^^ (action.high[vector / 64]?.getD 0)

def canonicalOrbitPrepared (actions : Array PreparedAction) (core : List Nat) : OrbitImage := Id.run do
  let mut result := { core := canonical core, action := Action.identity }
  for action in actions do
    let image := canonical (core.map action.apply)
    if compare image result.core == Ordering.lt then
      result := ⟨image, action.action⟩
  return result

end Lemmata.CocubicCovering.Compute.CoreSearch
