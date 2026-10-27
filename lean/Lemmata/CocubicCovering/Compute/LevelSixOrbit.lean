module

public import Lemmata.CocubicCovering.Compute.LevelSixTransport
public meta import Lemmata.CocubicCovering.Compute.LevelSixTransport
public import Lemmata.CocubicCovering.Compute.LevelSixTerminal
public meta import Lemmata.CocubicCovering.Compute.LevelSixTerminal
public import Lemmata.CocubicCovering.Compute.LevelSixRows
public meta import Lemmata.CocubicCovering.Compute.LevelSixRows

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.Compute.LevelSixModel

open Lemmata.CocubicCovering
open CoveringLevelSixReconstruction CoveringSystemGeometryData

def generators : CoreSearch.Generators := CommonModel.generators

def actions : Thunk (Array CoreSearch.Action) := CommonModel.actions

def stabilizers : Thunk (Array (Array ActionCache.Prepared)) :=
  ⟨fun _ => Array.ofFn fun root : Fin 30 =>
    (CoreSearch.force CommonModel.cachedActions).filter fun action =>
      CoreSearch.fastCombine action.prepared.action.localColumns (roots root.val).assignment ==
        (roots root.val).assignment⟩

def normalize (state : CoreSearch.State) : Option (CoreSearch.Normalized model state) := do
  let candidates := (CoreSearch.force stabilizers)[state.root % 30]?.getD #[]
  let image := ActionCache.canonicalOrbit candidates state.core
  let checked ← CoreSearch.force image.cached.checked
  let target : CoreSearch.State := ⟨state.root, image.core⟩
  let transport ← checkedTransport image.cached.prepared.action checked state target
  return ⟨target, transport.valid⟩

def profileState (profile : Fin 13) : CoreSearch.State :=
  let root := ((List.range 30).find? fun root =>
    (roots root).assignment == restriction profile &&
      (roots root).required == coreCount profile).getD 0
  ⟨root, core profile⟩

abbrev TerminalKey := Nat × Nat × List Nat

structure TerminalImage where
  profile : Fin 13
  forwardIndex : Nat

def terminalProfiles (root : Fin 30) : List (Fin 13) :=
  (List.finRange 13).filter fun profile =>
    coreCount profile == (roots root.val).required

def terminalTableFor (root : Fin 30) : Std.HashMap TerminalKey TerminalImage := Id.run do
  let profiles := terminalProfiles root
  if profiles.isEmpty then return ∅
  let actions := CoreSearch.force actions
  let assignment := (roots root.val).assignment
  let required := (roots root.val).required
  let mut result := Std.HashMap.emptyWithCapacity 128
  for profile in profiles do
    for index in [:actions.size] do
      if let some action := actions[index]? then
        if CoreSearch.fastCombine action.localColumns (restriction profile) == assignment then
          let image := CoreSearch.canonical ((core profile).map
            (CoreSearch.fastCombine action.coreColumns))
          let key : TerminalKey := (assignment, required, image)
          if !result.contains key then
            result := result.insert key ⟨profile, index⟩
  return result

def terminalTables : Thunk (Array (Thunk (Std.HashMap TerminalKey TerminalImage))) :=
  ⟨fun _ => Array.ofFn fun root : Fin 30 => ⟨fun _ => terminalTableFor root⟩⟩

def inverseAction (action : CoreSearch.Action) : CoreSearch.Action :=
  (CoreSearch.inverseWord action.word).foldl
    (fun previous generator => previous.next generators generator) CoreSearch.Action.identity

def inverseActions : Thunk (Array (Thunk ActionCache.Cached)) :=
  ⟨fun _ => (CoreSearch.force actions).map fun action =>
    ⟨fun _ => ActionCache.cache (inverseAction action)⟩⟩

def orbitTerminal (state : CoreSearch.State) : Option (CoreSearch.Closed model state) := do
  let table ← (CoreSearch.force terminalTables)[state.root % 30]?
  let key : TerminalKey :=
    ((roots state.root).assignment, (roots state.root).required, CoreSearch.canonical state.core)
  let image ← (CoreSearch.force table)[key]?
  let inverse ← (CoreSearch.force inverseActions)[image.forwardIndex]?
  let inverse := CoreSearch.force inverse
  let checked ← CoreSearch.force inverse.checked
  let target := profileState image.profile
  let transport ← checkedTransport inverse.action checked state target
  let closed ← terminal target
  return ⟨fun possible => closed.valid (transport.valid possible)⟩

namespace OrbitMemo

structure Key where
  root : Nat
  bits : Nat
  deriving BEq

instance : Hashable Key where
  hash key := mixHash (hash key.root)
    (mixHash (UInt64.ofNat key.bits)
      (mixHash (UInt64.ofNat (key.bits >>> 64)) (UInt64.ofNat (key.bits >>> 128))))

def key (root : Nat) (core : List Nat) : Key :=
  ⟨root, core.foldl (fun bits row => (bits <<< 12) ||| row) 0⟩

structure Hint where
  target : CoreSearch.State
  action : Thunk (Option ActionCache.Prepared)

abbrev Alias := Std.HashMap Key Hint

def initial : Alias := ∅

def groupIndex : Thunk (Std.HashMap (List Nat × List Nat) (Nat × ActionCache.Prepared)) :=
  ⟨fun _ => Id.run do
    let actions := CoreSearch.force CommonModel.cachedActions
    let mut result := Std.HashMap.emptyWithCapacity actions.size
    for index in [:actions.size] do
      if let some action := actions[index]? then
        result := result.insert action.prepared.action.key (index, action)
    return result⟩

@[noinline, never_extract]
def stored (fromAction toAction : ActionCache.Prepared) (target : CoreSearch.State) : Hint :=
  ⟨target, ⟨fun _ => do
    let index := CoreSearch.force groupIndex
    let fromEntry ← index[fromAction.prepared.action.key]?
    let inverse ← (CoreSearch.force inverseActions)[fromEntry.1]?
    let inverse := (CoreSearch.force inverse).action
    let coreColumns := inverse.coreColumns.map toAction.prepared.apply
    let localColumns := inverse.localColumns.map
      (CoreSearch.fastCombine toAction.prepared.action.localColumns)
    let selected ← index[(coreColumns, localColumns)]?
    return selected.2⟩⟩

def lookup (aliases : Alias) {state : CoreSearch.State}
    (base : CoreSearch.Normalized model state) : Option (CoreSearch.Normalized model state) := do
  let hint ← aliases[key base.state'.root base.state'.core]?
  let selected ← CoreSearch.force hint.action
  let validAction ← CoreSearch.force selected.checked
  let transport ← checkedTransport selected.prepared.action validAction base.state' hint.target
  return ⟨hint.target, fun possible => transport.valid (base.valid possible)⟩

def normalizeWith (capacity : Nat) (aliases : Alias) (state : CoreSearch.State) :
    Alias × Option (CoreSearch.Normalized model state) := Id.run do
  if capacity == 0 then return (aliases, normalize state)
  let some base := CoreSearch.normalize model state | return (aliases, none)
  if let some answer := lookup aliases base then return (aliases, some answer)
  let origin := base.state'
  let candidates := (CoreSearch.force stabilizers)[origin.root % 30]?.getD #[]
  let identity := CoreSearch.force ActionCache.identity
  let mut selected : ActionCache.Image := ⟨origin.core, identity⟩
  let mut images : Array ActionCache.Image := #[selected]
  for action in candidates do
    let image := CoreSearch.canonical (origin.core.map action.prepared.apply)
    images := images.push ⟨image, action⟩
    if compare image selected.core == Ordering.lt then
      selected := ⟨image, action⟩
  let target : CoreSearch.State := ⟨origin.root, selected.core⟩
  let some validAction := CoreSearch.force selected.cached.checked | return (aliases, none)
  let some transport := checkedTransport selected.cached.prepared.action validAction origin target
    | return (aliases, none)
  let answer : CoreSearch.Normalized model state :=
    ⟨target, fun possible => transport.valid (base.valid possible)⟩
  let mut aliases := if aliases.size + images.size > capacity then ∅ else aliases
  for image in images do
    if aliases.size < capacity then
      let source := key origin.root image.core
      if !aliases.contains source then
        aliases := aliases.insert source (stored image.cached selected.cached target)
  return (aliases, some answer)

def normalizeMemo : Alias → (state : CoreSearch.State) →
    Alias × Option (CoreSearch.Normalized model state) := normalizeWith 8000000

end OrbitMemo

def orbitChecked (root : Fin 21) : Bool :=
  CoreIncremental.refutesWith model LevelSixRows.source CoreIncremental.branch
    orbitTerminal OrbitMemo.normalizeMemo OrbitMemo.initial 32 ⟨root.val, []⟩

theorem orbitExcludes (root : Fin 21) (checked : orbitChecked root = true) :
    ¬CoreSearch.Feasible model ⟨root.val, []⟩ :=
  CoreIncremental.refutesWith_sound model LevelSixRows.source CoreIncremental.branch
    orbitTerminal OrbitMemo.normalizeMemo OrbitMemo.initial 32 ⟨root.val, []⟩ checked

end Lemmata.CocubicCovering.Compute.LevelSixModel
