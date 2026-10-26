module

public import Lemmata.CocubicCovering.Compute.LevelSixTransport
public meta import Lemmata.CocubicCovering.Compute.LevelSixTransport
public import Lemmata.CocubicCovering.Compute.LevelSixTerminal
public meta import Lemmata.CocubicCovering.Compute.LevelSixTerminal

@[expose] public section

namespace Lemmata.CocubicCovering.Compute.LevelSixModel

open Lemmata.CocubicCovering
open CoveringLevelSixReconstruction CoveringSystemGeometryData

def generators : CoreSearch.Generators := CommonModel.generators

def actions : Thunk (Array CoreSearch.Action) := CommonModel.actions

def stabilizers : Thunk (Array (Array CoreSearch.PreparedAction)) :=
  ⟨fun _ => Array.ofFn fun root : Fin 30 =>
    (CoreSearch.force CommonModel.preparedActions).filter fun action =>
      CoreSearch.fastCombine action.action.localColumns (roots root.val).assignment ==
        (roots root.val).assignment⟩

def normalize (state : CoreSearch.State) : Option (CoreSearch.Normalized model state) := do
  let candidates := (CoreSearch.force stabilizers)[state.root % 30]?.getD #[]
  let image := CoreSearch.canonicalOrbitPrepared candidates state.core
  let target : CoreSearch.State := ⟨state.root, image.core⟩
  let transport ← checkedTransport image.action state target
  return ⟨target, transport.valid⟩

def profileState (profile : Fin 13) : CoreSearch.State :=
  let root := ((List.range 30).find? fun root =>
    (roots root).assignment == restriction profile &&
      (roots root).required == coreCount profile).getD 0
  ⟨root, core profile⟩

def inverseActions : Thunk (Array CoreSearch.Action) :=
  ⟨fun _ => (CoreSearch.force actions).map fun action =>
    (CoreSearch.inverseWord action.word).foldl
      (fun previous generator => previous.next generators generator) CoreSearch.Action.identity⟩

structure TerminalImage where
  profile : Fin 13
  inverse : CoreSearch.Action

abbrev TerminalKey := Nat × Nat × List Nat

def terminalImages : Thunk (Std.HashMap TerminalKey TerminalImage) := ⟨fun _ => Id.run do
  let actions := CoreSearch.force actions
  let inverseActions := CoreSearch.force inverseActions
  let mut result := Std.HashMap.emptyWithCapacity (13 * actions.size)
  for profile in List.finRange 13 do
    for index in [:actions.size] do
      let action := actions[index]?.getD CoreSearch.Action.identity
      let assignment := CoreSearch.fastCombine action.localColumns (restriction profile)
      let image := CoreSearch.canonical ((core profile).map
        (CoreSearch.fastCombine action.coreColumns))
      let key : TerminalKey := (assignment, coreCount profile, image)
      if !result.contains key then
        let inverse := inverseActions[index]?.getD CoreSearch.Action.identity
        result := result.insert key ⟨profile, inverse⟩
  return result⟩

def orbitTerminal (state : CoreSearch.State) : Option (CoreSearch.Closed model state) := do
  let key : TerminalKey :=
    ((roots state.root).assignment, (roots state.root).required, CoreSearch.canonical state.core)
  let image ← (CoreSearch.force terminalImages)[key]?
  let target := profileState image.profile
  let transport ← checkedTransport image.inverse state target
  let closed ← terminal target
  return ⟨fun possible => closed.valid (transport.valid possible)⟩

def orbitChecked (root : Fin 21) : Bool :=
  CoreSearch.refutesWith model orbitTerminal normalize 32 ⟨root.val, []⟩

theorem orbitExcludes (root : Fin 21) (checked : orbitChecked root = true) :
    ¬CoreSearch.Feasible model ⟨root.val, []⟩ :=
  CoreSearch.refutesWith_sound model orbitTerminal normalize 32 ⟨root.val, []⟩ checked

end Lemmata.CocubicCovering.Compute.LevelSixModel
