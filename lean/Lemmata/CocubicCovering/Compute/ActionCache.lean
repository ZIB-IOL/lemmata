module

public import Lemmata.CocubicCovering.Compute.CoreOrbit
public meta import Lemmata.CocubicCovering.Compute.CoreOrbit
public import Lemmata.CocubicCovering.Proof.Word
public meta import Lemmata.CocubicCovering.Proof.Word
public import Lemmata.CocubicCovering.Proof.LevelSixCoreData
public meta import Lemmata.CocubicCovering.Proof.LevelSixCoreData

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.Compute.ActionCache

open Lemmata.CocubicCovering

structure Verified (action : CoreSearch.Action) : Type where
  core_valid : ∀ i : Fin 12,
    action.coreColumn i = CoveringWord.applyMask action.word (2 ^ i.val)
  local_valid : ∀ i : Fin 15,
    action.localColumn i = CoveringLevelSixCoreData.applyLocalWord action.word (2 ^ i.val)

def verify (action : CoreSearch.Action) : Option (Verified action) :=
  if hcore : ∀ i : Fin 12,
      action.coreColumn i = CoveringWord.applyMask action.word (2 ^ i.val) then
    if hlocal : ∀ i : Fin 15,
        action.localColumn i = CoveringLevelSixCoreData.applyLocalWord action.word (2 ^ i.val) then
      some ⟨hcore, hlocal⟩
    else none
  else none

structure Cached where
  action : CoreSearch.Action
  checked : Thunk (Option (Verified action))

def cache (action : CoreSearch.Action) : Cached :=
  ⟨action, ⟨fun _ => verify action⟩⟩

structure Prepared where
  prepared : CoreSearch.PreparedAction
  checked : Thunk (Option (Verified prepared.action))

def prepare (action : CoreSearch.Action) : Prepared :=
  ⟨CoreSearch.prepareAction action, ⟨fun _ => verify action⟩⟩

def identity : Thunk Prepared :=
  ⟨fun _ => prepare CoreSearch.Action.identity⟩

structure Image where
  core : List Nat
  cached : Prepared

def canonicalOrbit (actions : Array Prepared) (core : List Nat) : Image := Id.run do
  let mut result : Image := ⟨CoreSearch.canonical core, CoreSearch.force identity⟩
  for action in actions do
    let image := CoreSearch.canonical (core.map action.prepared.apply)
    if compare image result.core == Ordering.lt then
      result := ⟨image, action⟩
  return result

end Lemmata.CocubicCovering.Compute.ActionCache
