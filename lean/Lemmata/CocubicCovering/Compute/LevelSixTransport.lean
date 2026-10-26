module

public import Lemmata.CocubicCovering.Compute.LevelSixModel
public meta import Lemmata.CocubicCovering.Compute.LevelSixModel
public import Lemmata.CocubicCovering.Compute.CommonOrbit
public meta import Lemmata.CocubicCovering.Compute.CommonOrbit
public import Lemmata.CocubicCovering.Compute.CoreOrbit
public meta import Lemmata.CocubicCovering.Compute.CoreOrbit

@[expose] public section

namespace Lemmata.CocubicCovering.Compute.LevelSixModel

open Lemmata.CocubicCovering
open CoveringAffine CoveringBits CoveringWitness CoveringPackedWitness

structure Transport (source target : CoreSearch.State) : Type where
  valid : CoreSearch.Feasible model source → CoreSearch.Feasible model target

def checkedTransport (action : CoreSearch.Action) (source target : CoreSearch.State) :
    Option (Transport source target) := do
  if hcore : ∀ i : Fin 12, action.coreColumn i = CoveringWord.applyMask action.word (2 ^ i.val) then
    if hlocal : ∀ i : Fin 15, action.localColumn i =
        CoveringLevelSixCoreData.applyLocalWord action.word (2 ^ i.val) then
      if hassignment : CoveringAffine.composeRow (roots source.root).assignment action.localColumn =
          (roots target.root).assignment then
        if hdimension : (roots source.root).required = (roots target.root).required then
          let image := source.core.map fun mask => CoveringAffine.composeRow mask action.coreColumn
          let coefficients ← CoreSearch.coefficients target.core image
          if hspan : Certificate.CoreCertificate.listCheckSpan target.core image coefficients = true then
            have ha : ∀ mask, CoveringWord.action action.word (decodeMask mask) =
                (decodeMask (CoveringAffine.composeRow mask action.coreColumn) : Vector 12) :=
              CoveringWord.action_columns action.word action.coreColumn hcore
            have hs := Certificate.CoreCertificate.listCheckSpan_eq target.core image coefficients
            have hspan' : CoveringPackedWitness.listCheckSpan target.core image coefficients = true := by
              rw [← hs]
              exact hspan
            have hle := CoveringPackedWitness.listCheckSpan_sound 12 target.core image coefficients hspan'
            have himage := Lemmata.CocubicCovering.Compute.CommonModel.image_span_le action.coreColumn source.core
              (CoveringWord.action action.word) ha
            return ⟨by
              apply CoveringSearch.transport (allowed source.root) (allowed target.root) kernel kernel
                (decoded source.core.get) (decoded target.core.get)
                (CoveringLevelSixSymmetry.move action.word) (CoveringWord.action action.word)
                ?_ (fun v _ => CoveringLevelSixSymmetry.word_kernel_transport action.word v)
                (hle.trans himage)
              intro v hv
              apply CoveringLevelSixProblem.allowed_transform action.word
                (Fin.ofNat 30 source.root) (Fin.ofNat 30 target.root) ?_ hdimension v hv
              have he := funext hlocal
              rw [← he]
              exact hassignment⟩
          else return ← none
        else return ← none
      else return ← none
    else return ← none
  else return ← none

end Lemmata.CocubicCovering.Compute.LevelSixModel
