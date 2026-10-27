module

public import Lemmata.CocubicCovering.Compute.CommonModel
public meta import Lemmata.CocubicCovering.Compute.CommonModel
public import Lemmata.CocubicCovering.Compute.CoreOrbit
public meta import Lemmata.CocubicCovering.Compute.CoreOrbit
public import Lemmata.CocubicCovering.Proof.LevelSixCoreData
public meta import Lemmata.CocubicCovering.Proof.LevelSixCoreData

public import Lemmata.CocubicCovering.Compute.ActionCache
public meta import Lemmata.CocubicCovering.Compute.ActionCache

@[expose] public section

namespace Lemmata.CocubicCovering.Compute.CommonModel

open Lemmata.CocubicCovering
open CoveringAffine CoveringBits CoveringWitness CoveringPackedWitness
open CoveringSymmetry CoveringLocal

def generators : CoreSearch.Generators where
  coreColumns := unitCoreColumns
  localColumns := CoveringLevelSixCoreData.elementaryLocalColumns

def actions : Thunk (Array CoreSearch.Action) :=
  ⟨fun _ => CoreSearch.group generators 50000⟩

def preparedActions : Thunk (Array CoreSearch.PreparedAction) :=
  ⟨fun _ => (CoreSearch.force actions).map CoreSearch.prepareAction⟩

def cachedActions : Thunk (Array ActionCache.Prepared) :=
  ⟨fun _ => (CoreSearch.force actions).map ActionCache.prepare⟩

theorem action_injective (steps : List (Fin 8)) :
    Function.Injective (CoveringWord.action steps) := by
  induction steps with
  | nil => exact Function.injective_id
  | cons step rest ih => exact ih.comp (unitAction_injective step)

theorem allowed_move (steps : List (Fin 8)) (root : Nat)
    (guard : (roots root).assignment = 0 ∨ steps = []) (v : Vector 127)
    (hv : allowed root v) : allowed root (CoveringWord.move steps v) := by
  refine ⟨(CoveringWord.move_last steps v).trans hv.1, ?_, ?_⟩
  · rcases guard with hzero | rfl
    · have hp : localParameterProjection v = 0 := by
        have hprojection := hv.2.1
        rw [hzero, decodeMask_zero] at hprojection
        exact hprojection
      rw [CoveringWord.move_zero_projection steps v hp, hzero, decodeMask_zero]
    · exact hv.2.1
  · have he := (Submodule.equivMapOfInjective (CoveringWord.action steps)
        (action_injective steps) (kernel v)).finrank_eq
    have hm := Submodule.finrank_mono (CoveringWord.kernel_transport steps v)
    exact hv.2.2.trans (he.le.trans hm)

theorem image_span_le (columns : Fin 12 → Nat) (core : List Nat)
    (action : Vector 12 →ₗ[Field] Vector 12)
    (ha : ∀ mask, action (decodeMask mask) =
      (decodeMask (CoveringAffine.composeRow mask columns) : Vector 12)) :
    familySpan (decoded (n := 12) (core.map fun mask => CoveringAffine.composeRow mask columns).get) ≤
      (familySpan (decoded (n := 12) core.get)).map action := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have hi := List.get_mem (core.map fun mask => CoveringAffine.composeRow mask columns) i
  obtain ⟨mask, hmask, he⟩ := List.mem_map.mp hi
  refine ⟨decodeMask mask, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hmask
    rw [← hj]
    exact Submodule.subset_span ⟨j, rfl⟩
  · exact (ha mask).trans (congrArg (decodeMask (n := 12)) he)

def normalize (group : Array CoreSearch.PreparedAction) (state : CoreSearch.State) :
    Option (CoreSearch.Normalized model state) := do
  let image := CoreSearch.canonicalOrbitPrepared group state.core
  let columns : Fin 12 → Nat := fun i => image.action.coreColumns[i.val]?.getD 0
  if hguard : (roots state.root).assignment = 0 ∨ image.action.word = [] then
    if hcolumns : ∀ i : Fin 12, columns i = CoveringWord.applyMask image.action.word (2 ^ i.val) then
      let source := state.core.map fun mask => CoveringAffine.composeRow mask columns
      let coefficients ← CoreSearch.coefficients image.core source
      if hspan : Certificate.CoreCertificate.listCheckSpan image.core source coefficients = true then
        have ha : ∀ mask, CoveringWord.action image.action.word (decodeMask mask) =
            (decodeMask (CoveringAffine.composeRow mask columns) : Vector 12) :=
          CoveringWord.action_columns _ columns hcolumns
        have hs := Certificate.CoreCertificate.listCheckSpan_eq image.core source coefficients
        have hspan' : CoveringPackedWitness.listCheckSpan image.core source coefficients = true := by
          rw [← hs]
          exact hspan
        have hle := CoveringPackedWitness.listCheckSpan_sound 12 image.core source coefficients hspan'
        have himage := image_span_le columns state.core
          (CoveringWord.action image.action.word) ha
        return ⟨⟨state.root, image.core⟩, by
          apply CoveringSearch.transport (allowed state.root) (allowed state.root) kernel kernel
            (decoded state.core.get) (decoded image.core.get)
            (CoveringWord.move image.action.word) (CoveringWord.action image.action.word)
            (fun v hv => allowed_move image.action.word state.root hguard v hv)
            (fun v _ => CoveringWord.kernel_transport image.action.word v)
          apply hle.trans
          exact himage⟩
      else return ← none
    else return ← none
  else return ← none

def normalizer (root : Fin 6) :
    (state : CoreSearch.State) → Option (CoreSearch.Normalized model state) :=
  if (rootData root).assignment == 0 then normalize (CoreSearch.force preparedActions)
  else CoreSearch.normalize model

def orbitChecked (root : Fin 6) : Bool :=
  CoreSearch.refutesWith model (fun _ => none) (normalizer root) 32 ⟨root.val, []⟩

theorem orbitExcludes (root : Fin 6) (h : orbitChecked root = true) :
    ¬CoreSearch.Feasible model ⟨root.val, []⟩ :=
  CoreSearch.refutesWith_sound model (fun _ => none) (normalizer root) 32 ⟨root.val, []⟩ h

end Lemmata.CocubicCovering.Compute.CommonModel
