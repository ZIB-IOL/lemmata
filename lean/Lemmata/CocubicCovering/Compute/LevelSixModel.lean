module

public import Lemmata.CocubicCovering.Compute.CoreSearchSound
public meta import Lemmata.CocubicCovering.Compute.CoreSearchSound
public import Lemmata.CocubicCovering.Compute.Terminal
public meta import Lemmata.CocubicCovering.Compute.Terminal
public import Lemmata.CocubicCovering.Proof.LevelSixProblem
public meta import Lemmata.CocubicCovering.Proof.LevelSixProblem
public import Lemmata.CocubicCovering.Proof.LevelSixRootRanks
public meta import Lemmata.CocubicCovering.Proof.LevelSixRootRanks
public import Lemmata.CocubicCovering.Proof.LevelSixLeaf
public meta import Lemmata.CocubicCovering.Proof.LevelSixLeaf

@[expose] public section

namespace Lemmata.CocubicCovering.Compute.LevelSixModel

open Lemmata.CocubicCovering
open Module CoveringAffine CoveringBits CoveringWitness CoveringPackedWitness

def roots (root : Nat) : CoreSearch.Root :=
  let r := CoveringLevelSixCoreData.roots (Fin.ofNat 30 root)
  ⟨r.assignment, r.radical, r.required⟩

def allowed (root : Nat) (v : Vector 127) : Prop :=
  CoveringLevelSixProblem.allowed (Fin.ofNat 30 root) v ∧ Terminal.SystemsInconsistent

def kernel (v : Vector 127) : Submodule Field (Vector 12) :=
  CoveringLevelSixReduction.fullKernel v

theorem kernel_ambient (root : Nat) (v : Vector 127) (hv : allowed root v) :
    kernel v ≤ familySpan (decoded (n := 12) (roots root).radical.get) :=
  CoveringLevelSixRootRanks.fullKernel_le_radical (Fin.ofNat 30 root) v hv.1.2.1

def sourceRows (state : CoreSearch.State) : List Nat :=
  (List.range (15 + 27 * state.core.length)).map
    (CoveringLevelSixLeaf.sourceRow (roots state.root).assignment state.core)

theorem sourceRows_sound (state : CoreSearch.State) (row : Nat) (hrow : row ∈ sourceRows state)
    (v : Vector 127) (hv : allowed state.root v)
    (hc : familySpan (decoded (n := 12) state.core.get) ≤ kernel v) :
    evalRow row v = 0 := by
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp hrow
  apply CoveringLevelSixLeaf.sourceRow_zero _ _ v hv.1.1
    (CoveringLevelSixProblem.allowed_coordinates (Fin.ofNat 30 state.root) v hv.1)
  intro mask hmask column
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmask
  have hk : (decodeMask mask : Vector 12) ∈ kernel v := by
    rw [← hi]
    exact hc (Submodule.subset_span ⟨i, rfl⟩)
  exact CoveringLevelSixLeaf.kernelRow_zero v mask hk column

def model : CoreSearch.Model where
  roots := roots
  allowed := allowed
  kernel := kernel
  kernel_ambient := kernel_ambient
  kernel_dimension _ _ hv := hv.1.2.2.1.ge
  point _ _ hv := hv.1.1
  sourceRows := sourceRows
  sourceRows_sound := sourceRows_sound

end Lemmata.CocubicCovering.Compute.LevelSixModel
