module

public import Lemmata.CocubicCovering.Compute.CoreSearchSound
public meta import Lemmata.CocubicCovering.Compute.CoreSearchSound
public import Lemmata.CocubicCovering.Proof.Word
public meta import Lemmata.CocubicCovering.Proof.Word
public import Lemmata.CocubicCovering.Proof.LocalRanks
public meta import Lemmata.CocubicCovering.Proof.LocalRanks
public import Lemmata.CocubicCovering.Proof.PackedLeaf
public meta import Lemmata.CocubicCovering.Proof.PackedLeaf

@[expose] public section

namespace Lemmata.CocubicCovering.Compute.CommonModel

open Lemmata.CocubicCovering
open Module CoveringAffine CoveringBits CoveringWitness CoveringPackedWitness
open CoveringCongruence CoveringCovarianceData CoveringLocal CoveringSymmetry

def rootData (i : Fin 6) : CoreSearch.Root :=
  (#[
    ⟨0, [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048], 8⟩,
    ⟨1, [1, 2, 4, 8, 16, 32], 5⟩,
    ⟨8, [1, 2, 8, 64, 512, 1024], 5⟩,
    ⟨80, [1, 8, 272, 512], 4⟩,
    ⟨88, [1, 8, 496, 512], 4⟩,
    ⟨1400, [392, 272, 160, 320], 4⟩
  ][i.val]?).getD ⟨0, [], 0⟩

def roots (root : Nat) : CoreSearch.Root := rootData (Fin.ofNat 6 root)

theorem roots_val (root : Fin 6) : roots root.val = rootData root := by
  unfold roots
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt root.isLt)

def kernel (v : Vector 127) : Submodule Field (Vector 12) := fullKernel (fullForm v)

def allowed (root : Nat) (v : Vector 127) : Prop :=
  v (Fin.last 126) = 1 ∧
    localParameterProjection v = (decodeMask (roots root).assignment : Vector 15) ∧
    (roots root).required ≤ finrank Field (kernel v)

private theorem projection_rows : CoveringLocalRanks.localParameterRows = projectionRows := by
  native_decide

private theorem radical_family0 :
    (decoded (n := 12) (listColumns (rootData 0).radical) : Fin 12 → Vector 12) =
      CoveringLocalRanks.radical0 := by native_decide

private theorem radical_family1 :
    (decoded (n := 12) (listColumns (rootData 1).radical) : Fin 6 → Vector 12) =
      CoveringLocalRanks.radical1 := by native_decide

private theorem radical_family2 :
    (decoded (n := 12) (listColumns (rootData 2).radical) : Fin 6 → Vector 12) =
      CoveringLocalRanks.radical8 := by native_decide

private theorem radical_family3 :
    (decoded (n := 12) (listColumns (rootData 3).radical) : Fin 4 → Vector 12) =
      CoveringLocalRanks.radical80 := by native_decide

private theorem radical_family4 :
    (decoded (n := 12) (listColumns (rootData 4).radical) : Fin 4 → Vector 12) =
      CoveringLocalRanks.radical88 := by native_decide

private theorem radical_family5 :
    (decoded (n := 12) (listColumns (rootData 5).radical) : Fin 4 → Vector 12) =
      CoveringLocalRanks.radical1400 := by native_decide

theorem local_radical (root : Fin 6) (v : Vector 127)
    (hp : localParameterProjection v = (decodeMask (rootData root).assignment : Vector 15)) :
    localRadical (fullForm v) =
      familySpan (decoded (n := 12) (listColumns (rootData root).radical)) := by
  have hprojection : rowMap CoveringLocalRanks.localParameterRows v =
      (decodeMask (rootData root).assignment : Vector 15) := by
    rw [projection_rows]
    exact hp
  fin_cases root
  · change localRadical (fullForm v) = familySpan
      (decoded (n := 12) (listColumns (rootData 0).radical) : Fin 12 → Vector 12)
    rw [radical_family0]
    exact CoveringLocalRanks.localRadical_root0 v hprojection
  · change localRadical (fullForm v) = familySpan
      (decoded (n := 12) (listColumns (rootData 1).radical) : Fin 6 → Vector 12)
    rw [radical_family1]
    exact CoveringLocalRanks.localRadical_root1 v hprojection
  · change localRadical (fullForm v) = familySpan
      (decoded (n := 12) (listColumns (rootData 2).radical) : Fin 6 → Vector 12)
    rw [radical_family2]
    exact CoveringLocalRanks.localRadical_root8 v hprojection
  · change localRadical (fullForm v) = familySpan
      (decoded (n := 12) (listColumns (rootData 3).radical) : Fin 4 → Vector 12)
    rw [radical_family3]
    exact CoveringLocalRanks.localRadical_root80 v hprojection
  · change localRadical (fullForm v) = familySpan
      (decoded (n := 12) (listColumns (rootData 4).radical) : Fin 4 → Vector 12)
    rw [radical_family4]
    exact CoveringLocalRanks.localRadical_root88 v hprojection
  · change localRadical (fullForm v) = familySpan
      (decoded (n := 12) (listColumns (rootData 5).radical) : Fin 4 → Vector 12)
    rw [radical_family5]
    exact CoveringLocalRanks.localRadical_root1400 v hprojection

theorem kernel_ambient (root : Nat) (v : Vector 127) (hv : allowed root v) :
    kernel v ≤ familySpan (decoded (n := 12) (roots root).radical.get) := by
  have hlocal := local_radical (Fin.ofNat 6 root) v hv.2.1
  have hle := fullKernel_le_localRadical (fullForm v)
  rw [hlocal] at hle
  exact hle

theorem allowed_coordinates (root : Nat) (v : Vector 127) (hv : allowed root v)
    (i : Fin 15) : v ⟨111 + i.val, by omega⟩ =
      CoveringPolynomial.ofBool ((roots root).assignment.testBit i.val) := by
  have hi := congrFun hv.2.1 i
  have he : localParameterProjection v i = v ⟨111 + i.val, by omega⟩ :=
    CoveringEncoding.evalRow_two_pow ⟨111 + i.val, by omega⟩ v
  exact he.symm.trans hi

def sourceRows (state : CoreSearch.State) : List Nat :=
  (List.range (15 + 24 * state.core.length)).map
    (CoveringPackedLeaf.sourceRow (roots state.root).assignment state.core)

theorem sourceRows_sound (state : CoreSearch.State) (row : Nat) (hrow : row ∈ sourceRows state)
    (v : Vector 127) (hv : allowed state.root v)
    (hc : familySpan (decoded (n := 12) state.core.get) ≤ kernel v) :
    evalRow row v = 0 := by
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp hrow
  apply CoveringPackedLeaf.sourceRow_zero _ _ v hv.1 (allowed_coordinates state.root v hv)
  intro mask hmask column
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmask
  have hk : (decodeMask mask : Vector 12) ∈ kernel v := by
    rw [← hi]
    exact hc (Submodule.subset_span ⟨i, rfl⟩)
  exact evalRow_local_kernel_eq_zero matrixRows v mask hk column

def model : CoreSearch.Model where
  roots := roots
  allowed := allowed
  kernel := kernel
  kernel_ambient := kernel_ambient
  kernel_dimension _ _ hv := hv.2.2
  point _ _ hv := hv.1
  sourceRows := sourceRows
  sourceRows_sound := sourceRows_sound

def checked (root : Fin 6) : Bool :=
  CoreSearch.refutes model (fun _ => none) 32 ⟨root.val, []⟩

theorem excludes (root : Fin 6) (h : checked root = true) :
    ¬CoreSearch.Feasible model ⟨root.val, []⟩ :=
  CoreSearch.refutes_sound model (fun _ => none) 32 ⟨root.val, []⟩ h

end Lemmata.CocubicCovering.Compute.CommonModel
