module

public import Lemmata.CocubicCovering.Compute.LevelSixModel
public meta import Lemmata.CocubicCovering.Compute.LevelSixModel
public import Lemmata.CocubicCovering.Compute.KernelRows
public meta import Lemmata.CocubicCovering.Compute.KernelRows
public import Lemmata.CocubicCovering.Compute.CoreIncremental
public meta import Lemmata.CocubicCovering.Compute.CoreIncremental

@[expose] public section

namespace Lemmata.CocubicCovering.Compute.LevelSixRows

open KernelRows

def table : Thunk (Array (CachedRows 27 CoveringLevelSixLeaf.kernelRow)) :=
  ⟨fun _ => makeRowTable CoveringLevelSixLeaf.kernelRow 4096⟩

def sourceRow (root : Nat) (core : List Nat) (source : Nat) : Nat :=
  if source < 15 then
    (2 ^ (111 + source)) ^^^ (if root.testBit source then 2 ^ 126 else 0)
  else
    match core[(source - 15) / 27]? with
    | none => 0
    | some mask => cachedRow table mask ⟨(source - 15) % 27, Nat.mod_lt _ (by decide)⟩

theorem sourceRow_eq (root : Nat) (core : List Nat) (source : Nat) :
    sourceRow root core source = CoveringLevelSixLeaf.sourceRow root core source := by
  by_cases hs : source < 15
  · simp only [sourceRow, CoveringLevelSixLeaf.sourceRow, if_pos hs]
  · simp only [sourceRow, CoveringLevelSixLeaf.sourceRow, if_neg hs]
    cases hentry : core[(source - 15) / 27]? with
    | none => simp only [hentry]
    | some mask =>
        simpa only [hentry] using
          (cachedRow_eq table mask (⟨(source - 15) % 27, Nat.mod_lt _ (by decide)⟩ : Fin 27))

def sourceRows (state : CoreSearch.State) : List Nat :=
  (List.range (15 + 27 * state.core.length)).map
    (sourceRow (LevelSixModel.roots state.root).assignment state.core)

theorem sourceRows_eq (state : CoreSearch.State) :
    sourceRows state = LevelSixModel.sourceRows state := by
  unfold sourceRows LevelSixModel.sourceRows
  apply congrArg (fun f => List.map f (List.range (15 + 27 * state.core.length)))
  funext source
  exact sourceRow_eq _ _ _

def size (state : CoreSearch.State) : Nat :=
  15 + 27 * state.core.length

def rowsFrom (state : CoreSearch.State) (skip : Nat) : List Nat :=
  (List.range (size state - skip)).map fun offset =>
    sourceRow (LevelSixModel.roots state.root).assignment state.core (skip + offset)

theorem rowsFrom_mem (state : CoreSearch.State) (skip row : Nat)
    (hrow : row ∈ rowsFrom state skip) : row ∈ sourceRows state := by
  obtain ⟨offset, hoffset, rfl⟩ := List.mem_map.mp hrow
  apply List.mem_map.mpr
  refine ⟨skip + offset, List.mem_range.mpr ?_, rfl⟩
  have hbound := List.mem_range.mp hoffset
  unfold size at hbound
  omega

theorem rowsFrom_mem_original (state : CoreSearch.State) (skip row : Nat)
    (hrow : row ∈ rowsFrom state skip) : row ∈ LevelSixModel.model.sourceRows state := by
  have h := rowsFrom_mem state skip row hrow
  rw [sourceRows_eq] at h
  exact h

def source : CoreIncremental.RowsFrom LevelSixModel.model where
  size := LevelSixRows.size
  rows := LevelSixRows.rowsFrom
  valid := LevelSixRows.rowsFrom_mem_original

end Lemmata.CocubicCovering.Compute.LevelSixRows
