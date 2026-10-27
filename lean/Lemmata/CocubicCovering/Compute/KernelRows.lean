module

public import Lemmata.CocubicCovering.Compute.CoreOrbit
public meta import Lemmata.CocubicCovering.Compute.CoreOrbit

@[expose] public section

namespace Lemmata.CocubicCovering.Compute.KernelRows

structure CachedRows (width : Nat) (row : Nat → Fin width → Nat) where
  mask : Nat
  values : Array Nat
  valid : ∀ column : Fin width, (values[column.val]?).getD 0 = row mask column

def makeCachedRows {width : Nat} (row : Nat → Fin width → Nat) (mask : Nat) :
    CachedRows width row :=
  ⟨mask, Array.ofFn (row mask), by
    intro column
    simp [Array.getElem?_ofFn, column.isLt]⟩

@[noinline, never_extract]
def makeRowTable {width : Nat} (row : Nat → Fin width → Nat) (bound : Nat) :
    Array (CachedRows width row) :=
  Array.ofFn fun mask : Fin bound => makeCachedRows row mask.val

def cachedRow {width : Nat} {row : Nat → Fin width → Nat}
    (table : Thunk (Array (CachedRows width row))) (mask : Nat) (column : Fin width) : Nat :=
  match (CoreSearch.force table)[mask]? with
  | none => row mask column
  | some entry =>
      if entry.mask = mask then (entry.values[column.val]?).getD 0 else row mask column

theorem cachedRow_eq {width : Nat} {row : Nat → Fin width → Nat}
    (table : Thunk (Array (CachedRows width row))) (mask : Nat) (column : Fin width) :
    cachedRow table mask column = row mask column := by
  unfold cachedRow
  split
  · rfl
  · rename_i entry _
    split
    · rename_i h
      simpa only [h] using entry.valid column
    · rfl

end Lemmata.CocubicCovering.Compute.KernelRows
