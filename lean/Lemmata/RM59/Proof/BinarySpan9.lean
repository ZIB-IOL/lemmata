module

public import Lemmata.RM59.Proof.PackedLinear
public import Lemmata.RM59.Compute.SimplexSearch
public meta import Lemmata.RM59.Compute.SimplexSearch
public import Mathlib.LinearAlgebra.Span.Defs
public import Init.Data.Vector.Lemmas
public import Init.Data.Vector.OfFn

@[expose] public section

namespace Lemmata.RM59.BinarySpan9

open Packed

private theorem point_add_self (x : Point 9) : x + x = 0 := by
  funext i
  exact field_add_self _

theorem fold_mem (state : State) (U : Submodule Field (Point 9))
    (hrows : ∀ i, decodePoint (state.rows.get i) ∈ U)
    (positions : List (Fin 9)) (original initial : PackedPoint)
    (hinitial : decodePoint original + decodePoint initial ∈ U) :
    decodePoint original + decodePoint (positions.foldl (step state) initial) ∈ U := by
  induction positions generalizing initial with
  | nil => exact hinitial
  | cons i positions ih =>
    apply ih
    change decodePoint original + decodePoint (step state initial i) ∈ U
    unfold step
    split_ifs
    · change decodePoint original + decodePoint (xorPoint initial (state.rows.get i)) ∈ U
      rw [decodePoint_xorPoint, ← add_assoc]
      exact U.add_mem hinitial (hrows i)
    · exact hinitial

theorem reduce_add_mem (state : State) (U : Submodule Field (Point 9))
    (hrows : ∀ i, decodePoint (state.rows.get i) ∈ U) (value : PackedPoint) :
    decodePoint value + decodePoint (reduce state value) ∈ U :=
  fold_mem state U hrows indices value value (by rw [point_add_self]; exact U.zero_mem)

theorem mem_of_reduce_eq_zero (state : State) (U : Submodule Field (Point 9))
    (hrows : ∀ i, decodePoint (state.rows.get i) ∈ U) (value : PackedPoint)
    (hzero : reduce state value = 0) : decodePoint value ∈ U := by
  have h := reduce_add_mem state U hrows value
  simpa only [hzero, decodePoint_zero, add_zero] using h

theorem empty_rows_mem (U : Submodule Field (Point 9)) :
    ∀ i, decodePoint (empty.rows.get i) ∈ U := by
  intro i
  change decodePoint ((Vector.replicate 9 (0 : PackedPoint))[i.val]) ∈ U
  rw [Vector.getElem_replicate, decodePoint_zero]
  exact U.zero_mem

theorem insert_rows_mem (state : State) (U : Submodule Field (Point 9))
    (hrows : ∀ i, decodePoint (state.rows.get i) ∈ U)
    (value : PackedPoint) (hvalue : decodePoint value ∈ U) :
    ∀ i, decodePoint ((insert state value).rows.get i) ∈ U := by
  have hresidual : decodePoint (reduce state value) ∈ U := by
    have h := U.add_mem hvalue (reduce_add_mem state U hrows value)
    simpa only [← add_assoc, point_add_self, zero_add] using h
  intro i
  unfold insert
  dsimp only
  split_ifs with hzero
  · exact hrows i
  · change decodePoint ((state.rows.set (pivot (reduce state value)).val
      (reduce state value) (pivot (reduce state value)).isLt)[i.val]) ∈ U
    rw [Vector.getElem_set]
    split_ifs
    · exact hresidual
    · exact hrows i

end Lemmata.RM59.BinarySpan9
