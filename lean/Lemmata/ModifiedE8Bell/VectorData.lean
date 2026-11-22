module

public import Lemmata.ModifiedE8Bell.Data
public meta import Lemmata.ModifiedE8Bell.Statement

@[expose] public section
namespace Lemmata.ModifiedE8Bell
open scoped BigOperators

def complementRows : Array (Array ℤ) := Array.ofFn fun i : Setting =>
  Array.ofFn fun j : Setting => (if i = j then 308 else 0) - fourMatrix i j

def complementMatrix (i j : Setting) : ℤ :=
  (complementRows[i.val]?.getD #[])[j.val]?.getD 0

lemma complement_eq (i j : Setting) :
    complementMatrix i j = (if i = j then 308 else 0) - fourMatrix i j := by
  simp [complementMatrix, complementRows]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem complement_square : ∀ i j,
    (∑ k, complementMatrix k i * complementMatrix k j) = 360 * complementMatrix i j := by
  native_decide

set_option maxHeartbeats 0 in
theorem root_norm : ∀ i, (∑ k, root i k ^ 2) = 8 := by decide +kernel

set_option maxHeartbeats 0 in
theorem vector_witness_integer :
    (∑ i, ∑ j, fourMatrix i j * (∑ k, root i k * root j k)) = 295680 := by
  native_decide


end Lemmata.ModifiedE8Bell
