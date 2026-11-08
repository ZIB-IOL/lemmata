module

public import Lemmata.RM59.Proof.FlagActions
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public meta import Lemmata.RM59.Proof.FlagActions

@[expose] public section

set_option maxRecDepth 10000

namespace Lemmata.RM59.FlagSelectionChecks

open Lemmata.RM59.Packed
open scoped BigOperators Matrix

def quartets : List (Vector (Fin 9) 4) :=
  (List.finRange 9).flatMap fun i => ((List.finRange 9).filter fun j => j < i).flatMap fun j =>
    ((List.finRange 9).filter fun k => k < j).flatMap fun k =>
      ((List.finRange 9).filter fun l => l < k).map fun l => #v[l, k, j, i]

def bitSum (bits : Point 9) (q : Vector (Fin 9) 4) : Field :=
  bits (q.get 0) + bits (q.get 1) + bits (q.get 2) + bits (q.get 3)

def mixedQuad (bits : Point 9) : Option (Vector (Fin 9) 4) :=
  quartets.find? fun q => decide (bitSum bits q = 1)

def mixedCheck (bits : Point 9) : Bool :=
  match mixedQuad bits with
  | none => false
  | some q => decide (Function.Injective (fun i : Fin 4 => q.get i) ∧ bitSum bits q = 1)

theorem mixed_checked : ∀ bits : Point 9, (∃ i j, bits i ≠ bits j) → mixedCheck bits = true := by
  native_decide

theorem mixed_exists (bits : Point 9) (h : ∃ i j, bits i ≠ bits j) :
    ∃ q : Vector (Fin 9) 4,
      Function.Injective (fun i : Fin 4 => q.get i) ∧ bitSum bits q = 1 := by
  have hc := mixed_checked bits h
  cases hq : mixedQuad bits with
  | none => simp only [mixedCheck, hq, Bool.false_eq_true] at hc
  | some q =>
    refine ⟨q, ?_⟩
    simpa only [mixedCheck, hq, decide_eq_true_eq] using hc

def tripleRows : Vector (Vector (Fin 6) 3) 6 :=
  #v[#v[0, 1, 2], #v[0, 1, 3], #v[0, 1, 4], #v[0, 1, 5], #v[0, 2, 3], #v[1, 2, 3]]

def triple (i : Fin 6) (j : Fin 3) : Fin 6 := (tripleRows.get i).get j

def coefficient (i : Fin 6) : Point 6 := fun j =>
  if j = triple i 0 ∨ j = triple i 1 ∨ j = triple i 2 then 1 else 0

theorem triple_injective : ∀ i : Fin 6, Function.Injective (triple i) := by decide

theorem coefficients_independent : LinearIndependent Field coefficient := by
  rw [Fintype.linearIndependent_iff]
  decide

def cube (r : Field) : Finset (Point 9) :=
  (decodeWord [0, 1, 4, 5, 8, 9, 12, 13]).image (fun x => x + r • decodePoint 2)

theorem cube_checked : ∀ r : Field, (cube r).card = 8 ∧ ∀ x ∈ cube r, x 1 = r := by
  native_decide

end Lemmata.RM59.FlagSelectionChecks
