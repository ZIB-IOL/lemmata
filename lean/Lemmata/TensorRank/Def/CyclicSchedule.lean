module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Range
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

set_option autoImplicit false

open Classical

noncomputable section

namespace Lemmata.TensorRank.CyclicSchedule

variable {k : ℕ}

/-- Two polynomial factors have each fixed output party. -/
abbrev Token (k : ℕ) := ZMod k × Bool

/-- The parties strictly after `a`, up to cyclic distance `l`. -/
def interval (a : ZMod k) (l : ℕ) : Finset (ZMod k) :=
  (Finset.range l).image (fun t => a + ((t + 1 : ℕ) : ZMod k))

def rightReader (a : ZMod k) (l : ℕ) : ZMod k :=
  a + ((l + 1 : ℕ) : ZMod k)

/-- A token's output stays fixed throughout the cyclic schedule. -/
def shortened (l : ℕ) (t : Token k) : Finset (ZMod k) :=
  match t.2 with
  | false => interval t.1 l
  | true => interval (t.1 - ((l + 1 : ℕ) : ZMod k)) l

/-- Values at the output party are harmless placeholders; only other inputs are used. -/
def inputLength (b l : ℕ) (t : Token k) (p : ZMod k) : ℕ :=
  if p ∈ shortened l t then b else b + 1

/-- At a stage, the false token at `a` is paired with the true token at its right reader. -/
def pairingEquiv (l : ℕ) : Token k ≃ Token k where
  toFun t := match t.2 with
    | false => (t.1, false)
    | true => (rightReader t.1 l, true)
  invFun t := match t.2 with
    | false => (t.1, false)
    | true => (t.1 - ((l + 1 : ℕ) : ZMod k), true)
  left_inv := by
    rintro ⟨a, b⟩
    cases b <;> simp [rightReader]
  right_inv := by
    rintro ⟨a, b⟩
    cases b <;> simp [rightReader]

abbrev Shared (a z : ZMod k) := {p : ZMod k // p ≠ a ∧ p ≠ z}

abbrev OrderedReaders (k : ℕ) := {r : ZMod k × ZMod k // r.1 ≠ r.2}

abbrev ReaderStep (k : ℕ) := ZMod k × Fin (k - 1)

/-- The two readers are put first, with every other party in the shared summand. -/
def readerPartiesEquiv (a z : ZMod k) (h : a ≠ z) :
    ZMod k ≃ (Bool ⊕ Shared a z) where
  toFun p := if ha : p = a then .inl false else
    if hz : p = z then .inl true else .inr ⟨p, ha, hz⟩
  invFun p := match p with
    | .inl false => a
    | .inl true => z
    | .inr p => p.val
  left_inv := by
    intro p
    by_cases ha : p = a
    · simp [ha]
    · by_cases hz : p = z <;> simp [ha, hz, h.symm]
  right_inv := by
    rintro (b | p)
    · cases b <;> simp [h.symm]
    · simp [p.property.1, p.property.2]

end Lemmata.TensorRank.CyclicSchedule
