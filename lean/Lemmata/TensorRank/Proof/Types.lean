module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Basic

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.Types

variable {C : Type*} [Fintype C] {N : ℕ}

def histogram (w : Fin N → C) : C → Fin (N + 1) :=
  fun c => ⟨Fintype.card {j // w j = c}, Nat.lt_succ_of_le (by
    simpa using Fintype.card_subtype_le (fun j : Fin N => w j = c))⟩

abbrev Words (h : C → Fin (N + 1)) := {w : Fin N → C // histogram w = h}

def wordEquiv {w z : Fin N → C} (h : histogram w = histogram z) : Equiv.Perm (Fin N) :=
  Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq
    (show Fintype.card {j // w j = c} = Fintype.card {j // z j = c} from
      congrArg (fun t : C → Fin (N + 1) => (t c).val) h))

omit [Fintype C] in
theorem wordEquiv_map {w z : Fin N → C} (h : histogram w = histogram z) (j : Fin N) :
    z (wordEquiv h j) = w j :=
  Equiv.ofFiberEquiv_map _ j

theorem exists_large_word (h N : ℕ) (hh : 0 < h) :
    ∃ w : Fin N → Fin h, 0 < Fintype.card (Words (histogram w)) ∧
      h ^ N ≤ (N + 1) ^ h * Fintype.card (Words (histogram w)) := by
  have hsum : (∑ H : Fin h → Fin (N + 1), Fintype.card (Words H)) = h ^ N := by
    have hs := Fintype.sum_fiberwise (histogram (C := Fin h) (N := N))
      (fun _ : Fin N → Fin h => (1 : ℕ))
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Fintype.card_fun, Fintype.card_fin, Nat.cast_id] using hs
  let f (H : Fin h → Fin (N + 1)) := Fintype.card (Words H)
  have hne : (Finset.univ : Finset (Fin h → Fin (N + 1))).Nonempty :=
    ⟨fun _ => 0, Finset.mem_univ _⟩
  obtain ⟨H, _, hmax⟩ := Finset.exists_max_image Finset.univ f hne
  have hs := Finset.sum_le_card_nsmul Finset.univ f (f H) hmax
  have hb : h ^ N ≤ (N + 1) ^ h * Fintype.card (Words H) := by
    calc
      _ = ∑ K : Fin h → Fin (N + 1), Fintype.card (Words K) := by
        exact hsum.symm
      _ ≤ _ := by simpa only [f, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_id] using hs
  have hM : 0 < Fintype.card (Words H) := by
    apply Nat.pos_of_ne_zero
    intro hzero
    rw [hzero, mul_zero] at hb
    have hpos : 0 < h ^ N := Nat.pow_pos hh
    exact (not_le_of_gt hpos) hb
  obtain ⟨base⟩ := Fintype.card_pos_iff.mp hM
  have hcard : Fintype.card (Words (histogram base.val)) = Fintype.card (Words H) := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun w => by rw [base.property])
  refine ⟨base.val, ?_, ?_⟩
  · rw [hcard]
    exact hM
  · rw [hcard]
    exact hb

end Lemmata.TensorRank.Types
