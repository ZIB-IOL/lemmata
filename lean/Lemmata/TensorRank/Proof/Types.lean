module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Basic.Real.Basic
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

theorem word_weight {R : Type*} [CommMonoid R] (v : C → R) (w : Fin N → C) :
    (∏ j, v (w j)) = ∏ c, v c ^ (histogram w c).val := by
  simpa [histogram] using (Fintype.prod_fiberwise' w v).symm

theorem histogram_sum (w : Fin N → C) : (∑ c, (histogram w c).val) = N := by
  simpa [histogram] using Fintype.sum_fiberwise w (fun _ => (1 : ℕ))

def wordEquiv {w z : Fin N → C} (h : histogram w = histogram z) : Equiv.Perm (Fin N) :=
  Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq
    (show Fintype.card {j // w j = c} = Fintype.card {j // z j = c} from
      congrArg (fun t : C → Fin (N + 1) => (t c).val) h))

omit [Fintype C] in
theorem wordEquiv_map {w z : Fin N → C} (h : histogram w = histogram z) (j : Fin N) :
    z (wordEquiv h j) = w j :=
  Equiv.ofFiberEquiv_map _ j

theorem sum_weights {R : Type*} [CommSemiring R] (v : C → R) :
    (∑ h : C → Fin (N + 1), (Fintype.card (Words h) : R) * ∏ c, v c ^ (h c).val) =
      (∑ c, v c) ^ N := by
  have hh (h : C → Fin (N + 1)) :
      (∑ w : Words h, ∏ j, v (w.val j)) =
        (Fintype.card (Words h) : R) * ∏ c, v c ^ (h c).val := by
    have he (w : Words h) : (∏ j, v (w.val j)) = ∏ c, v c ^ (h c).val := by
      rw [word_weight, w.property]
    simp_rw [he]
    simp [nsmul_eq_mul]
  have hs := Fintype.sum_fiberwise histogram (fun w : Fin N → C => ∏ j, v (w j))
  simp_rw [hh] at hs
  rw [hs]
  simpa using (Fintype.prod_sum (fun _ : Fin N => v)).symm

theorem exists_large_type (v : C → ℝ) :
    ∃ h : C → Fin (N + 1),
      (∑ c, v c) ^ N ≤ ((N + 1 : ℕ) : ℝ) ^ Fintype.card C *
        ((Fintype.card (Words h) : ℝ) * ∏ c, v c ^ (h c).val) := by
  let f (h : C → Fin (N + 1)) :=
    (Fintype.card (Words h) : ℝ) * ∏ c, v c ^ (h c).val
  have hne : (Finset.univ : Finset (C → Fin (N + 1))).Nonempty :=
    ⟨fun _ => 0, Finset.mem_univ _⟩
  obtain ⟨h, _, hmax⟩ := Finset.exists_max_image Finset.univ f hne
  refine ⟨h, ?_⟩
  have hs := Finset.sum_le_card_nsmul Finset.univ f (f h) hmax
  simpa [f, sum_weights, nsmul_eq_mul] using hs

theorem words_nonempty_of_weight_pos (v : C → ℝ)
    (h : C → Fin (N + 1))
    (hh : 0 < (Fintype.card (Words h) : ℝ) * ∏ c, v c ^ (h c).val) :
    Nonempty (Words h) := by
  apply Fintype.card_pos_iff.mp
  by_contra hc
  have hzero : Fintype.card (Words h) = 0 := by omega
  simp [hzero] at hh

end Lemmata.TensorRank.Types
