module

public import Lemmata.TensorRank.Def.Tensor
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace Lemmata.TensorRank.Tensor

universe u v w

variable {R : Type u} [CommSemiring R] {I : Type v} [Fintype I]
variable {V : I → Type w}

/-- A sum of `r` weighted pure tensors, with one factor at every party. -/
def RankLE (T : Tensor R I V) (r : ℕ) : Prop :=
  ∃ (c : Fin r → R) (v : Fin r → ∀ i, V i → R),
    T = fun x => ∑ j, c j * pure (v j) x

theorem rankLE_zero (r : ℕ) : RankLE (0 : Tensor R I V) r := by
  refine ⟨fun _ => 0, fun _ _ _ => 1, ?_⟩
  funext x
  simp

theorem rankLE_zero_iff (T : Tensor R I V) : RankLE T 0 ↔ T = 0 := by
  constructor
  · rintro ⟨c, v, h⟩
    funext x
    simpa using congrFun h x
  · rintro rfl
    exact rankLE_zero 0

theorem rankLE_pure (v : ∀ i, V i → R) : RankLE (pure v) 1 := by
  refine ⟨fun _ => 1, fun _ => v, ?_⟩
  funext x
  simp

theorem RankLE.add {T S : Tensor R I V} {r s : ℕ}
    (hT : RankLE T r) (hS : RankLE S s) : RankLE (T + S) (r + s) := by
  obtain ⟨c, v, hc⟩ := hT
  obtain ⟨d, w, hd⟩ := hS
  refine ⟨Fin.append c d, Fin.append v w, ?_⟩
  funext x
  rw [Pi.add_apply, congrFun hc x, congrFun hd x, Fin.sum_univ_add]
  simp

theorem RankLE.mono {T : Tensor R I V} {r s : ℕ}
    (h : RankLE T r) (hrs : r ≤ s) : RankLE T s := by
  simpa only [add_zero, Nat.add_sub_of_le hrs] using h.add (rankLE_zero (s - r))

theorem rankLE_card [∀ i, Fintype (V i)] (T : Tensor R I V) :
    RankLE T (Fintype.card (∀ i, V i)) := by
  classical
  let e := (Fintype.equivFin (∀ i, V i)).symm
  refine ⟨fun j => T (e j), fun j i a => if a = e j i then 1 else 0, ?_⟩
  funext x
  have h := Fintype.sum_equiv e
    (fun j => T (e j) * pure (fun i a => if a = e j i then 1 else 0) x)
    (fun a => T a * if x = a then 1 else 0)
    (fun j => by simp only [pure, Fintype.prod_boole, ← funext_iff])
  rw [h]
  simp

variable [∀ i, Fintype (V i)]

noncomputable def rank (T : Tensor R I V) : ℕ :=
  Nat.find (show ∃ r, RankLE T r from ⟨_, rankLE_card T⟩)

theorem rankLE_rank (T : Tensor R I V) : RankLE T (rank T) :=
  Nat.find_spec _

theorem rank_le_iff (T : Tensor R I V) (r : ℕ) : rank T ≤ r ↔ RankLE T r := by
  constructor
  · exact (rankLE_rank T).mono
  · exact Nat.find_min' _

@[simp] theorem rank_zero : rank (0 : Tensor R I V) = 0 := by
  exact Nat.eq_zero_of_le_zero ((rank_le_iff _ _).mpr (rankLE_zero 0))

@[simp] theorem rank_eq_zero_iff (T : Tensor R I V) : rank T = 0 ↔ T = 0 := by
  rw [← Nat.le_zero, rank_le_iff, rankLE_zero_iff]

theorem rank_le_card (T : Tensor R I V) : rank T ≤ Fintype.card (∀ i, V i) :=
  (rank_le_iff _ _).mpr (rankLE_card T)

end Lemmata.TensorRank.Tensor
