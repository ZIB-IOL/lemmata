module

public import Lemmata.TensorRank.Def.WeightedGraph
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank

private theorem card_finset_stabilizer {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α) :
    Nat.card {σ : Equiv.Perm α // s.map σ.toEmbedding = s} =
      s.card.factorial * (Fintype.card α - s.card).factorial := by
  let color : α → Bool := fun x => decide (x ∈ s)
  have hp (σ : Equiv.Perm α) : s.map σ.toEmbedding = s ↔ color ∘ σ = color := by
    constructor
    · intro h
      funext x
      have hm : σ x ∈ s ↔ x ∈ s := by
        have hm : σ x ∈ s.map σ.toEmbedding ↔ x ∈ s := by simp
        simpa only [h] using hm
      simpa only [Function.comp_apply, color, decide_eq_decide] using hm
    · intro h
      ext x
      simp only [Finset.mem_map_equiv]
      have hm := congrFun h (σ.symm x)
      simpa only [Function.comp_apply, color, Equiv.apply_symm_apply, decide_eq_decide] using hm.symm
  have ht : Fintype.card {x : α // color x = true} = s.card :=
    Fintype.card_of_subtype s (fun x => by simp [color])
  have hf : Fintype.card {x : α // color x = false} = Fintype.card α - s.card := by
    rw [← Finset.card_compl s]
    exact Fintype.card_of_subtype sᶜ (fun x => by simp [color])
  calc
    _ = Nat.card {σ : Equiv.Perm α // color ∘ σ = color} :=
      Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) hp)
    _ = Fintype.card {σ : Equiv.Perm α // color ∘ σ = color} := Nat.card_eq_fintype_card
    _ = ∏ b : Bool, (Fintype.card {x : α // color x = b}).factorial :=
      DomMulAct.stabilizer_card color
    _ = _ := by rw [Fintype.prod_bool, ht, hf]

theorem finset_map_fiber_card {α : Type*} [Fintype α] [DecidableEq α] (s t : Finset α)
    (hst : s.card = t.card) :
    Nat.card {σ : Equiv.Perm α // s.map σ.toEmbedding = t} =
      s.card.factorial * (Fintype.card α - s.card).factorial := by
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq s t hst
  let e : {σ : Equiv.Perm α // s.map σ.toEmbedding = s} ≃
      {σ : Equiv.Perm α // s.map σ.toEmbedding = t} :=
    Equiv.subtypeEquiv (Equiv.mulLeft τ) (fun σ => by
      change s.map σ.toEmbedding = s ↔ s.map (τ * σ).toEmbedding = t
      rw [← hτ]
      have hm : s.map (τ * σ).toEmbedding = (s.map σ.toEmbedding).map τ.toEmbedding := by
        rw [Finset.map_map]
        rfl
      rw [hm, Finset.map_inj])
  exact (Nat.card_congr e).symm.trans (card_finset_stabilizer s)

theorem edgeMap_fiber_natCard {k : ℕ} (e f : Edge k) :
    Nat.card {σ : Equiv.Perm (Fin k) // edgeMap σ e = f} =
      2 * (k - 2).factorial := by
  have hpred (σ : Equiv.Perm (Fin k)) : edgeMap σ e = f ↔ e.val.map σ.toEmbedding = f.val :=
    Subtype.ext_iff
  calc
    _ = Nat.card {σ : Equiv.Perm (Fin k) // e.val.map σ.toEmbedding = f.val} :=
      Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) hpred)
    _ = e.val.card.factorial * (Fintype.card (Fin k) - e.val.card).factorial :=
      finset_map_fiber_card e.val f.val (e.prop.trans f.prop.symm)
    _ = _ := by simp [e.prop]

theorem edgeMap_fiber_card {k : ℕ} (_hk : 2 ≤ k) (e f : Edge k) :
    Fintype.card {σ : Equiv.Perm (Fin k) // edgeMap σ e = f} =
      2 * (k - 2).factorial :=
  (Nat.card_eq_fintype_card).symm.trans (edgeMap_fiber_natCard e f)

theorem prod_edgeMap {k : ℕ} (hk : 2 ≤ k) {A : Type*} [CommMonoid A]
    (d : Edge k → A) (e : Edge k) :
    (∏ σ : Equiv.Perm (Fin k), d (edgeMap σ e)) =
      (∏ f : Edge k, d f) ^ (2 * (k - 2).factorial) := by
  rw [← Fintype.prod_fiberwise' (fun σ : Equiv.Perm (Fin k) => edgeMap σ e) d]
  simp only [Finset.prod_const, Finset.card_univ, edgeMap_fiber_card hk]
  exact Finset.prod_pow _ _ _

theorem edge_multiplicity_factorial {k : ℕ} (hk : 2 ≤ k) :
    k.choose 2 * (2 * (k - 2).factorial) = k.factorial := by
  simpa only [Nat.factorial_two, Nat.mul_assoc] using Nat.choose_mul_factorial_mul_factorial hk

end Lemmata.TensorRank
