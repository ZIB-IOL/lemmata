module

public import Lemmata.TensorRank.Proof.Products
public import Mathlib.Logic.Equiv.Basic

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.TensorRank.Tensor

universe u v w z

variable {R : Type u} {I : Type v} {J : Type w} {V : I → Type z}

def relabel (e : J ≃ I) (T : Tensor R I V) : Tensor R J (fun j => V (e j)) :=
  fun x => T (Equiv.piCongrLeft V e x)

variable [CommSemiring R] [Fintype I] [Fintype J]

theorem relabel_pure (e : J ≃ I) (v : ∀ i, V i → R) :
    relabel e (pure v) = pure (fun j => v (e j)) := by
  funext x
  exact (Fintype.prod_equiv e _ _ (fun j => by simp)).symm

theorem rankLE_relabel_iff (e : J ≃ I) (T : Tensor R I V) (r : ℕ) :
    RankLE (relabel e T) r ↔ RankLE T r := by
  constructor
  · rintro ⟨c, v, h⟩
    refine ⟨c, fun a => Equiv.piCongrLeft (fun i => V i → R) e (v a), ?_⟩
    funext x
    have hx := congrFun h ((Equiv.piCongrLeft V e).symm x)
    simp only [relabel, Equiv.apply_symm_apply] at hx
    rw [hx]
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    exact Fintype.prod_equiv e _ _ (fun j => by simp)
  · rintro ⟨c, v, h⟩
    refine ⟨c, fun a j => v a (e j), ?_⟩
    funext x
    have hx := congrFun h (Equiv.piCongrLeft V e x)
    change T (Equiv.piCongrLeft V e x) = _ at hx
    rw [show relabel e T x = T (Equiv.piCongrLeft V e x) from rfl, hx]
    apply Finset.sum_congr rfl
    intro a _
    rw [← relabel_pure]
    rfl

variable [∀ i, Fintype (V i)]

theorem rank_relabel (e : J ≃ I) (T : Tensor R I V) : rank (relabel e T) = rank T := by
  apply le_antisymm
  · exact (rank_le_iff _ _).mpr ((rankLE_relabel_iff e T _).mpr (rankLE_rank T))
  · exact (rank_le_iff _ _).mpr ((rankLE_relabel_iff e T _).mp (rankLE_rank _))

omit [Fintype I] [Fintype J] [∀ i, Fintype (V i)] in
theorem relabel_power (e : J ≃ I) (T : Tensor R I V) (n : ℕ) :
    relabel e (power T n) = power (relabel e T) n := by
  funext x
  simp only [relabel, power]
  apply Finset.prod_congr rfl
  intro a _
  congr 1
  funext i
  obtain ⟨j, rfl⟩ := e.surjective i
  simp

theorem asymptoticRank_relabel (e : J ≃ I) (T : Tensor R I V) :
    asymptoticRank (relabel e T) = asymptoticRank T := by
  simp only [asymptoticRank, rankRoot, ← relabel_power]
  congr 1
  funext n
  rw [rank_relabel e (power T (n + 1))]

end Lemmata.TensorRank.Tensor
