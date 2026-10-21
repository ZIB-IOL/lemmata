module

public import Lemmata.TensorRank.Def.IndexedProduct
public import Lemmata.TensorRank.Proof.Asymptotic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

@[expose] public section

set_option autoImplicit false

open Filter
open Classical
open scoped Topology BigOperators

namespace Lemmata.TensorRank.Tensor

variable {R I J : Type*} [CommSemiring R] [Fintype J]
variable {V : J → I → Type*}

theorem power_indexedProduct_reindex (T : ∀ j, Tensor R I (V j)) (n : ℕ) :
    reindex (fun i => Equiv.piComm (fun (_ : Fin n) j => V j i))
      (indexedProduct (fun j => power (T j) n)) =
      power (indexedProduct T) n := by
  funext x
  exact Finset.prod_comm

variable [Fintype I]

theorem RankLE.indexedProduct {T : ∀ j, Tensor R I (V j)} {r : J → ℕ}
    (hT : ∀ j, RankLE (T j) (r j)) : RankLE (indexedProduct T) (∏ j, r j) := by
  classical
  choose c v hv using hT
  let e : Fin (∏ j, r j) ≃ (∀ j, Fin (r j)) :=
    (Fintype.equivFinOfCardEq (by simp : Fintype.card (∀ j, Fin (r j)) = ∏ j, r j)).symm
  refine ⟨fun a => ∏ j, c j (e a j), fun a i x => ∏ j, v j (e a j) i (x j), ?_⟩
  funext x
  have h := Fintype.sum_equiv e
    (fun a => (∏ j, c j (e a j)) * pure (fun i y => ∏ j, v j (e a j) i (y j)) x)
    (fun f => ∏ j, c j (f j) * pure (v j (f j)) (fun i => x i j))
    (fun a => by
      simp only [pure]
      rw [Finset.prod_comm]
      exact (Finset.prod_mul_distrib : _).symm)
  change (∏ j, T j (fun i => x i j)) = _
  simp_rw [congrFun (hv _) _]
  rw [Fintype.prod_sum, h]

variable [∀ j i, Fintype (V j i)]

theorem rank_indexedProduct_le (T : ∀ j, Tensor R I (V j)) :
    rank (indexedProduct T) ≤ ∏ j, rank (T j) :=
  (rank_le_iff _ _).mpr (RankLE.indexedProduct (fun j => rankLE_rank (T j)))

theorem rank_power_indexedProduct_le (T : ∀ j, Tensor R I (V j)) (n : ℕ) :
    rank (power (indexedProduct T) n) ≤ ∏ j, rank (power (T j) n) := by
  rw [← power_indexedProduct_reindex, rank_reindex]
  exact rank_indexedProduct_le _

variable [Nontrivial R] [NoZeroDivisors R]

theorem asymptoticRank_indexedProduct_le (T : ∀ j, Tensor R I (V j)) :
    asymptoticRank (indexedProduct T) ≤ ∏ j, asymptoticRank (T j) := by
  apply le_of_tendsto_of_tendsto' (tendsto_power_rank_root (indexedProduct T))
    (tendsto_finsetProd _ (fun j _ => tendsto_power_rank_root (T j)))
  intro n
  calc
    (rank (power (indexedProduct T) n) : ℝ) ^ ((n : ℝ)⁻¹) ≤
        (∏ j, (rank (power (T j) n) : ℝ)) ^ ((n : ℝ)⁻¹) := by
      apply Real.rpow_le_rpow (Nat.cast_nonneg _)
      · exact_mod_cast rank_power_indexedProduct_le T n
      · positivity
    _ = ∏ j, (rank (power (T j) n) : ℝ) ^ ((n : ℝ)⁻¹) :=
      (Real.finsetProd_rpow _ _ (fun j _ => Nat.cast_nonneg _) _).symm

end Lemmata.TensorRank.Tensor
