module

public import Lemmata.TensorRank.Def.Maps
public import Lemmata.TensorRank.Proof.Basic

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace Lemmata.TensorRank.Tensor

universe u v w z

variable {R : Type u} [CommSemiring R] {I : Type v} [Fintype I]
variable {V : I → Type w} {W : I → Type z} [∀ i, Fintype (V i)]

theorem localMap_pure (A : ∀ i, W i → V i → R) (v : ∀ i, V i → R) :
    localMap A (pure v) = pure (fun i y => ∑ x, A i y x * v i x) := by
  funext y
  simp only [localMap, pure]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun _ _ => (Finset.prod_mul_distrib : _).symm

@[simp] theorem localMap_zero (A : ∀ i, W i → V i → R) :
    localMap A (0 : Tensor R I V) = 0 := by
  funext y
  simp [localMap]

theorem localMap_add (A : ∀ i, W i → V i → R) (T S : Tensor R I V) :
    localMap A (T + S) = localMap A T + localMap A S := by
  funext y
  simp [localMap, mul_add, Finset.sum_add_distrib]

theorem localMap_smul (A : ∀ i, W i → V i → R) (c : R) (T : Tensor R I V) :
    localMap A (c • T) = c • localMap A T := by
  funext y
  simp only [localMap, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _

theorem localMap_sum {J : Type*} [Fintype J] (A : ∀ i, W i → V i → R)
    (T : J → Tensor R I V) : localMap A (∑ j, T j) = ∑ j, localMap A (T j) := by
  funext y
  simp only [localMap, Finset.sum_apply]
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem localMap_select (e : ∀ i, W i → V i) (T : Tensor R I V) :
    localMap (fun i y x => if x = e i y then 1 else 0) T = reindex e T := by
  classical
  funext y
  simp [localMap, reindex, Fintype.prod_boole, ← funext_iff]

theorem localMap_comp [∀ i, Fintype (W i)] {U : I → Type*}
    (B : ∀ i, U i → W i → R) (A : ∀ i, W i → V i → R) (T : Tensor R I V) :
    localMap B (localMap A T) = localMap (fun i z x => ∑ y, B i z y * A i y x) T := by
  funext z
  simp only [localMap]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, Fintype.prod_sum]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => (Finset.prod_mul_distrib : _).symm

theorem RankLE.localMap {T : Tensor R I V} {r : ℕ} (h : RankLE T r)
    (A : ∀ i, W i → V i → R) : RankLE (localMap A T) r := by
  obtain ⟨c, v, rfl⟩ := h
  refine ⟨c, fun j i y => ∑ x, A i y x * v j i x, ?_⟩
  funext y
  simp only [Lemmata.TensorRank.Tensor.localMap]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← localMap_pure]
  change (∑ x, (∏ i, A i (y i) (x i)) * (c j * pure (v j) x)) =
    c j * ∑ x, (∏ i, A i (y i) (x i)) * pure (v j) x
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _

theorem localMap_power (A : ∀ i, W i → V i → R) (T : Tensor R I V) (n : ℕ) :
    localMap (powerKernel A n) (power T n) = power (localMap A T) n := by
  funext y
  simp only [localMap, powerKernel, power]
  rw [Fintype.prod_sum]
  apply Fintype.sum_equiv (Equiv.piComm (fun i (_ : Fin n) => V i))
  intro x
  simp only [Equiv.piComm_apply]
  rw [Finset.prod_comm]
  exact (Finset.prod_mul_distrib : _).symm

theorem localMap_product {U Z : I → Type*} [∀ i, Fintype (U i)]
    (A : ∀ i, W i → V i → R) (B : ∀ i, Z i → U i → R)
    (T : Tensor R I V) (S : Tensor R I U) :
    localMap (productKernel A B) (product T S) = product (localMap A T) (localMap B S) := by
  let e : (∀ i, V i × U i) ≃ (∀ i, V i) × (∀ i, U i) :=
    { toFun := fun x => (fun i => (x i).1, fun i => (x i).2)
      invFun := fun x i => (x.1 i, x.2 i)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  funext y
  simp only [localMap, productKernel, product]
  have h := Fintype.sum_equiv e
    (fun x => (∏ i, A i (y i).1 (x i).1 * B i (y i).2 (x i).2) *
      (T (fun i => (x i).1) * S (fun i => (x i).2)))
    (fun x => ((∏ i, A i (y i).1 (x.1 i)) * T x.1) *
      ((∏ i, B i (y i).2 (x.2 i)) * S x.2))
    (fun _ => by rw [Finset.prod_mul_distrib]; exact mul_mul_mul_comm _ _ _ _)
  rw [h, Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem Restricts.refl (T : Tensor R I V) : Restricts T T := by
  classical
  exact ⟨fun _ y x => if x = y then 1 else 0, (localMap_select (fun _ => id) T).symm⟩

theorem Restricts.trans [∀ i, Fintype (W i)] {U : I → Type*}
    {S : Tensor R I W} {T : Tensor R I V} {Q : Tensor R I U}
    (hQS : Restricts Q S) (hST : Restricts S T) : Restricts Q T := by
  obtain ⟨B, rfl⟩ := hQS
  obtain ⟨A, rfl⟩ := hST
  exact ⟨fun i z x => ∑ y, B i z y * A i y x, localMap_comp B A T⟩

theorem Restricts.power {S : Tensor R I W} {T : Tensor R I V}
    (h : Restricts S T) (n : ℕ) : Restricts (power S n) (power T n) := by
  obtain ⟨A, rfl⟩ := h
  exact ⟨powerKernel A n, (localMap_power A T n).symm⟩

theorem Restricts.product {U Z : I → Type*} [∀ i, Fintype (U i)]
    {S : Tensor R I W} {T : Tensor R I V} {P : Tensor R I Z} {Q : Tensor R I U}
    (hST : Restricts S T) (hPQ : Restricts P Q) : Restricts (product S P) (product T Q) := by
  obtain ⟨A, rfl⟩ := hST
  obtain ⟨B, rfl⟩ := hPQ
  exact ⟨productKernel A B, (localMap_product A B T Q).symm⟩

theorem reindex_restricts (e : ∀ i, W i → V i) (T : Tensor R I V) :
    Restricts (reindex e T) T := by
  classical
  exact ⟨fun i y x => if x = e i y then 1 else 0, (localMap_select e T).symm⟩

variable [∀ i, Fintype (W i)]

theorem rank_localMap_le (A : ∀ i, W i → V i → R) (T : Tensor R I V) :
    rank (localMap A T) ≤ rank T :=
  (rank_le_iff _ _).mpr ((rankLE_rank T).localMap A)

theorem rank_power_localMap_le (A : ∀ i, W i → V i → R) (T : Tensor R I V) (n : ℕ) :
    rank (power (localMap A T) n) ≤ rank (power T n) := by
  rw [← localMap_power]
  exact rank_localMap_le _ _

theorem rankRoot_localMap_le (A : ∀ i, W i → V i → R) (T : Tensor R I V) (n : ℕ) :
    rankRoot (localMap A T) n ≤ rankRoot T n := by
  apply Real.rpow_le_rpow (Nat.cast_nonneg _)
  · exact_mod_cast rank_power_localMap_le A T (n + 1)
  · positivity

theorem asymptoticRank_localMap_le (A : ∀ i, W i → V i → R) (T : Tensor R I V) :
    asymptoticRank (localMap A T) ≤ asymptoticRank T :=
  ciInf_mono ⟨0, by rintro y ⟨n, rfl⟩; exact rankRoot_nonneg _ n⟩
    (rankRoot_localMap_le A T)

theorem Restricts.rank_le {S : Tensor R I W} {T : Tensor R I V} (h : Restricts S T) :
    rank S ≤ rank T := by
  obtain ⟨A, rfl⟩ := h
  exact rank_localMap_le A T

theorem Restricts.asymptoticRank_le {S : Tensor R I W} {T : Tensor R I V}
    (h : Restricts S T) : asymptoticRank S ≤ asymptoticRank T := by
  obtain ⟨A, rfl⟩ := h
  exact asymptoticRank_localMap_le A T

end Lemmata.TensorRank.Tensor
