module

public import Lemmata.TensorRank.Proof.Basic

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.TensorRank.Tensor

universe u v w z

variable {R : Type u} [CommSemiring R] {I : Type v}
variable {V : I → Type w} {W : I → Type z}

theorem power_reindex (e : ∀ i, W i → V i) (T : Tensor R I V) (n : ℕ) :
    power (reindex e T) n =
      reindex (fun i a j => e i (a j)) (power T n) := rfl

theorem power_add_reindex (T : Tensor R I V) (m n : ℕ) :
    reindex (fun i => (Fin.appendEquiv m n :
      ((Fin m → V i) × (Fin n → V i)) ≃ (Fin (m + n) → V i))) (power T (m + n)) =
      product (power T m) (power T n) := by
  funext x
  change (∏ j : Fin (m + n), T (fun i => Fin.append (x i).1 (x i).2 j)) = _
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right, product, power]

def wordFlatten (A : Type w) (m n : ℕ) :
    (Fin n → Fin m → A) ≃ (Fin (n * m) → A) :=
  (Equiv.curry (Fin n) (Fin m) A).symm.trans
    (Equiv.arrowCongr finProdFinEquiv (Equiv.refl A))

theorem power_mul_reindex (T : Tensor R I V) (m n : ℕ) :
    reindex (fun i => wordFlatten (V i) m n) (power T (n * m)) =
      power (power T m) n := by
  funext x
  have h := Fintype.prod_equiv (finProdFinEquiv.symm : Fin (n * m) ≃ Fin n × Fin m)
    (fun j => T (fun i => wordFlatten (V i) m n (x i) j))
    (fun p => T (fun i => x i p.1 p.2)) (fun _ => rfl)
  simpa only [reindex, power, Fintype.prod_prod_type] using h

section Rank

variable [Fintype I]

theorem RankLE.product {T : Tensor R I V} {S : Tensor R I W} {r s : ℕ}
    (hT : RankLE T r) (hS : RankLE S s) : RankLE (product T S) (r * s) := by
  obtain ⟨c, v, hT⟩ := hT
  obtain ⟨d, w, hS⟩ := hS
  let e : Fin (r * s) ≃ Fin r × Fin s := finProdFinEquiv.symm
  refine ⟨fun j => c (e j).1 * d (e j).2,
    fun j i p => v (e j).1 i p.1 * w (e j).2 i p.2, ?_⟩
  funext x
  change T (fun i => (x i).1) * S (fun i => (x i).2) = _
  rw [congrFun hT _, congrFun hS _]
  have h := Fintype.sum_equiv e
    (fun j => (c (e j).1 * d (e j).2) *
      pure (fun i p => v (e j).1 i p.1 * w (e j).2 i p.2) x)
    (fun p => (c p.1 * pure (v p.1) (fun i => (x i).1)) *
      (d p.2 * pure (w p.2) (fun i => (x i).2)))
    (fun j => by
      simp only [pure, Finset.prod_mul_distrib]
      exact mul_mul_mul_comm _ _ _ _)
  rw [h, Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem RankLE.power {T : Tensor R I V} {r : ℕ} (hT : RankLE T r) (n : ℕ) :
    RankLE (power T n) (r ^ n) := by
  classical
  obtain ⟨c, v, rfl⟩ := hT
  let e : Fin (r ^ n) ≃ (Fin n → Fin r) :=
    (Fintype.equivFinOfCardEq (by simp : Fintype.card (Fin n → Fin r) = r ^ n)).symm
  refine ⟨fun a => ∏ j, c (e a j), fun a i x => ∏ j, v (e a j) i (x j), ?_⟩
  funext x
  have h := Fintype.sum_equiv e
    (fun a => (∏ j, c (e a j)) * pure (fun i y => ∏ j, v (e a j) i (y j)) x)
    (fun f => ∏ j, c (f j) * pure (v (f j)) (fun i => x i j))
    (fun a => by
      simp only [pure]
      rw [Finset.prod_comm]
      exact (Finset.prod_mul_distrib : _).symm)
  simp only [Lemmata.TensorRank.Tensor.power]
  rw [Fintype.prod_sum, h]

variable [∀ i, Fintype (V i)]

theorem rank_product_le [∀ i, Fintype (W i)] (T : Tensor R I V) (S : Tensor R I W) :
    rank (product T S) ≤ rank T * rank S :=
  (rank_le_iff _ _).mpr ((rankLE_rank T).product (rankLE_rank S))

theorem rank_power_le (T : Tensor R I V) (n : ℕ) : rank (power T n) ≤ rank T ^ n :=
  (rank_le_iff _ _).mpr ((rankLE_rank T).power n)

theorem rank_power_add_le (T : Tensor R I V) (m n : ℕ) :
    rank (power T (m + n)) ≤ rank (power T m) * rank (power T n) := by
  calc
    rank (power T (m + n)) =
        rank (reindex (fun i => (Fin.appendEquiv m n :
          ((Fin m → V i) × (Fin n → V i)) ≃ (Fin (m + n) → V i)))
            (power T (m + n))) := (rank_reindex _ _).symm
    _ = rank (product (power T m) (power T n)) := by rw [power_add_reindex]
    _ ≤ rank (power T m) * rank (power T n) := rank_product_le _ _

theorem rank_power_mul (T : Tensor R I V) (m n : ℕ) :
    rank (power (power T m) n) = rank (power T (m * n)) := by
  rw [← power_mul_reindex, rank_reindex, Nat.mul_comm n m]

@[simp] theorem rank_power_zero [Nontrivial R] (T : Tensor R I V) : rank (power T 0) = 1 := by
  apply le_antisymm
  · simpa using rank_power_le T 0
  · apply Nat.one_le_iff_ne_zero.mpr
    intro h
    have hz := congrFun ((rank_eq_zero_iff _).mp h) (fun _ => Fin.elim0)
    simp [power] at hz

theorem rankRoot_reindex [∀ i, Fintype (W i)] (e : ∀ i, W i ≃ V i)
    (T : Tensor R I V) (n : ℕ) : rankRoot (reindex (fun i => e i) T) n = rankRoot T n := by
  have h : power (reindex (fun i => e i) T) (n + 1) =
      reindex (fun i => Equiv.arrowCongr (Equiv.refl (Fin (n + 1))) (e i))
        (power T (n + 1)) := rfl
  simp only [rankRoot, h, rank_reindex]

theorem asymptoticRank_reindex [∀ i, Fintype (W i)] (e : ∀ i, W i ≃ V i)
    (T : Tensor R I V) : asymptoticRank (reindex (fun i => e i) T) = asymptoticRank T := by
  simp only [asymptoticRank, rankRoot_reindex]

theorem asymptoticRank_pure_le (v : ∀ i, V i → R) : asymptoticRank (pure v) ≤ 1 := by
  exact (asymptoticRank_le_rank _).trans (by exact_mod_cast rank_pure_le v)

theorem asymptoticRank_pure [Nontrivial R] [NoZeroDivisors R]
    (v : ∀ i, V i → R) (hv : pure v ≠ 0) : asymptoticRank (pure v) = 1 :=
  le_antisymm (asymptoticRank_pure_le v) (one_le_asymptoticRank hv)

end Rank
end Lemmata.TensorRank.Tensor
