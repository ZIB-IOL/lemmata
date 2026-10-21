module

public import Lemmata.TensorRank.Def.Asymptotic

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.TensorRank.Tensor

universe u v w z

variable {R : Type u} [CommSemiring R] {I : Type v} [Fintype I]
variable {V : I → Type w} {W : I → Type z}

theorem product_pure (v : ∀ i, V i → R) (w : ∀ i, W i → R) :
    product (pure v) (pure w) = pure (fun i p => v i p.1 * w i p.2) := by
  funext x
  exact (Finset.prod_mul_distrib : _).symm

theorem power_pure (v : ∀ i, V i → R) (n : ℕ) :
    power (pure v) n = pure (fun i a => ∏ j, v i (a j)) := by
  funext x
  exact Finset.prod_comm

@[simp] theorem reindex_pure (e : ∀ i, W i → V i) (v : ∀ i, V i → R) :
    reindex e (pure v) = pure (fun i a => v i (e i a)) := rfl

theorem RankLE.reindex {T : Tensor R I V} {r : ℕ} (h : RankLE T r)
    (e : ∀ i, W i → V i) : RankLE (reindex e T) r := by
  obtain ⟨c, v, rfl⟩ := h
  exact ⟨c, fun j i a => v j i (e i a), rfl⟩

theorem pure_absorb [DecidableEq I] (c : R) (v : ∀ i, V i → R) (i₀ : I) :
    pure (fun i a => (if i = i₀ then c else 1) * v i a) = fun x => c * pure v x := by
  classical
  funext x
  simp only [pure]
  rw [Finset.prod_mul_distrib]
  simp

theorem rankLE_iff_sum_pure [Nonempty I] (T : Tensor R I V) (r : ℕ) :
    RankLE T r ↔ ∃ v : Fin r → ∀ i, V i → R, T = fun x => ∑ j, pure (v j) x := by
  classical
  constructor
  · rintro ⟨c, v, h⟩
    refine ⟨fun j i a => (if i = Classical.arbitrary I then c j else 1) * v j i a, ?_⟩
    funext x
    rw [congrFun h x]
    apply Finset.sum_congr rfl
    intro j _
    exact (congrFun (pure_absorb (c j) (v j) (Classical.arbitrary I)) x).symm
  · rintro ⟨v, h⟩
    exact ⟨fun _ => 1, v, by simpa using h⟩

variable [∀ i, Fintype (V i)]

theorem rank_add_le (T S : Tensor R I V) : rank (T + S) ≤ rank T + rank S :=
  (rank_le_iff _ _).mpr ((rankLE_rank T).add (rankLE_rank S))

theorem rank_pure_le (v : ∀ i, V i → R) : rank (pure v) ≤ 1 :=
  (rank_le_iff _ _).mpr (rankLE_pure v)

theorem rank_reindex_le [∀ i, Fintype (W i)]
    (e : ∀ i, W i → V i) (T : Tensor R I V) : rank (reindex e T) ≤ rank T :=
  (rank_le_iff _ _).mpr ((rankLE_rank T).reindex e)

theorem rank_reindex [∀ i, Fintype (W i)]
    (e : ∀ i, W i ≃ V i) (T : Tensor R I V) : rank (reindex (fun i => e i) T) = rank T := by
  apply le_antisymm (rank_reindex_le _ T)
  have h := rank_reindex_le (fun i => (e i).symm) (reindex (fun i => e i) T)
  have hid : reindex (fun i => (e i).symm) (reindex (fun i => e i) T) = T := by
    funext x
    change T (fun i => e i ((e i).symm (x i))) = T x
    congr 1
    funext i
    exact (e i).apply_symm_apply (x i)
  rw [hid] at h
  exact h

@[simp] theorem rank_power_one (T : Tensor R I V) : rank (power T 1) = rank T := by
  have h : power T 1 = reindex (fun i => Equiv.funUnique (Fin 1) (V i)) T := by
    funext x
    simp [power, reindex, Equiv.funUnique, Equiv.piUnique]
  rw [h]
  exact rank_reindex _ T

theorem rankRoot_nonneg (T : Tensor R I V) (n : ℕ) : 0 ≤ rankRoot T n :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem asymptoticRank_nonneg (T : Tensor R I V) : 0 ≤ asymptoticRank T :=
  le_ciInf (rankRoot_nonneg T)

theorem asymptoticRank_le_rankRoot (T : Tensor R I V) (n : ℕ) :
    asymptoticRank T ≤ rankRoot T n :=
  ciInf_le ⟨0, by rintro y ⟨m, rfl⟩; exact rankRoot_nonneg T m⟩ n

theorem asymptoticRank_le_rank (T : Tensor R I V) : asymptoticRank T ≤ rank T := by
  simpa [rankRoot] using asymptoticRank_le_rankRoot T 0

omit [Fintype I] [∀ i, Fintype (V i)] in
theorem power_zero (n : ℕ) : power (0 : Tensor R I V) (n + 1) = 0 := by
  funext x
  simp [power]

@[simp] theorem rankRoot_zero (n : ℕ) : rankRoot (0 : Tensor R I V) n = 0 := by
  rw [rankRoot, power_zero, rank_zero, Nat.cast_zero]
  exact Real.zero_rpow (inv_ne_zero (by positivity))

@[simp] theorem asymptoticRank_zero : asymptoticRank (0 : Tensor R I V) = 0 := by
  simp [asymptoticRank]

omit [Fintype I] [∀ i, Fintype (V i)] in
theorem power_ne_zero [NoZeroDivisors R] {T : Tensor R I V} (hT : T ≠ 0) (n : ℕ) :
    power T (n + 1) ≠ 0 := by
  intro h
  apply hT
  funext x
  have hpow : T x ^ (n + 1) = 0 := by
    simpa [power] using congrFun h (fun i _ => x i)
  exact eq_zero_of_pow_eq_zero hpow

theorem one_le_asymptoticRank [Nontrivial R] [NoZeroDivisors R]
    {T : Tensor R I V} (hT : T ≠ 0) : 1 ≤ asymptoticRank T := by
  apply le_ciInf
  intro n
  apply Real.one_le_rpow
  · have h : 0 < rank (power T (n + 1)) := Nat.pos_of_ne_zero
      (fun hz => power_ne_zero hT n ((rank_eq_zero_iff _).mp hz))
    exact_mod_cast Nat.succ_le_of_lt h
  · positivity

end Lemmata.TensorRank.Tensor
