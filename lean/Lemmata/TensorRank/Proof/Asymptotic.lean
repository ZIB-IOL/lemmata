module

public import Lemmata.TensorRank.Proof.Products
public import Mathlib.Analysis.Subadditive

@[expose] public section

set_option autoImplicit false

open Filter Set
open scoped Topology BigOperators

namespace Lemmata.TensorRank.Tensor

universe u v w z

variable {R : Type u} [CommSemiring R] [Nontrivial R] [NoZeroDivisors R]
variable {I : Type v} [Fintype I] {V : I → Type w} [∀ i, Fintype (V i)]

private theorem one_le_power_rank {T : Tensor R I V} (hT : T ≠ 0) (n : ℕ) :
    1 ≤ rank (power T n) := by
  cases n with
  | zero => simp
  | succ n =>
    apply Nat.one_le_iff_ne_zero.mpr
    exact fun h => power_ne_zero hT n ((rank_eq_zero_iff _).mp h)

theorem tendsto_rankRoot (T : Tensor R I V) :
    Tendsto (rankRoot T) atTop (𝓝 (asymptoticRank T)) := by
  by_cases hT : T = 0
  · subst T
    rw [asymptoticRank_zero]
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr
      fun n => (rankRoot_zero n).symm
  let a (n : ℕ) : ℝ := rank (power T n)
  have ha (n : ℕ) : 1 ≤ a n := by
    change 1 ≤ (rank (power T n) : ℝ)
    exact_mod_cast one_le_power_rank hT n
  have hpos (n : ℕ) : 0 < a n := lt_of_lt_of_le zero_lt_one (ha n)
  have hs : Subadditive (fun n => Real.log (a n)) := by
    intro m n
    calc
      Real.log (a (m + n)) ≤ Real.log (a m * a n) := by
        apply Real.log_le_log (hpos _)
        change (rank (power T (m + n)) : ℝ) ≤ (rank (power T m) : ℝ) * rank (power T n)
        exact_mod_cast rank_power_add_le T m n
      _ = Real.log (a m) + Real.log (a n) :=
        Real.log_mul (ne_of_gt (hpos m)) (ne_of_gt (hpos n))
  have hb : BddBelow (range fun n : ℕ => Real.log (a n) / (n : ℝ)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    exact div_nonneg (Real.log_nonneg (ha n)) (Nat.cast_nonneg n)
  have hroot (n : ℕ) : rankRoot T n =
      Real.exp (Real.log (a (n + 1)) / ((n + 1 : ℕ) : ℝ)) := by
    change a (n + 1) ^ ((n + 1 : ℝ)⁻¹) = _
    rw [Real.rpow_def_of_pos (hpos _), div_eq_mul_inv, Nat.cast_add, Nat.cast_one]
  have hlim := Real.continuous_exp.continuousAt.tendsto.comp
    ((hs.tendsto_lim hb).comp (tendsto_add_atTop_nat 1))
  have ht : Tendsto (rankRoot T) atTop (𝓝 (Real.exp hs.lim)) :=
    hlim.congr fun n => (hroot n).symm
  have hvalue : Real.exp hs.lim = asymptoticRank T := by
    apply le_antisymm
    · apply le_ciInf
      intro n
      rw [hroot n]
      exact Real.exp_le_exp.mpr (hs.lim_le_div hb (Nat.succ_ne_zero n))
    · exact ge_of_tendsto' ht (asymptoticRank_le_rankRoot T)
  simpa only [hvalue] using ht

theorem tendsto_power_rank_root (T : Tensor R I V) :
    Tendsto (fun n : ℕ => (rank (power T n) : ℝ) ^ ((n : ℝ)⁻¹))
      atTop (𝓝 (asymptoticRank T)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  convert tendsto_rankRoot T using 1
  funext n
  simp only [rankRoot, Nat.cast_add, Nat.cast_one]

theorem asymptoticRank_power (T : Tensor R I V) (q : ℕ) :
    asymptoticRank (power T q) = asymptoticRank T ^ q := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp only [pow_zero]
    apply le_antisymm
    · simpa using asymptoticRank_le_rank (power T 0)
    · apply one_le_asymptoticRank
      intro hz
      have h := (rank_eq_zero_iff _).mpr hz
      simp at h
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  have h := ((tendsto_power_rank_root T).comp (tendsto_id.const_mul_atTop' hq)).pow q
  have hlim : Tendsto (fun n : ℕ =>
      (rank (power (power T q) n) : ℝ) ^ ((n : ℝ)⁻¹))
      atTop (𝓝 (asymptoticRank T ^ q)) := by
    apply h.congr
    intro n
    change ((rank (power T (q * n)) : ℝ) ^ (((q * n : ℕ) : ℝ)⁻¹)) ^ q = _
    rw [rank_power_mul, ← Real.rpow_mul_natCast (Nat.cast_nonneg _) _ q]
    congr 1
    rw [Nat.cast_mul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hq0, mul_one]
  exact tendsto_nhds_unique (tendsto_power_rank_root (power T q)) hlim

variable {W : I → Type z} [∀ i, Fintype (W i)]

omit [Nontrivial R] [NoZeroDivisors R] [Fintype I]
    [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] in
theorem power_product_reindex (T : Tensor R I V) (S : Tensor R I W) (n : ℕ) :
    reindex (fun i => Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => V i) (fun _ => W i))
      (product (power T n) (power S n)) = power (product T S) n := by
  funext x
  exact (Finset.prod_mul_distrib : _).symm

omit [Nontrivial R] [NoZeroDivisors R] in
theorem rank_power_product_le (T : Tensor R I V) (S : Tensor R I W) (n : ℕ) :
    rank (power (product T S) n) ≤ rank (power T n) * rank (power S n) := by
  rw [← power_product_reindex, rank_reindex]
  exact rank_product_le _ _

theorem asymptoticRank_product_le (T : Tensor R I V) (S : Tensor R I W) :
    asymptoticRank (product T S) ≤ asymptoticRank T * asymptoticRank S := by
  apply le_of_tendsto_of_tendsto' (tendsto_power_rank_root (product T S))
    ((tendsto_power_rank_root T).mul (tendsto_power_rank_root S))
  intro n
  calc
    (rank (power (product T S) n) : ℝ) ^ ((n : ℝ)⁻¹) ≤
        ((rank (power T n) : ℝ) * (rank (power S n) : ℝ)) ^ ((n : ℝ)⁻¹) := by
      apply Real.rpow_le_rpow (Nat.cast_nonneg _)
      · exact_mod_cast rank_power_product_le T S n
      · positivity
    _ = (rank (power T n) : ℝ) ^ ((n : ℝ)⁻¹) *
        (rank (power S n) : ℝ) ^ ((n : ℝ)⁻¹) :=
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end Lemmata.TensorRank.Tensor
