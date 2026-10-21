module

public import Lemmata.TensorRank.Proof.CharacterProducts
public import Lemmata.TensorRank.Proof.TensorPermutation
public import Lemmata.TensorRank.Proof.WeightedCounting
public import Lemmata.TensorRank.Proof.Star

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank

theorem rank_weighted_le_prod {k : ℕ} (d : Edge k → ℕ) :
    Tensor.rank (weightedComplete d) ≤ ∏ e, d e := by
  let e : Fin (∏ a, d a) ≃ (∀ a, Fin (d a)) :=
    (Fintype.equivFinOfCardEq (by simp)).symm
  apply (Tensor.rank_le_iff _ _).mpr
  refine ⟨fun _ => 1, fun j i x => if x = weightedAssignment (e j) i then 1 else 0, ?_⟩
  funext x
  rw [weightedComplete_eq_sum]
  simp only [Finset.sum_apply, one_mul]
  exact Fintype.sum_equiv e.symm _ _ (fun _ => by simp)

theorem diagonal_restricts_completeGraph (k n : ℕ) [Nonempty (Fin k)] :
    Tensor.Restricts (Tensor.diagonal (R := ℂ) (I := Fin k) n) (completeGraph k n) := by
  classical
  have h := Tensor.reindex_restricts (fun (i : Fin k) (a : Fin n) (_ : Neighbors i) => a) (completeGraph k n)
  have he : Tensor.reindex (fun (i : Fin k) (a : Fin n) (_ : Neighbors i) => a)
      (completeGraph k n) = Tensor.diagonal n := by
    funext y
    have hi : (∀ (i j : Fin k), i ≠ j → y i = y j) ↔ ∃ a : Fin n, ∀ i, y i = a := by
      constructor
      · intro h
        let i : Fin k := Classical.arbitrary (Fin k)
        refine ⟨y i, fun j => ?_⟩
        by_cases hji : j = i
        · exact congrArg y hji
        · exact h j i hji
      · rintro ⟨a, ha⟩ i j _
        exact (ha i).trans (ha j).symm
    unfold Tensor.reindex completeGraph Tensor.diagonal
    split_ifs with hp hq hq
    · rfl
    · exact False.elim (hq (hi.mp hp))
    · exact False.elim (hp (hi.mpr hq))
    · rfl
  rw [he] at h
  exact h

end Lemmata.TensorRank

namespace Lemmata.TensorRank.TensorSemiring.Character

variable {k : ℕ} (f : Character k)

def pairValue (e : Edge k) (n : ℕ) : ℝ :=
  f.eval (weightedComplete (singleEdgeDimensions e n))

def pairExponent (e : Edge k) : ℝ := Real.log (f.pairValue e 2) / Real.log 2

theorem pairValue_mul (e : Edge k) (m n : ℕ) :
    f.pairValue e (m * n) = f.pairValue e m * f.pairValue e n := by
  have hd : (fun a => singleEdgeDimensions e m a * singleEdgeDimensions e n a) =
      singleEdgeDimensions e (m * n) := by
    funext a
    by_cases ha : a = e <;> simp [singleEdgeDimensions, ha]
  unfold pairValue
  rw [← hd, eval_weighted_product]

theorem pairValue_mono (e : Edge k) : Monotone (f.pairValue e) := by
  intro m n hmn
  have hd : ∀ a, singleEdgeDimensions e m a ≤ singleEdgeDimensions e n a := by
    intro a
    by_cases ha : a = e <;> simp [singleEdgeDimensions, ha, hmn]
  have hr := Tensor.reindex_restricts
    (fun i (x : WeightedCoordinate (singleEdgeDimensions e m) i) a => Fin.castLE (hd a.val) (x a))
    (weightedComplete (singleEdgeDimensions e n))
  rw [weighted_padding] at hr
  exact f.monotone hr

variable [Nonempty (Fin k)]

theorem one_le_pairValue (e : Edge k) {n : ℕ} (hn : 1 ≤ n) : 1 ≤ f.pairValue e n :=
  f.one_le_eval (weightedComplete_ne_zero (singleEdgeDimensions_pos e (by omega)))

theorem pairValue_le (e : Edge k) (n : ℕ) : f.pairValue e n ≤ n := by
  apply (f.eval_le_rank _).trans
  have h := rank_weighted_le_prod (singleEdgeDimensions e n)
  rw [prod_singleEdgeDimensions] at h
  exact_mod_cast h

@[simp] theorem pairValue_one (e : Edge k) : f.pairValue e 1 = 1 :=
  le_antisymm (by simpa only [Nat.cast_one] using f.pairValue_le e 1) (f.one_le_pairValue e le_rfl)

theorem pairExponent_nonneg (e : Edge k) : 0 ≤ f.pairExponent e :=
  div_nonneg (Real.log_nonneg (f.one_le_pairValue e (by omega : 1 ≤ 2))) (Real.log_pos (by norm_num)).le

theorem pairExponent_le_one (e : Edge k) : f.pairExponent e ≤ 1 := by
  apply (div_le_one (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  exact Real.log_le_log (zero_lt_one.trans_le (f.one_le_pairValue e (by omega : 1 ≤ 2))) (f.pairValue_le e 2)

theorem pairValue_eq_rpow (e : Edge k) {n : ℕ} (hn : 1 ≤ n) :
    f.pairValue e n = (n : ℝ) ^ f.pairExponent e :=
  monotone_multiplicative_eq_rpow (f.pairValue_one e) (f.pairValue_mul e) (f.pairValue_mono e) hn

theorem eval_weighted_eq_prod_rpow (d : Edge k → ℕ) (hd : ∀ e, 1 ≤ d e) :
    f.eval (weightedComplete d) = ∏ e, (d e : ℝ) ^ f.pairExponent e := by
  rw [eval_weighted_eq_prod_edges]
  apply Finset.prod_congr rfl
  intro e _
  exact f.pairValue_eq_rpow e (hd e)

theorem eval_completeGraph {n : ℕ} (hn : 1 ≤ n) :
    f.eval (completeGraph k n) = (n : ℝ) ^ (∑ e, f.pairExponent e) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h := f.eval_reindex (fun i => (constantCoordinate (n := n) i).symm)
    (weightedComplete (fun _ : Edge k => n))
  rw [weighted_constant_reindex] at h
  calc
    _ = f.eval (weightedComplete (fun _ : Edge k => n)) := h
    _ = ∏ e, (n : ℝ) ^ f.pairExponent e := f.eval_weighted_eq_prod_rpow _ (fun _ => hn)
    _ = _ := (Real.rpow_sum_of_pos hn0 _ _).symm

theorem one_le_sum_pairExponent : 1 ≤ ∑ e, f.pairExponent e := by
  have h := f.monotone (diagonal_restricts_completeGraph k 2)
  rw [eval_diagonal, eval_completeGraph f (by omega : 1 ≤ 2)] at h
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h
  simp only [Nat.cast_ofNat] at hl
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hl
  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

theorem sum_pairExponent_pos : 0 < ∑ e, f.pairExponent e :=
  zero_lt_one.trans_le f.one_le_sum_pairExponent

omit [Nonempty (Fin k)] in
theorem eval_relabel_pair (σ : Equiv.Perm (Fin k)) (e : Edge k) (n : ℕ) :
    f.eval (Tensor.relabel σ (weightedComplete (singleEdgeDimensions e n))) =
      f.pairValue ((edgeMap σ).symm e) n := by
  have hd : (fun a => singleEdgeDimensions e n (edgeMap σ a)) =
      singleEdgeDimensions ((edgeMap σ).symm e) n := by
    funext a
    simp only [singleEdgeDimensions, ← (edgeMap σ).eq_symm_apply]
  have h := f.eval_reindex (weightedRelabelCoordinate (singleEdgeDimensions e n) σ)
    (weightedComplete (fun a => singleEdgeDimensions e n (edgeMap σ a)))
  rw [weighted_relabel_reindex] at h
  rw [hd] at h
  exact h

theorem prod_eval_relabel_pair (hk : 2 ≤ k) (e : Edge k) {n : ℕ} (hn : 1 ≤ n) :
    (∏ σ : Equiv.Perm (Fin k),
      f.eval (Tensor.relabel σ (weightedComplete (singleEdgeDimensions e n)))) =
        (n : ℝ) ^ (((2 * (k - 2).factorial : ℕ) : ℝ) * ∑ a, f.pairExponent a) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hi : (∏ σ : Equiv.Perm (Fin k), f.pairValue ((edgeMap σ).symm e) n) =
      ∏ σ : Equiv.Perm (Fin k), f.pairValue (edgeMap σ e) n := by
    exact Fintype.prod_equiv (Equiv.inv (Equiv.Perm (Fin k))) _ _ (fun _ => rfl)
  calc
    _ = ∏ σ : Equiv.Perm (Fin k), f.pairValue ((edgeMap σ).symm e) n := by
      apply Finset.prod_congr rfl
      intro σ _
      exact f.eval_relabel_pair σ e n
    _ = (∏ a, f.pairValue a n) ^ (2 * (k - 2).factorial) :=
      hi.trans (prod_edgeMap hk (fun a => f.pairValue a n) e)
    _ = ((n : ℝ) ^ (∑ a, f.pairExponent a)) ^ (2 * (k - 2).factorial) := by
      congr 1
      calc
        _ = ∏ a, (n : ℝ) ^ f.pairExponent a := by
          apply Finset.prod_congr rfl
          intro a _
          exact f.pairValue_eq_rpow a hn
        _ = _ := (Real.rpow_sum_of_pos hn0 _ _).symm
    _ = _ := by rw [← Real.rpow_mul_natCast hn0.le]; congr 1; ring

end Lemmata.TensorRank.TensorSemiring.Character
