module

public import Lemmata.TensorRank.Proof.WeightedGraph
public import Lemmata.TensorRank.Proof.WeightedCounting
public import Lemmata.TensorRank.Proof.GraphExponent

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace Lemmata.TensorRank

theorem edgeProduct_le_asymptoticRank_weighted {k : ℕ} (hk : 2 ≤ k)
    (d : Edge k → ℕ) (hd : ∀ e, 0 < d e) :
    ((∏ e, d e : ℕ) : ℝ) ^ edgeExponent k ≤ Tensor.asymptoticRank (weightedComplete d) := by
  let D : ℕ := ∏ e, d e
  let m : ℕ := 2 * (k - 2).factorial
  let A := Tensor.asymptoticRank (weightedComplete d)
  have hD : 0 < D := Finset.prod_pos (fun e _ => hd e)
  have hm : 0 < m := Nat.mul_pos (by decide) (Nat.factorial_pos _)
  have hA : 1 ≤ A := Tensor.one_le_asymptoticRank (weightedComplete_ne_zero hd)
  by_cases hD1 : D = 1
  · change (D : ℝ) ^ edgeExponent k ≤ A
    simpa only [hD1, Nat.cast_one, Real.one_rpow] using hA
  have hD2 : 2 ≤ D := by omega
  have hDm : 2 ≤ D ^ m := hD2.trans (le_self_pow (by omega) (Nat.ne_of_gt hm))
  have hsym := asymptoticRank_weighted_indexedProduct_le
    (fun σ : Equiv.Perm (Fin k) => fun e => d (edgeMap σ e))
  have hdim : (fun e => ∏ σ : Equiv.Perm (Fin k), d (edgeMap σ e)) =
      (fun _ : Edge k => D ^ m) := funext (prod_edgeMap hk d)
  rw [hdim] at hsym
  have hright : (∏ σ : Equiv.Perm (Fin k),
      Tensor.asymptoticRank (weightedComplete (fun e => d (edgeMap σ e)))) = A ^ k.factorial := by
    calc
      _ = ∏ _σ : Equiv.Perm (Fin k), A := Finset.prod_congr rfl
        (fun σ _ => asymptoticRank_weighted_relabel d σ)
      _ = _ := by simp [Fintype.card_perm]
  rw [hright] at hsym
  have hbound : ((D ^ m : ℕ) : ℝ) ^ graphExponent k ≤ A ^ k.factorial := by
    rw [asymptoticRank_weighted_constant, asymptoticRank_completeGraph hDm] at hsym
    exact hsym
  have hE : (k.choose 2 : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hk)
  have hfactor : (k.factorial : ℝ) = (k.choose 2 : ℝ) * m := by
    exact_mod_cast (edge_multiplicity_factorial hk).symm
  have hexp : edgeExponent k * (k.factorial : ℝ) = (m : ℝ) * graphExponent k := by
    rw [hfactor, edgeExponent]
    field_simp [hE]
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg (Nat.cast_nonneg D) _)
    (zero_le_one.trans hA) (Nat.cast_pos.mpr (Nat.factorial_pos k))).mp
  rw [← Real.rpow_mul (Nat.cast_nonneg D), hexp,
    Real.rpow_natCast_mul (Nat.cast_nonneg D), Real.rpow_natCast, ← Nat.cast_pow]
  exact hbound

end Lemmata.TensorRank
