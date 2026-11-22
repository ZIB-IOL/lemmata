module

public import Lemmata.GrothendieckLowerBounds.Statement
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

/-! # From the unit ball to the unit sphere

For fixed column vectors the value `∑ M_ij ⟨u_i, v_j⟩` is linear in each row vector `u_i`:
it is `∑_i ⟨u_i, w_i⟩` with `w_i = ∑_j M_ij v_j`. Replacing every `u_i` in the unit ball by the
unit vector in the direction of `w_i` therefore does not decrease the value, by Cauchy–Schwarz;
the same then holds for the column vectors. Appending zero coordinates keeps unit vectors and
values, so lower bounds pass to higher orders. -/

@[expose] public section

namespace Lemmata.GrothendieckLowerBounds

open scoped BigOperators

/-- The unit vector in the direction of `w`, or the first basis vector when `w = 0`. -/
noncomputable def unitDir {d : ℕ} (hd : 0 < d) (w : Fin d → ℝ) : Fin d → ℝ :=
  if ∑ k, w k ^ 2 = 0 then fun k => if k = ⟨0, hd⟩ then 1 else 0
  else fun k => w k / Real.sqrt (∑ k, w k ^ 2)

theorem unitDir_unit {d : ℕ} (hd : 0 < d) (w : Fin d → ℝ) : ∑ k, unitDir hd w k ^ 2 = 1 := by
  unfold unitDir
  split_ifs with h
  · simp [ite_pow, Finset.sum_ite_eq']
  · have hpos : 0 < ∑ k, w k ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun k _ => sq_nonneg _) (Ne.symm h)
    simp only [div_pow, Real.sq_sqrt hpos.le, ← Finset.sum_div]
    exact div_self h

theorem le_unitDir {d : ℕ} (hd : 0 < d) (w x : Fin d → ℝ) (hx : ∑ k, x k ^ 2 ≤ 1) :
    ∑ k, x k * w k ≤ ∑ k, unitDir hd w k * w k := by
  unfold unitDir
  split_ifs with h
  · have hw : ∀ k, w k = 0 := fun k =>
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
        ((Finset.sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg (w k)).mp h k (Finset.mem_univ _))
    simp [hw]
  · have hpos : 0 < ∑ k, w k ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun k _ => sq_nonneg _) (Ne.symm h)
    have hs : 0 < Real.sqrt (∑ k, w k ^ 2) := Real.sqrt_pos.mpr hpos
    have hr : ∑ k, w k / Real.sqrt (∑ k, w k ^ 2) * w k = Real.sqrt (∑ k, w k ^ 2) := by
      have : ∑ k, w k / Real.sqrt (∑ k, w k ^ 2) * w k =
          (∑ k, w k ^ 2) / Real.sqrt (∑ k, w k ^ 2) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [this, div_eq_iff hs.ne', Real.mul_self_sqrt hpos.le]
    rw [hr]
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ x w
    have hx1 : Real.sqrt (∑ k, x k ^ 2) ≤ 1 := by
      rw [Real.sqrt_le_one]
      exact hx
    calc ∑ k, x k * w k ≤ Real.sqrt (∑ k, x k ^ 2) * Real.sqrt (∑ k, w k ^ 2) := hcs
      _ ≤ 1 * Real.sqrt (∑ k, w k ^ 2) := mul_le_mul_of_nonneg_right hx1 hs.le
      _ = Real.sqrt (∑ k, w k ^ 2) := one_mul _

theorem vectorObj_rows {n m d : ℕ} (M : BellMatrix n m) (u : Fin n → Fin d → ℝ)
    (v : Fin m → Fin d → ℝ) : vectorObj M u v = ∑ i, ∑ k, u i k * ∑ j, M i j * v j k := by
  unfold vectorObj
  refine Finset.sum_congr rfl fun i _ => ?_
  calc ∑ j, M i j * ∑ k, u i k * v j k = ∑ j, ∑ k, u i k * (M i j * v j k) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ k, u i k * ∑ j, M i j * v j k := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm

theorem vectorObj_cols {n m d : ℕ} (M : BellMatrix n m) (u : Fin n → Fin d → ℝ)
    (v : Fin m → Fin d → ℝ) : vectorObj M u v = ∑ j, ∑ k, v j k * ∑ i, M i j * u i k := by
  unfold vectorObj
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc ∑ i, M i j * ∑ k, u i k * v j k = ∑ i, ∑ k, v j k * (M i j * u i k) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ k, v j k * ∑ i, M i j * u i k := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm

/-- Vectors in the unit ball can be replaced by unit vectors without decreasing the value. -/
theorem exists_unit_ge {n m d : ℕ} (hd : 0 < d) (M : BellMatrix n m)
    (u : Fin n → Fin d → ℝ) (v : Fin m → Fin d → ℝ)
    (hu : ∀ i, ∑ k, u i k ^ 2 ≤ 1) (hv : ∀ j, ∑ k, v j k ^ 2 ≤ 1) :
    ∃ (u' : Fin n → Fin d → ℝ) (v' : Fin m → Fin d → ℝ), UnitVectors u' ∧ UnitVectors v' ∧
      vectorObj M u v ≤ vectorObj M u' v' := by
  let u' : Fin n → Fin d → ℝ := fun i => unitDir hd fun k => ∑ j, M i j * v j k
  let v' : Fin m → Fin d → ℝ := fun j => unitDir hd fun k => ∑ i, M i j * u' i k
  refine ⟨u', v', fun i => unitDir_unit hd _, fun j => unitDir_unit hd _, ?_⟩
  calc vectorObj M u v = ∑ i, ∑ k, u i k * ∑ j, M i j * v j k := vectorObj_rows M u v
    _ ≤ ∑ i, ∑ k, u' i k * ∑ j, M i j * v j k :=
        Finset.sum_le_sum fun i _ => le_unitDir hd _ (u i) (hu i)
    _ = vectorObj M u' v := (vectorObj_rows M u' v).symm
    _ = ∑ j, ∑ k, v j k * ∑ i, M i j * u' i k := vectorObj_cols M u' v
    _ ≤ ∑ j, ∑ k, v' j k * ∑ i, M i j * u' i k :=
        Finset.sum_le_sum fun j _ => le_unitDir hd _ (v j) (hv j)
    _ = vectorObj M u' v' := (vectorObj_cols M u' v').symm

theorem sum_pad {d d' : ℕ} (h : d ≤ d') (f : Fin d → ℝ) (g : Fin d' → ℝ)
    (hg : ∀ k : Fin d', d ≤ k.val → g k = 0) (hfg : ∀ k : Fin d, f k = g (Fin.castLE h k)) :
    ∑ k, f k = ∑ k, g k :=
  Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) f g
    (fun k hk => hg k (by
      by_contra hlt
      exact hk ⟨⟨k.val, by omega⟩, Fin.ext rfl⟩)) hfg

/-- Zero-padding of a vector from `ℝ^d` to `ℝ^{d'}`. -/
noncomputable def padv {d d' : ℕ} (a : Fin d → ℝ) : Fin d' → ℝ :=
  fun k => if hk : k.val < d then a ⟨k.val, hk⟩ else 0

theorem padv_inner {d d' : ℕ} (h : d ≤ d') (a b : Fin d → ℝ) :
    ∑ k : Fin d', padv a k * padv b k = ∑ k, a k * b k := by
  refine (sum_pad h _ _ (fun k hk => ?_) (fun k => ?_)).symm
  · simp [padv, show ¬ k.val < d by omega]
  · simp [padv, Fin.castLE, k.isLt]

/-- A lower bound for `K_G(d)` is one for every larger order. -/
theorem GrothendieckLowerBound.mono {d d' : ℕ} (h : d ≤ d') {x : ℝ}
    (hx : GrothendieckLowerBound d x) : GrothendieckLowerBound d' x := by
  obtain ⟨n, m, M, B, hB, hC, u, v, hu, hv, hlt⟩ := hx
  refine ⟨n, m, M, B, hB, hC, fun i => padv (u i), fun j => padv (v j), fun i => ?_,
    fun j => ?_, ?_⟩
  · simp only [sq]
    rw [padv_inner h]
    simpa [sq] using hu i
  · simp only [sq]
    rw [padv_inner h]
    simpa [sq] using hv j
  · have : vectorObj M (fun i => padv (d' := d') (u i)) (fun j => padv (d' := d') (v j)) =
        vectorObj M u v := by
      unfold vectorObj
      simp only [padv_inner h]
    rw [this]
    exact hlt

end Lemmata.GrothendieckLowerBounds
