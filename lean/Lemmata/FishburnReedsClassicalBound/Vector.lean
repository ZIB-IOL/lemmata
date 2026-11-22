module

public import Lemmata.FishburnReedsClassicalBound.Upper
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

/-! # The vector value at the fixed shift

The columns of `V` are orthogonal of squared length `2(d-1)`, so `‖Vᵀ w‖² ≤ 2(d-1) ‖w‖²`
and `F₄ = 3 V Vᵀ - 4 I` satisfies `-(6d-10) I ⪯ F₄ ⪯ (6d-10) I` for `d ≥ 2`. Hence
`|∑ F₄(r,s) ⟨X_r, Y_s⟩| ≤ (6d-10) N = 2N(3d-5)` for unit vectors in any dimension, and the
normalized roots `V_r / √2` attain it in dimension `d`. -/

@[expose] public section

namespace Lemmata.FishburnReedsClassicalBound

open scoped BigOperators

/-! ### The column Gram matrix -/

theorem sum_pair_low (d : ℕ) (i k : Fin d) :
    ∑ j : Fin i.val, (if k = low i j then (1 : ℤ) else 0) = if k < i then 1 else 0 := by
  split_ifs with hki
  · rw [Finset.sum_eq_single (⟨k.val, hki⟩ : Fin i.val)]
    · simp [low]
    · intro j _ hj
      rw [if_neg]
      intro h
      apply hj
      ext
      simp [h, low]
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]
    intro h
    apply hki
    rw [h]
    exact low_lt i j

/-- `Vᵀ V = 2(d-1) I`. -/
theorem col_gram (d : ℕ) (k l : Fin d) :
    ∑ r, rootsZ d r k * rootsZ d r l = if k = l then 2 * ((d : ℤ) - 1) else 0 := by
  rw [sum_root]
  have hpair : ∀ (i : Fin d) (j : Fin i.val),
      rootsZ d ⟨i, (j, true)⟩ k * rootsZ d ⟨i, (j, true)⟩ l +
        rootsZ d ⟨i, (j, false)⟩ k * rootsZ d ⟨i, (j, false)⟩ l =
      2 * ((if k = i then 1 else 0) * (if l = i then 1 else 0) +
        (if k = low i j then 1 else 0) * (if l = low i j then 1 else 0)) := by
    intro i j
    rw [rootsZ_pair, rootsZ_pair, rootsZ_pair, rootsZ_pair]
    simp only [ite_true, Bool.false_eq_true, ite_false]
    split_ifs <;> ring
  simp_rw [hpair]
  split_ifs with hkl
  · subst hkl
    have hsq : ∀ (i : Fin d) (j : Fin i.val),
        (if k = i then (1 : ℤ) else 0) * (if k = i then 1 else 0) +
          (if k = low i j then 1 else 0) * (if k = low i j then 1 else 0) =
        (if k = i then 1 else 0) + (if k = low i j then 1 else 0) := by
      intro i j
      split_ifs <;> ring
    simp_rw [hsq, ← Finset.mul_sum, Finset.sum_add_distrib, sum_pair_low, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h1 : ∑ i : Fin d, ((i.val : ℕ) : ℤ) * (if k = i then 1 else 0) = k.val := by
      simp [mul_ite, Finset.sum_ite_eq]
    have h2 : ∑ i : Fin d, (if k < i then (1 : ℤ) else 0) = ((d - 1 - k.val : ℕ) : ℤ) := by
      rw [Finset.sum_boole, ← Fin.card_Ioi]
      congr 2
      ext i
      simp
    rw [h1, h2]
    have := k.isLt
    omega
  · refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs <;> simp_all


/-! ### The spectral bounds -/

theorem roots_col_gram (d : ℕ) (k l : Fin d) :
    ∑ r, roots d r k * roots d r l = if k = l then 2 * ((d : ℝ) - 1) else 0 := by
  simp only [roots_cast]
  have := col_gram d k l
  split_ifs at this ⊢ <;> exact_mod_cast this

/-- `∑_r (∑_k V_rk u_k)² = 2(d-1) ‖u‖²`. -/
theorem sum_sq_rows (d : ℕ) (u : Fin d → ℝ) :
    ∑ r, (∑ k, roots d r k * u k) ^ 2 = 2 * ((d : ℝ) - 1) * ∑ k, u k ^ 2 := by
  calc ∑ r, (∑ k, roots d r k * u k) ^ 2
      = ∑ r, ∑ k, ∑ l, u k * u l * (roots d r k * roots d r l) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    _ = ∑ k, ∑ l, u k * u l * ∑ r, roots d r k * roots d r l := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ k, u k * u k * (2 * ((d : ℝ) - 1)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [roots_col_gram, mul_ite, mul_zero]
        rw [Finset.sum_ite_eq]
        simp
    _ = 2 * ((d : ℝ) - 1) * ∑ k, u k ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring

/-- `‖Vᵀ w‖² ≤ 2(d-1) ‖w‖²`. -/
theorem energy_le (d : ℕ) (w : Root d → ℝ) :
    energy (roots d) w ≤ 2 * ((d : ℝ) - 1) * ∑ r, w r ^ 2 := by
  set u := coord (roots d) w with hu
  have hpair : ∑ k, u k ^ 2 = ∑ r, w r * ∑ k, roots d r k * u k := by
    calc ∑ k, u k ^ 2 = ∑ k, ∑ r, w r * roots d r k * u k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [sq, show u k * u k = (∑ r, w r * roots d r k) * u k from rfl, Finset.sum_mul]
      _ = ∑ r, w r * ∑ k, roots d r k * u k := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w (fun r => ∑ k, roots d r k * u k)
  rw [← hpair, sum_sq_rows] at hcs
  show ∑ k, u k ^ 2 ≤ _
  have hnn : 0 ≤ ∑ k, u k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hw : 0 ≤ ∑ r, w r ^ 2 := Finset.sum_nonneg fun r _ => sq_nonneg _
  rcases hnn.eq_or_lt with h0 | hpos
  · rw [← h0]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      exact mul_nonneg (by linarith) hw
  · nlinarith

/-- In order two the rows are orthogonal of squared length two. -/
theorem row_gram_two : ∀ r s : Root 2,
    ∑ k, rootsZ 2 r k * rootsZ 2 s k = if r = s then 2 else 0 := by
  decide

theorem energy_two (w : Root 2 → ℝ) : energy (roots 2) w = 2 * ∑ r, w r ^ 2 := by
  unfold energy coord
  calc ∑ k : Fin 2, (∑ r, w r * roots 2 r k) ^ 2
      = ∑ k : Fin 2, ∑ r, ∑ s, w r * w s * (roots 2 r k * roots 2 s k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring
    _ = ∑ r, ∑ s, w r * w s * ∑ k : Fin 2, roots 2 r k * roots 2 s k := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ r, w r * w r * 2 := by
        refine Finset.sum_congr rfl fun r _ => ?_
        have hg : ∀ s, ∑ k : Fin 2, roots 2 r k * roots 2 s k = if r = s then 2 else 0 := by
          intro s
          simp only [roots_cast]
          have := row_gram_two r s
          split_ifs at this ⊢ <;> exact_mod_cast this
        simp only [hg, mul_ite, mul_zero]
        rw [Finset.sum_ite_eq]
        simp
    _ = 2 * ∑ r, w r ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => by ring

/-- The bilinear form of `F₄` on two vectors indexed by the rows. -/
def formF (d : ℕ) (x y : Root d → ℝ) : ℝ :=
  ∑ r, ∑ s, (3 * ∑ k, roots d r k * roots d s k - 4 * (if r = s then 1 else 0)) * (x r * y s)

theorem formF_eq (d : ℕ) (x y : Root d → ℝ) :
    formF d x y = 3 * ∑ k, coord (roots d) x k * coord (roots d) y k - 4 * ∑ r, x r * y r := by
  have hG : ∑ r, ∑ s, (∑ k, roots d r k * roots d s k) * (x r * y s) =
      ∑ k, coord (roots d) x k * coord (roots d) y k := by
    unfold coord
    calc ∑ r, ∑ s, (∑ k, roots d r k * roots d s k) * (x r * y s)
        = ∑ r, ∑ s, ∑ k, x r * roots d r k * (y s * roots d s k) := by
          refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = ∑ k, ∑ r, ∑ s, x r * roots d r k * (y s * roots d s k) := by
          have hswap : ∀ r, ∑ s, ∑ k, x r * roots d r k * (y s * roots d s k) =
              ∑ k, ∑ s, x r * roots d r k * (y s * roots d s k) := fun r => Finset.sum_comm
          simp_rw [hswap]
          exact Finset.sum_comm
      _ = ∑ k, (∑ r, x r * roots d r k) * ∑ s, y s * roots d s k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul_sum]
  have hD : ∑ r, ∑ s, (if r = s then (1 : ℝ) else 0) * (x r * y s) = ∑ r, x r * y r := by
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp
  unfold formF
  rw [← hG, ← hD, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring


/-- `x ↦ Vᵀ x` is additive. -/
theorem coord_add (d : ℕ) (x y : Root d → ℝ) (k : Fin d) :
    coord (roots d) (fun r => x r + y r) k = coord (roots d) x k + coord (roots d) y k := by
  unfold coord
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun r _ => by ring

theorem coord_sub (d : ℕ) (x y : Root d → ℝ) (k : Fin d) :
    coord (roots d) (fun r => x r - y r) k = coord (roots d) x k - coord (roots d) y k := by
  unfold coord
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun r _ => by ring

/-- `F₄ ⪯ (6d-10) I` and `-(6d-10) I ⪯ F₄` give the bilinear bound. -/
theorem formF_le (d : ℕ) (hd : 2 ≤ d) (x y : Root d → ℝ) :
    formF d x y ≤ (3 * (d : ℝ) - 5) * (∑ r, x r ^ 2 + ∑ r, y r ^ 2) := by
  set u := coord (roots d) x
  set v := coord (roots d) y
  have hm := energy_le d (fun r => x r + y r)
  have hq : 0 ≤ (6 * (d : ℝ) - 14) * ∑ r, (x r - y r) ^ 2 +
      3 * energy (roots d) (fun r => x r - y r) := by
    rcases Nat.lt_or_ge d 3 with h3 | h3
    · obtain rfl : d = 2 := by omega
      rw [energy_two]
      have := Finset.sum_nonneg fun r (_ : r ∈ Finset.univ) => sq_nonneg (x r - y r)
      norm_num
      linarith
    · have h3' : (3 : ℝ) ≤ d := by exact_mod_cast h3
      have e0 : 0 ≤ energy (roots d) (fun r => x r - y r) :=
        Finset.sum_nonneg fun k _ => sq_nonneg _
      have s0 := Finset.sum_nonneg fun r (_ : r ∈ Finset.univ) => sq_nonneg (x r - y r)
      nlinarith
  have hm' : energy (roots d) (fun r => x r + y r) = ∑ k, (u k + v k) ^ 2 :=
    Finset.sum_congr rfl fun k _ => by rw [coord_add]
  have hq' : energy (roots d) (fun r => x r - y r) = ∑ k, (u k - v k) ^ 2 :=
    Finset.sum_congr rfl fun k _ => by rw [coord_sub]
  rw [hm'] at hm
  rw [hq'] at hq
  rw [formF_eq]
  have e1 : ∑ r, (x r + y r) ^ 2 = ∑ r, x r ^ 2 + 2 * ∑ r, x r * y r + ∑ r, y r ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  have e2 : ∑ r, (x r - y r) ^ 2 = ∑ r, x r ^ 2 - 2 * ∑ r, x r * y r + ∑ r, y r ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  have e3 : ∑ k, (u k + v k) ^ 2 = ∑ k, u k ^ 2 + 2 * ∑ k, u k * v k + ∑ k, v k ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e4 : ∑ k, (u k - v k) ^ 2 = ∑ k, u k ^ 2 - 2 * ∑ k, u k * v k + ∑ k, v k ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e1, e3] at hm
  rw [e2, e4] at hq
  nlinarith

/-- The vector value splits over the coordinates of the vectors. -/
theorem vectorValue_eq (d n : ℕ) (X Y : Root d → Fin n → ℝ) :
    vectorValue (roots d) X Y = ∑ l, formF d (fun r => X r l) (fun r => Y r l) := by
  unfold vectorValue formF
  have h1 : ∀ r s, (3 * ∑ k, roots d r k * roots d s k - 4 * (if r = s then (1 : ℝ) else 0)) *
      ∑ l, X r l * Y s l = ∑ l, (3 * ∑ k, roots d r k * roots d s k -
        4 * (if r = s then (1 : ℝ) else 0)) * (X r l * Y s l) := fun r s => Finset.mul_sum _ _ _
  simp_rw [h1]
  have hswap : ∀ r, ∑ s, ∑ l,
      (3 * ∑ k, roots d r k * roots d s k - 4 * (if r = s then (1 : ℝ) else 0)) *
        (X r l * Y s l) =
      ∑ l, ∑ s, (3 * ∑ k, roots d r k * roots d s k - 4 * (if r = s then (1 : ℝ) else 0)) *
        (X r l * Y s l) := fun r => Finset.sum_comm
  simp_rw [hswap]
  exact Finset.sum_comm

theorem card_root (d : ℕ) : (Fintype.card (Root d) : ℝ) = d * ((d : ℝ) - 1) := by
  have h : Fintype.card (Root d) = ∑ i : Fin d, i.val * 2 := by
    simp [Root, Fintype.card_sigma, Fintype.card_prod]
  have h2 : ∑ i : Fin d, i.val * 2 = d * (d - 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i * 2), ← Finset.sum_mul,
      Finset.sum_range_id_mul_two]
  rw [h, h2]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · push_cast [Nat.cast_sub (show 1 ≤ d from hd)]
    ring

theorem unitRows_sum {n d : ℕ} (X : Root d → Fin n → ℝ) (hX : UnitRows X) :
    ∑ l, ∑ r, X r l ^ 2 = d * ((d : ℝ) - 1) := by
  rw [Finset.sum_comm]
  have hX' : ∀ r, ∑ l, X r l ^ 2 = 1 := hX
  simp only [hX', Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact card_root d

/-- The upper bound in every dimension. -/
theorem vectorValue_le (d : ℕ) (hd : 2 ≤ d) (n : ℕ) (X Y : Root d → Fin n → ℝ)
    (hX : UnitRows X) (hY : UnitRows Y) :
    vectorValue (roots d) X Y ≤ 2 * (d : ℝ) * ((d : ℝ) - 1) * (3 * (d : ℝ) - 5) := by
  rw [vectorValue_eq]
  calc ∑ l, formF d (fun r => X r l) (fun r => Y r l)
      ≤ ∑ l, (3 * (d : ℝ) - 5) * (∑ r, X r l ^ 2 + ∑ r, Y r l ^ 2) :=
        Finset.sum_le_sum fun l _ => formF_le d hd _ _
    _ = (3 * (d : ℝ) - 5) * (∑ l, ∑ r, X r l ^ 2 + ∑ l, ∑ r, Y r l ^ 2) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
    _ = 2 * (d : ℝ) * ((d : ℝ) - 1) * (3 * (d : ℝ) - 5) := by
        rw [unitRows_sum X hX, unitRows_sum Y hY]
        ring

theorem vectorValue_neg (d n : ℕ) (X Y : Root d → Fin n → ℝ) :
    vectorValue (roots d) (fun r l => -X r l) Y = -vectorValue (roots d) X Y := by
  unfold vectorValue
  simp only [neg_mul, Finset.sum_neg_distrib, mul_neg]

/-- Squared length two for every root row. -/
theorem row_sq (d : ℕ) (r : Root d) : ∑ k, roots d r k ^ 2 = 2 := by
  obtain ⟨i, j, b⟩ := r
  have hne : low i j ≠ i := ne_of_lt (low_lt i j)
  have h : ∀ k : Fin d, roots d ⟨i, (j, b)⟩ k ^ 2 =
      (if k = i then 1 else 0) + (if k = low i j then 1 else 0) := by
    intro k
    rw [roots_cast, rootsZ_pair]
    by_cases h1 : k = i <;> by_cases h2 : k = low i j
    · exact absurd (h2.symm.trans h1) hne
    all_goals cases b <;> simp [h1, h2, hne, hne.symm]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num

/-- The normalized roots attain the bound in dimension `d`. -/
theorem vectorValue_roots (d : ℕ) :
    vectorValue (roots d) (fun r l => roots d r l / Real.sqrt 2)
      (fun r l => roots d r l / Real.sqrt 2) =
      2 * (d : ℝ) * ((d : ℝ) - 1) * (3 * (d : ℝ) - 5) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  have hcoord : ∀ l k, coord (roots d) (fun r => roots d r l / Real.sqrt 2) k =
      (if l = k then 2 * ((d : ℝ) - 1) else 0) / Real.sqrt 2 := by
    intro l k
    unfold coord
    rw [← roots_col_gram, Finset.sum_div]
    exact Finset.sum_congr rfl fun r _ => by ring
  have hform : ∀ l, formF d (fun r => roots d r l / Real.sqrt 2)
      (fun r => roots d r l / Real.sqrt 2) = 6 * ((d : ℝ) - 1) ^ 2 - 4 * ((d : ℝ) - 1) := by
    intro l
    rw [formF_eq]
    simp only [hcoord]
    have hsq : ∀ k, (if l = k then 2 * ((d : ℝ) - 1) else 0) / Real.sqrt 2 *
        ((if l = k then 2 * ((d : ℝ) - 1) else 0) / Real.sqrt 2) =
        if l = k then 2 * ((d : ℝ) - 1) ^ 2 else 0 := by
      intro k
      split_ifs
      · field_simp
        rw [h2]
        ring
      · simp
    simp only [hsq, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hcol : ∑ r, roots d r l / Real.sqrt 2 * (roots d r l / Real.sqrt 2) = (d : ℝ) - 1 := by
      have := roots_col_gram d l l
      simp only [ite_true] at this
      have e : ∀ r, roots d r l / Real.sqrt 2 * (roots d r l / Real.sqrt 2) =
          roots d r l * roots d r l / 2 := by
        intro r
        field_simp
        rw [h2]
      simp only [e, ← Finset.sum_div, this]
      ring
    rw [hcol]
    ring
  rw [vectorValue_eq]
  simp only [hform, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem unitRows_roots (d : ℕ) : UnitRows (fun (r : Root d) (l : Fin d) => roots d r l / Real.sqrt 2) := by
  intro r
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [div_pow, h2, ← Finset.sum_div, row_sq]
  norm_num

/-- **The exact vector value at the fixed shift.** -/
theorem fixedVectorValue (d : ℕ) (hd : 2 ≤ d) : FixedVectorValue d := by
  refine ⟨fun n X Y hX hY => abs_le.mpr ⟨?_, vectorValue_le d hd n X Y hX hY⟩,
    ⟨_, unitRows_roots d, vectorValue_roots d⟩⟩
  have hnX : UnitRows (fun r l => -X r l) := fun r => by simpa using hX r
  have := vectorValue_le d hd n (fun r l => -X r l) Y hnX hY
  rw [vectorValue_neg] at this
  linarith

end Lemmata.FishburnReedsClassicalBound
