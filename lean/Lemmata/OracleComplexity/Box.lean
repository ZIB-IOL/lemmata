module

public import Lemmata.OracleComplexity.StringGuess

@[expose] public section

/-!
# The hard functions of Section IV.A

The hard function of a string `S ∈ {0,1}^M` is the maximum of the pieces
`V_j(x) = b_j - 8^{-j} + 2^{-j} |x - c_j(S)|`, `j ≤ M`, where the centers `c_j(S)` follow the bits
of `S` into nested intervals of radius `4^{-j}`. Outside the interval of depth `j` the piece of
depth `j + 1` lies below the piece of depth `j` (`piece_step`), so outside it all deeper pieces do.
The greedy path towards a point `x` recovers the string of every function that is nearly minimal at
`x` (`path_of_near`), which gives the packing property.
-/

namespace Lemmata.OracleComplexity

open Real

variable {M : ℕ}

theorem bitSign_abs (b : Bool) : |bitSign b| = 1 := by cases b <;> simp [bitSign]

theorem boxLevel_succ (j : ℕ) : boxLevel (j + 1) = boxLevel j - 1 / 2 * (1 / 8) ^ j := by
  unfold boxLevel
  rw [pow_succ]
  ring

theorem boxCenter_succ (S : Fin M → Bool) {j : ℕ} (hj : j < M) :
    boxCenter S (j + 1) = boxCenter S j + bitSign (S ⟨j, hj⟩) * (1 / 4) ^ (j + 1) := by
  unfold boxCenter
  have h : ∀ i : Fin M, (if (i : ℕ) < j + 1 then bitSign (S i) * (1 / 4) ^ ((i : ℕ) + 1) else 0) =
      (if (i : ℕ) < j then bitSign (S i) * (1 / 4) ^ ((i : ℕ) + 1) else 0) +
      (if i = ⟨j, hj⟩ then bitSign (S i) * (1 / 4) ^ ((i : ℕ) + 1) else 0) := by
    intro i
    by_cases h1 : (i : ℕ) < j
    · have hne : i ≠ ⟨j, hj⟩ := fun e => by rw [e] at h1; exact lt_irrefl _ h1
      simp [h1, Nat.lt_succ_of_lt h1, hne]
    · by_cases h2 : (i : ℕ) = j
      · have he : i = ⟨j, hj⟩ := Fin.ext h2
        subst he
        simp
      · have h3 : ¬ (i : ℕ) < j + 1 := by omega
        have hne : i ≠ ⟨j, hj⟩ := fun e => h2 (by rw [e])
        simp [h1, h3, hne]
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem boxCenter_congr {S S' : Fin M → Bool} {j : ℕ}
    (h : ∀ i : Fin M, (i : ℕ) < j → S i = S' i) : boxCenter S j = boxCenter S' j := by
  unfold boxCenter
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [h i hi]
  · rfl

theorem boxCenter_step (S : Fin M → Bool) {j : ℕ} (hj : j < M) :
    |boxCenter S (j + 1) - boxCenter S j| = (1 / 4) ^ (j + 1) := by
  rw [boxCenter_succ S hj, add_sub_cancel_left, abs_mul, bitSign_abs, one_mul,
    abs_of_pos (by positivity)]

theorem boxCenter_tail (S : Fin M → Bool) : ∀ d j, j + d = M →
    |boxCenter S M - boxCenter S j| ≤ ((1 / 4) ^ j - (1 / 4) ^ M) / 3 := by
  intro d
  induction d with
  | zero =>
    intro j hj
    simp only [add_zero] at hj
    subst hj
    simp
  | succ d ih =>
    intro j hj
    have hjM : j < M := by omega
    have h1 := ih (j + 1) (by omega)
    have h2 := boxCenter_step S hjM
    calc |boxCenter S M - boxCenter S j|
        ≤ |boxCenter S M - boxCenter S (j + 1)| + |boxCenter S (j + 1) - boxCenter S j| :=
          abs_sub_le _ _ _
      _ ≤ ((1 / 4) ^ (j + 1) - (1 / 4) ^ M) / 3 + (1 / 4) ^ (j + 1) := by rw [h2]; linarith
      _ = ((1 / 4) ^ j - (1 / 4) ^ M) / 3 := by rw [pow_succ]; ring

/-- Outside the interval of depth `j`, the piece of depth `j + 1` lies below the piece of depth
`j`, and the point is outside the interval of depth `j + 1`. -/
theorem piece_step (S : Fin M → Bool) {j : ℕ} (hj : j < M) {x : ℝ}
    (hx : (1 / 4) ^ j ≤ |x - boxCenter S j|) :
    boxPiece S (j + 1) x ≤ boxPiece S j x ∧ (1 / 4) ^ (j + 1) ≤ |x - boxCenter S (j + 1)| := by
  have hd := boxCenter_step S hj
  have htri : |x - boxCenter S (j + 1)| ≤ |x - boxCenter S j| + (1 / 4) ^ (j + 1) := by
    calc |x - boxCenter S (j + 1)| ≤ |x - boxCenter S j| + |boxCenter S j - boxCenter S (j + 1)| :=
          abs_sub_le _ _ _
      _ = |x - boxCenter S j| + (1 / 4) ^ (j + 1) := by
          rw [abs_sub_comm (boxCenter S j) (boxCenter S (j + 1)), hd]
  have htri2 : |x - boxCenter S j| - (1 / 4) ^ (j + 1) ≤ |x - boxCenter S (j + 1)| := by
    have := abs_sub_le x (boxCenter S (j + 1)) (boxCenter S j)
    rw [hd] at this
    linarith
  have e1 : (1 / 8 : ℝ) ^ j = (1 / 2) ^ j * (1 / 4) ^ j := by rw [← mul_pow]; norm_num
  have e2 : (1 / 2 : ℝ) ^ (j + 1) = (1 / 2) ^ j / 2 := by rw [pow_succ]; ring
  have e3 : (1 / 8 : ℝ) ^ (j + 1) = (1 / 8) ^ j / 8 := by rw [pow_succ]; ring
  have e4 : (1 / 4 : ℝ) ^ (j + 1) = (1 / 4) ^ j / 4 := by rw [pow_succ]; ring
  rw [e4] at htri htri2
  refine ⟨?_, ?_⟩
  · unfold boxPiece
    rw [boxLevel_succ, e2, e3, e1]
    have ha : (0 : ℝ) ≤ (1 / 2) ^ j / 2 := by positivity
    have k1 := mul_le_mul_of_nonneg_left htri ha
    have k2 := mul_le_mul_of_nonneg_left hx ha
    nlinarith
  · rw [e4]
    have : (0 : ℝ) ≤ (1 / 4) ^ j := by positivity
    linarith

/-- The descending chain of pieces outside the interval of depth `k`. -/
theorem piece_chain (S : Fin M → Bool) {k : ℕ} {x : ℝ}
    (hx : (1 / 4) ^ k ≤ |x - boxCenter S k|) : ∀ d, k + d ≤ M →
      boxPiece S (k + d) x ≤ boxPiece S k x ∧ (1 / 4) ^ (k + d) ≤ |x - boxCenter S (k + d)| := by
  intro d
  induction d with
  | zero => intro _; exact ⟨le_rfl, hx⟩
  | succ d ih =>
    intro hd
    obtain ⟨h1, h2⟩ := ih (by omega)
    obtain ⟨h3, h4⟩ := piece_step S (j := k + d) (by omega) h2
    exact ⟨h3.trans h1, h4⟩

theorem boxPiece_congr {S S' : Fin M → Bool} {j : ℕ}
    (h : ∀ i : Fin M, (i : ℕ) < j → S i = S' i) (x : ℝ) :
    boxPiece S j x = boxPiece S' j x ∧ pieceSlope S j x = pieceSlope S' j x := by
  unfold boxPiece pieceSlope
  rw [boxCenter_congr h]
  exact ⟨rfl, rfl⟩

/-- The fold computes the maximum of the pieces. -/
theorem boxBest_fst (S : Fin M → Bool) (x : ℝ) : ∀ j, (boxBest S x j).1 =
    (Finset.range (j + 1)).sup' Finset.nonempty_range_add_one (fun l => boxPiece S l x) := by
  intro j
  induction j with
  | zero => simp [boxBest]
  | succ j ih =>
    have hr : Finset.range (j + 1 + 1) = insert (j + 1) (Finset.range (j + 1)) :=
      Finset.range_add_one
    simp only [boxBest]
    rw [Finset.sup'_congr Finset.nonempty_range_add_one hr (fun _ _ => rfl),
      Finset.sup'_insert Finset.nonempty_range_add_one, ← ih]
    split_ifs with h
    · exact (max_eq_left h.le).symm
    · push Not at h
      exact (max_eq_right h).symm

/-- The fold returns a piece attaining the maximum, with its slope. -/
theorem boxBest_piece (S : Fin M → Bool) (x : ℝ) :
    ∀ j, ∃ l ≤ j, boxBest S x j = (boxPiece S l x, pieceSlope S l x) := by
  intro j
  induction j with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ j ih =>
    obtain ⟨l, hl, hb⟩ := ih
    simp only [boxBest]
    split_ifs
    · exact ⟨j + 1, le_rfl, rfl⟩
    · exact ⟨l, by omega, hb⟩

theorem boxBest_ge (S : Fin M → Bool) (x : ℝ) (j : ℕ) {l : ℕ} (hl : l ≤ j) :
    boxPiece S l x ≤ (boxBest S x j).1 := by
  rw [boxBest_fst]
  exact Finset.le_sup' (fun l => boxPiece S l x) (Finset.mem_range.mpr (by omega))

/-- If the pieces beyond depth `k` do not exceed the maximum up to `k`, the fold is constant from
`k` on. -/
theorem boxBest_stable (S : Fin M → Bool) (x : ℝ) {k : ℕ}
    (h : ∀ l, k < l → l ≤ M → boxPiece S l x ≤ (boxBest S x k).1) :
    ∀ d, k + d ≤ M → boxBest S x (k + d) = boxBest S x k := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
    intro hd
    have ih' := ih (by omega)
    show boxBest S x (k + d + 1) = _
    simp only [boxBest]
    rw [ih', ite_eq_right (not_lt.mpr (h (k + d + 1) (by omega) (by omega)))]

/-- The fold up to depth `k` depends only on the first `k` bits. -/
theorem boxBest_congr {S S' : Fin M → Bool} {k : ℕ} (h : ∀ i : Fin M, (i : ℕ) < k → S i = S' i)
    (x : ℝ) : ∀ j ≤ k, boxBest S x j = boxBest S' x j := by
  intro j
  induction j with
  | zero =>
    intro _
    have hc := boxPiece_congr (S := S) (S' := S') (j := 0) (fun i hi => absurd hi (by omega)) x
    simp only [boxBest, hc.1, hc.2]
  | succ j ih =>
    intro hj
    have hc := boxPiece_congr (S := S) (S' := S') (j := j + 1)
      (fun i hi => h i (by omega)) x
    simp only [boxBest, ih (by omega), hc.1, hc.2]

/-- The subgradient inequality of a piece. -/
theorem boxPiece_subgrad (S : Fin M → Bool) (j : ℕ) (x y : ℝ) :
    boxPiece S j x + pieceSlope S j x * (y - x) ≤ boxPiece S j y := by
  unfold boxPiece pieceSlope
  have key : |x - boxCenter S j| + Real.sign (x - boxCenter S j) * (y - x) ≤
      |y - boxCenter S j| := by
    rcases lt_trichotomy (x - boxCenter S j) 0 with hlt | heq | hgt
    · rw [Real.sign_of_neg hlt, abs_of_neg hlt]
      have := neg_abs_le (y - boxCenter S j)
      linarith
    · rw [heq, Real.sign_zero, abs_zero]
      simp
    · rw [Real.sign_of_pos hgt, abs_of_pos hgt]
      have := le_abs_self (y - boxCenter S j)
      linarith
  have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ (1 / 2) ^ j)
  nlinarith

namespace Proof

theorem box_oracle_valid : BoxOracleValid := by
  intro M S
  refine ⟨?_, ?_, fun x => ⟨?_, fun y => ?_⟩⟩
  · -- convexity: the maximum of convex pieces
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    obtain ⟨l, hl, hmax⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
      (fun j => boxPiece S j (a • x + b • y))
    have hfx : boxPiece S l x ≤ boxFn S x :=
      Finset.le_sup' (fun j => boxPiece S j x) hl
    have hfy : boxPiece S l y ≤ boxFn S y :=
      Finset.le_sup' (fun j => boxPiece S j y) hl
    have hpiece : boxPiece S l (a • x + b • y) ≤ a • boxPiece S l x + b • boxPiece S l y := by
      simp only [smul_eq_mul, boxPiece]
      have h1 : |a * x + b * y - boxCenter S l| ≤
          a * |x - boxCenter S l| + b * |y - boxCenter S l| := by
        have e : a * x + b * y - boxCenter S l =
            a * (x - boxCenter S l) + b * (y - boxCenter S l) := by
          rw [show a * (x - boxCenter S l) + b * (y - boxCenter S l) =
            a * x + b * y - (a + b) * boxCenter S l by ring, hab, one_mul]
        rw [e]
        calc |a * (x - boxCenter S l) + b * (y - boxCenter S l)|
            ≤ |a * (x - boxCenter S l)| + |b * (y - boxCenter S l)| := abs_add_le _ _
          _ = a * |x - boxCenter S l| + b * |y - boxCenter S l| := by
              rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (1 / 2) ^ l)
      have e2 : boxLevel l - (1 / 8) ^ l = a * (boxLevel l - (1 / 8) ^ l) +
          b * (boxLevel l - (1 / 8) ^ l) := by rw [← add_mul, hab, one_mul]
      nlinarith
    show boxFn S (a • x + b • y) ≤ a • boxFn S x + b • boxFn S y
    unfold boxFn
    rw [hmax]
    simp only [smul_eq_mul] at hpiece ⊢
    have k1 := mul_le_mul_of_nonneg_left hfx ha
    have k2 := mul_le_mul_of_nonneg_left hfy hb
    unfold boxFn at k1 k2
    linarith
  · -- the Lipschitz bound
    apply LipschitzWith.of_le_add_mul
    intro x y
    unfold boxFn
    apply Finset.sup'_le
    intro j hj
    have h1 : boxPiece S j x ≤ boxPiece S j y + dist x y := by
      unfold boxPiece
      have h3 : |x - boxCenter S j| ≤ |y - boxCenter S j| + |x - y| := by
        calc |x - boxCenter S j| ≤ |x - y| + |y - boxCenter S j| := abs_sub_le _ _ _
          _ = _ := by ring
      have h4 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have h5 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ (1 / 2) ^ j)
      have h6 : (1 / 2 : ℝ) ^ j * |x - y| ≤ |x - y| := by
        have := abs_nonneg (x - y)
        nlinarith
      rw [Real.dist_eq]
      linarith
    have h2 : boxPiece S j y ≤ boxFn S y := Finset.le_sup' (fun j => boxPiece S j y) hj
    unfold boxFn at h2
    simp only [NNReal.coe_one, one_mul]
    linarith
  · exact boxBest_fst S x M
  · obtain ⟨l, hl, hb⟩ := boxBest_piece S x M
    have hval : (boxOracle S x).1 = boxFn S x := boxBest_fst S x M
    unfold boxOracle at hval ⊢
    rw [hb] at hval ⊢
    simp only at hval ⊢
    rw [← hval]
    have h1 := boxPiece_subgrad S l x y
    have h2 : boxPiece S l y ≤ boxFn S y :=
      Finset.le_sup' (fun j => boxPiece S j y) (Finset.mem_range.mpr (by omega))
    linarith

end Proof

end Lemmata.OracleComplexity
