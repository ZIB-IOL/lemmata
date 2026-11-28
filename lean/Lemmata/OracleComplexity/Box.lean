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

/-- The distance of centers at depths `i ≤ i + d ≤ M`. -/
theorem boxCenter_diff (S : Fin M → Bool) (i : ℕ) : ∀ d, i + d ≤ M →
    |boxCenter S (i + d) - boxCenter S i| ≤ ((1 / 4) ^ i - (1 / 4) ^ (i + d)) / 3 := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have h1 := ih (by omega)
    have h2 := boxCenter_step S (j := i + d) (by omega)
    calc |boxCenter S (i + (d + 1)) - boxCenter S i|
        ≤ |boxCenter S (i + d + 1) - boxCenter S (i + d)| + |boxCenter S (i + d) - boxCenter S i| :=
          abs_sub_le _ _ _
      _ ≤ (1 / 4) ^ (i + d + 1) + ((1 / 4) ^ i - (1 / 4) ^ (i + d)) / 3 := by rw [h2]; linarith
      _ = ((1 / 4) ^ i - (1 / 4) ^ (i + (d + 1))) / 3 := by
          rw [show i + (d + 1) = i + d + 1 by ring, pow_succ]; ring

/-- Strictly outside the interval of depth `j`, the piece of depth `j + 1` lies strictly below. -/
theorem piece_step_strict (S : Fin M → Bool) {j : ℕ} (hj : j < M) {x : ℝ}
    (hx : (1 / 4) ^ j < |x - boxCenter S j|) : boxPiece S (j + 1) x < boxPiece S j x := by
  have hd := boxCenter_step S hj
  have htri : |x - boxCenter S (j + 1)| ≤ |x - boxCenter S j| + (1 / 4) ^ (j + 1) := by
    calc |x - boxCenter S (j + 1)| ≤ |x - boxCenter S j| + |boxCenter S j - boxCenter S (j + 1)| :=
          abs_sub_le _ _ _
      _ = |x - boxCenter S j| + (1 / 4) ^ (j + 1) := by
          rw [abs_sub_comm (boxCenter S j) (boxCenter S (j + 1)), hd]
  have e1 : (1 / 8 : ℝ) ^ j = (1 / 2) ^ j * (1 / 4) ^ j := by rw [← mul_pow]; norm_num
  have e2 : (1 / 2 : ℝ) ^ (j + 1) = (1 / 2) ^ j / 2 := by rw [pow_succ]; ring
  have e3 : (1 / 8 : ℝ) ^ (j + 1) = (1 / 8) ^ j / 8 := by rw [pow_succ]; ring
  have e4 : (1 / 4 : ℝ) ^ (j + 1) = (1 / 4) ^ j / 4 := by rw [pow_succ]; ring
  rw [e4] at htri
  unfold boxPiece
  rw [boxLevel_succ, e2, e3, e1]
  have ha : (0 : ℝ) < (1 / 2) ^ j / 2 := by positivity
  have k1 := mul_le_mul_of_nonneg_left htri ha.le
  have k2 := mul_lt_mul_of_pos_left hx ha
  nlinarith

theorem boxPiece_congr {S S' : Fin M → Bool} {j : ℕ}
    (h : ∀ i : Fin M, (i : ℕ) < j → S i = S' i) (x : ℝ) :
    boxPiece S j x = boxPiece S' j x ∧ pieceLeft S j x = pieceLeft S' j x ∧
      pieceRight S j x = pieceRight S' j x := by
  unfold boxPiece pieceLeft pieceRight
  rw [boxCenter_congr h]
  exact ⟨rfl, rfl, rfl⟩

theorem piece_le_fn (S : Fin M → Bool) {j : ℕ} (hj : j ≤ M) (y : ℝ) :
    boxPiece S j y ≤ boxFn S y :=
  Finset.le_sup' (fun j => boxPiece S j y) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

theorem exists_active (S : Fin M → Bool) (x : ℝ) :
    ∃ j ≤ M, boxPiece S j x = boxFn S x := by
  obtain ⟨j, hj, h⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
    (fun j => boxPiece S j x)
  exact ⟨j, Nat.lt_succ_iff.mp (Finset.mem_range.mp hj), h.symm⟩

theorem pieceLeft_le_one (S : Fin M → Bool) (j : ℕ) (x : ℝ) : pieceLeft S j x ≤ 1 := by
  unfold pieceLeft
  have h1 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : (0 : ℝ) ≤ (1 / 2) ^ j := by positivity
  split_ifs <;> linarith

theorem neg_one_le_pieceRight (S : Fin M → Bool) (j : ℕ) (x : ℝ) : -1 ≤ pieceRight S j x := by
  unfold pieceRight
  have h1 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : (0 : ℝ) ≤ (1 / 2) ^ j := by positivity
  split_ifs <;> linarith

theorem pieceLeft_le_pieceRight (S : Fin M → Bool) (j : ℕ) (x : ℝ) :
    pieceLeft S j x ≤ pieceRight S j x := by
  unfold pieceLeft pieceRight
  have h2 : (0 : ℝ) ≤ (1 / 2) ^ j := by positivity
  split_ifs with h1 h3 <;> linarith

theorem pieceLeft_ne_zero (S : Fin M → Bool) (j : ℕ) (x : ℝ) : pieceLeft S j x ≠ 0 := by
  unfold pieceLeft
  have h2 : (0 : ℝ) < (1 / 2) ^ j := by positivity
  split_ifs <;> [exact h2.ne'; exact neg_ne_zero.mpr h2.ne']

/-- The left slope of a piece is a subgradient of the piece. -/
theorem pieceLeft_subgrad (S : Fin M → Bool) (j : ℕ) (x y : ℝ) :
    boxPiece S j x + pieceLeft S j x * (y - x) ≤ boxPiece S j y := by
  unfold boxPiece pieceLeft
  have ha : (0 : ℝ) ≤ (1 / 2) ^ j := by positivity
  split_ifs with h
  · have h1 : |x - boxCenter S j| = x - boxCenter S j := abs_of_pos (by linarith)
    have h2 := le_abs_self (y - boxCenter S j)
    rw [h1]
    nlinarith
  · have h1 : |x - boxCenter S j| = boxCenter S j - x := by
      rw [abs_of_nonpos (by linarith)]; ring
    have h2 := neg_abs_le (y - boxCenter S j)
    rw [h1]
    nlinarith

/-- The right slope of a piece is a subgradient of the piece. -/
theorem pieceRight_subgrad (S : Fin M → Bool) (j : ℕ) (x y : ℝ) :
    boxPiece S j x + pieceRight S j x * (y - x) ≤ boxPiece S j y := by
  unfold boxPiece pieceRight
  have ha : (0 : ℝ) ≤ (1 / 2) ^ j := by positivity
  split_ifs with h
  · have h1 : |x - boxCenter S j| = boxCenter S j - x := by
      rw [abs_of_neg (by linarith)]; ring
    have h2 := neg_abs_le (y - boxCenter S j)
    rw [h1]
    nlinarith
  · have h1 : |x - boxCenter S j| = x - boxCenter S j := abs_of_nonneg (by linarith)
    have h2 := le_abs_self (y - boxCenter S j)
    rw [h1]
    nlinarith

open Classical in
/-- The left derivative is the left slope of an active piece and at most the left slope of every
active piece. -/
theorem boxLeft_spec (S : Fin M → Bool) (x : ℝ) :
    (∃ j ≤ M, boxPiece S j x = boxFn S x ∧ boxLeft S x = pieceLeft S j x) ∧
      ∀ j ≤ M, boxPiece S j x = boxFn S x → boxLeft S x ≤ pieceLeft S j x := by
  refine ⟨?_, fun j hj hact => ?_⟩
  · obtain ⟨j, hj, h⟩ := Finset.exists_mem_eq_inf' Finset.nonempty_range_add_one
      (fun j => if boxPiece S j x = boxFn S x then pieceLeft S j x else 1)
    have hjM := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    by_cases hact : boxPiece S j x = boxFn S x
    · refine ⟨j, hjM, hact, ?_⟩
      unfold boxLeft
      rw [h, ite_eq_left hact]
    · -- the minimum is the penalty `1`, so every active piece has left slope `1`
      obtain ⟨l, hl, hlact⟩ := exists_active S x
      have hle : boxLeft S x ≤ pieceLeft S l x := by
        have := Finset.inf'_le (fun j => if boxPiece S j x = boxFn S x then pieceLeft S j x else 1)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))
        exact this.trans_eq (ite_eq_left hlact)
      have heq : boxLeft S x = 1 := by
        unfold boxLeft
        rw [h, ite_eq_right hact]
      refine ⟨l, hl, hlact, le_antisymm hle ?_⟩
      rw [heq]
      exact pieceLeft_le_one S l x
  · have := Finset.inf'_le (fun j => if boxPiece S j x = boxFn S x then pieceLeft S j x else 1)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    exact this.trans_eq (ite_eq_left hact)

open Classical in
/-- The right derivative is the right slope of an active piece and at least the right slope of
every active piece. -/
theorem boxRight_spec (S : Fin M → Bool) (x : ℝ) :
    (∃ j ≤ M, boxPiece S j x = boxFn S x ∧ boxRight S x = pieceRight S j x) ∧
      ∀ j ≤ M, boxPiece S j x = boxFn S x → pieceRight S j x ≤ boxRight S x := by
  refine ⟨?_, fun j hj hact => ?_⟩
  · obtain ⟨j, hj, h⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
      (fun j => if boxPiece S j x = boxFn S x then pieceRight S j x else -1)
    have hjM := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    by_cases hact : boxPiece S j x = boxFn S x
    · refine ⟨j, hjM, hact, ?_⟩
      unfold boxRight
      rw [h, ite_eq_left hact]
    · obtain ⟨l, hl, hlact⟩ := exists_active S x
      have hle : pieceRight S l x ≤ boxRight S x := by
        have := Finset.le_sup'
          (fun j => if boxPiece S j x = boxFn S x then pieceRight S j x else -1)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))
        exact (ite_eq_left hlact).symm.trans_le this
      have heq : boxRight S x = -1 := by
        unfold boxRight
        rw [h, ite_eq_right hact]
      refine ⟨l, hl, hlact, le_antisymm ?_ hle⟩
      rw [heq]
      exact neg_one_le_pieceRight S l x
  · have := Finset.le_sup' (fun j => if boxPiece S j x = boxFn S x then pieceRight S j x else -1)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    exact (ite_eq_left hact).symm.trans_le this

theorem boxLeft_le_boxRight (S : Fin M → Bool) (x : ℝ) : boxLeft S x ≤ boxRight S x := by
  obtain ⟨j, hj, hact, -⟩ := (boxLeft_spec S x).1
  exact ((boxLeft_spec S x).2 j hj hact).trans
    ((pieceLeft_le_pieceRight S j x).trans ((boxRight_spec S x).2 j hj hact))

theorem boxLeft_ne_zero (S : Fin M → Bool) (x : ℝ) : boxLeft S x ≠ 0 := by
  obtain ⟨j, -, -, h⟩ := (boxLeft_spec S x).1
  rw [h]
  exact pieceLeft_ne_zero S j x

/-- The slope of the oracle is a subgradient. -/
theorem boxOracle_subgrad (S : Fin M → Bool) (x y : ℝ) :
    boxFn S x + (boxOracle S x).2 * (y - x) ≤ boxFn S y := by
  unfold boxOracle
  simp only
  split_ifs
  · obtain ⟨j, hj, hact, h⟩ := (boxRight_spec S x).1
    rw [h, ← hact]
    exact (pieceRight_subgrad S j x y).trans (piece_le_fn S hj y)
  · obtain ⟨j, hj, hact, h⟩ := (boxLeft_spec S x).1
    rw [h, ← hact]
    exact (pieceLeft_subgrad S j x y).trans (piece_le_fn S hj y)

namespace Proof

theorem box_oracle_valid : BoxOracleValid := by
  intro M S
  refine ⟨?_, ?_, fun x => ⟨rfl, fun y => boxOracle_subgrad S x y⟩⟩
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
      have h5 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ (1 / 2) ^ j)
      have h6 : (1 / 2 : ℝ) ^ j * |x - y| ≤ |x - y| := by
        have := abs_nonneg (x - y)
        have h4 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        nlinarith
      rw [Real.dist_eq]
      linarith
    have h2 : boxPiece S j y ≤ boxFn S y := Finset.le_sup' (fun j => boxPiece S j y) hj
    unfold boxFn at h2
    simp only [NNReal.coe_one, one_mul]
    linarith

end Proof

end Lemmata.OracleComplexity
