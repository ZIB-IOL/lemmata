module

public import Lemmata.OracleComplexity.BoxBound

@[expose] public section

/-!
# Locality of the one-dimensional oracle

Every piece is affine on each side of `x` near `x`, with its left and right slopes, and the pieces
that do not attain the maximum stay below it nearby. So the hard function is affine on each side of
`x` near `x`, with the left and right derivatives `boxLeft` and `boxRight` as slopes. Functions that
agree near `x` therefore have the same one-sided derivatives at `x`, and the oracle, which answers
the value and one of them, is local.
-/

namespace Lemmata.OracleComplexity

variable {M : ℕ}

theorem piece_right_affine (S : Fin M → Bool) (j : ℕ) (x : ℝ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : x < boxCenter S j → t ≤ boxCenter S j - x) :
    boxPiece S j (x + t) = boxPiece S j x + t * pieceRight S j x := by
  unfold boxPiece pieceRight
  split_ifs with h
  · have h1 := ht h
    rw [abs_of_nonpos (by linarith), abs_of_neg (by linarith)]
    ring
  · push Not at h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    ring

theorem piece_left_affine (S : Fin M → Bool) (j : ℕ) (x : ℝ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : boxCenter S j < x → t ≤ x - boxCenter S j) :
    boxPiece S j (x - t) = boxPiece S j x - t * pieceLeft S j x := by
  unfold boxPiece pieceLeft
  split_ifs with h
  · have h1 := ht h
    rw [abs_of_nonneg (by linarith), abs_of_pos (by linarith)]
    ring
  · push Not at h
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    ring

theorem abs_pieceRight_le (S : Fin M → Bool) (j : ℕ) (x : ℝ) : |pieceRight S j x| ≤ 1 := by
  unfold pieceRight
  have h1 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : (0 : ℝ) ≤ (1 / 2) ^ j := by positivity
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

theorem abs_pieceLeft_le (S : Fin M → Bool) (j : ℕ) (x : ℝ) : |pieceLeft S j x| ≤ 1 := by
  unfold pieceLeft
  have h1 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : (0 : ℝ) ≤ (1 / 2) ^ j := by positivity
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

open Classical in
/-- The hard function is affine to the right of `x` near `x`, with slope `boxRight`. -/
theorem box_right_affine (S : Fin M → Bool) (x : ℝ) : ∃ δ > 0, ∀ t, 0 < t → t ≤ δ →
    boxFn S (x + t) = boxFn S x + t * boxRight S x := by
  set ρ : ℕ → ℝ := fun j => min (if x < boxCenter S j then boxCenter S j - x else 1)
    (if boxPiece S j x = boxFn S x then 1 else (boxFn S x - boxPiece S j x) / 2) with hρ
  have hρpos : ∀ j ≤ M, 0 < ρ j := by
    intro j hj
    simp only [hρ]
    apply lt_min
    · split_ifs with h <;> linarith
    · split_ifs with h
      · norm_num
      · have := lt_of_le_of_ne (piece_le_fn S hj x) h
        linarith
  obtain ⟨j₀, hj₀, hδeq⟩ := Finset.exists_mem_eq_inf' Finset.nonempty_range_add_one ρ
  refine ⟨(Finset.range (M + 1)).inf' Finset.nonempty_range_add_one ρ,
    by rw [hδeq]; exact hρpos j₀ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj₀)), ?_⟩
  intro t ht0 htδ
  have hρle : ∀ j ≤ M, t ≤ ρ j := fun j hj =>
    htδ.trans (Finset.inf'_le ρ (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))
  have haff : ∀ j ≤ M, boxPiece S j (x + t) = boxPiece S j x + t * pieceRight S j x := by
    intro j hj
    refine piece_right_affine S j x ht0.le (fun h => ?_)
    have := (hρle j hj).trans (min_le_left _ _)
    rwa [ite_eq_left h] at this
  obtain ⟨jR, hjR, hactR, hR⟩ := (boxRight_spec S x).1
  have hRge : -1 ≤ boxRight S x := by rw [hR]; exact neg_one_le_pieceRight S jR x
  apply le_antisymm
  · apply Finset.sup'_le
    intro j hj
    have hjM := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    show boxPiece S j (x + t) ≤ _
    rw [haff j hjM]
    by_cases hact : boxPiece S j x = boxFn S x
    · have := (boxRight_spec S x).2 j hjM hact
      rw [hact]
      nlinarith
    · have hgap : t ≤ (boxFn S x - boxPiece S j x) / 2 := by
        have := (hρle j hjM).trans (min_le_right _ _)
        rwa [ite_eq_right hact] at this
      have hsl := (abs_le.mp (abs_pieceRight_le S j x)).2
      nlinarith
  · calc boxFn S x + t * boxRight S x = boxPiece S jR (x + t) := by
          rw [haff jR hjR, hactR, hR]
      _ ≤ boxFn S (x + t) := piece_le_fn S hjR _

open Classical in
/-- The hard function is affine to the left of `x` near `x`, with slope `boxLeft`. -/
theorem box_left_affine (S : Fin M → Bool) (x : ℝ) : ∃ δ > 0, ∀ t, 0 < t → t ≤ δ →
    boxFn S (x - t) = boxFn S x - t * boxLeft S x := by
  set ρ : ℕ → ℝ := fun j => min (if boxCenter S j < x then x - boxCenter S j else 1)
    (if boxPiece S j x = boxFn S x then 1 else (boxFn S x - boxPiece S j x) / 2) with hρ
  have hρpos : ∀ j ≤ M, 0 < ρ j := by
    intro j hj
    simp only [hρ]
    apply lt_min
    · split_ifs with h <;> linarith
    · split_ifs with h
      · norm_num
      · have := lt_of_le_of_ne (piece_le_fn S hj x) h
        linarith
  obtain ⟨j₀, hj₀, hδeq⟩ := Finset.exists_mem_eq_inf' Finset.nonempty_range_add_one ρ
  refine ⟨(Finset.range (M + 1)).inf' Finset.nonempty_range_add_one ρ,
    by rw [hδeq]; exact hρpos j₀ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj₀)), ?_⟩
  intro t ht0 htδ
  have hρle : ∀ j ≤ M, t ≤ ρ j := fun j hj =>
    htδ.trans (Finset.inf'_le ρ (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))
  have haff : ∀ j ≤ M, boxPiece S j (x - t) = boxPiece S j x - t * pieceLeft S j x := by
    intro j hj
    refine piece_left_affine S j x ht0.le (fun h => ?_)
    have := (hρle j hj).trans (min_le_left _ _)
    rwa [ite_eq_left h] at this
  obtain ⟨jL, hjL, hactL, hL⟩ := (boxLeft_spec S x).1
  have hLle : boxLeft S x ≤ 1 := by rw [hL]; exact pieceLeft_le_one S jL x
  apply le_antisymm
  · apply Finset.sup'_le
    intro j hj
    have hjM := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    show boxPiece S j (x - t) ≤ _
    rw [haff j hjM]
    by_cases hact : boxPiece S j x = boxFn S x
    · have := (boxLeft_spec S x).2 j hjM hact
      rw [hact]
      nlinarith
    · have hgap : t ≤ (boxFn S x - boxPiece S j x) / 2 := by
        have := (hρle j hjM).trans (min_le_right _ _)
        rwa [ite_eq_right hact] at this
      have hsl := (abs_le.mp (abs_pieceLeft_le S j x)).1
      nlinarith
  · calc boxFn S x - t * boxLeft S x = boxPiece S jL (x - t) := by
          rw [haff jL hjL, hactL, hL]
      _ ≤ boxFn S (x - t) := piece_le_fn S hjL _

/-- Functions that agree near `x` have the same value and one-sided derivatives at `x`. -/
theorem box_local_data {S S' : Fin M → Bool} {x : ℝ}
    (h : ∀ᶠ y in nhds x, boxFn S y = boxFn S' y) :
    boxFn S x = boxFn S' x ∧ boxRight S x = boxRight S' x ∧ boxLeft S x = boxLeft S' x := by
  obtain ⟨ε, hε, hU⟩ := Metric.eventually_nhds_iff.mp h
  obtain ⟨δ₁, hδ₁, h1⟩ := box_right_affine S x
  obtain ⟨δ₂, hδ₂, h2⟩ := box_right_affine S' x
  obtain ⟨δ₃, hδ₃, h3⟩ := box_left_affine S x
  obtain ⟨δ₄, hδ₄, h4⟩ := box_left_affine S' x
  set t := min (min δ₁ δ₂) (min (min δ₃ δ₄) (ε / 2)) with htdef
  have ht : 0 < t := by
    simp only [htdef]
    exact lt_min (lt_min hδ₁ hδ₂) (lt_min (lt_min hδ₃ hδ₄) (by linarith))
  have htε : t < ε := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)
  have hx : boxFn S x = boxFn S' x := hU (by simpa using hε)
  have hxp : boxFn S (x + t) = boxFn S' (x + t) := hU (by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos ht]; exact htε)
  have hxm : boxFn S (x - t) = boxFn S' (x - t) := hU (by
    rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos ht]; exact htε)
  have t1 : t ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have t2 : t ≤ δ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have t3 : t ≤ δ₃ := ((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_left _ _)
  have t4 : t ≤ δ₄ := ((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_right _ _)
  rw [h1 t ht t1, h2 t ht t2, hx] at hxp
  rw [h3 t ht t3, h4 t ht t4, hx] at hxm
  refine ⟨hx, ?_, ?_⟩
  · exact mul_left_cancel₀ ht.ne' (by linarith)
  · exact mul_left_cancel₀ ht.ne' (by linarith)

namespace Proof

theorem box_local : BoxLocal := by
  intro M S S' x h
  obtain ⟨hx, hR, hL⟩ := box_local_data h
  show boxOracle S x = boxOracle S' x
  unfold boxOracle
  rw [hx, hR, hL]

end Proof

end Lemmata.OracleComplexity
