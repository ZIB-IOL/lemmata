module

public import Lemmata.SpanningTreeMinSplit.Main

public section

namespace Lemmata.SpanningTreeMinSplit

/-- The factor index handles empty sizes without a truncated-arithmetic artifact. -/
theorem count_boundary :
    Fintype.card (Cert 0) = 0 ∧ Fintype.card (Cert 1) = 0 ∧
    Fintype.card (Cert 3) = 5 ∧ Fintype.card (Cert 4) = 14 := by
  exact ⟨card_cert 0, card_cert 1, card_cert 3, card_cert 4⟩

/-- The first promised graph size gives the five-factor full-matrix bound. -/
theorem rank_at_three : nonnegativeRank (fullSlack 3) ≤ 5 := by
  simpa using fullSlack_rank_bound 3 (by decide)

/-- A genuine negative entry cannot acquire a nonnegative factorization. -/
theorem negative_has_no_factorization (k : ℕ) :
    ¬ Nonempty (NonnegativeFactorization (fun (_ _ : Unit) => (-1 : ℝ)) k) := by
  rintro ⟨F⟩
  have h := F.nonneg () ()
  norm_num at h

/-- The rank definition assigns infinity, not a spurious zero, when no
nonnegative factorization exists. -/
theorem negative_rank_top :
    nonnegativeRank (fun (_ _ : Unit) => (-1 : ℝ)) = ⊤ := by
  unfold nonnegativeRank
  have h : {r : ℕ∞ | ∃ k : ℕ, r = k ∧
      Nonempty (NonnegativeFactorization (fun (_ _ : Unit) => (-1 : ℝ)) k)} = ∅ := by
    ext r
    simp [negative_has_no_factorization]
  rw [h, sInf_empty]

/-- The empty sum really is a zero-factor decomposition of a zero matrix. -/
theorem zero_rank_zero : nonnegativeRank (fun (_ _ : Unit) => (0 : ℝ)) = 0 := by
  let F : NonnegativeFactorization (fun (_ _ : Unit) => (0 : ℝ)) 0 := {
    left := fun l => Fin.elim0 l
    right := fun l => Fin.elim0 l
    left_nonneg := fun l => Fin.elim0 l
    right_nonneg := fun l => Fin.elim0 l
    reconstruct := by intro i j; simp }
  exact le_antisymm (by simpa using nonnegativeRank_le F) zero_le

end Lemmata.SpanningTreeMinSplit
