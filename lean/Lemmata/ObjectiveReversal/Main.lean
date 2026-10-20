module

public import Lemmata.ObjectiveReversal.Statement
public import Lemmata.NonnegativeRankReduction.Main
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Lemmata.ObjectiveReversal

open Lemmata.SpanningTreeMinSplit Lemmata.NonnegativeRankReduction

-- DOCS_BEGIN_MAIN
/-- An instance-independent completion transfers the maximum exactly to the
minimum of the reversed objective. -/
theorem optimum_transfer : OptimumTransfer := by
  intro I S T value cost baseline D i opt hupper hattain
  constructor
  · intro t
    have h := D.completion_dominates i t
    rw [D.objective_identity] at h
    have hu := hupper (D.complete t)
    linarith
  · obtain ⟨s, hs⟩ := hattain
    exact ⟨D.encode s, by rw [D.objective_identity, hs]⟩

/-- Exact relation between a maximization slack and a minimization
approximation slack. -/
theorem reversal_slack_identity (N C opt v α : ℝ) :
    C - v =
      (N - v - (N - opt) / α) +
        (C - opt - (1 - 1 / α) * (N - opt)) := by
  simp only [div_eq_mul_inv]
  ring

/-- At approximation factor `1 + 1/(4N)`, a source slack margin of `1/4`
pays for the entire approximation loss whenever the source optimum is
nonnegative. -/
theorem near_exact_offset_nonnegative (N C opt : ℝ)
    (hN : 0 < N) (hopt : 0 ≤ opt) (hmargin : 1 / 4 ≤ C - opt) :
    0 ≤ reversalOffset N C opt := by
  have h4 : 4 * N ≠ 0 := ne_of_gt (by linarith)
  have hd : 0 < 4 * N + 1 := by linarith
  have ha : 0 < 1 + 1 / (4 * N) :=
    add_pos_of_pos_of_nonneg zero_lt_one (le_of_lt (one_div_pos.mpr (by linarith)))
  have heq : 1 - 1 / (1 + 1 / (4 * N)) = 1 / (4 * N + 1) := by
    field_simp
    ring
  have hbound : (N - opt) / (4 * N + 1) ≤ (1 : ℝ) / 4 := by
    apply (div_le_iff₀ hd).2
    linarith
  unfold reversalOffset
  rw [heq]
  have heq' : 1 / (4 * N + 1) * (N - opt) = (N - opt) / (4 * N + 1) := by
    ring
  rw [heq']
  linarith

/-- The edge-cover approximation scale transfers any factorization to the
source with at most one additional rank-one term. The graph-specific
encoding and completion are supplied as an explicit `Reversal`. -/
theorem near_exact_factorization
    {I S T : Type*} {value : I → S → ℝ} {cost : I → T → ℝ}
    {C opt : I → ℝ} {N : ℝ} {k : ℕ}
    (D : Reversal value cost (fun _ => N))
    (hN : 0 < N) (hopt : ∀ i, 0 ≤ opt i)
    (hmargin : ∀ i, 1 / 4 ≤ C i - opt i)
    (F : NonnegativeFactorization
      (fun i t => cost i t - (N - opt i) / (1 + 1 / (4 * N))) k) :
    Nonempty (NonnegativeFactorization (fun i s => C i - value i s) (k + 1)) := by
  have G := factorRowOffset (factorPullback F id D.encode)
    (fun i => reversalOffset N (C i) (opt i))
    (fun i => near_exact_offset_nonnegative N (C i) (opt i) hN (hopt i) (hmargin i))
  have heq : (fun i s => C i - value i s) =
      (fun i s => cost i (D.encode s) - (N - opt i) / (1 + 1 / (4 * N)) +
        reversalOffset N (C i) (opt i)) := by
    funext i s
    rw [D.objective_identity]
    exact reversal_slack_identity N (C i) (opt i) (value i s) (1 + 1 / (4 * N))
  rw [heq]
  exact ⟨G⟩

/-- A source nonnegative-rank lower bound transfers at the near-exact
approximation scale, with an explicitly accounted-for extra factor. -/
theorem near_exact_rank_transfer
    {I S T : Type*} {value : I → S → ℝ} {cost : I → T → ℝ}
    {C opt : I → ℝ} {N : ℝ} {k L : ℕ}
    (D : Reversal value cost (fun _ => N))
    (hN : 0 < N) (hopt : ∀ i, 0 ≤ opt i)
    (hmargin : ∀ i, 1 / 4 ≤ C i - opt i)
    (source_lower_bound : (L : ℕ∞) ≤ nonnegativeRank (fun i s => C i - value i s))
    (F : NonnegativeFactorization
      (fun i t => cost i t - (N - opt i) / (1 + 1 / (4 * N))) k) :
    L ≤ k + 1 := by
  obtain ⟨G⟩ := near_exact_factorization D hN hopt hmargin F
  exact ENat.natCast_le_natCast.mp (source_lower_bound.trans (nonnegativeRank_le G))
-- DOCS_END_MAIN

end Lemmata.ObjectiveReversal
