module

public import Lemmata.SDPHardnessInP.Factorization

@[expose] public section

namespace Lemmata.SDPHardnessInP

open Lemmata.LPHardnessInP
open Lemmata.LPHardnessInP.Matching

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The concrete matching slack is a positive multiple of the shifted source. -/
theorem matchingSlack_eq (α : ℝ) (hα : 1 < α)
    (U : OddCut V) (M : PerfectMatching V) :
    matchingSlack α U M = penalty V α * (crossing U M - 1 / (2 * α)) := by
  have hα0 : α ≠ 0 := ne_of_gt (lt_trans zero_lt_one hα)
  rw [matchingSlack, matchingValue_eq, penalty_eq]
  field_simp
  ring

/-- Both shifts lie strictly inside the range of the external PSD theorem. -/
theorem shifts_in_range (α : ℝ) (hα : 1 < α) :
    (0 < 1 - 1 / (2 * α) ∧ 1 - 1 / (2 * α) < 1) ∧
    (0 < 1 - 1 / α ∧ 1 - 1 / α < 1) := by
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  have htwo : 1 < 2 * α := by linarith
  have h₁ : 0 < 1 / (2 * α) := by positivity
  have h₂ : 1 / (2 * α) < 1 := (div_lt_one (by positivity)).mpr htwo
  have h₃ : 0 < 1 / α := by positivity
  have h₄ : 1 / α < 1 := (div_lt_one hα0).mpr hα
  constructor <;> constructor <;> linarith

variable {K E : Type} [Fintype K] [AddCommGroup E] [Module ℝ E]

-- DOCS_BEGIN_MAIN
/-- An SDP certificate yields a PSD slack factorization with one scalar block. -/
theorem certified_slack_lower_bound {I J : Type} {value : I → J → ℝ}
    {bound : I → ℝ} {L : ℕ}
    (C : CertifiedSDP (E := E) value bound K)
    (source : PSDLowerBound (fun i j => value i j - bound i) L) :
    L ≤ Fintype.card K + 1 := by
  simpa using source (K ⊕ Unit) (certifiedSlackFactorization C)

/-- Shifted matching PSD hardness transfers to positive metric matching costs. -/
theorem matching_sdp_lower_bound [Nonempty V] (α : ℝ) (hα : 1 < α) {L : ℕ}
    (C : CertifiedSDP (E := E) (matchingValue (V := V) α)
      (fun _ => (halfOrder V + penalty V α) / α) K)
    (source : PSDLowerBound
      (fun U M => crossing (V := V) U M - 1 / (2 * α)) L) :
    L ≤ Fintype.card K + 1 := by
  have hp : 0 < penalty V α := by unfold penalty; positivity
  let F := (certifiedSlackFactorization C).scale (penalty V α)⁻¹ (by positivity)
  have h : (fun U M => (penalty V α)⁻¹ * matchingSlack α U M) =
      (fun U M => crossing (V := V) U M - 1 / (2 * α)) := by
    funext U M
    rw [matchingSlack_eq α hα, ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
  have F' : PSDFactorization
      (fun U M => crossing (V := V) U M - 1 / (2 * α)) (K ⊕ Unit) := h ▸ F
  simpa using source (K ⊕ Unit) F'

/-- Retaining the matching columns transfers the same bound to all V-joins. -/
theorem vjoin_sdp_lower_bound [Nonempty V] (α : ℝ) (hα : 1 < α) {L : ℕ}
    (C : CertifiedSDP (E := E) (Joins.joinValue (V := V) α)
      (fun _ => (halfOrder V + penalty V α) / α) K)
    (source : PSDLowerBound
      (fun U M => crossing (V := V) U M - 1 / (2 * α)) L) :
    L ≤ Fintype.card K + 1 :=
  matching_sdp_lower_bound α hα (C.pullback id Joins.ofMatching) source

omit [DecidableEq V] in
/-- Transposing the slack matrix transfers the bound to minimum odd cut. -/
theorem oddCut_sdp_lower_bound (α : ℝ) {L : ℕ}
    (C : CertifiedSDP (E := E) (oddCutValue (V := V)) (fun _ => 1 / α) K)
    (source : PSDLowerBound (fun U M => crossing (V := V) U M - 1 / α) L) :
    L ≤ Fintype.card K + 1 := by
  simpa using source (K ⊕ Unit) (certifiedSlackFactorization C).transpose
-- DOCS_END_MAIN

end Lemmata.SDPHardnessInP
