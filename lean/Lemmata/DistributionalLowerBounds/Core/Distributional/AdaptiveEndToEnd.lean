module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.YoungOld

@[expose] public section

/-!
# End-to-end adaptive transcript wrapper

A history node stores the conditional Ferrers posterior and exact water query.
A finite PMF over histories is the tower-of-expectations distribution.  The
local one-query theorem is averaged at each level and then telescoped.
-/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

/-- One conditional history at ambient dimension `d`. -/
inductive HistoryNode (d : ℕ) where
  | resolved
  | active (m : ℕ) (D : FerrersData m)
      (hm : 0 < m) (hmle : m ≤ d)
      (query : QueryRanks.WaterQuery D)

namespace HistoryNode

/-- Conditional expected deficit drop at one history. -/
noncomputable def localDrop {d : ℕ} : HistoryNode d → ℝ
  | resolved => 0
  | active _ D _ _ query =>
      uniformAverage (fun sigma =>
        (DownEdge.natDeficit D : ℝ) -
          DownEdge.internalOutdegree query.answer sigma)

/-- Every history obeys the ambient one-query bound. -/
theorem localDrop_le {d : ℕ} (node : HistoryNode d) :
    node.localDrop ≤ 8 * (d : ℝ) * Real.sqrt d := by
  cases node with
  | resolved => positivity
  | active m D hm hmle query =>
      have hlocal := oneQuery_expected_deficit_drop query hm
      have hmR : (0 : ℝ) ≤ m := by positivity
      have hdR : (0 : ℝ) ≤ d := by positivity
      have hmd : (m : ℝ) ≤ d := by exact_mod_cast hmle
      have hsqrt : Real.sqrt (m : ℝ) ≤ Real.sqrt d := Real.sqrt_le_sqrt hmd
      have hprod : (m : ℝ) * Real.sqrt m ≤ (d : ℝ) * Real.sqrt d := by
        exact mul_le_mul hmd hsqrt (Real.sqrt_nonneg _) hdR
      calc
        (uniformAverage fun sigma =>
          (DownEdge.natDeficit D : ℝ) -
            DownEdge.internalOutdegree query.answer sigma) ≤
            8 * (m : ℝ) * Real.sqrt m := hlocal
        _ = 8 * ((m : ℝ) * Real.sqrt m) := by ring
        _ ≤ 8 * ((d : ℝ) * Real.sqrt d) :=
          mul_le_mul_of_nonneg_left hprod (show (0 : ℝ) ≤ 8 by norm_num)
        _ = 8 * (d : ℝ) * Real.sqrt d := by ring

end HistoryNode

/-- One level of the adaptive transcript tree. -/
structure TranscriptLevel (d : ℕ) where
  History : Type*
  fintypeHistory : Fintype History
  historyLaw : FinitePMF History
  node : History → HistoryNode d

attribute [instance] TranscriptLevel.fintypeHistory

namespace TranscriptLevel

/-- Mean deficit decrease at this level. -/
noncomputable def meanDrop {d : ℕ} (L : TranscriptLevel d) : ℝ :=
  L.historyLaw.expect (fun h => (L.node h).localDrop)

/-- Tower averaging preserves the ambient one-query bound. -/
theorem meanDrop_le {d : ℕ} (L : TranscriptLevel d) :
    L.meanDrop ≤ 8 * (d : ℝ) * Real.sqrt d := by
  unfold meanDrop
  rw [← L.historyLaw.expect_const (8 * (d : ℝ) * Real.sqrt d)]
  exact L.historyLaw.expect_mono (fun h => (L.node h).localDrop_le)

end TranscriptLevel

/-- A depth-`T` adaptive exact-LMO transcript process.  `step_eq` is the finite
law of total expectation: the change in global mean deficit equals the PMF
average of conditional history drops. -/
structure AdaptiveTranscriptProcess (d T : ℕ) where
  level : Fin T → TranscriptLevel d
  meanDeficit : ℕ → ℝ
  step_eq : ∀ t : Fin T,
    meanDeficit t.val - meanDeficit (t.val + 1) = (level t).meanDrop

namespace AdaptiveTranscriptProcess

/-- Every adaptive process inherits a global per-step deficit bound. -/
theorem meanDeficit_step_le {d T : ℕ} (M : AdaptiveTranscriptProcess d T) :
    ∀ t < T, M.meanDeficit t - M.meanDeficit (t + 1) ≤
      8 * (d : ℝ) * Real.sqrt d := by
  intro t ht
  let ft : Fin T := ⟨t, ht⟩
  rw [M.step_eq ft]
  exact (M.level ft).meanDrop_le

/-- End-to-end telescoping for an adaptive transcript tree. -/
theorem meanDeficit_telescope {d T : ℕ} (M : AdaptiveTranscriptProcess d T) :
    M.meanDeficit 0 - (T : ℝ) * (8 * (d : ℝ) * Real.sqrt d) ≤
      M.meanDeficit T :=
  expected_deficit_telescope M.meanDeficit T M.meanDeficit_step_le

end AdaptiveTranscriptProcess

/-- Paper-facing end-to-end theorem at the chosen dimension.  All local
posterior/query work is discharged through the transcript levels; no one-query
or variance hypothesis remains. -/
theorem adaptive_distributional_lower_bound
    {Omega : Type*} [Fintype Omega]
    (P : FinitePMF Omega) (Delta loss : Omega → ℝ)
    (T : ℕ) (M : AdaptiveTranscriptProcess (proofDimension T) T)
    {rho : ℝ}
    (hrhoIoo : rho ∈ Set.Ioo (0 : ℝ) 1)
    (hrhoEq :
      rhoLHS (hardWeight (proofDimension T))
          (hardTopWeight (proofDimension T)) rho =
        hardC (proofDimension T) ^ 2)
    (hzero : M.meanDeficit 0 = initialDeficit (proofDimension T))
    (hfinal : M.meanDeficit T = P.expect Delta)
    (hloss : ∀ omega,
      rho ^ 2 * hardC (proofDimension T) ^ 2 * Delta omega ^ 2 /
          (48 * (proofDimension T : ℝ) ^ 2) ≤ loss omega) :
    hardC (proofDimension T) ^ 2 /
        (768 * (proofDimension T : ℝ) ^ 2) ≤ P.expect loss := by
  have hdimSqrt : Real.sqrt (proofDimension T : ℝ) =
      64 * (T + 1 : ℝ) := by
    have hnonneg : (0 : ℝ) ≤ 64 * (T + 1 : ℝ) := by
      have hT : (0 : ℝ) ≤ T := by exact_mod_cast Nat.zero_le T
      nlinarith
    rw [proofDimension_cast, Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]
  have hstep : ∀ t < T,
      M.meanDeficit t - M.meanDeficit (t + 1) ≤
        8 * (proofDimension T : ℝ) * (64 * (T + 1 : ℝ)) := by
    intro t ht
    simpa [hdimSqrt] using M.meanDeficit_step_le t ht
  exact concrete_distributional_lower_bound_from_steps P Delta loss
    M.meanDeficit T hrhoIoo hrhoEq hzero hstep hfinal hloss

end Lemmata.DistributionalLowerBounds.Core.Distributional
