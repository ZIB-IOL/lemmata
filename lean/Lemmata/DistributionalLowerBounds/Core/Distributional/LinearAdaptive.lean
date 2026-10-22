module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.LinearDrift
public import Lemmata.DistributionalLowerBounds.Core.Distributional.FiniteStrategy

@[expose] public section

/-!
# Sharp-rate composition for finite certified adaptive strategies

The new linear local drift is propagated through the existing history/strategy
interfaces without changing them. The dimension is `64 * (T+1)`. As before,
`CertifiedStrategy` supplies per-history nodes and a mass-weighted drop identity;
constructing that certificate from raw exact-LMO transcripts is out of scope.
The finite seed and instance PMFs, their independence, and all loss/optimizer
hypotheses are explicit. No project-local axioms or proof placeholders are used.
-/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

/-- Linear rather than quadratic dimension for the sharp distributional rate. -/
def linearProofDimension (T : ℕ) : ℕ := 64 * (T + 1)

lemma linearProofDimension_cast (T : ℕ) :
    (linearProofDimension T : ℝ) = 64 * ((T : ℝ) + 1) := by
  simp [linearProofDimension]

lemma linearProofDimension_ge_three (T : ℕ) : 3 ≤ linearProofDimension T := by
  unfold linearProofDimension
  omega

namespace HistoryNode

theorem localDrop_le_linear {d : ℕ} (node : HistoryNode d) :
    node.localDrop ≤ 6 * (d : ℝ) := by
  cases node with
  | resolved => simp [localDrop]
  | active m D hm hmle query =>
      have hlocal := oneQuery_expected_deficit_drop_linear query
      have hmd : (m : ℝ) ≤ d := by exact_mod_cast hmle
      change (uniformAverage fun sigma =>
        (DownEdge.natDeficit D : ℝ) -
          DownEdge.internalOutdegree query.answer sigma) ≤ 6 * (d : ℝ)
      linarith

end HistoryNode

namespace TranscriptLevel

theorem meanDrop_le_linear {d : ℕ} (L : TranscriptLevel d) :
    L.meanDrop ≤ 6 * (d : ℝ) := by
  unfold meanDrop
  rw [← L.historyLaw.expect_const (6 * (d : ℝ))]
  exact L.historyLaw.expect_mono (fun h => (L.node h).localDrop_le_linear)

end TranscriptLevel

namespace AdaptiveTranscriptProcess

theorem meanDeficit_step_le_linear {d T : ℕ} (M : AdaptiveTranscriptProcess d T) :
    ∀ t < T, M.meanDeficit t - M.meanDeficit (t + 1) ≤ 6 * (d : ℝ) := by
  intro t ht
  let ft : Fin T := ⟨t, ht⟩
  rw [M.step_eq ft]
  exact (M.level ft).meanDrop_le_linear

theorem meanDeficit_telescope_linear {d T : ℕ} (M : AdaptiveTranscriptProcess d T) :
    M.meanDeficit 0 - (T : ℝ) * (6 * (d : ℝ)) ≤ M.meanDeficit T :=
  expected_deficit_telescope M.meanDeficit T M.meanDeficit_step_le_linear

end AdaptiveTranscriptProcess

/-- Constant-sensitive loss bound for a large remaining mean deficit. -/
theorem loss_from_large_mean_deficit
    {Omega : Type*} [Fintype Omega]
    (P : FinitePMF Omega) (Delta loss : Omega → ℝ)
    {d rho C : ℝ} (hd : 0 < d)
    (hrho : 2 / d ^ 2 ≤ rho)
    (hmean : d ^ 2 / 8 ≤ P.expect Delta)
    (hloss : ∀ omega,
      rho ^ 2 * C ^ 2 * Delta omega ^ 2 / (48 * d ^ 2) ≤ loss omega) :
    C ^ 2 / (768 * d ^ 2) ≤ P.expect loss := by
  have hbase := P.expected_loss_from_pointwise_deficit Delta loss hd hmean hloss
  have hsmall0 : 0 ≤ 2 / d ^ 2 := by positivity
  have hrho0 : 0 ≤ rho := le_trans hsmall0 hrho
  have hrhoSq : (2 / d ^ 2) ^ 2 ≤ rho ^ 2 := by nlinarith
  have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
  have hraw : 4 * C ^ 2 ≤ rho ^ 2 * C ^ 2 * d ^ 4 := by
    have h := mul_le_mul_of_nonneg_right hrhoSq hC2
    field_simp [hd.ne'] at h
    nlinarith
  have hscale : C ^ 2 / (768 * d ^ 2) ≤ rho ^ 2 * C ^ 2 * d ^ 2 / 3072 := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 768 * d ^ 2)
      (by norm_num : (0 : ℝ) < 3072)).2
    nlinarith
  exact hscale.trans hbase

/-- Sharp-rate expectation endpoint for a certified adaptive process. -/
theorem adaptive_distributional_lower_bound_linear
    {Omega : Type*} [Fintype Omega]
    (P : FinitePMF Omega) (Delta loss : Omega → ℝ)
    (T : ℕ) (M : AdaptiveTranscriptProcess (linearProofDimension T) T)
    {rho : ℝ}
    (hrhoIoo : rho ∈ Set.Ioo (0 : ℝ) 1)
    (hrhoEq :
      rhoLHS (hardWeight (linearProofDimension T))
          (hardTopWeight (linearProofDimension T)) rho =
        hardC (linearProofDimension T) ^ 2)
    (hzero : M.meanDeficit 0 = initialDeficit (linearProofDimension T))
    (hfinal : M.meanDeficit T = P.expect Delta)
    (hloss : ∀ omega,
      rho ^ 2 * hardC (linearProofDimension T) ^ 2 * Delta omega ^ 2 /
          (48 * (linearProofDimension T : ℝ) ^ 2) ≤ loss omega) :
    hardC (linearProofDimension T) ^ 2 /
        (768 * (linearProofDimension T : ℝ) ^ 2) ≤ P.expect loss := by
  have hT : (0 : ℝ) ≤ T := by positivity
  have hd3 : 3 ≤ linearProofDimension T := linearProofDimension_ge_three T
  have hd : (0 : ℝ) < linearProofDimension T := by exact_mod_cast (by omega : 0 < linearProofDimension T)
  have ht := M.meanDeficit_telescope_linear
  rw [hzero, hfinal] at ht
  have hmean : (linearProofDimension T : ℝ) ^ 2 / 8 ≤ P.expect Delta := by
    dsimp [initialDeficit] at ht
    rw [linearProofDimension_cast] at ht ⊢
    nlinarith [sq_nonneg (T : ℝ)]
  exact loss_from_large_mean_deficit P Delta loss hd
    (concrete_rho_lower_bound hd3 hrhoIoo hrhoEq) hmean hloss

/-- Sharp-rate result stated for explicit finite-seed transcript strategies.
The hard-family per-history certificate and deficit-to-loss hypotheses remain
explicit, exactly as in the earlier finite-strategy endpoint. -/
theorem finiteSeed_strategy_distributional_lower_bound_linear
    {Seed Omega Query Answer Output : Type}
    [Fintype Seed] [Fintype Omega]
    (seedLaw : FinitePMF Seed) (instanceLaw : FinitePMF Omega)
    (strategy : Seed → DeterministicAdaptiveStrategy Query Answer Output)
    (oracle : Omega → Query → Answer)
    (loss : Omega → Output → ℝ)
    (deficit : Seed → ℕ → Omega → ℝ)
    (T : ℕ)
    (certificate : ∀ seed,
      CertifiedStrategy (linearProofDimension T) T instanceLaw
        (strategy seed) oracle (deficit seed))
    {rho : ℝ}
    (hrhoIoo : rho ∈ Set.Ioo (0 : ℝ) 1)
    (hrhoEq :
      rhoLHS (hardWeight (linearProofDimension T))
          (hardTopWeight (linearProofDimension T)) rho =
        hardC (linearProofDimension T) ^ 2)
    (hzero : ∀ seed,
      instanceLaw.expect (deficit seed 0) = initialDeficit (linearProofDimension T))
    (hloss : ∀ seed omega,
      rho ^ 2 * hardC (linearProofDimension T) ^ 2 * deficit seed T omega ^ 2 /
          (48 * (linearProofDimension T : ℝ) ^ 2) ≤
        loss omega ((strategy seed).run oracle omega T)) :
    hardC (linearProofDimension T) ^ 2 /
        (768 * (linearProofDimension T : ℝ) ^ 2) ≤
      (seedLaw.product instanceLaw).expect
        (fun pair => loss pair.2 ((strategy pair.1).run oracle pair.2 T)) := by
  rw [seedLaw.product_expect instanceLaw]
  apply seedLaw.expect_seedwise_ge
  intro seed
  exact adaptive_distributional_lower_bound_linear instanceLaw
    (deficit seed T) (fun omega => loss omega ((strategy seed).run oracle omega T))
    T (certificate seed).toAdaptiveProcess hrhoIoo hrhoEq (hzero seed) rfl (hloss seed)

end Lemmata.DistributionalLowerBounds.Core.Distributional
