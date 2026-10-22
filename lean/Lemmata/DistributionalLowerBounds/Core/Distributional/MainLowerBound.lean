module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.FiniteProbability
public import Mathlib.Tactic

@[expose] public section

/-!
# Paper-facing arithmetic endpoint

This theorem composes the formally verified horizon arithmetic, finite Jensen
inequality, optimizer-distance loss conversion, and the concrete lower bound on
`rho`.  Its two substantive hypotheses correspond exactly to the still
unformalized adaptive posterior lemmas:

1. expected deficit loss is at most `8 T d^(3/2)`;
2. conditional loss is bounded below by the squared deficit.

Thus the endpoint is conditional: its assumptions are explicit, and it is not
an unconditional Lean proof of the paper's main theorem.
-/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

open FinitePMF

/-- Composition of all constant-sensitive arithmetic in the expectation lower
bound. -/
theorem distributional_lower_bound_arithmetic
    {Ω : Type*} [Fintype Ω]
    (P : FinitePMF Ω) (Delta loss : Ω → ℝ)
    (T : ℕ) {rho C : ℝ}
    (hrho : 2 / (proofDimension T : ℝ) ^ 2 ≤ rho)
    (hmean :
      initialDeficit (proofDimension T) -
        8 * (T : ℝ) * (proofDimension T : ℝ) * (64 * (T + 1 : ℝ)) ≤
          P.expect Delta)
    (hloss : ∀ ω,
      rho ^ 2 * C ^ 2 * Delta ω ^ 2 /
          (48 * (proofDimension T : ℝ) ^ 2) ≤ loss ω) :
    C ^ 2 / (768 * (proofDimension T : ℝ) ^ 2) ≤ P.expect loss := by
  let d : ℝ := proofDimension T
  have hd2 : (2 : ℝ) ≤ d := by
    dsimp [d]
    simp [proofDimension]
    have hT : (0 : ℝ) ≤ T := by positivity
    nlinarith [sq_nonneg ((T : ℝ) + 1)]
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hd2
  have hDelta : d ^ 2 / 8 ≤ P.expect Delta := by
    apply remaining_deficit_lower_bound T
    simpa [d] using hmean
  have hbase : rho ^ 2 * C ^ 2 * d ^ 2 / 3072 ≤ P.expect loss := by
    exact P.expected_loss_from_pointwise_deficit Delta loss hd hDelta
      (by simpa [d] using hloss)
  have hsmall0 : 0 ≤ 2 / d ^ 2 := by positivity
  have hrho0 : 0 ≤ rho := le_trans hsmall0 hrho
  have hrhoSq : (2 / d ^ 2) ^ 2 ≤ rho ^ 2 := by nlinarith
  have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
  have hscale : C ^ 2 / (768 * d ^ 2) ≤
      rho ^ 2 * C ^ 2 * d ^ 2 / 3072 := by
    have hd2pos : 0 < d ^ 2 := sq_pos_of_pos hd
    have hd4pos : 0 < d ^ 4 := by positivity
    have hraw : 4 * C ^ 2 ≤ rho ^ 2 * C ^ 2 * d ^ 4 := by
      have := mul_le_mul_of_nonneg_right hrhoSq hC2
      field_simp [hd.ne'] at this
      nlinarith
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 768 * d ^ 2)
      (by positivity : (0 : ℝ) < 3072)).2
    nlinarith
  exact hscale.trans hbase

/-- Concrete version using the formally verified `rho ≥ 2/d²` theorem. -/
theorem concrete_distributional_lower_bound_arithmetic
    {Ω : Type*} [Fintype Ω]
    (P : FinitePMF Ω) (Delta loss : Ω → ℝ)
    (T : ℕ) {rho : ℝ}
    (hrhoIoo : rho ∈ Set.Ioo (0 : ℝ) 1)
    (hrhoEq :
      rhoLHS (hardWeight (proofDimension T))
          (hardTopWeight (proofDimension T)) rho =
        hardC (proofDimension T) ^ 2)
    (hmean :
      initialDeficit (proofDimension T) -
        8 * (T : ℝ) * (proofDimension T : ℝ) * (64 * (T + 1 : ℝ)) ≤
          P.expect Delta)
    (hloss : ∀ ω,
      rho ^ 2 * hardC (proofDimension T) ^ 2 * Delta ω ^ 2 /
          (48 * (proofDimension T : ℝ) ^ 2) ≤ loss ω) :
    hardC (proofDimension T) ^ 2 /
        (768 * (proofDimension T : ℝ) ^ 2) ≤ P.expect loss := by
  apply distributional_lower_bound_arithmetic P Delta loss T
  · apply concrete_rho_lower_bound (d := proofDimension T)
      (by
        have hpow : 1 ≤ (T + 1) ^ 2 := Nat.one_le_pow 2 (T + 1) (by omega)
        calc
          3 ≤ 4096 := by norm_num
          _ = 4096 * 1 := by norm_num
          _ ≤ 4096 * (T + 1) ^ 2 := Nat.mul_le_mul_left 4096 hpow
          _ = proofDimension T := by rfl)
      hrhoIoo hrhoEq
  · exact hmean
  · exact hloss

end Lemmata.DistributionalLowerBounds.Core.Distributional
