module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.Optimizer
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic

@[expose] public section

/-!
# Arithmetic core of the Ferrers-posterior lower bound

This module verifies the constant-sensitive inequalities used after the
combinatorial/probabilistic posterior lemmas.  The missing theorem in the
current Lean coverage is the construction of the conditional variances and the
one-query drift bound themselves; those are represented here by explicit
hypotheses, never by axioms.
-/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

/-- Cauchy--Schwarz and the elementary bound `c²-1 ≥ (c-1)²` turn componentwise
conditional-variance estimates into the paper's deficit estimate. -/
theorem deficit_variance_arithmetic {m : ℕ} (hm : 0 < m)
    (c variance : Fin m → ℝ)
    (hc : ∀ i, 1 ≤ c i)
    (hvariance : ∀ i, (c i ^ 2 - 1) / 12 ≤ variance i) :
    ((∑ i, (c i - 1)) ^ 2) / (12 * m) ≤ ∑ i, variance i := by
  have hcomponent : ∀ i, (c i - 1) ^ 2 / 12 ≤ variance i := by
    intro i
    have hsq : (c i - 1) ^ 2 ≤ c i ^ 2 - 1 := by
      nlinarith [hc i]
    exact le_trans (div_le_div_of_nonneg_right hsq (by norm_num)) (hvariance i)
  have hsum_component : (∑ i, (c i - 1) ^ 2) / 12 ≤ ∑ i, variance i := by
    calc
      (∑ i, (c i - 1) ^ 2) / 12 = ∑ i, ((c i - 1) ^ 2 / 12) := by
        rw [Finset.sum_div]
      _ ≤ ∑ i, variance i := Finset.sum_le_sum (fun i _ => hcomponent i)
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ) (f := fun i : Fin m => c i - 1)
  simp only [Finset.card_univ, Fintype.card_fin] at hcs
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h12m : (0 : ℝ) < 12 * m := by positivity
  have hfirst : ((∑ i, (c i - 1)) ^ 2) / (12 * m) ≤
      (∑ i, (c i - 1) ^ 2) / 12 := by
    apply (div_le_iff₀ h12m).2
    have hmul : (∑ i, (c i - 1)) ^ 2 ≤
        (m : ℝ) * ∑ i, (c i - 1) ^ 2 := by simpa using hcs
    nlinarith
  exact hfirst.trans hsum_component

/-- Difference of square roots loses at most `2 sqrt(d)`. -/
theorem sqrt_difference_lower_bound
    {u v d : ℝ} (hd : 0 < d)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hud : u ≤ d) (hvd : v ≤ d) :
    |Real.sqrt u - Real.sqrt v| ≥ |u - v| / (2 * Real.sqrt d) := by
  have hsdu : Real.sqrt u ≤ Real.sqrt d := Real.sqrt_le_sqrt hud
  have hsdv : Real.sqrt v ≤ Real.sqrt d := Real.sqrt_le_sqrt hvd
  have hden : 0 < 2 * Real.sqrt d := by positivity
  have hsum : Real.sqrt u + Real.sqrt v ≤ 2 * Real.sqrt d := by linarith
  have hprod :
      |Real.sqrt u - Real.sqrt v| * (Real.sqrt u + Real.sqrt v) = |u - v| := by
    have huu := Real.sq_sqrt hu
    have hvv := Real.sq_sqrt hv
    have hsum0 : 0 ≤ Real.sqrt u + Real.sqrt v := by positivity
    calc
      |Real.sqrt u - Real.sqrt v| * (Real.sqrt u + Real.sqrt v) =
          |Real.sqrt u - Real.sqrt v| * |Real.sqrt u + Real.sqrt v| := by
            rw [abs_of_nonneg hsum0]
      _ = |(Real.sqrt u - Real.sqrt v) *
          (Real.sqrt u + Real.sqrt v)| := (abs_mul _ _).symm
      _ = |u - v| := by
        congr 1
        nlinarith
  apply (div_le_iff₀ hden).2
  calc
    |u - v| = |Real.sqrt u - Real.sqrt v| *
        (Real.sqrt u + Real.sqrt v) := hprod.symm
    _ ≤ |Real.sqrt u - Real.sqrt v| * (2 * Real.sqrt d) := by
      exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)

/-- The horizon choice used in the paper. -/
def proofDimension (T : ℕ) : ℕ := 4096 * (T + 1) ^ 2

lemma proofDimension_cast (T : ℕ) :
    (proofDimension T : ℝ) = (64 * (T + 1 : ℝ)) ^ 2 := by
  simp [proofDimension]
  ring

/-- With `d=4096(T+1)²`, the accumulated `8 d^(3/2)` drift is at most `d²/8`.
The statement writes `d^(3/2)` as `d * sqrt(d)` using the exact square root
`64(T+1)`. -/
theorem accumulated_drift_le_eighth (T : ℕ) :
    8 * (T : ℝ) * (proofDimension T : ℝ) * (64 * (T + 1 : ℝ)) ≤
      (proofDimension T : ℝ) ^ 2 / 8 := by
  rw [proofDimension_cast]
  have hT : (0 : ℝ) ≤ T := by positivity
  nlinarith [sq_nonneg (64 * (T + 1 : ℝ))]

/-- Telescoping a uniform one-step expected-drift bound. -/
theorem expected_deficit_telescope
    (delta : ℕ → ℝ) (T : ℕ) {B : ℝ}
    (hstep : ∀ t < T, delta t - delta (t + 1) ≤ B) :
    delta 0 - (T : ℝ) * B ≤ delta T := by
  induction T with
  | zero => simp
  | succ T ih =>
      have hprev : ∀ t < T, delta t - delta (t + 1) ≤ B :=
        fun t ht => hstep t (ht.trans (Nat.lt_succ_self T))
      have hih := ih hprev
      have hlast := hstep T (Nat.lt_succ_self T)
      push_cast
      linarith

/-- Initial unconstrained deficit. -/
noncomputable def initialDeficit (d : ℕ) : ℝ := (d : ℝ) * (d - 1) / 2

/-- Convert one-query bounds into the mean-deficit hypothesis used by the
main arithmetic endpoint. -/
theorem mean_deficit_from_oneQuery_steps
    (delta : ℕ → ℝ) (T : ℕ)
    (hzero : delta 0 = initialDeficit (proofDimension T))
    (hstep : ∀ t < T,
      delta t - delta (t + 1) ≤
        8 * (proofDimension T : ℝ) * (64 * (T + 1 : ℝ))) :
    initialDeficit (proofDimension T) -
        8 * (T : ℝ) * (proofDimension T : ℝ) * (64 * (T + 1 : ℝ)) ≤
      delta T := by
  have ht := expected_deficit_telescope delta T hstep
  rw [hzero] at ht
  nlinarith

/-- The chosen dimension has enough initial deficit that, after the allowed
drift, at least `d²/8` remains. -/
theorem remaining_deficit_lower_bound (T : ℕ) {delta : ℝ}
    (hdelta :
      initialDeficit (proofDimension T) -
        8 * (T : ℝ) * (proofDimension T : ℝ) * (64 * (T + 1 : ℝ)) ≤ delta) :
    (proofDimension T : ℝ) ^ 2 / 8 ≤ delta := by
  have hd : (2 : ℝ) ≤ proofDimension T := by
    simp [proofDimension]
    have hT : (0 : ℝ) ≤ T := by positivity
    nlinarith [sq_nonneg ((T : ℝ) + 1)]
  have hdrift := accumulated_drift_le_eighth T
  dsimp [initialDeficit] at hdelta
  nlinarith

/-- Constant-sensitive endgame of the expectation proof.  The assumptions are
exactly the two currently separate paper lemmas: an average remaining-deficit
bound and the conditional quadratic-loss bound. -/
theorem expected_loss_from_deficit
    {d rho C meanDelta meanDeltaSq meanLoss : ℝ}
    (hd : 0 < d)
    (hmean : d ^ 2 / 8 ≤ meanDelta)
    (hjensen : meanDelta ^ 2 ≤ meanDeltaSq)
    (hloss : rho ^ 2 * C ^ 2 * meanDeltaSq / (48 * d ^ 2) ≤ meanLoss) :
    rho ^ 2 * C ^ 2 * d ^ 2 / 3072 ≤ meanLoss := by
  have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
  have hmd : 0 ≤ meanDelta := le_trans (by positivity) hmean
  have hsq : d ^ 4 / 64 ≤ meanDelta ^ 2 := by
    nlinarith [sq_nonneg (meanDelta - d ^ 2 / 8)]
  have hnonneg : 0 ≤ rho ^ 2 * C ^ 2 := by positivity
  have hnum : rho ^ 2 * C ^ 2 * (d ^ 4 / 64) ≤
      rho ^ 2 * C ^ 2 * meanDeltaSq := by
    gcongr
    exact hsq.trans hjensen
  have hscale :
      rho ^ 2 * C ^ 2 * d ^ 2 / 3072 ≤
        rho ^ 2 * C ^ 2 * meanDeltaSq / (48 * d ^ 2) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 3072)
      (by positivity : (0 : ℝ) < 48 * d ^ 2)).2
    nlinarith
  exact hscale.trans hloss

end Lemmata.DistributionalLowerBounds.Core.Distributional
