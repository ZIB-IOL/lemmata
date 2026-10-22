module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.ExactLMO
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Order.Lattice

@[expose] public section

/-!
# A measurable, total exact LMO for the concrete family

The inverse water level is a finite maximum of continuous subset scores.
This gives a measurable explicit oracle without assuming measurability of an
argmin selection. At direction zero the formula returns zero, as required.
The finite maximum is a proof representation, not a claim of efficient oracle
implementation or a restriction on the query algorithm.
-/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

noncomputable def subsetScore {d : ℕ} (rank p : Fin d → ℝ) (A : Finset (Fin d)) : ℝ :=
  (∑ i ∈ A, p i^2) / (1 + ∑ i ∈ A, rank i)

noncomputable def waterInverse {d : ℕ} (rank p : Fin d → ℝ) : ℝ :=
  (Finset.univ : Finset (Finset (Fin d))).sup' Finset.univ_nonempty (subsetScore rank p)

lemma subset_den_pos {d : ℕ} (rank : Fin d → ℝ) (hrank : ∀ i, 0 ≤ rank i)
    (A : Finset (Fin d)) : 0 < 1 + ∑ i ∈ A, rank i := by
  have h := Finset.sum_nonneg (fun i (_ : i ∈ A) => hrank i)
  linarith

/-- Every subset's affine water contribution is bounded by the full positive sum. -/
lemma subset_water_le {d : ℕ} (p rank : Fin d → ℝ) (tau : ℝ)
    (A : Finset (Fin d)) :
    tau*(∑ i ∈ A, p i^2) - (∑ i ∈ A, rank i) ≤ waterProfile p rank tau := by
  calc
    _ = ∑ i ∈ A, (tau*p i^2-rank i) := by rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ ≤ ∑ i ∈ A, max 0 (tau*p i^2-rank i) :=
      Finset.sum_le_sum (fun i _ => le_max_right _ _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
      (fun i _ _ => le_max_left _ _)

/-- Equality is attained by the actual strictly active set. -/
lemma active_subset_water_eq {d : ℕ} (p rank : Fin d → ℝ) (tau : ℝ) :
    let A := Finset.univ.filter (fun i => 0 < tau*p i^2-rank i)
    tau*(∑ i ∈ A, p i^2) - (∑ i ∈ A, rank i) = waterProfile p rank tau := by
  classical
  dsimp only
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_filter]
  unfold waterProfile
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : 0 < tau*p i^2-rank i
  · simp [h, max_eq_right h.le]
  · simp [h, max_eq_left (le_of_not_gt h)]

/-- The finite maximum is the inverse of any positive unit-profile water level. -/
theorem waterInverse_eq_inv {d : ℕ} (p rank : Fin d → ℝ)
    (hrank : ∀ i, 0 ≤ rank i) {tau : ℝ} (htau : 0 < tau)
    (hprofile : waterProfile p rank tau = 1) : waterInverse rank p = tau⁻¹ := by
  classical
  apply le_antisymm
  · apply Finset.sup'_le
    intro A _
    have h := subset_water_le p rank tau A
    rw [hprofile] at h
    unfold subsetScore
    apply (div_le_iff₀ (subset_den_pos rank hrank A)).2
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ htau).2
    nlinarith
  · let A := Finset.univ.filter (fun i => 0 < tau*p i^2-rank i)
    have he : subsetScore rank p A = tau⁻¹ := by
      have h := active_subset_water_eq p rank tau
      rw [hprofile] at h
      change tau*(∑ i ∈ A, p i^2) - (∑ i ∈ A, rank i) = 1 at h
      unfold subsetScore
      apply (div_eq_iff (subset_den_pos rank hrank A).ne').2
      rw [inv_mul_eq_div]
      apply (eq_div_iff htau.ne').2
      nlinarith
    rw [← he]
    exact Finset.le_sup' (subsetScore rank p) (Finset.mem_univ A)

/-- The explicit inverse maximum supplies the positive root, not just a
measurable function with an assumed root property. -/
theorem waterInverse_inv_spec {d : ℕ} (p rank : Fin d → ℝ)
    (hrank : ∀ i, 0 ≤ rank i) (hp : ∃ i, p i ≠ 0) :
    0 < (waterInverse rank p)⁻¹ ∧ waterProfile p rank ((waterInverse rank p)⁻¹) = 1 := by
  obtain ⟨tau, htau, _⟩ := existsUnique_waterLevel p rank hrank hp
  rw [waterInverse_eq_inv p rank hrank htau.1 htau.2, inv_inv]
  exact htau

lemma continuous_waterInverse (d : ℕ) (rank : Fin d → ℝ) :
    Continuous (waterInverse rank) := by
  apply Continuous.finset_sup'_apply
  intro A _
  unfold subsetScore
  fun_prop

@[simp] lemma waterInverse_zero (d : ℕ) (rank : Fin d → ℝ) :
    waterInverse rank 0 = 0 := by
  unfold waterInverse
  apply Finset.sup'_eq_of_forall
  intro A _
  simp [subsetScore]

/-- Total formula, including the mandated zero answer at the zero direction. -/
noncomputable def explicitLMO {d : ℕ} (C : ℝ) (w rank p : Fin d → ℝ) : Fin d → ℝ :=
  fun i => softCoordinate (p i) (w i) (multiplierOfTau C ((waterInverse rank p)⁻¹))

lemma explicitLMO_zero {d : ℕ} (C : ℝ) (w rank : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) : explicitLMO C w rank 0 = 0 := by
  funext i
  simp [explicitLMO, softCoordinate, softAmount, max_eq_left (neg_nonpos.mpr (hw i))]

lemma measurable_explicitLMO {d : ℕ} (C : ℝ) (w rank : Fin d → ℝ) :
    Measurable (explicitLMO C w rank) := by
  have hg := (continuous_waterInverse d rank).measurable
  have hm : Measurable (fun p => multiplierOfTau C ((waterInverse rank p)⁻¹)) := by
    unfold multiplierOfTau
    fun_prop
  apply measurable_pi_iff.mpr
  intro i
  unfold explicitLMO softCoordinate softAmount
  apply Measurable.ite (measurableSet_le measurable_const (measurable_pi_apply i))
  · fun_prop
  · fun_prop

/-- Feasibility and exact minimization for the total formula. No oracle-
measurability or argmin-selection assumption is present. -/
theorem explicitLMO_correct {d : ℕ} (p w rank : Fin d → ℝ) {C : ℝ}
    (hC : 0 < C) (hw0 : ∀ i, 0 ≤ w i) (hrank : ∀ i, 0 ≤ rank i)
    (hw : ∀ i, w i^2 = 2*C^2*rank i) :
    coordinateEnergy w (explicitLMO C w rank p) ≤ C^2 ∧
    ∀ x : Fin d → ℝ, coordinateEnergy w x ≤ C^2 →
      (∑ i, p i*explicitLMO C w rank p i) ≤ ∑ i, p i*x i := by
  by_cases hp : ∃ i, p i ≠ 0
  · obtain ⟨tau, htau, _⟩ := existsUnique_waterLevel p rank hrank hp
    have hg := waterInverse_eq_inv p rank hrank htau.1 htau.2
    have hlevel : (waterInverse rank p)⁻¹ = tau := by rw [hg, inv_inv]
    have hl := multiplierOfTau_pos hC htau.1
    have hprofile : waterProfile p rank (waterTau C (multiplierOfTau C tau)) = 1 := by
      rw [waterTau_multiplierOfTau hC htau.1]
      exact htau.2
    have hb := softCoordinate_boundary_of_waterProfile p w rank hC hl hw0 hw hprofile
    unfold explicitLMO
    rw [hlevel]
    exact ⟨hb.le, softCoordinate_is_LMO p w hw0 hl hb⟩
  · have hp0 : p = 0 := by
      push Not at hp
      funext i
      exact hp i
    subst p
    rw [explicitLMO_zero C w rank hw0]
    simp [coordinateEnergy, sq_nonneg C]

/-- Nonzero-direction uniqueness identifies this formula with any exact LMO
selection; there is no new tie-breaking freedom for a nonzero direction. -/
theorem explicitLMO_unique {d : ℕ} (p w rank : Fin d → ℝ) {C : ℝ}
    (hC : 0 < C) (hw0 : ∀ i, 0 ≤ w i) (hrank : ∀ i, 0 ≤ rank i)
    (hw : ∀ i, w i^2 = 2*C^2*rank i) (hp : ∃ i, p i ≠ 0)
    {x : Fin d → ℝ} (hx : coordinateEnergy w x ≤ C^2)
    (hvalue : (∑ i, p i*x i) = ∑ i, p i*explicitLMO C w rank p i) :
    x = explicitLMO C w rank p := by
  have ht := waterInverse_inv_spec p rank hrank hp
  have hl := multiplierOfTau_pos hC ht.1
  have hp' : waterProfile p rank
      (waterTau C (multiplierOfTau C ((waterInverse rank p)⁻¹))) = 1 := by
    rw [waterTau_multiplierOfTau hC ht.1]
    exact ht.2
  exact softCoordinate_unique_LMO p w hw0 hl
    (softCoordinate_boundary_of_waterProfile p w rank hC hl hw0 hw hp') hx hvalue

noncomputable def concreteLMO (d : ℕ) (π : Equiv.Perm (Fin d)) : (Fin d → ℝ) → Fin d → ℝ :=
  explicitLMO (hardC d) (permutedHardWeight d π) (permutedRank π)

lemma concreteLMO_measurable (d : ℕ) (π : Equiv.Perm (Fin d)) :
    Measurable (concreteLMO d π) := measurable_explicitLMO _ _ _

lemma concreteLMO_zero (d : ℕ) (π : Equiv.Perm (Fin d)) : concreteLMO d π 0 = 0 :=
  explicitLMO_zero _ _ _ (fun i => hardWeight_nonneg d (π i))

theorem concreteLMO_correct (d : ℕ) (π : Equiv.Perm (Fin d)) (p : Fin d → ℝ) :
    coordinateEnergy (permutedHardWeight d π) (concreteLMO d π p) ≤ hardC d^2 ∧
    ∀ x : Fin d → ℝ, coordinateEnergy (permutedHardWeight d π) x ≤ hardC d^2 →
      (∑ i, p i*concreteLMO d π p i) ≤ ∑ i, p i*x i :=
  explicitLMO_correct p _ _ (hardC_pos d) (fun i => hardWeight_nonneg d (π i))
    (fun i => by dsimp [permutedRank]; positivity) (permutedHardWeight_sq_rank π)

end Lemmata.DistributionalLowerBounds.Core.Distributional
