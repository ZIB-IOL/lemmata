module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.DistributionalTheorem

@[expose] public section

/-! Coordinate conjugation of actual oracle controllers. -/
namespace Lemmata.DistributionalLowerBounds.Core.Distributional

noncomputable def relabel {d : ℕ} (g : Equiv.Perm (Fin d)) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => x (g.symm i)

@[simp] lemma relabel_zero {d : ℕ} (g : Equiv.Perm (Fin d)) :
    relabel g (0 : Fin d → ℝ) = 0 := by funext i; rfl

lemma relabel_cancel {d : ℕ} (g : Equiv.Perm (Fin d)) (x : Fin d → ℝ) :
    relabel g.symm (relabel g x) = x := by funext i; simp [relabel]

lemma energy_relabel {d : ℕ} (g π : Equiv.Perm (Fin d)) (x : Fin d → ℝ) :
    coordinateEnergy (permutedHardWeight d π) (relabel g x) =
      coordinateEnergy (permutedHardWeight d (g.trans π)) x := by
  have h := Equiv.sum_comp g (fun i => (1/2 : ℝ)*(relabel g x i)^2 +
    permutedHardWeight d π i*|relabel g x i|)
  simpa [coordinateEnergy, relabel, permutedHardWeight] using h.symm

lemma objective_relabel {d : ℕ} (g : Equiv.Perm (Fin d)) (M : ℝ) (x : Fin d → ℝ) :
    coordinateObjective M (relabel g x) = coordinateObjective M x :=
  Equiv.sum_comp g.symm (fun i => (1/2 : ℝ)*(x i-M)^2)

lemma dot_relabel {d : ℕ} (g : Equiv.Perm (Fin d)) (p z : Fin d → ℝ) :
    (∑ i, relabel g p i*z i) = ∑ i, p i*relabel g.symm z i := by
  have h := Equiv.sum_comp g (fun i => relabel g p i*z i)
  simpa [relabel] using h.symm

lemma concreteLMO_relabel {d : ℕ} (g π : Equiv.Perm (Fin d)) (p : Fin d → ℝ) :
    relabel g.symm (concreteLMO d π (relabel g p)) = concreteLMO d (g.trans π) p := by
  by_cases hp : p = 0
  · subst p; simp only [relabel_zero, concreteLMO_zero]
  · let z := concreteLMO d π (relabel g p)
    let y := concreteLMO d (g.trans π) p
    have hz := concreteLMO_correct d π (relabel g p)
    have hy := concreteLMO_correct d (g.trans π) p
    have he : relabel g (relabel g.symm z) = z := relabel_cancel g.symm z
    have hf : coordinateEnergy (permutedHardWeight d (g.trans π)) (relabel g.symm z) ≤ hardC d^2 := by
      rw [← energy_relabel g π, he]
      exact hz.1
    have hpp : ∃ i, p i ≠ 0 := by
      by_contra h
      push Not at h
      exact hp (funext h)
    apply concreteLMO_unique (g.trans π) p hpp _ hf
    have hh := hz.2 (relabel g y) (by rw [energy_relabel g π]; exact hy.1)
    rw [dot_relabel g, dot_relabel g, relabel_cancel] at hh
    exact le_antisymm hh (hy.2 _ hf)

noncomputable def conjugateQuery {d : ℕ} (g : Equiv.Perm (Fin d)) (q : PairedQuery d) : PairedQuery d :=
  (relabel g q.1, relabel g q.2)
noncomputable def conjugateAnswer {d : ℕ} (g : Equiv.Perm (Fin d)) (a : PairedAnswer d) : PairedAnswer d :=
  (a.1, relabel g.symm a.2.1, relabel g.symm a.2.2)

lemma scaledOracle_conjugate {d : ℕ} (g π : Equiv.Perm (Fin d)) (rho L alpha : ℝ)
    (q : PairedQuery d) :
    conjugateAnswer g (scaledConcreteOracle d rho L alpha π (conjugateQuery g q)) =
      scaledConcreteOracle d rho L alpha (g.trans π) q := by
  have hscale : alpha • relabel g q.1 = relabel g (alpha • q.1) := rfl
  apply Prod.ext
  · dsimp [conjugateAnswer, scaledConcreteOracle, scaleAnswer, conjugateQuery, scaleQuery, concreteOracle]
    rw [hscale, objective_relabel]
  · apply Prod.ext
    · funext i
      simp [conjugateAnswer, scaledConcreteOracle, scaleAnswer, conjugateQuery, scaleQuery,
        concreteOracle, relabel]
    · change relabel g.symm (alpha⁻¹ • concreteLMO d π (relabel g q.2)) =
        alpha⁻¹ • concreteLMO d (g.trans π) q.2
      change alpha⁻¹ • relabel g.symm (concreteLMO d π (relabel g q.2)) = _
      rw [concreteLMO_relabel]

noncomputable def conjugateStrategy {d : ℕ} (g : Equiv.Perm (Fin d)) (s : FamilyStrategy d) :
    FamilyStrategy d := s.transport (conjugateQuery g) (conjugateAnswer g) (relabel g)

lemma conjugateStrategy_run {d : ℕ} (g π : Equiv.Perm (Fin d)) (s : FamilyStrategy d)
    (rho L alpha : ℝ) (T : ℕ) :
    (conjugateStrategy g s).run (scaledConcreteOracle d rho L alpha) π T =
      relabel g (s.run (scaledConcreteOracle d rho L alpha) (g.trans π) T) := by
  rw [conjugateStrategy, DeterministicAdaptiveStrategy.transport_run]
  have he : (fun π q => conjugateAnswer g (scaledConcreteOracle d rho L alpha π (conjugateQuery g q))) =
      (fun π q => scaledConcreteOracle d rho L alpha (g.trans π) q) := by
    funext π q; exact scaledOracle_conjugate g π rho L alpha q
  rw [he, DeterministicAdaptiveStrategy.run_reindex]

lemma scaledFamilyLoss_relabel {d : ℕ} (g π : Equiv.Perm (Fin d)) (rho L alpha : ℝ)
    (x : Fin d → ℝ) :
    scaledFamilyLoss d rho L alpha π (relabel g x) =
      scaledFamilyLoss d rho L alpha (g.trans π) x := by
  have he : alpha • relabel g x = relabel g (alpha • x) := rfl
  simp only [scaledFamilyLoss, hardFamilyLoss, he, objective_relabel,
    concrete_optimal_value_permutation_invariant]

noncomputable def permutationTranslate {d : ℕ} (π : Equiv.Perm (Fin d)) :
    Equiv.Perm (Equiv.Perm (Fin d)) where
  toFun g := g.trans π
  invFun g := g.trans π.symm
  left_inv g := by ext i; simp
  right_inv g := by ext i; simp

/-- Uniform coordinate conjugation equalizes the expected loss on every
instance to the original uniform-prior loss. Applies also to any real statistic
of the loss, e.g. the indicator of a non-strict failure threshold. -/
theorem conjugate_uniform_risk {d : ℕ} (s : FamilyStrategy d) (rho L alpha : ℝ)
    (T : ℕ) (π : Equiv.Perm (Fin d)) (statistic : ℝ → ℝ) :
    (FinitePMF.uniform (Equiv.Perm (Fin d))).expect (fun g => statistic
      (scaledFamilyLoss d rho L alpha π
        ((conjugateStrategy g s).run (scaledConcreteOracle d rho L alpha) π T))) =
    (FinitePMF.uniform (Equiv.Perm (Fin d))).expect (fun σ => statistic
      (scaledFamilyLoss d rho L alpha σ (s.run (scaledConcreteOracle d rho L alpha) σ T))) := by
  simp only [conjugateStrategy_run, scaledFamilyLoss_relabel, FinitePMF.uniform_expect]
  exact uniformAverage_comp_equiv (permutationTranslate π) (fun σ => statistic
    (scaledFamilyLoss d rho L alpha σ (s.run (scaledConcreteOracle d rho L alpha) σ T)))

lemma conjugateStrategy_measurable {Seed : Type} [MeasurableSpace Seed] {d T : ℕ}
    (g : Equiv.Perm (Fin d)) {s : Seed → FamilyStrategy d} (hs : MeasurableStrategy s T) :
    MeasurableStrategy (fun seed => conjugateStrategy g (s seed)) T :=
  hs.transport _ _ _ (by unfold conjugateQuery relabel; fun_prop)
    (by unfold conjugateAnswer relabel; fun_prop) (by unfold relabel; fun_prop)

lemma conjugateStrategy_feasible {d : ℕ} (g : Equiv.Perm (Fin d)) (s : FamilyStrategy d)
    (rho L alpha : ℝ) (T : ℕ)
    (hf : ∀ π, ScaledFeasible alpha π (s.run (scaledConcreteOracle d rho L alpha) π T)) :
    ∀ π, ScaledFeasible alpha π
      ((conjugateStrategy g s).run (scaledConcreteOracle d rho L alpha) π T) := by
  intro π
  rw [conjugateStrategy_run]
  change coordinateEnergy (permutedHardWeight d π)
    (relabel g (alpha • s.run (scaledConcreteOracle d rho L alpha) (g.trans π) T)) ≤ _
  rw [energy_relabel]
  exact hf (g.trans π)

/-- Adding an independent finite permutation to any seed retains measurability.
The finite permutation space is equipped with its full sigma-algebra. -/
lemma conjugate_mixture_measurable {Seed : Type} [MeasurableSpace Seed] {d T : ℕ}
    [MeasurableSpace (Equiv.Perm (Fin d))] [MeasurableSingletonClass (Equiv.Perm (Fin d))]
    {s : Seed → FamilyStrategy d} (hs : MeasurableStrategy s T) :
    MeasurableStrategy (fun z : Seed × Equiv.Perm (Fin d) => conjugateStrategy z.2 (s z.1)) T := by
  constructor
  · intro t ht
    have h : Measurable (fun w : (Seed × (Fin t → PairedAnswer d)) × Equiv.Perm (Fin d) =>
        (conjugateStrategy w.2 (s w.1.1)).nextQuery t (List.ofFn w.1.2)) :=
      measurable_from_prod_countable_left (fun g => (conjugateStrategy_measurable g hs).query t ht)
    exact h.comp (by fun_prop : Measurable
      (fun z : (Seed × Equiv.Perm (Fin d)) × (Fin t → PairedAnswer d) => ((z.1.1,z.2),z.1.2)))
  · have h : Measurable (fun w : (Seed × (Fin T → PairedAnswer d)) × Equiv.Perm (Fin d) =>
        (conjugateStrategy w.2 (s w.1.1)).output (List.ofFn w.1.2)) :=
      measurable_from_prod_countable_left (fun g => (conjugateStrategy_measurable g hs).output)
    exact h.comp (by fun_prop : Measurable
      (fun z : (Seed × Equiv.Perm (Fin d)) × (Fin T → PairedAnswer d) => ((z.1.1,z.2),z.1.2)))

end Lemmata.DistributionalLowerBounds.Core.Distributional
