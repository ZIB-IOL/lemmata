module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.FiniteStrategy

@[expose] public section

/-!
# Uniform finite fibers and their expectation transport

These identities construct the uniform PMF and the mass-weighted finite-fiber
law; they do not assume a conditional-probability identity. Nonempty fibers
can be normalized, while empty/unreachable fibers contribute zero. For the
hard-family application, the numerical transcript/fiber equivalence must still
be constructed. Classical decidable equality is proof infrastructure, not a
computability or finite-alphabet restriction on oracle answers.
-/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

lemma uniformAverage_comp_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (X : B → ℝ) :
    uniformAverage (fun a => X (e a)) = uniformAverage X := by
  unfold uniformAverage
  rw [Fintype.card_congr e, Equiv.sum_comp]

namespace FinitePMF

/-- A uniform law exists on every nonempty finite instance type. -/
noncomputable def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FinitePMF Ω where
  weight _ := 1 / (Fintype.card Ω : ℝ)
  nonneg _ := by positivity
  sum_weight := by
    have h : (Fintype.card Ω : ℝ) ≠ 0 := (card_cast_pos (Ω := Ω)).ne'
    simp [h]

lemma uniform_expect {Ω : Type*} [Fintype Ω] [Nonempty Ω] (X : Ω → ℝ) :
    (uniform Ω).expect X = uniformAverage X := by
  unfold expect uniform uniformAverage
  simp only [one_div]
  rw [← Finset.mul_sum]
  ring

variable {Ω H : Type*} [Fintype Ω] [Nonempty Ω] [Fintype H] [DecidableEq H]

omit [Nonempty Ω] [Fintype H] in
lemma sum_over_fiber (history : Ω → H) (X : Ω → ℝ) (h : H) :
    (∑ ω, if history ω = h then X ω else 0) =
      ∑ ω : {ω // history ω = h}, X ω.val := by
  classical
  calc
    _ = ∑ ω ∈ Finset.univ.filter (fun ω => history ω = h), X ω := by
      rw [Finset.sum_filter]
    _ = _ := Finset.sum_subtype _ (by simp) _

omit [Fintype H] in
lemma uniform_fiberContribution (history : Ω → H) (X : Ω → ℝ) (h : H) :
    (uniform Ω).fiberContribution history X h =
      (∑ ω : {ω // history ω = h}, X ω.val) / (Fintype.card Ω : ℝ) := by
  classical
  unfold fiberContribution uniform
  calc
    _ = ∑ ω, (if history ω = h then X ω else 0) / (Fintype.card Ω : ℝ) := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases he : history ω = h <;> simp [he, div_eq_mul_inv, mul_comm]
    _ = (∑ ω, if history ω = h then X ω else 0) / (Fintype.card Ω : ℝ) :=
      (Finset.sum_div _ _ _).symm
    _ = _ := by rw [sum_over_fiber]

lemma uniform_history_mass (history : Ω → H) (h : H) :
    ((uniform Ω).map history).weight h =
      (Fintype.card {ω // history ω = h} : ℝ) / (Fintype.card Ω : ℝ) := by
  calc
    _ = (uniform Ω).fiberContribution history (fun _ => (1 : ℝ)) h := by
      unfold map fiberContribution
      apply Finset.sum_congr rfl
      intro ω _
      by_cases he : history ω = h <;> simp [he]
    _ = _ := by simpa using uniform_fiberContribution history (fun _ => (1 : ℝ)) h

/-- No positive-fiber premise is needed for the MASS-WEIGHTED identity.
The empty-fiber case is proved separately and never normalized to a PMF. -/
theorem uniform_mass_mul_fiber_average (history : Ω → H) (X : Ω → ℝ) (h : H) :
    (uniform Ω).fiberContribution history X h =
      ((uniform Ω).map history).weight h *
        uniformAverage (fun ω : {ω // history ω = h} => X ω.val) := by
  rw [uniform_history_mass, uniform_fiberContribution]
  by_cases hz : Fintype.card {ω // history ω = h} = 0
  · letI : IsEmpty {ω // history ω = h} := Fintype.card_eq_zero_iff.mp hz
    simp [uniformAverage]
  · have hn : (Fintype.card {ω // history ω = h} : ℝ) ≠ 0 := by exact_mod_cast hz
    unfold uniformAverage
    field_simp

/-- Conditional normalization is legitimate only for a nonempty fiber. -/
theorem uniform_conditional_average (history : Ω → H) (X : Ω → ℝ) (h : H)
    (hne : ∃ ω, history ω = h) :
    (uniform Ω).fiberContribution history X h / ((uniform Ω).map history).weight h =
      uniformAverage (fun ω : {ω // history ω = h} => X ω.val) := by
  obtain ⟨ω, hω⟩ := hne
  have hm : 0 < ((uniform Ω).map history).weight h := by
    rw [uniform_history_mass]
    letI : Nonempty {ω // history ω = h} := ⟨⟨ω, hω⟩⟩
    exact div_pos card_cast_pos card_cast_pos
  rw [uniform_mass_mul_fiber_average]
  exact mul_div_cancel_left₀ _ hm.ne'

/-- An actual equivalence of a transcript fiber with a reduced finite model
transports arbitrary statistics, including deficit drop and conditional loss.
The equivalence/statistic identification is NOT manufactured by this lemma. -/
theorem uniform_fiberContribution_equiv {B : Type*} [Fintype B]
    (history : Ω → H) (X : Ω → ℝ) (h : H)
    (e : {ω // history ω = h} ≃ B) (Y : B → ℝ)
    (hXY : ∀ ω : {ω // history ω = h}, X ω.val = Y (e ω)) :
    (uniform Ω).fiberContribution history X h =
      ((uniform Ω).map history).weight h * uniformAverage Y := by
  rw [uniform_mass_mul_fiber_average]
  apply congrArg (fun a => ((uniform Ω).map history).weight h * a)
  calc
    uniformAverage (fun ω : {ω // history ω = h} => X ω.val) =
        uniformAverage (fun ω => Y (e ω)) := by
          congr 1
          funext ω
          exact hXY ω
    _ = _ := uniformAverage_comp_equiv e Y

end FinitePMF

/-- Specialization to the EXISTING reachable-history law. Answer/query spaces
may be infinite; only the hidden instance type and the reduced model are finite. -/
theorem reachable_uniform_fiberContribution_equiv
    {Ω Query Answer Output B : Type} [Fintype Ω] [Nonempty Ω] [Fintype B]
    (strategy : DeterministicAdaptiveStrategy Query Answer Output)
    (oracle : Ω → Query → Answer) (t : ℕ) (h : ReachableHistory strategy oracle t)
    (X : Ω → ℝ) (Y : B → ℝ)
    (e : {ω // reachableHistoryOf strategy oracle t ω = h} ≃ B)
    (hXY : ∀ ω : {ω // reachableHistoryOf strategy oracle t ω = h}, X ω.val = Y (e ω)) :
    (FinitePMF.uniform Ω).fiberContribution (reachableHistoryOf strategy oracle t) X h =
      (reachableHistoryLaw strategy oracle (FinitePMF.uniform Ω) t).weight h * uniformAverage Y := by
  classical
  exact FinitePMF.uniform_fiberContribution_equiv (reachableHistoryOf strategy oracle t) X h e Y hXY

end Lemmata.DistributionalLowerBounds.Core.Distributional
