module

public import Lemmata.FrankWolfe.Statement
public import Lemmata.FrankWolfe.Proof.Hilbert

@[expose] public section

/-!
# Proofs of the statements

Each statement of `Statement.lean` from the lemmas of `Calculus.lean`, `Rate.lean` and
`Hilbert.lean`.
-/

namespace Lemmata.FrankWolfe

universe u

namespace Proof

theorem gap_inequalities : GapInequalities.{u} := by
  intro E _ _ C f hC hconv hdiff xStar hxs x hx
  refine ⟨?_, ?_⟩
  · have := add_fderiv_le_of_convexOn hconv hdiff x xStar
    rw [map_sub] at this ⊢
    linarith
  · refine le_csSup ?_ ⟨xStar, hxs.1, rfl⟩
    have hcont : Continuous fun v => fderiv ℝ f x (x - v) := by fun_prop
    exact (hC.image hcont).bddAbove

theorem descent_lemma : DescentLemma.{u} := by
  intro E _ _ f L h x y
  exact h.le_quadratic x y

theorem progress_lemma : ProgressLemma.{u} := by
  intro E _ _ f L h x v γ
  exact h.progress x v γ

theorem standard_rate : StandardRate.{u} := by
  intro E _ _ C lmo f L h σ hσ xStar hxs x₀ hx₀ t ht
  have hγ : ∀ t : ℕ, (2 / ((t : ℝ) + 2)) ∈ Set.Icc (0 : ℝ) 1 := fun t =>
    ⟨by positivity, by rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]⟩
  refine ⟨?_, ?_, ?_⟩
  · exact rate_of_dominated h (step := openLoopStep 2) (fun t _ _ => hγ t)
      (fun _ _ _ => Or.inl le_rfl) hxs hx₀ t ht
  · refine rate_of_dominated h (step := shortStep lmo (fderiv ℝ f) L) (fun t x hx => ?_)
      (fun t x hx => Or.inr (shortStep_le h hx (hγ t) t)) hxs hx₀ t ht
    have hg : 0 ≤ fderiv ℝ f x (x - lmo (fderiv ℝ f x)) := by
      have := (h.isLMO (fderiv ℝ f x)).2 x hx
      rw [map_sub]; linarith
    have hL : (0 : ℝ) ≤ L := L.2
    exact ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩
  · exact rate_of_dominated h (step := fun _ => σ) (fun _ x _ => (hσ x).1)
      (fun t x _ => Or.inl ((hσ x).2 _ (hγ t))) hxs hx₀ t ht

theorem standard_rate_hilbert : StandardRateHilbert.{u} := by
  intro E _ _ _ C lmo f L h σ hσ xStar hxs x₀ hx₀ t ht
  obtain ⟨h1, h2, h3⟩ := standard_rate C (dualLMO lmo) f L (hilbert_standingAssumptions h) σ
    ((hilbert_isExactLineSearch_iff lmo f σ).mp hσ) xStar hxs x₀ hx₀ t ht
  refine ⟨?_, ?_, ?_⟩
  · rw [hilbert_fwIterates_eq]; exact h1
  · rw [hilbert_fwIterates_eq, hilbert_shortStep_eq]; exact h2
  · rw [hilbert_fwIterates_eq]; exact h3

end Proof

end Lemmata.FrankWolfe
