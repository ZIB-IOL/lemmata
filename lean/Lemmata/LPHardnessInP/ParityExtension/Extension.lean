module

public import Lemmata.LPHardnessInP.ParityExtension.Charging
public import Lemmata.LPHardnessInP.ParityExtension.Witness

@[expose] public section

namespace Lemmata.LPHardnessInP.ParityExtension

open scoped BigOperators
open Lemmata.SpanningTreeMinSplit

/-- The precise finite hypotheses used from the JSY partition framework
for one rectangle. The new good-triple charge is not a field.

`H` indexes triples, `Ω` indexes partitions, and `Fin 3` indexes the
three pairs of a triple. The comparison fields express the old goodness
condition applied to permitted completions. The concrete new completions
and their local consistency are proved in `Core`; the entropy estimates
and the existence of the partition/permutation data remain hypotheses. -/
structure JSYRectangleData (H Ω : Type*) [Fintype H] [DecidableEq H] [Fintype Ω]
    (K : ℕ) (epsilon muThree muHigh nuOne smallError badError : ℝ) where
  weight : Ω → ℝ
  weight_nonneg : ∀ o, 0 ≤ weight o
  good : Ω → Finset H
  relation : Ω → H → H → Fin 3 → Prop
  hereditary : ∀ o, HereditaryWitness (good o) (relation o) K
  highRow : Ω → ℝ
  highCol : Ω → ℝ
  row : Ω → H → ℝ
  col : Ω → H → ℝ
  newRow : Ω → H → Fin 3 → ℝ
  newCol : Ω → H → Fin 3 → ℝ
  highRow_nonneg : ∀ o, 0 ≤ highRow o
  highCol_nonneg : ∀ o, 0 ≤ highCol o
  row_nonneg : ∀ o a, 0 ≤ row o a
  col_nonneg : ∀ o a, 0 ≤ col o a
  newRow_nonneg : ∀ o a p, 0 ≤ newRow o a p
  newCol_nonneg : ∀ o a p, 0 ≤ newCol o a p
  row_upper : ∀ o a, a ∈ good o → row o a ≤ (1 + epsilon) * highRow o
  col_upper : ∀ o a, a ∈ good o → col o a ≤ (1 + epsilon) * highCol o
  highRow_upper : ∀ o a, a ∈ good o → highRow o ≤ (1 + epsilon) * row o a
  highCol_upper : ∀ o a, a ∈ good o → highCol o ≤ (1 + epsilon) * col o a
  replacementRow : ∀ o a, a ∈ good o → ∀ b, b ∈ good o → ∀ p,
    relation o a b p → row o a ≤ (1 + epsilon) * newRow o b p
  replacementCol : ∀ o a, a ∈ good o → ∀ b, b ∈ good o → ∀ p,
    relation o a b p → col o b ≤ (1 + epsilon) * newCol o b p
  high_average : (∑ o, weight o * (highRow o * highCol o)) = muHigh
  one_average : (∑ o, weight o *
    ((∑ b, ∑ p, newRow o b p * newCol o b p) / (3 * (Fintype.card H : ℝ)))) = nuOne
  small : ℝ
  bad : ℝ
  cover : muThree ≤ (∑ o, weight o *
    ((∑ b ∈ good o, row o b * col o b) / (Fintype.card H : ℝ))) + small + bad
  small_bound : small ≤ smallError
  bad_bound : bad ≤ epsilon * muThree + badError

/-- Two successive goodness comparisons give the squared-factor loss. -/
theorem replacement_lower_bound {c high canonical replacement : ℝ}
    (hc : 0 < c) (h₁ : high ≤ c * canonical) (h₂ : canonical ≤ c * replacement) :
    high / c ^ 2 ≤ replacement := by
  apply (div_le_iff₀ (pow_pos hc 2)).mpr
  have h := h₁.trans (mul_le_mul_of_nonneg_left h₂ hc.le)
  nlinarith

/-- The local one-violation probability estimate is derived from the
separate old goodness comparisons, not included among the hypotheses. -/
theorem JSYRectangleData.replacement_product_lower_bound
    {H Ω : Type*} [Fintype H] [DecidableEq H] [Fintype Ω]
    {K : ℕ} {epsilon muThree muHigh nuOne smallError badError : ℝ}
    (D : JSYRectangleData H Ω K epsilon muThree muHigh nuOne smallError badError)
    (hc : 0 < 1 + epsilon) (o : Ω) (a : H) (ha : a ∈ D.good o)
    (b : H) (hb : b ∈ D.good o) (p : Fin 3) (hab : D.relation o a b p) :
    (D.highRow o * D.highCol o) / (1 + epsilon) ^ 4 ≤
      D.newRow o b p * D.newCol o b p := by
  apply product_probability_lower_bound hc (D.highRow_nonneg o) (D.highCol_nonneg o)
  · exact replacement_lower_bound hc (D.highRow_upper o a ha)
      (D.replacementRow o a ha b hb p hab)
  · exact replacement_lower_bound hc (D.highCol_upper o b hb)
      (D.replacementCol o a ha b hb p hab)

-- DOCS_BEGIN_MAIN
/-- The new finite corruption inequality, derived from explicit JSY
sampling, permutation, goodness, and small/bad hypotheses. -/
theorem JSYRectangleData.corruption_bound
    {H Ω : Type*} [Fintype H] [DecidableEq H] [Nonempty H] [Fintype Ω]
    {K : ℕ} {epsilon muThree muHigh nuOne smallError badError : ℝ}
    (D : JSYRectangleData H Ω K epsilon muThree muHigh nuOne smallError badError)
    (he0 : 0 ≤ epsilon) (he1 : epsilon < 1) :
    muThree ≤
      ((K : ℝ) * (1 + epsilon) ^ 2 /
        ((1 - epsilon) * (Fintype.card H : ℝ))) * muHigh +
      (3 * (1 + epsilon) ^ 6 / (1 - epsilon)) * nuOne +
      (smallError + badError) / (1 - epsilon) := by
  have hc : 0 < 1 + epsilon := by linarith
  apply rectangle_bound_of_averaged_charging D.weight
    (fun o => (∑ b ∈ D.good o, D.row o b * D.col o b) / (Fintype.card H : ℝ))
    (fun o => D.highRow o * D.highCol o)
    (fun o => (∑ b, ∑ p, D.newRow o b p * D.newCol o b p) /
      (3 * (Fintype.card H : ℝ)))
    D.weight_nonneg (by exact_mod_cast Fintype.card_pos) he1
    ?_ D.high_average D.one_average D.cover D.small_bound D.bad_bound
  intro o
  apply normalized_good_mass_bound (D.good o) (D.relation o)
    (fun b => D.row o b * D.col o b)
    (fun b p => D.newRow o b p * D.newCol o b p)
    (D.hereditary o) hc
    (mul_nonneg (D.highRow_nonneg o) (D.highCol_nonneg o))
    (fun b p => mul_nonneg (D.newRow_nonneg o b p) (D.newCol_nonneg o b p))
  · intro b hb
    have h := mul_le_mul (D.row_upper o b hb) (D.col_upper o b hb)
      (D.col_nonneg o b) (mul_nonneg hc.le (D.highRow_nonneg o))
    nlinarith
  · intro a ha b hb p hab
    exact D.replacement_product_lower_bound hc o a ha b hb p hab

/-- End-to-end finite source-rank extension. The assumptions are stated
at the level of the JSY partition lemmas and finite probability data;
neither a corruption inequality nor a rank lower bound is assumed. -/
theorem shifted_rank_lower_bound_from_jsy
    {I J H Ω : Type*} [Fintype I] [Fintype J]
    [Fintype H] [DecidableEq H] [Nonempty H] [Fintype Ω]
    (μ₃ μₕ μ₁ : ProbabilityMatrix I J) (t : I → J → ℝ)
    {K L : ℕ} {epsilon smallError badError h U r : ℝ}
    (he0 : 0 ≤ epsilon) (he1 : epsilon < 1)
    (hs : 0 ≤ smallError) (hb : 0 ≤ badError)
    (h₃ : SupportedAt μ₃ t 3) (hₕ : SupportedAt μₕ t h) (h₁ : SupportedAt μ₁ t 1)
    (data : ∀ R : Finset I, ∀ C : Finset J,
      JSYRectangleData H Ω K epsilon
        (rectangleMass μ₃ R C) (rectangleMass μₕ R C) (rectangleMass μ₁ R C)
        smallError badError)
    (hU : 0 ≤ U) (hupper : ∀ i j, t i j - r ≤ U)
    (hgap : ((L : ℝ) - 1) * ((smallError + badError) / (1 - epsilon)) * U <
      (3 - r) -
        ((K : ℝ) * (1 + epsilon) ^ 2 /
          ((1 - epsilon) * (Fintype.card H : ℝ))) * (h - r) -
        (3 * (1 + epsilon) ^ 6 / (1 - epsilon)) * (1 - r)) :
    (L : ℕ∞) ≤ nonnegativeRank (fun i j => t i j - r) := by
  apply shifted_rank_lower_bound μ₃ μₕ μ₁ t h₃ hₕ h₁
    (fun R C => (data R C).corruption_bound he0 he1)
    (div_nonneg (add_nonneg hs hb) (by linarith)) hU hupper hgap
-- DOCS_END_MAIN

end Lemmata.LPHardnessInP.ParityExtension
