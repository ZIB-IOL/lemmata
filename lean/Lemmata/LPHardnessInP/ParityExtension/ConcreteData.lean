module

public import Lemmata.LPHardnessInP.ParityExtension.Goodness

@[expose] public section

namespace Lemmata.LPHardnessInP.ParityExtension

open scoped BigOperators
open Lemmata.LPHardnessInP.Parity

/-- The old partition and goodness data, expressed using actual colored
matchings and vertex labelings. New-completion probability comparisons are
not fields: they follow from the generic goodness laws and core geometry. -/
structure ConcreteCompletions (H Ω : Type*) [DecidableEq H]
    (h : ℕ) (epsilon : ℝ) where
  odd_core : Odd h
  triple : H → Finset (Fin h)
  triple_card : ∀ b, (triple b).card = 3
  first : H → Fin 3 → Fin h
  second : H → Fin 3 → Fin h
  pair_distinct : ∀ b p, first b p ≠ second b p
  first_mem : ∀ b p, first b p ∈ triple b
  second_mem : ∀ b p, second b p ∈ triple b
  rowProbability : Ω → ParityMatching h → ℝ
  colProbability : Ω → ParityLabel h → ℝ
  rowProbability_nonneg : ∀ o M, 0 ≤ rowProbability o M
  colProbability_nonneg : ∀ o L, 0 ≤ colProbability o L
  canonicalMatching : Ω → H → ParityMatching h
  canonicalLabel : Ω → H → ParityLabel h
  highMatching : Ω → ParityMatching h
  highLabel : Ω → ParityLabel h
  matching_on : ∀ o b x, x ∈ triple b →
    (canonicalMatching o b).perm x = x ∧ (canonicalMatching o b).red x = true
  matching_red_off : ∀ o b x, x ∉ triple b → (canonicalMatching o b).red x = true
  matching_closed_off : ∀ o b x, x ∉ triple b →
    (canonicalMatching o b).perm x ∉ triple b
  label_on : ∀ o b x, x ∈ triple b →
    (canonicalLabel o b).left x = true ∧ (canonicalLabel o b).right x = false
  label_equal_off : ∀ o b x, x ∉ triple b →
    (canonicalLabel o b).left x = (canonicalLabel o b).right x
  good : Ω → Finset H
  relation : Ω → H → H → Fin 3 → Prop
  row_good : ∀ o b, b ∈ good o →
    GoodCompletionComparison (PermittedMatching (triple b) (canonicalLabel o b))
      (rowProbability o) (rowProbability o (canonicalMatching o b)) (1 + epsilon)
  col_good : ∀ o b, b ∈ good o →
    GoodCompletionComparison (PermittedLabel (triple b) (canonicalMatching o b))
      (colProbability o) (colProbability o (canonicalLabel o b)) (1 + epsilon)
  high_matching_permitted : ∀ o b, b ∈ good o →
    PermittedMatching (triple b) (canonicalLabel o b) (highMatching o)
  high_label_permitted : ∀ o b, b ∈ good o →
    PermittedLabel (triple b) (canonicalMatching o b) (highLabel o)
  first_outside : ∀ o a b p, relation o a b p → first b p ∉ triple a
  second_outside : ∀ o a b p, relation o a b p → second b p ∉ triple a
  opposite_labels : ∀ o a b p, relation o a b p →
    (canonicalLabel o a).left (first b p) ≠ (canonicalLabel o a).left (second b p)

namespace ConcreteCompletions

variable {H Ω : Type*} [DecidableEq H] {h : ℕ} {epsilon : ℝ}

/-- The new matching is the concrete two-edge core swap. -/
def newMatching (D : ConcreteCompletions H Ω h epsilon) (b : H) (p : Fin 3) :
    ParityMatching h :=
  coreMatching D.odd_core (D.first b p) (D.second b p) (D.pair_distinct b p)

/-- The new labeling is one everywhere except on the triple's right vertices. -/
def newLabel (D : ConcreteCompletions H Ω h epsilon) (b : H) : ParityLabel h :=
  coreLabel D.odd_core (D.triple b) (D.triple_card b)

def newRow (D : ConcreteCompletions H Ω h epsilon) (o : Ω) (b : H) (p : Fin 3) : ℝ :=
  D.rowProbability o (D.newMatching b p)

def newCol (D : ConcreteCompletions H Ω h epsilon) (o : Ω) (b : H) (_p : Fin 3) : ℝ :=
  D.colProbability o (D.newLabel b)

/-- Every new sampled core pair, including pairs not chosen by the charging
argument, has exactly one violation. -/
theorem new_violationCount (D : ConcreteCompletions H Ω h epsilon) (b : H) (p : Fin 3) :
    violationCount (D.newLabel b) (D.newMatching b p) = 1 :=
  core_violationCount D.odd_core (D.triple b) (D.triple_card b)
    (D.first b p) (D.second b p) (D.pair_distinct b p) (D.first_mem b p) (D.second_mem b p)

/-- Matching probability comparison obtained from generic old goodness
and the verified admissibility of the actual new matching. -/
theorem replacementRow (D : ConcreteCompletions H Ω h epsilon)
    (o : Ω) (a : H) (ha : a ∈ D.good o) (b : H) (p : Fin 3)
    (hab : D.relation o a b p) :
    D.rowProbability o (D.canonicalMatching o a) ≤ (1 + epsilon) * D.newRow o b p :=
  coreMatching_replacement_bound D.odd_core (D.first b p) (D.second b p)
    (D.pair_distinct b p) (D.canonicalLabel o a) (D.triple a)
    (D.first_outside o a b p hab) (D.second_outside o a b p hab)
    (D.label_equal_off o a) (D.opposite_labels o a b p hab)
    (D.rowProbability o) _ _ (D.row_good o a ha)

/-- Label probability comparison obtained from generic old goodness
and the verified admissibility of the actual new labeling. -/
theorem replacementCol (D : ConcreteCompletions H Ω h epsilon)
    (o : Ω) (b : H) (hb : b ∈ D.good o) (p : Fin 3) :
    D.colProbability o (D.canonicalLabel o b) ≤ (1 + epsilon) * D.newCol o b p :=
  coreLabel_replacement_bound D.odd_core (D.triple b) (D.triple_card b)
    (D.canonicalMatching o b) (D.matching_red_off o b) (D.matching_closed_off o b)
    (D.colProbability o) _ _ (D.col_good o b hb)

end ConcreteCompletions

/-- Concrete old source data together with explicit sampling identities
and the published small- and bad-family estimates. The new completions
are fixed by `ConcreteCompletions.newMatching` and `newLabel`; no
replacement-specific comparison or corruption inequality is assumed. -/
structure ConcreteJSYRectangleData (H Ω : Type*) [Fintype H] [DecidableEq H] [Fintype Ω]
    (h K : ℕ) (epsilon muThree muHigh nuOne smallError badError : ℝ) where
  completion : ConcreteCompletions H Ω h epsilon
  weight : Ω → ℝ
  weight_nonneg : ∀ o, 0 ≤ weight o
  hereditary : ∀ o, HereditaryWitness (completion.good o) (completion.relation o) K
  high_average : (∑ o, weight o *
    (completion.rowProbability o (completion.highMatching o) *
      completion.colProbability o (completion.highLabel o))) = muHigh
  one_average : (∑ o, weight o *
    ((∑ b, ∑ p, completion.newRow o b p * completion.newCol o b p) /
      (3 * (Fintype.card H : ℝ)))) = nuOne
  small : ℝ
  bad : ℝ
  cover : muThree ≤ (∑ o, weight o *
    ((∑ b ∈ completion.good o,
      completion.rowProbability o (completion.canonicalMatching o b) *
        completion.colProbability o (completion.canonicalLabel o b)) /
      (Fintype.card H : ℝ))) + small + bad
  small_bound : small ≤ smallError
  bad_bound : bad ≤ epsilon * muThree + badError

namespace ConcreteJSYRectangleData

variable {H Ω : Type*} [Fintype H] [DecidableEq H] [Fintype Ω]
    {h K : ℕ} {epsilon muThree muHigh nuOne smallError badError : ℝ}

/-- Construct the finite charging interface from actual matching and
labeling probabilities. Every comparison involving a new completion is
proved from the generic source goodness law. -/
def toJSYRectangleData
    (D : ConcreteJSYRectangleData H Ω h K epsilon muThree muHigh nuOne smallError badError) :
    JSYRectangleData H Ω K epsilon muThree muHigh nuOne smallError badError where
  weight := D.weight
  weight_nonneg := D.weight_nonneg
  good := D.completion.good
  relation := D.completion.relation
  hereditary := D.hereditary
  highRow := fun o => D.completion.rowProbability o (D.completion.highMatching o)
  highCol := fun o => D.completion.colProbability o (D.completion.highLabel o)
  row := fun o b => D.completion.rowProbability o (D.completion.canonicalMatching o b)
  col := fun o b => D.completion.colProbability o (D.completion.canonicalLabel o b)
  newRow := D.completion.newRow
  newCol := D.completion.newCol
  highRow_nonneg := fun o => D.completion.rowProbability_nonneg o _
  highCol_nonneg := fun o => D.completion.colProbability_nonneg o _
  row_nonneg := fun o _b => D.completion.rowProbability_nonneg o _
  col_nonneg := fun o _b => D.completion.colProbability_nonneg o _
  newRow_nonneg := fun o _b _p => D.completion.rowProbability_nonneg o _
  newCol_nonneg := fun o _b _p => D.completion.colProbability_nonneg o _
  row_upper := fun o b hb =>
    (D.completion.row_good o b hb _ (D.completion.high_matching_permitted o b hb)).1
  col_upper := fun o b hb =>
    (D.completion.col_good o b hb _ (D.completion.high_label_permitted o b hb)).1
  highRow_upper := fun o b hb =>
    (D.completion.row_good o b hb _ (D.completion.high_matching_permitted o b hb)).2
  highCol_upper := fun o b hb =>
    (D.completion.col_good o b hb _ (D.completion.high_label_permitted o b hb)).2
  replacementRow := fun o a ha b _hb p hab => D.completion.replacementRow o a ha b p hab
  replacementCol := fun o _a _ha b hb p _hab => D.completion.replacementCol o b hb p
  high_average := D.high_average
  one_average := D.one_average
  small := D.small
  bad := D.bad
  cover := D.cover
  small_bound := D.small_bound
  bad_bound := D.bad_bound

-- DOCS_BEGIN_MAIN
/-- The new finite corruption inequality from concrete colored matching
and labeling data. The only analytic assumptions are the generic old
goodness comparisons, the sampling identities and the small/bad estimates. -/
theorem corruption_bound [Nonempty H]
    (D : ConcreteJSYRectangleData H Ω h K epsilon muThree muHigh nuOne smallError badError)
    (he0 : 0 ≤ epsilon) (he1 : epsilon < 1) :
    muThree ≤
      ((K : ℝ) * (1 + epsilon) ^ 2 /
        ((1 - epsilon) * (Fintype.card H : ℝ))) * muHigh +
      (3 * (1 + epsilon) ^ 6 / (1 - epsilon)) * nuOne +
      (smallError + badError) / (1 - epsilon) :=
  D.toJSYRectangleData.corruption_bound he0 he1
-- DOCS_END_MAIN

end ConcreteJSYRectangleData

end Lemmata.LPHardnessInP.ParityExtension
