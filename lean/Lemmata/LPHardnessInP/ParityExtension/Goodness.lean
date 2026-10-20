module

public import Lemmata.LPHardnessInP.ParityExtension.Core
public import Lemmata.LPHardnessInP.ParityExtension.Extension

@[expose] public section

namespace Lemmata.LPHardnessInP.ParityExtension

open Lemmata.LPHardnessInP.Parity

/-- A permitted matching completion preserves the canonical red identity
on the witness core and is consistent with the fixed labeling elsewhere. -/
def PermittedMatching {h : ℕ} (H : Finset (Fin h)) (L : ParityLabel h)
    (M : ParityMatching h) : Prop :=
  (∀ x ∈ H, M.perm x = x ∧ M.red x = true) ∧
    (∀ x, x ∉ H → ¬ Violates L x (M.perm x) (M.red x))

/-- A permitted labeling completion preserves the canonical labels on the
new core and is consistent with the fixed matching elsewhere. -/
def PermittedLabel {h : ℕ} (H' : Finset (Fin h)) (M : ParityMatching h)
    (L : ParityLabel h) : Prop :=
  (∀ x ∈ H', L.left x = true ∧ L.right x = false) ∧
    (∀ x, x ∉ H' → ¬ Violates L x (M.perm x) (M.red x))

/-- The old multiplicative goodness comparison, stated for every permitted
completion. The sampling probabilities and the fact that a triple is good
are inputs; admissibility of the new completions is proved below. -/
def GoodCompletionComparison {T : Type*} (permitted : T → Prop)
    (probability : T → ℝ) (canonical c : ℝ) : Prop :=
  ∀ x, permitted x →
    canonical ≤ c * probability x ∧ probability x ≤ c * canonical

theorem coreMatching_permitted {h : ℕ} (hodd : Odd h)
    (i j : Fin h) (hij : i ≠ j) (L : ParityLabel h)
    (H : Finset (Fin h)) (hi : i ∉ H) (hj : j ∉ H)
    (hequal : ∀ x, x ∉ H → L.left x = L.right x)
    (hopposite : L.left i ≠ L.left j) :
    PermittedMatching H L (coreMatching hodd i j hij) :=
  ⟨coreMatching_agrees_on hodd i j hij H hi hj,
    coreMatching_consistent_off hodd i j hij L H hi hj hequal hopposite⟩

theorem coreLabel_permitted {h : ℕ} (hodd : Odd h)
    (H' : Finset (Fin h)) (hcard : H'.card = 3) (M : ParityMatching h)
    (hred : ∀ x, x ∉ H' → M.red x = true)
    (hperm : ∀ x, x ∉ H' → M.perm x ∉ H') :
    PermittedLabel H' M (coreLabel hodd H' hcard) :=
  ⟨fun x hx => coreLabel_on hodd H' hcard x hx,
    coreLabel_consistent_off hodd H' hcard M hred hperm⟩

-- DOCS_BEGIN_MAIN
/-- Apply the old good-completion comparison to the new matching. Its
agreement and consistency requirements follow from the actual core swap. -/
theorem coreMatching_replacement_bound {h : ℕ} (hodd : Odd h)
    (i j : Fin h) (hij : i ≠ j) (L : ParityLabel h)
    (H : Finset (Fin h)) (hi : i ∉ H) (hj : j ∉ H)
    (hequal : ∀ x, x ∉ H → L.left x = L.right x)
    (hopposite : L.left i ≠ L.left j)
    (probability : ParityMatching h → ℝ) (canonical c : ℝ)
    (hgood : GoodCompletionComparison (PermittedMatching H L) probability canonical c) :
    canonical ≤ c * probability (coreMatching hodd i j hij) :=
  (hgood _ (coreMatching_permitted hodd i j hij L H hi hj hequal hopposite)).1

/-- Apply the old comparison to the new labeling, using the proved
canonical labels and consistency with an arbitrary red complement. -/
theorem coreLabel_replacement_bound {h : ℕ} (hodd : Odd h)
    (H' : Finset (Fin h)) (hcard : H'.card = 3) (M : ParityMatching h)
    (hred : ∀ x, x ∉ H' → M.red x = true)
    (hperm : ∀ x, x ∉ H' → M.perm x ∉ H')
    (probability : ParityLabel h → ℝ) (canonical c : ℝ)
    (hgood : GoodCompletionComparison (PermittedLabel H' M) probability canonical c) :
    canonical ≤ c * probability (coreLabel hodd H' hcard) :=
  (hgood _ (coreLabel_permitted hodd H' hcard M hred hperm)).1

/-- The row completion loses at most the square of the goodness factor:
one comparison to the canonical completion and one to the new matching. -/
theorem coreMatching_squared_comparison {h : ℕ} (hodd : Odd h)
    (i j : Fin h) (hij : i ≠ j) (L : ParityLabel h)
    (H : Finset (Fin h)) (hi : i ∉ H) (hj : j ∉ H)
    (hequal : ∀ x, x ∉ H → L.left x = L.right x)
    (hopposite : L.left i ≠ L.left j)
    (probability : ParityMatching h → ℝ) (high canonical c : ℝ) (hc : 0 < c)
    (hhigh : high ≤ c * canonical)
    (hgood : GoodCompletionComparison (PermittedMatching H L) probability canonical c) :
    high / c ^ 2 ≤ probability (coreMatching hodd i j hij) :=
  replacement_lower_bound hc hhigh
    (coreMatching_replacement_bound hodd i j hij L H hi hj hequal hopposite
      probability canonical c hgood)

/-- The corresponding squared-factor comparison for the new labeling. -/
theorem coreLabel_squared_comparison {h : ℕ} (hodd : Odd h)
    (H' : Finset (Fin h)) (hcard : H'.card = 3) (M : ParityMatching h)
    (hred : ∀ x, x ∉ H' → M.red x = true)
    (hperm : ∀ x, x ∉ H' → M.perm x ∉ H')
    (probability : ParityLabel h → ℝ) (high canonical c : ℝ) (hc : 0 < c)
    (hhigh : high ≤ c * canonical)
    (hgood : GoodCompletionComparison (PermittedLabel H' M) probability canonical c) :
    high / c ^ 2 ≤ probability (coreLabel hodd H' hcard) :=
  replacement_lower_bound hc hhigh
    (coreLabel_replacement_bound hodd H' hcard M hred hperm probability canonical c hgood)

/-- The new matching and labeling have product probability at least the
high-core product divided by the fourth power of the goodness factor.
Only the old generic comparisons are inputs; the two new replacements are
admissible by the core lemmas. -/
theorem core_replacement_product_lower_bound {h : ℕ} (hodd : Odd h)
    (i j : Fin h) (hij : i ≠ j) (L : ParityLabel h)
    (H : Finset (Fin h)) (hi : i ∉ H) (hj : j ∉ H)
    (hequal : ∀ x, x ∉ H → L.left x = L.right x)
    (hopposite : L.left i ≠ L.left j)
    (H' : Finset (Fin h)) (hcard : H'.card = 3) (M : ParityMatching h)
    (hred : ∀ x, x ∉ H' → M.red x = true)
    (hperm : ∀ x, x ∉ H' → M.perm x ∉ H')
    (rowProbability : ParityMatching h → ℝ) (colProbability : ParityLabel h → ℝ)
    (highRow highCol canonicalRow canonicalCol c : ℝ) (hc : 0 < c)
    (hhighRow_nonneg : 0 ≤ highRow) (hhighCol_nonneg : 0 ≤ highCol)
    (hhighRow : highRow ≤ c * canonicalRow) (hhighCol : highCol ≤ c * canonicalCol)
    (hrowgood : GoodCompletionComparison (PermittedMatching H L)
      rowProbability canonicalRow c)
    (hcolgood : GoodCompletionComparison (PermittedLabel H' M)
      colProbability canonicalCol c) :
    highRow * highCol / c ^ 4 ≤
      rowProbability (coreMatching hodd i j hij) * colProbability (coreLabel hodd H' hcard) := by
  apply product_probability_lower_bound hc hhighRow_nonneg hhighCol_nonneg
  · exact coreMatching_squared_comparison hodd i j hij L H hi hj hequal hopposite
      rowProbability highRow canonicalRow c hc hhighRow hrowgood
  · exact coreLabel_squared_comparison hodd H' hcard M hred hperm
      colProbability highCol canonicalCol c hc hhighCol hcolgood
-- DOCS_END_MAIN

end Lemmata.LPHardnessInP.ParityExtension
