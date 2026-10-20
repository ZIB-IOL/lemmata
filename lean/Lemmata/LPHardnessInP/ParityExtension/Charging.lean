module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Lemmata.LPHardnessInP.ParityExtension

open scoped BigOperators

variable {H : Type*}

/-- A good index is exceptional if it has no witness coming from another
good index, with any of the three pair choices. -/
noncomputable def exceptional (G : Finset H) (Rel : H → H → Fin 3 → Prop) : Finset H := by
  classical
  exact G.filter (fun b => ¬∃ a ∈ G, ∃ p, Rel a b p)

/-- The regular indices are the remaining good indices. -/
noncomputable def regular (G : Finset H) (Rel : H → H → Fin 3 → Prop) : Finset H := by
  classical
  exact G \ exceptional G Rel

/-- The combinatorial source hypothesis is hereditary: every sufficiently
large subfamily of the good indices has an internal witness. -/
def HereditaryWitness (G : Finset H) (Rel : H → H → Fin 3 → Prop) (K : ℕ) : Prop :=
  ∀ F : Finset H, F ⊆ G → K ≤ F.card →
    ∃ a ∈ F, ∃ b ∈ F, ∃ p, Rel a b p

theorem exceptional_subset (G : Finset H) (Rel : H → H → Fin 3 → Prop) :
    exceptional G Rel ⊆ G := by
  classical
  exact Finset.filter_subset _ _

/-- Applying the hereditary witness lemma to the exceptional subfamily
itself proves the strict exceptional-family bound. -/
theorem exceptional_card_lt (G : Finset H) (Rel : H → H → Fin 3 → Prop)
    {K : ℕ} (h : HereditaryWitness G Rel K) :
    (exceptional G Rel).card < K := by
  classical
  by_contra hn
  obtain ⟨a, ha, b, hb, p, hab⟩ :=
    h (exceptional G Rel) (exceptional_subset G Rel) (Nat.le_of_not_gt hn)
  have hb' := (Finset.mem_filter.mp hb).2
  exact hb' ⟨a, exceptional_subset G Rel ha, p, hab⟩

theorem regular_subset (G : Finset H) (Rel : H → H → Fin 3 → Prop) :
    regular G Rel ⊆ G := by
  classical
  exact Finset.sdiff_subset

theorem regular_has_pair (G : Finset H) (Rel : H → H → Fin 3 → Prop)
    {b : H} (hb : b ∈ regular G Rel) :
    ∃ p, ∃ a ∈ G, Rel a b p := by
  classical
  have hg : b ∈ G := regular_subset G Rel hb
  have he : b ∉ exceptional G Rel := (Finset.mem_sdiff.mp hb).2
  have hw : ∃ a ∈ G, ∃ p, Rel a b p := by
    by_contra hn
    exact he (Finset.mem_filter.mpr ⟨hg, hn⟩)
  obtain ⟨a, ha, p, hp⟩ := hw
  exact ⟨p, a, ha, hp⟩

/-- Select one pair choice for every regular index. -/
noncomputable def selectedPair (G : Finset H) (Rel : H → H → Fin 3 → Prop)
    (b : {b // b ∈ regular G Rel}) : Fin 3 :=
  Classical.choose (regular_has_pair G Rel b.property)

theorem selectedPair_has_witness (G : Finset H) (Rel : H → H → Fin 3 → Prop)
    (b : {b // b ∈ regular G Rel}) :
    ∃ a ∈ G, Rel a b.val (selectedPair G Rel b) :=
  Classical.choose_spec (regular_has_pair G Rel b.property)

/-- Distinct regular triples are charged to distinct sampling indices,
irrespective of how their witness pair is chosen. -/
theorem selected_sampling_indices_injective (G : Finset H)
    (Rel : H → H → Fin 3 → Prop) :
    Function.Injective
      (fun b : {b // b ∈ regular G Rel} => (b.val, selectedPair G Rel b)) := by
  intro a b hab
  exact Subtype.ext (congrArg Prod.fst hab)

/-- Separate row and column stability estimates imply the product estimate
for the rectangle probability. No aggregate charging inequality is assumed. -/
theorem product_probability_lower_bound
    {c row col newRow newCol : ℝ}
    (hc : 0 < c) (hrow : 0 ≤ row) (hcol : 0 ≤ col)
    (hnewRow : row / c ^ 2 ≤ newRow)
    (hnewCol : col / c ^ 2 ≤ newCol) :
    (row * col) / c ^ 4 ≤ newRow * newCol := by
  calc
    (row * col) / c ^ 4 = (row / c ^ 2) * (col / c ^ 2) := by
      field_simp
    _ ≤ newRow * newCol :=
      mul_le_mul hnewRow hnewCol (div_nonneg hcol (sq_nonneg c))
        ((div_nonneg hrow (sq_nonneg c)).trans hnewRow)

/-- The mass of an individual regular index is bounded by the sum of its
three one-violation sampling probabilities. -/
theorem regular_mass_le (G : Finset H) (Rel : H → H → Fin 3 → Prop)
    (g : H → ℝ) (nu : H → Fin 3 → ℝ) {c w : ℝ}
    (hc : 0 < c) (hnu : ∀ b p, 0 ≤ nu b p)
    (hgood : ∀ b ∈ G, g b ≤ c ^ 2 * w)
    (hwitness : ∀ a ∈ G, ∀ b ∈ G, ∀ p, Rel a b p → w / c ^ 4 ≤ nu b p)
    {b : H} (hb : b ∈ regular G Rel) :
    g b ≤ c ^ 6 * ∑ p, nu b p := by
  obtain ⟨p, a, ha, hp⟩ := regular_has_pair G Rel hb
  have hprob := hwitness a ha b (regular_subset G Rel hb) p hp
  have hw : w ≤ nu b p * c ^ 4 := (div_le_iff₀ (pow_pos hc 4)).mp hprob
  have hterm : nu b p ≤ ∑ q, nu b q :=
    Finset.single_le_sum (fun q _ => hnu b q) (Finset.mem_univ p)
  calc
    g b ≤ c ^ 2 * w := hgood b (regular_subset G Rel hb)
    _ ≤ c ^ 2 * (nu b p * c ^ 4) := mul_le_mul_of_nonneg_left hw (sq_nonneg c)
    _ = c ^ 6 * nu b p := by ring
    _ ≤ c ^ 6 * ∑ p, nu b p :=
      mul_le_mul_of_nonneg_left hterm (pow_nonneg hc.le 6)

/-- The finite charging bound before normalizing the sampling measures. -/
theorem good_mass_bound [Fintype H] (G : Finset H) (Rel : H → H → Fin 3 → Prop)
    (g : H → ℝ) (nu : H → Fin 3 → ℝ) {K : ℕ} {c w : ℝ}
    (hhereditary : HereditaryWitness G Rel K)
    (hc : 0 < c) (hw : 0 ≤ w) (hnu : ∀ b p, 0 ≤ nu b p)
    (hgood : ∀ b ∈ G, g b ≤ c ^ 2 * w)
    (hwitness : ∀ a ∈ G, ∀ b ∈ G, ∀ p, Rel a b p → w / c ^ 4 ≤ nu b p) :
    (∑ b ∈ G, g b) ≤ (K : ℝ) * c ^ 2 * w + c ^ 6 * ∑ b, ∑ p, nu b p := by
  classical
  have hex : (∑ b ∈ exceptional G Rel, g b) ≤ (K : ℝ) * c ^ 2 * w := by
    calc
      (∑ b ∈ exceptional G Rel, g b) ≤
          ∑ _b ∈ exceptional G Rel, c ^ 2 * w :=
        Finset.sum_le_sum (fun b hb => hgood b (exceptional_subset G Rel hb))
      _ = ((exceptional G Rel).card : ℝ) * (c ^ 2 * w) := by simp
      _ ≤ (K : ℝ) * (c ^ 2 * w) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (sq_nonneg c) hw)
        exact_mod_cast (Nat.le_of_lt (exceptional_card_lt G Rel hhereditary))
      _ = (K : ℝ) * c ^ 2 * w := by ring
  have hreg : (∑ b ∈ regular G Rel, g b) ≤ c ^ 6 * ∑ b, ∑ p, nu b p := by
    calc
      (∑ b ∈ regular G Rel, g b) ≤ ∑ b ∈ regular G Rel, c ^ 6 * ∑ p, nu b p :=
        Finset.sum_le_sum (fun b hb => regular_mass_le G Rel g nu hc hnu hgood hwitness hb)
      _ = c ^ 6 * ∑ b ∈ regular G Rel, ∑ p, nu b p := by rw [Finset.mul_sum]
      _ ≤ c ^ 6 * ∑ b, ∑ p, nu b p := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hc.le 6)
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro b _ _
        exact Finset.sum_nonneg (fun p _ => hnu b p)
  have hsplit : (∑ b ∈ regular G Rel, g b) + (∑ b ∈ exceptional G Rel, g b) =
      ∑ b ∈ G, g b := by
    exact Finset.sum_sdiff (exceptional_subset G Rel)
  linarith

/-- Uniform sampling of triples and their three pair choices gives the
coefficient `3 * c^6`. The exceptional term has coefficient `K*c^2/P`. -/
theorem normalized_good_mass_bound [Fintype H] [Nonempty H]
    (G : Finset H) (Rel : H → H → Fin 3 → Prop)
    (g : H → ℝ) (nu : H → Fin 3 → ℝ) {K : ℕ} {c w : ℝ}
    (hhereditary : HereditaryWitness G Rel K)
    (hc : 0 < c) (hw : 0 ≤ w) (hnu : ∀ b p, 0 ≤ nu b p)
    (hgood : ∀ b ∈ G, g b ≤ c ^ 2 * w)
    (hwitness : ∀ a ∈ G, ∀ b ∈ G, ∀ p, Rel a b p → w / c ^ 4 ≤ nu b p) :
    (∑ b ∈ G, g b) / (Fintype.card H : ℝ) ≤
      ((K : ℝ) * c ^ 2 / (Fintype.card H : ℝ)) * w +
        3 * c ^ 6 * ((∑ b, ∑ p, nu b p) / (3 * (Fintype.card H : ℝ))) := by
  have hP : (0 : ℝ) < (Fintype.card H : ℝ) := by exact_mod_cast Fintype.card_pos
  calc
    (∑ b ∈ G, g b) / (Fintype.card H : ℝ) ≤
        ((K : ℝ) * c ^ 2 * w + c ^ 6 * ∑ b, ∑ p, nu b p) /
          (Fintype.card H : ℝ) :=
      div_le_div_of_nonneg_right
        (good_mass_bound G Rel g nu hhereditary hc hw hnu hgood hwitness) hP.le
    _ = _ := by field_simp

/-- Averaging pointwise bounds with nonnegative weights preserves the exact
coefficients of the high- and one-violation terms. -/
theorem average_good_mass_bound {Ω : Type*} [Fintype Ω]
    (weight good high one : Ω → ℝ) {A B : ℝ}
    (hweight : ∀ omega, 0 ≤ weight omega)
    (hlocal : ∀ omega, good omega ≤ A * high omega + B * one omega) :
    (∑ omega, weight omega * good omega) ≤
      A * (∑ omega, weight omega * high omega) +
        B * (∑ omega, weight omega * one omega) := by
  calc
    (∑ omega, weight omega * good omega) ≤
        ∑ omega, weight omega * (A * high omega + B * one omega) :=
      Finset.sum_le_sum (fun omega _ => mul_le_mul_of_nonneg_left (hlocal omega) (hweight omega))
    _ = ∑ omega, (A * (weight omega * high omega) +
        B * (weight omega * one omega)) := by
      apply Finset.sum_congr rfl
      intro omega _
      ring
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The small- and bad-triple estimates are absorbed only after the new
good-triple charging inequality has been averaged. -/
theorem rectangle_bound_of_averaged_charging {Ω : Type*} [Fintype Ω]
    (weight good high one : Ω → ℝ)
    {K p c epsilon muThree muHigh nuOne small bad smallError badError : ℝ}
    (hweight : ∀ omega, 0 ≤ weight omega)
    (hp : 0 < p) (hepsilon : epsilon < 1)
    (hlocal : ∀ omega,
      good omega ≤ (K * c ^ 2 / p) * high omega + 3 * c ^ 6 * one omega)
    (hhigh : (∑ omega, weight omega * high omega) = muHigh)
    (hone : (∑ omega, weight omega * one omega) = nuOne)
    (hcover : muThree ≤ (∑ omega, weight omega * good omega) + small + bad)
    (hsmall : small ≤ smallError)
    (hbad : bad ≤ epsilon * muThree + badError) :
    muThree ≤
      (K * c ^ 2 / ((1 - epsilon) * p)) * muHigh +
        (3 * c ^ 6 / (1 - epsilon)) * nuOne +
          (smallError + badError) / (1 - epsilon) := by
  have hgood := average_good_mass_bound weight good high one hweight hlocal
  rw [hhigh, hone] at hgood
  have hden : 0 < 1 - epsilon := by linarith
  have habsorb :
      (1 - epsilon) * muThree ≤
        (K * c ^ 2 / p) * muHigh + 3 * c ^ 6 * nuOne + smallError + badError := by
    linarith
  have hdiv : muThree ≤
      ((K * c ^ 2 / p) * muHigh + 3 * c ^ 6 * nuOne + smallError + badError) /
        (1 - epsilon) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [habsorb]
  calc
    muThree ≤ ((K * c ^ 2 / p) * muHigh + 3 * c ^ 6 * nuOne +
        smallError + badError) / (1 - epsilon) := hdiv
    _ = _ := by field_simp; ring

/-- End-to-end finite corruption inequality from the hereditary source
lemma, pointwise stability comparisons, sampling identities, and the
small/bad estimates. The good-triple charging bound is a conclusion of the
proof, not a supplied hypothesis. -/
theorem finite_corruption_bound_of_source_estimates
    {Ω : Type*} [Fintype Ω] [Fintype H] [Nonempty H]
    (weight : Ω → ℝ) (G : Ω → Finset H)
    (Rel : Ω → H → H → Fin 3 → Prop)
    (g : Ω → H → ℝ) (nu : Ω → H → Fin 3 → ℝ) (w : Ω → ℝ)
    {K : ℕ} {c epsilon muThree muHigh nuOne small bad smallError badError : ℝ}
    (hweight : ∀ omega, 0 ≤ weight omega)
    (hhereditary : ∀ omega, HereditaryWitness (G omega) (Rel omega) K)
    (hc : 0 < c) (hepsilon : epsilon < 1)
    (hw : ∀ omega, 0 ≤ w omega)
    (hnu : ∀ omega b p, 0 ≤ nu omega b p)
    (hgood : ∀ omega b, b ∈ G omega → g omega b ≤ c ^ 2 * w omega)
    (hwitness : ∀ omega a, a ∈ G omega → ∀ b, b ∈ G omega →
      ∀ p, Rel omega a b p → w omega / c ^ 4 ≤ nu omega b p)
    (hhigh : (∑ omega, weight omega * w omega) = muHigh)
    (hone : (∑ omega, weight omega *
      ((∑ b, ∑ p, nu omega b p) / (3 * (Fintype.card H : ℝ)))) = nuOne)
    (hcover : muThree ≤
      (∑ omega, weight omega *
        ((∑ b ∈ G omega, g omega b) / (Fintype.card H : ℝ))) + small + bad)
    (hsmall : small ≤ smallError)
    (hbad : bad ≤ epsilon * muThree + badError) :
    muThree ≤
      ((K : ℝ) * c ^ 2 / ((1 - epsilon) * (Fintype.card H : ℝ))) * muHigh +
        (3 * c ^ 6 / (1 - epsilon)) * nuOne +
          (smallError + badError) / (1 - epsilon) := by
  have hP : (0 : ℝ) < (Fintype.card H : ℝ) := by exact_mod_cast Fintype.card_pos
  exact rectangle_bound_of_averaged_charging weight
    (fun omega => (∑ b ∈ G omega, g omega b) / (Fintype.card H : ℝ))
    w (fun omega => (∑ b, ∑ p, nu omega b p) / (3 * (Fintype.card H : ℝ)))
    hweight hP hepsilon
    (fun omega => normalized_good_mass_bound (G omega) (Rel omega) (g omega) (nu omega)
      (hhereditary omega) hc (hw omega) (hnu omega) (hgood omega) (hwitness omega))
    hhigh hone hcover hsmall hbad

end Lemmata.LPHardnessInP.ParityExtension
