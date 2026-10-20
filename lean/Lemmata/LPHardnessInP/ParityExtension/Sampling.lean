module

public import Lemmata.LPHardnessInP.ParityExtension.Core
public import Lemmata.LPHardnessInP.ParityExtension.Witness

@[expose] public section

namespace Lemmata.LPHardnessInP.ParityExtension

open scoped BigOperators
open Lemmata.LPHardnessInP.Parity

variable {Ω I J : Type*} [Fintype Ω] [Fintype I] [Fintype J]

/-- Push a finite probability distribution through two maps. A sample need
not be determined by the pair to which it is sent. -/
noncomputable def sampleProbability (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (htotal : ∑ ω, w ω = 1) (row : Ω → I) (col : Ω → J) :
    ProbabilityMatrix I J := by
  classical
  refine {
    mass := fun i j => ∑ ω, if i = row ω then (if j = col ω then w ω else 0) else 0
    nonneg := ?_
    total := ?_
  }
  · intro i j
    apply Finset.sum_nonneg
    intro ω _
    split_ifs <;> first | exact hw ω | exact le_refl 0
  · calc
      (∑ i, ∑ j, ∑ ω, if i = row ω then (if j = col ω then w ω else 0) else 0) =
          ∑ i, ∑ ω, ∑ j, if i = row ω then (if j = col ω then w ω else 0) else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_comm]
      _ = ∑ ω, ∑ i, ∑ j, if i = row ω then (if j = col ω then w ω else 0) else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ ω, w ω := by
            apply Finset.sum_congr rfl
            intro ω _
            simp
      _ = 1 := htotal

theorem sampleProbability_mass [DecidableEq I] [DecidableEq J]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (htotal : ∑ ω, w ω = 1) (row : Ω → I) (col : Ω → J) (i : I) (j : J) :
    (sampleProbability w hw htotal row col).mass i j =
      ∑ ω, if i = row ω ∧ j = col ω then w ω else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp_all

/-- If every sample has a specified statistic, so does every pair of
positive mass in its pushforward. -/
theorem sampleProbability_supported (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (htotal : ∑ ω, w ω = 1) (row : Ω → I) (col : Ω → J)
    (t : I → J → ℝ) (a : ℝ) (hs : ∀ ω, t (row ω) (col ω) = a) :
    SupportedAt (sampleProbability w hw htotal row col) t a := by
  classical
  intro i j hmass
  by_contra hne
  apply hmass
  apply Finset.sum_eq_zero
  intro ω _
  split_ifs with hi hj
  · exact False.elim (hne (by rw [hi, hj]; exact hs ω))
  · rfl
  · rfl

/-- Rectangle mass is exactly the total weight of samples whose images
belong to the rectangle. This identity retains collisions between samples. -/
theorem sampleProbability_rectangleMass [DecidableEq I] [DecidableEq J]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (htotal : ∑ ω, w ω = 1) (row : Ω → I) (col : Ω → J)
    (R : Finset I) (C : Finset J) :
    rectangleMass (sampleProbability w hw htotal row col) R C =
      ∑ ω, if row ω ∈ R ∧ col ω ∈ C then w ω else 0 := by
  classical
  have hmass : ∀ i j, (sampleProbability w hw htotal row col).mass i j =
      ∑ ω, if i = row ω then (if j = col ω then w ω else 0) else 0 := by
    intro i j
    rw [sampleProbability_mass]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> simp_all
  unfold rectangleMass
  simp_rw [hmass]
  calc
    _ = ∑ i ∈ R, ∑ ω, ∑ j ∈ C,
        if i = row ω then (if j = col ω then w ω else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
    _ = ∑ ω, ∑ i ∈ R, ∑ j ∈ C,
        if i = row ω then (if j = col ω then w ω else 0) else 0 := by
          rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hr : row ω ∈ R <;> by_cases hc : col ω ∈ C <;> simp [hr, hc]

/-- Weighted samples of the new core construction define a probability
matrix on actual admissible labelings and actual odd-red matchings. -/
noncomputable def coreProbability {h : ℕ} (hodd : Odd h)
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (htotal : ∑ ω, w ω = 1)
    (H' : Ω → Finset (Fin h)) (hcard : ∀ ω, (H' ω).card = 3)
    (i j : Ω → Fin h) (hij : ∀ ω, i ω ≠ j ω) :
    ProbabilityMatrix (ParityLabel h) (ParityMatching h) :=
  sampleProbability w hw htotal
    (fun ω => coreLabel hodd (H' ω) (hcard ω))
    (fun ω => coreMatching hodd (i ω) (j ω) (hij ω))

-- DOCS_BEGIN_MAIN
/-- The distribution used to charge good triples is supported at exactly
one violation because of the proved core swap, not an assumed support
property. The weights may depend on the surrounding sample. -/
theorem coreProbability_supported {h : ℕ} (hodd : Odd h)
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (htotal : ∑ ω, w ω = 1)
    (H' : Ω → Finset (Fin h)) (hcard : ∀ ω, (H' ω).card = 3)
    (i j : Ω → Fin h) (hij : ∀ ω, i ω ≠ j ω)
    (hi : ∀ ω, i ω ∈ H' ω) (hj : ∀ ω, j ω ∈ H' ω) :
    SupportedAt (coreProbability hodd w hw htotal H' hcard i j hij)
      (fun L M => (violationCount L M : ℝ)) 1 := by
  apply sampleProbability_supported
  intro ω
  rw [core_violationCount hodd (H' ω) (hcard ω) (i ω) (j ω) (hij ω) (hi ω) (hj ω)]
  norm_num

/-- Completion maps may add an outside part to each core sample. If that
part preserves the violation count, the resulting distribution on the full
graph is again supported at one. This is the interface for the old outside
partition construction. -/
theorem completed_coreProbability_supported {h n : ℕ} (hodd : Odd h)
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (htotal : ∑ ω, w ω = 1)
    (H' : Ω → Finset (Fin h)) (hcard : ∀ ω, (H' ω).card = 3)
    (i j : Ω → Fin h) (hij : ∀ ω, i ω ≠ j ω)
    (hi : ∀ ω, i ω ∈ H' ω) (hj : ∀ ω, j ω ∈ H' ω)
    (row : Ω → ParityLabel n) (col : Ω → ParityMatching n)
    (hcompletion : ∀ ω, violationCount (row ω) (col ω) =
      violationCount (coreLabel hodd (H' ω) (hcard ω))
        (coreMatching hodd (i ω) (j ω) (hij ω))) :
    SupportedAt (sampleProbability w hw htotal row col)
      (fun L M => (violationCount L M : ℝ)) 1 := by
  apply sampleProbability_supported
  intro ω
  rw [hcompletion ω,
    core_violationCount hodd (H' ω) (hcard ω) (i ω) (j ω) (hij ω) (hi ω) (hj ω)]
  norm_num
-- DOCS_END_MAIN

end Lemmata.LPHardnessInP.ParityExtension
