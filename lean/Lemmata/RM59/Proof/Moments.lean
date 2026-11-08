module

public import Lemmata.RM59.Proof.Model
public meta import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Lemmata.RM59

open scoped BigOperators

def interpolationCoefficient {m : ℕ} (f : BooleanFunction m) : ANF m :=
  fun s => ∑ x, f x * ∏ i ∈ sᶜ, (1 + x i)

theorem interpolationCoefficient_eq_sum_moments {m : ℕ} (f : BooleanFunction m)
    (s : Finset (Fin m)) :
    interpolationCoefficient f s = ∑ a ∈ sᶜ.powerset, moment f a := by
  classical
  simp only [interpolationCoefficient, Finset.prod_one_add, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [moment, monomial_eq_prod]

private theorem interpolation_kernel {m : ℕ} (x y : Point m) :
    (∏ i, (y i + (1 + x i))) = if x = y then 1 else 0 := by
  classical
  by_cases h : x = y
  · subst y
    rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro i hi
    rw [add_left_comm, field_add_self, add_zero]
  · rw [if_neg h]
    have hcoordinate : ∃ i, x i ≠ y i := by
      by_contra hn
      apply h
      funext i
      by_contra hi
      exact hn ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hcoordinate
    apply Finset.prod_eq_zero (i := i) (Finset.mem_univ i)
    rcases field_eq_zero_or_one (x i) with hx | hx <;>
      rcases field_eq_zero_or_one (y i) with hy | hy <;> simp_all

theorem evaluate_interpolation {m : ℕ} (f : BooleanFunction m) :
    evaluate (interpolationCoefficient f) = f := by
  classical
  funext y
  calc
    evaluate (interpolationCoefficient f) y =
        ∑ x, f x * ∑ s, monomial s y * ∏ i ∈ sᶜ, (1 + x i) := by
      simp only [evaluate_eq_sum, interpolationCoefficient, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ = ∑ x, f x * ∏ i, (y i + (1 + x i)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Fintype.prod_add]
      simp only [monomial_eq_prod]
    _ = f y := by
      simp [interpolation_kernel, mul_ite]

theorem zero_moments_mem_reedMuller {m r d : ℕ} (f : BooleanFunction m)
    (hm : m ≤ r + d + 1)
    (hf : ∀ s, s.card ≤ d → moment f s = 0) : f ∈ reedMuller m r := by
  classical
  apply Lemmata.CocubicCovering.Covering.mem_reedMuller_iff.mpr
  refine ⟨interpolationCoefficient f, ?_, evaluate_interpolation f⟩
  intro s hs
  rw [interpolationCoefficient_eq_sum_moments]
  apply Finset.sum_eq_zero
  intro a ha
  apply hf
  have hsub := Finset.mem_powerset.mp ha
  have hcard := Finset.card_le_card hsub
  have hcompl := Finset.card_compl_add_card s
  simp only [Fintype.card_fin] at hcompl
  omega

theorem zero_cubic_moments_mem_rm59 (f : BooleanFunction 9)
    (hf : ∀ s, s.card ≤ 3 → moment f s = 0) : f ∈ reedMuller 9 5 :=
  zero_moments_mem_reedMuller f (by decide) hf

theorem equal_cubic_moments_mem_rm59 {f g : BooleanFunction 9}
    (h : ∀ s, s.card ≤ 3 → moment f s = moment g s) :
    f + g ∈ reedMuller 9 5 := by
  apply zero_cubic_moments_mem_rm59
  intro s hs
  rw [moment_add, h s hs, field_add_self]

theorem match_support_moments_mem_rm59 {P Q : Finset (Point 9)}
    (h : MatchSupportMoments 3 P Q) :
    indicator P + indicator Q ∈ reedMuller 9 5 := by
  apply equal_cubic_moments_mem_rm59
  intro s hs
  simpa only [moment_indicator] using h s hs

end Lemmata.RM59
