module

public import Lemmata.FrankWolfePS.Unique.Stability
public import Lemmata.FrankWolfePS.Lower.Family

@[expose] public section

/-!
# Why the vertices are jittered

Uniqueness of the minimizers alone does not remove the leak. Without jitter, the bulged body
over the regular simplex is symmetric in the hidden labels, and its unique lowest point lies
above the barycenter: its horizontal coordinates are `A / |I|` on the hidden set and `0`
elsewhere, so one vertical query reveals the whole hidden set.
-/

namespace Lemmata.FrankWolfePS.Unique
open Finset
open scoped BigOperators RealInnerProductSpace
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sq_barycenter_le {I : Finset ι} (hne : I.Nonempty) {w : ι → ℝ} (hw : Base I w) :
    sq (simplexBarycenter I) ≤ sq w := by
  have hc : 0 < (I.card : ℝ) := by exact_mod_cast card_pos.mpr hne
  have hb : sq (simplexBarycenter I) = 1 / I.card := by
    unfold sq
    change (∑ i, (if i ∈ I then 1 / (I.card : ℝ) else 0) ^ 2) = _
    simp_rw [ite_pow, zero_pow (by decide : 2 ≠ 0)]
    simp only [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
    field_simp
  have cs : (∑ i ∈ I, w i) ^ 2 ≤ I.card * ∑ i ∈ I, w i ^ 2 := sq_sum_le_card_mul_sum_sq
  rw [hw.2.2, one_pow] at cs
  have sub : ∑ i ∈ I, w i ^ 2 ≤ sq w :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => _root_.sq_nonneg _
  rw [hb, div_le_iff₀ hc]
  nlinarith

/-- **Symmetric bulging reveals the hidden set.** The lowest point of the unjittered bulged body
has horizontal coordinates `A / |I|` on `I` and `0` off `I`. -/
theorem symmetric_lowest_point {A s : ℝ} (hs : 0 < s) {I : Finset ι} (hne : I.Nonempty)
    {x : Ambient ι} (hx : MinAt (Body (baseV A) s I) vert x) (i : ι) :
    x (some i) = if i ∈ I then A / I.card else 0 := by
  obtain ⟨u, hu, rfl, fu⟩ := min_rep hs.le norm_vert hx
  have hval (w : ι → ℝ) (hw : Base I w) : loss (baseV A) s vert w = 1 + s * sq w := by
    rw [loss, base_center hw, inner_vert]; rfl
  have fb (t : ι → ℝ) (ht : Base I t) :
      loss (baseV A) s vert (simplexBarycenter I) ≤ loss (baseV A) s vert t := by
    rw [hval _ (barycenter_base hne), hval t ht]
    nlinarith [sq_barycenter_le hne ht]
  have e := weights_unique hs hu (barycenter_base hne) fu fb
  subst e
  have hv : (vert : Ambient ι) (some i) = 0 := rfl
  have hc : center (baseV A) (simplexBarycenter I) (some i) = A * simplexBarycenter I i := by
    rw [base_center (barycenter_base hne)]; rfl
  simp only [point, edge, PiLp.sub_apply, PiLp.smul_apply, hc, hv, smul_eq_mul, mul_zero,
    sub_zero]
  by_cases hi : i ∈ I <;> simp [simplexBarycenter, hi, div_eq_mul_inv]

end Lemmata.FrankWolfePS.Unique
