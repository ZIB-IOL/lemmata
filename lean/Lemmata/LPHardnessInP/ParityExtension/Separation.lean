module

public import Lemmata.LPHardnessInP.RankReduction.Main
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace Lemmata.LPHardnessInP.ParityExtension

open scoped BigOperators
open Lemmata.SpanningTreeMinSplit

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The finite pairing of a signed matrix with a real matrix. -/
def pairing (W S : I → J → ℝ) : ℝ :=
  ∑ i, ∑ j, W i j * S i j

/-- Every rectangle has signed weight at most `E`. -/
def RectangleBound (W : I → J → ℝ) (E : ℝ) : Prop :=
  ∀ A : Finset I, ∀ B : Finset J, (∑ i ∈ A, ∑ j ∈ B, W i j) ≤ E

/-- A linear functional on a finite unit cube is bounded by its value
at an indicator vector. The coefficients need not be nonnegative. -/
theorem exists_indicator_sum_ge {K : Type*} [Fintype K]
    (c x : K → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1) :
    ∃ A : Finset K, (∑ i, c i * x i) ≤ ∑ i ∈ A, c i := by
  classical
  refine ⟨Finset.univ.filter (fun i => 0 ≤ c i), ?_⟩
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i _
  by_cases hc : 0 ≤ c i
  · simpa [hc] using mul_le_mul_of_nonneg_left (hx1 i) hc
  · simpa [hc] using mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) (hx0 i)

/-- A rectangle bound also bounds the pairing with a rank-one matrix
whose two factors belong to the unit cube. -/
theorem pairing_unit_factors_le (W : I → J → ℝ) {E : ℝ}
    (hrect : RectangleBound W E) (a : I → ℝ) (b : J → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (hb0 : ∀ j, 0 ≤ b j) (hb1 : ∀ j, b j ≤ 1) :
    pairing W (fun i j => a i * b j) ≤ E := by
  obtain ⟨A, hA⟩ := exists_indicator_sum_ge (fun i => ∑ j, W i j * b j) a ha0 ha1
  obtain ⟨B, hB⟩ := exists_indicator_sum_ge (fun j => ∑ i ∈ A, W i j) b hb0 hb1
  calc
    pairing W (fun i j => a i * b j)
        = ∑ i, (∑ j, W i j * b j) * a i := by
          simp only [pairing, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ ≤ ∑ i ∈ A, ∑ j, W i j * b j := hA
    _ = ∑ j, (∑ i ∈ A, W i j) * b j := by
      simp only [Finset.sum_mul]
      exact Finset.sum_comm
    _ ≤ ∑ j ∈ B, ∑ i ∈ A, W i j := hB
    _ = ∑ i ∈ A, ∑ j ∈ B, W i j := Finset.sum_comm
    _ ≤ E := hrect A B

/-- Signed rectangle bounds control nonnegative rank-one matrices.
The statement also covers empty index sets and zero factors. -/
theorem pairing_rankOne_le (W : I → J → ℝ) {E U : ℝ}
    (hrect : RectangleBound W E) (hE : 0 ≤ E) (hU : 0 ≤ U)
    (a : I → ℝ) (b : J → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hupper : ∀ i j, a i * b j ≤ U) :
    pairing W (fun i j => a i * b j) ≤ E * U := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hI =>
      simpa [pairing] using mul_nonneg hE hU
  | inr hI =>
      cases isEmpty_or_nonempty J with
      | inl hJ =>
          simpa [pairing] using mul_nonneg hE hU
      | inr hJ =>
          obtain ⟨i₀, _, hi₀⟩ :=
            Finset.exists_max_image Finset.univ a Finset.univ_nonempty
          obtain ⟨j₀, _, hj₀⟩ :=
            Finset.exists_max_image Finset.univ b Finset.univ_nonempty
          by_cases haz : a i₀ = 0
          · have ha_zero : ∀ i, a i = 0 := fun i =>
              le_antisymm (by simpa [haz] using hi₀ i (Finset.mem_univ i)) (ha i)
            simpa [pairing, ha_zero] using mul_nonneg hE hU
          by_cases hbz : b j₀ = 0
          · have hb_zero : ∀ j, b j = 0 := fun j =>
              le_antisymm (by simpa [hbz] using hj₀ j (Finset.mem_univ j)) (hb j)
            simpa [pairing, hb_zero] using mul_nonneg hE hU
          have hap : 0 < a i₀ := lt_of_le_of_ne (ha i₀) (Ne.symm haz)
          have hbp : 0 < b j₀ := lt_of_le_of_ne (hb j₀) (Ne.symm hbz)
          have hunit := pairing_unit_factors_le W hrect
            (fun i => a i / a i₀) (fun j => b j / b j₀)
            (fun i => div_nonneg (ha i) hap.le)
            (fun i => (div_le_one hap).mpr (hi₀ i (Finset.mem_univ i)))
            (fun j => div_nonneg (hb j) hbp.le)
            (fun j => (div_le_one hbp).mpr (hj₀ j (Finset.mem_univ j)))
          have hscale :
              pairing W (fun i j => a i * b j) =
                (a i₀ * b j₀) *
                  pairing W (fun i j => (a i / a i₀) * (b j / b j₀)) := by
            simp only [pairing, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            field_simp
          calc
            pairing W (fun i j => a i * b j)
                = (a i₀ * b j₀) *
                    pairing W (fun i j => (a i / a i₀) * (b j / b j₀)) := hscale
            _ ≤ (a i₀ * b j₀) * E :=
              mul_le_mul_of_nonneg_left hunit (mul_nonneg hap.le hbp.le)
            _ = E * (a i₀ * b j₀) := mul_comm _ _
            _ ≤ E * U := mul_le_mul_of_nonneg_left (hupper i₀ j₀) hE

-- DOCS_BEGIN_MAIN
/-- A signed rectangle bound yields a lower-bound certificate against
every nonnegative factorization. No nonempty-index assumption is needed. -/
theorem pairing_factorization_le {W S : I → J → ℝ} {k : ℕ} {E U : ℝ}
    (F : NonnegativeFactorization S k)
    (hupper : ∀ i j, S i j ≤ U) (hE : 0 ≤ E) (hU : 0 ≤ U)
    (hrect : RectangleBound W E) :
    pairing W S ≤ (k : ℝ) * E * U := by
  have hterm : ∀ l : Fin k,
      pairing W (fun i j => F.left l i * F.right l j) ≤ E * U := by
    intro l
    apply pairing_rankOne_le W hrect hE hU (F.left l) (F.right l)
      (F.left_nonneg l) (F.right_nonneg l)
    intro i j
    calc
      F.left l i * F.right l j ≤ ∑ t, F.left t i * F.right t j :=
        Finset.single_le_sum
          (fun t _ => mul_nonneg (F.left_nonneg t i) (F.right_nonneg t j))
          (Finset.mem_univ l)
      _ = S i j := (F.reconstruct i j).symm
      _ ≤ U := hupper i j
  calc
    pairing W S = ∑ l : Fin k, pairing W (fun i j => F.left l i * F.right l j) := by
      simp only [pairing, F.reconstruct, Finset.mul_sum]
      calc
        (∑ i, ∑ j, ∑ l, W i j * (F.left l i * F.right l j)) =
            ∑ i, ∑ l, ∑ j, W i j * (F.left l i * F.right l j) := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ ≤ ∑ _l : Fin k, E * U := Finset.sum_le_sum (fun l _ => hterm l)
    _ = (k : ℝ) * E * U := by simp [mul_assoc]

/-- A strict separation threshold gives a finite nonnegative-rank lower
bound. The subtraction in the threshold is subtraction in the reals. -/
theorem rank_lower_bound_of_rectangle_bound
    {W S : I → J → ℝ} {L : ℕ} {E U : ℝ}
    (hupper : ∀ i j, S i j ≤ U) (hE : 0 ≤ E) (hU : 0 ≤ U)
    (hrect : RectangleBound W E)
    (hgap : ((L : ℝ) - 1) * E * U < pairing W S) :
    (L : ℕ∞) ≤ nonnegativeRank S := by
  apply Lemmata.LPHardnessInP.RankReduction.factorizationLowerBound_iff.mp
  intro k F
  by_contra hL
  have hk : k + 1 ≤ L := Nat.succ_le_of_lt (Nat.lt_of_not_ge hL)
  have hk' : (k : ℝ) ≤ (L : ℝ) - 1 := by
    have : (k : ℝ) + 1 ≤ (L : ℝ) := by exact_mod_cast hk
    linarith
  have hbound := pairing_factorization_le F hupper hE hU hrect
  have hmul : (k : ℝ) * E * U ≤ ((L : ℝ) - 1) * E * U :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk' hE) hU
  linarith
-- DOCS_END_MAIN

end Lemmata.LPHardnessInP.ParityExtension
