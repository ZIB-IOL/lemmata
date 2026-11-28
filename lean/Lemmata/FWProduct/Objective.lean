module

public import Lemmata.FWProduct.Statement
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

/-!
# The feasibility objective (Proposition 5.1) and Lemma A.2

With the mean `x̄ = (1/k) ∑_j x^j` and the centering map `c(x) = (x^i - x̄)_i`, the objective is
`f(x) = ‖c(x)‖²/2`. The centering map is the orthogonal projection onto the complement of the
diagonal, so `f'(x) = ⟨c(x), ·⟩`, `‖f'(x)‖ = ‖c(x)‖` and `‖c(h)‖ ≤ ‖h‖`.
-/

namespace Lemmata.FWProduct

open Lemmata.FrankWolfe

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}

/-- The mean of the blocks. -/
noncomputable def mean (x : PiLp 2 (fun _ : Fin k => E)) : E :=
  (1 / (k : ℝ)) • ∑ j, x j

/-- The centering map. -/
noncomputable def centerL : PiLp 2 (fun _ : Fin k => E) →ₗ[ℝ] PiLp 2 (fun _ : Fin k => E) where
  toFun x := WithLp.toLp 2 (fun i => x i - mean x)
  map_add' x y := by
    apply PiLp.ext; intro i
    simp only [mean, PiLp.add_apply, Finset.sum_add_distrib, smul_add]
    abel
  map_smul' c x := by
    apply PiLp.ext; intro i
    simp only [mean, PiLp.smul_apply, RingHom.id_apply, ← Finset.smul_sum, smul_sub,
      smul_comm c (1 / (k : ℝ))]

theorem centerL_apply (x : PiLp 2 (fun _ : Fin k => E)) (i : Fin k) :
    centerL x i = x i - mean x := rfl

theorem centerL_continuous : Continuous (centerL (E := E) (k := k)) := by
  show Continuous fun x : PiLp 2 (fun _ : Fin k => E) => WithLp.toLp 2 (fun i => x i - mean x)
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi; intro i
  exact (PiLp.continuous_apply 2 _ i).sub (continuous_const.smul
    (continuous_finsetSum _ fun j _ => PiLp.continuous_apply 2 _ j))

/-- The centering map as a continuous linear map. -/
noncomputable def center : PiLp 2 (fun _ : Fin k => E) →L[ℝ] PiLp 2 (fun _ : Fin k => E) :=
  ⟨centerL, centerL_continuous⟩

theorem center_apply (x : PiLp 2 (fun _ : Fin k => E)) (i : Fin k) :
    center x i = x i - mean x := rfl

/-- The blocks of `c(x)` sum to zero. -/
theorem sum_center (x : PiLp 2 (fun _ : Fin k => E)) : ∑ i, center x i = 0 := by
  simp only [center_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, mean]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, show (k : ℝ) * (1 / k) = 1 by field_simp,
      one_smul, sub_self]

/-- `c(x)` is orthogonal to `h - c(h)`, a constant vector. -/
theorem inner_center_sub (x h : PiLp 2 (fun _ : Fin k => E)) :
    inner ℝ (center x) (h - center h) = 0 := by
  rw [PiLp.inner_apply]
  have : ∀ i, (h - center h) i = mean h := by
    intro i; rw [PiLp.sub_apply, center_apply]; abel
  simp only [this, ← sum_inner, sum_center, inner_zero_left]

theorem inner_center (x h : PiLp 2 (fun _ : Fin k => E)) :
    inner ℝ (center x) (center h) = inner ℝ (center x) h := by
  have := inner_center_sub x h
  rw [inner_sub_right] at this
  linarith

theorem norm_center_le (h : PiLp 2 (fun _ : Fin k => E)) : ‖center h‖ ≤ ‖h‖ := by
  have h1 : ‖h‖ ^ 2 = ‖center h‖ ^ 2 + ‖h - center h‖ ^ 2 := by
    have := norm_add_sq_real (center h) (h - center h)
    rw [add_sub_cancel, inner_center_sub, mul_zero, add_zero] at this
    exact this
  have : ‖center h‖ ^ 2 ≤ ‖h‖ ^ 2 := by nlinarith [sq_nonneg ‖h - center h‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp this

/-- Twice the pairwise sum over `i < j` is the full double sum. -/
theorem pair_sum (g : Fin k → Fin k → ℝ) (hsym : ∀ i j, g i j = g j i) (hdiag : ∀ i, g i i = 0) :
    2 * ∑ i, ∑ j ∈ Finset.Ioi i, g i j = ∑ i, ∑ j, g i j := by
  have hsplit : ∀ i, ∑ j, g i j = ∑ j ∈ Finset.Ioi i, g i j + ∑ j ∈ Finset.Iio i, g i j := by
    intro i
    have h1 : (Finset.univ : Finset (Fin k)) = Finset.Ioi i ∪ ({i} ∪ Finset.Iio i) := by
      ext j; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_Ioi, Finset.mem_singleton,
        Finset.mem_Iio, true_iff]; omega
    rw [h1, Finset.sum_union, Finset.sum_union, Finset.sum_singleton, hdiag, zero_add]
    · rw [Finset.disjoint_singleton_left]; simp
    · rw [Finset.disjoint_union_right]; constructor
      · rw [Finset.disjoint_singleton_right]; simp
      · rw [Finset.disjoint_left]; intro a ha hb; simp at ha hb; omega
  simp only [hsplit, Finset.sum_add_distrib]
  have hswap : ∑ i, ∑ j ∈ Finset.Iio i, g i j = ∑ i, ∑ j ∈ Finset.Ioi i, g i j := by
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun j => Finset.Ioi j) (by
      intro i j; simp only [Finset.mem_univ, Finset.mem_Iio, Finset.mem_Ioi, true_and, and_true])]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    exact hsym _ _
  rw [hswap]; ring

/-- `f(x) = ‖c(x)‖²/2`. -/
theorem objective_eq (x : PiLp 2 (fun _ : Fin k => E)) :
    feasibilityObjective k x = ‖center x‖ ^ 2 / 2 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp [feasibilityObjective, PiLp.norm_sq_eq_of_L2]
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  unfold feasibilityObjective
  rw [show (1 : ℝ) / (2 * k) * ∑ i, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖ ^ 2 =
      1 / (4 * k) * (2 * ∑ i, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖ ^ 2) by field_simp; ring,
    pair_sum _ (fun i j => by rw [norm_sub_rev]) (fun i => by simp)]
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [center_apply]
  set S := ∑ j, x j with hS
  have hm : mean x = (1 / (k : ℝ)) • S := rfl
  -- expand both sides
  have e1 : ∀ i j, ‖x i - x j‖ ^ 2 = ‖x i‖ ^ 2 - 2 * inner ℝ (x i) (x j) + ‖x j‖ ^ 2 := by
    intro i j; rw [norm_sub_sq_real]
  have e2 : ∀ i, ‖x i - mean x‖ ^ 2 =
      ‖x i‖ ^ 2 - 2 * inner ℝ (x i) (mean x) + ‖mean x‖ ^ 2 := by
    intro i; rw [norm_sub_sq_real]
  simp only [e1, e2, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hinner : ∑ i, ∑ j, inner ℝ (x i) (x j) = ‖S‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hS, sum_inner]
    apply Finset.sum_congr rfl; intro i _; rw [inner_sum]
  have hinner2 : ∑ i, inner ℝ (x i) (mean x) = inner ℝ S (mean x) := by rw [hS, sum_inner]
  rw [hinner, hinner2, hm, inner_smul_right, norm_smul, real_inner_self_eq_norm_sq,
    Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / k)]
  field_simp
  ring

theorem hasFDerivAt_objective (x : PiLp 2 (fun _ : Fin k => E)) :
    HasFDerivAt (feasibilityObjective (E := E) k) (innerSL ℝ (center x)) x := by
  have h1 := (center (E := E) (k := k)).hasFDerivAt (x := x) |>.norm_sq
  have h2 := h1.const_mul (1 / 2 : ℝ)
  have hfun : feasibilityObjective (E := E) k = fun y => (1 / 2 : ℝ) * ‖center y‖ ^ 2 := by
    funext y; rw [objective_eq]; ring
  have h3 : HasFDerivAt (fun y => (1 / 2 : ℝ) * ‖center y‖ ^ 2)
      ((innerSL ℝ (center x)).comp center) x := by
    convert h2 using 1
    ext h
    simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      smul_eq_mul]
    rw [two_nsmul]; ring
  have h4 : (innerSL ℝ (center x)).comp center = innerSL ℝ (center x) := by
    ext h
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, innerSL_apply_apply]
    exact inner_center x h
  rw [hfun, ← h4]
  exact h3

theorem fderiv_objective (x : PiLp 2 (fun _ : Fin k => E)) :
    fderiv ℝ (feasibilityObjective (E := E) k) x = innerSL ℝ (center x) :=
  (hasFDerivAt_objective x).fderiv

theorem objective_props :
    Differentiable ℝ (feasibilityObjective (E := E) k) ∧
      ConvexOn ℝ Set.univ (feasibilityObjective (E := E) k) ∧
      (∀ x y, feasibilityObjective k y ≤ feasibilityObjective k x +
        fderiv ℝ (feasibilityObjective (E := E) k) x (y - x) + 1 / 2 * ‖y - x‖ ^ 2) ∧
      LipschitzWith 1 (fderiv ℝ (feasibilityObjective (E := E) k)) ∧
      ∀ x, ‖fderiv ℝ (feasibilityObjective (E := E) k) x‖ ^ 2 = 2 * feasibilityObjective k x := by
  refine ⟨fun x => (hasFDerivAt_objective x).differentiableAt, ?_, ?_, ?_, ?_⟩
  · have hfun : feasibilityObjective (E := E) k =
        (fun y => (1 / 2 : ℝ) • (fun z : PiLp 2 (fun _ : Fin k => E) => ‖z‖ ^ 2) (centerL y)) := by
      funext y; rw [objective_eq]
      show ‖centerL y‖ ^ 2 / 2 = (1 / 2 : ℝ) • ‖centerL y‖ ^ 2
      rw [smul_eq_mul]; ring
    rw [hfun]
    have h1 : ConvexOn ℝ Set.univ (fun z : PiLp 2 (fun _ : Fin k => E) => ‖z‖ ^ 2) := by
      have := ConvexOn.pow (convexOn_norm (convex_univ (𝕜 := ℝ)
        (E := PiLp 2 (fun _ : Fin k => E)))) (fun z _ => norm_nonneg z) 2
      convert this using 1
    have h2 := ConvexOn.comp_linearMap h1 (centerL (E := E) (k := k))
    simp only [Set.preimage_univ] at h2
    exact ConvexOn.smul (by norm_num : (0 : ℝ) ≤ 1 / 2) h2
  · intro x y
    rw [objective_eq, objective_eq, fderiv_objective, innerSL_apply_apply]
    have hy : center y = center x + center (y - x) := by rw [map_sub]; abel
    rw [hy, norm_add_sq_real, inner_center]
    have := norm_center_le (y - x)
    have := pow_le_pow_left₀ (norm_nonneg _) this 2
    linarith
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [fderiv_objective, fderiv_objective, dist_eq_norm, dist_eq_norm, ← map_sub, ← map_sub,
      innerSL_apply_norm, NNReal.coe_one, one_mul]
    exact norm_center_le _
  · intro x
    rw [fderiv_objective, innerSL_apply_norm, objective_eq]; ring

theorem prep_bounds : PreparatoryBounds := by
  refine ⟨fun a b ha hb => ?_, fun a a' b ha haa hb => ?_⟩
  · have hab : 0 < a ^ 2 + b ^ 2 := by positivity
    constructor
    · rw [div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num)), ← Real.sqrt_mul (by positivity)]
      rw [Real.le_sqrt (by positivity) (by positivity)]
      rw [div_mul_eq_mul_div, le_div_iff₀ hab]
      rcases le_total a b with h | h
      · rw [min_eq_left h]
        nlinarith [mul_pos ha hb, sq_nonneg (a - b), mul_le_mul h h ha.le hb.le]
      · rw [min_eq_right h]
        nlinarith [mul_pos ha hb, sq_nonneg (a - b), mul_le_mul h h hb.le ha.le]
    · rw [Real.sqrt_lt' (lt_min ha hb), div_lt_iff₀ hab]
      rcases le_total a b with h | h
      · rw [min_eq_left h]; nlinarith [pow_pos ha 4, pow_pos hb 2, mul_pos ha hb]
      · rw [min_eq_right h]; nlinarith [pow_pos hb 4, pow_pos ha 2, mul_pos ha hb]
  · apply Real.sqrt_le_sqrt
    have ha' : 0 < a' := lt_of_lt_of_le ha haa
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : a ^ 2 ≤ a' ^ 2 := pow_le_pow_left₀ ha.le haa 2
    nlinarith [pow_pos hb 4, mul_nonneg (sq_nonneg b) (sq_nonneg b)]

namespace Proof

theorem feasibility_objective : FeasibilityObjective.{u} := by
  intro E _ _ k
  exact objective_props

theorem preparatory_bounds : PreparatoryBounds := prep_bounds

end Proof

end Lemmata.FWProduct
