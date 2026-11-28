module

public import Lemmata.FWCaratheodory.Statement
public import Lemmata.FrankWolfeIntro.Caratheodory.Theorem
public import Lemmata.CGBasics.Smoothness
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Convex.Mul

@[expose] public section

/-!
# The objective `‖z - x⋆‖_p²/2` (Lemma 3.1)

The entry on the introduction to Frank–Wolfe provides the functional `lpDual u` and the quadratic
upper bound `‖u + h‖² ≤ ‖u‖² + lpDual u h + (p - 1)‖h‖²`. Hölder's inequality gives
`|lpDual u h| ≤ 2‖u‖‖h‖`, hence also the lower bound `lpDual u h ≤ ‖u + h‖² - ‖u‖²`, so
`lpDual u` is the derivative of `‖·‖²` at `u` and `‖lpDual u‖ = 2‖u‖`.
-/

namespace Lemmata.FWCaratheodory

open Lemmata.FrankWolfe Lemmata.FrankWolfeIntro.Proof Filter Topology

variable {n : ℕ} {p : ENNReal}

/-- Hölder's inequality for `lpDual`: `lpDual u h ≤ 2 ‖u‖ ‖h‖`. -/
theorem lpDual_le [Fact (1 ≤ p)] (hp2 : 2 ≤ p.toReal) (u h : PiLp p (fun _ : Fin n => ℝ)) :
    lpDual u h ≤ 2 * ‖u‖ * ‖h‖ := by
  have hr : 0 < p.toReal := by linarith
  rw [lpDual_apply]
  unfold lpJ
  have hnh : (∑ i, |h i| ^ p.toReal) ^ (1 / p.toReal) = ‖h‖ := by
    rw [PiLp.norm_eq_sum hr]; simp [Real.norm_eq_abs]
  have hnu : (∑ i, |u i| ^ p.toReal) ^ (1 / p.toReal) = ‖u‖ := by
    rw [PiLp.norm_eq_sum hr]; simp [Real.norm_eq_abs]
  set P := p.toReal with hP
  set S := ∑ i, (u i ^ 2) ^ (P / 2) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (sq_nonneg _) _
  set a : Fin n → ℝ := fun i => (u i ^ 2) ^ (P / 2 - 1) * u i with hadef
  have hpow : ∀ y : ℝ, (y ^ 2) ^ (P / 2) = |y| ^ P := by
    intro y
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    congr 1; push_cast; ring
  have ha : ∀ i, |a i| = |u i| ^ (P - 1) := by
    intro i
    simp only [hadef]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (sq_nonneg _) _), ← sq_abs, ← Real.rpow_natCast,
      ← Real.rpow_mul (abs_nonneg _)]
    rcases eq_or_lt_of_le (abs_nonneg (u i)) with h0 | hpos
    · rw [← h0, Real.zero_rpow (by linarith : P - 1 ≠ 0), mul_zero]
    · rw [mul_comm, ← Real.rpow_one_add' hpos.le (by push_cast; linarith)]
      congr 1; push_cast; ring
  have hq := Real.HolderConjugate.conjExponent (show 1 < P by linarith)
  have hHolder := Real.inner_le_Lp_mul_Lq Finset.univ a (fun i => h i) hq.symm
  beta_reduce at hHolder
  have hqP : (P - 1) * Real.conjExponent P = P := by
    unfold Real.conjExponent
    have : P - 1 ≠ 0 := by linarith
    field_simp
  have hsum : ∑ i, |a i| ^ Real.conjExponent P = S := by
    rw [hS]
    apply Finset.sum_congr rfl
    intro i _
    rw [ha, ← Real.rpow_mul (abs_nonneg _), hqP, hpow]
  have hh : (∑ i, |h i| ^ P) ^ (1 / P) = ‖h‖ := hnh
  have hu : S ^ (1 / P) = ‖u‖ := by
    rw [← hnu, hS]; simp only [hpow]
  rw [hsum, hh] at hHolder
  have hinvq : 1 / Real.conjExponent P = (P - 1) / P := by
    unfold Real.conjExponent; field_simp
  rw [hinvq] at hHolder
  show 2 * S ^ (2 / P - 1) * ∑ i, a i * h i ≤ 2 * ‖u‖ * ‖h‖
  have hSx : 0 ≤ S ^ (2 / P - 1) := Real.rpow_nonneg hS0 _
  have hcomb : S ^ (2 / P - 1) * S ^ ((P - 1) / P) = S ^ (1 / P) := by
    rcases eq_or_lt_of_le hS0 with h0 | hpos
    · have hne : (P - 1) / P ≠ 0 := by apply div_ne_zero <;> linarith
      have hne' : 1 / P ≠ 0 := by positivity
      rw [← h0, Real.zero_rpow (x := (P - 1) / P) hne, mul_zero, Real.zero_rpow hne']
    · rw [← Real.rpow_add hpos]; congr 1; field_simp; ring
  calc 2 * S ^ (2 / P - 1) * ∑ i, a i * h i
      ≤ 2 * S ^ (2 / P - 1) * (S ^ ((P - 1) / P) * ‖h‖) :=
        mul_le_mul_of_nonneg_left hHolder (by positivity)
    _ = 2 * (S ^ (2 / P - 1) * S ^ ((P - 1) / P)) * ‖h‖ := by ring
    _ = 2 * ‖u‖ * ‖h‖ := by rw [hcomb, hu]

theorem abs_lpDual_le [Fact (1 ≤ p)] (hp2 : 2 ≤ p.toReal) (u h : PiLp p (fun _ : Fin n => ℝ)) :
    |lpDual u h| ≤ 2 * ‖u‖ * ‖h‖ := by
  rw [abs_le]
  refine ⟨?_, lpDual_le hp2 u h⟩
  have := lpDual_le hp2 u (-h)
  rw [map_neg, norm_neg] at this
  linarith

theorem norm_lpDual_le [Fact (1 ≤ p)] (hp2 : 2 ≤ p.toReal) (u : PiLp p (fun _ : Fin n => ℝ)) :
    ‖lpDual u‖ ≤ 2 * ‖u‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => by
    rw [Real.norm_eq_abs]; exact abs_lpDual_le hp2 u h

/-- `lpDual u` is the derivative of `‖·‖²` at `u`. -/
theorem hasFDerivAt_norm_sq [Fact (1 ≤ p)] (hp2 : 2 ≤ p.toReal)
    (u : PiLp p (fun _ : Fin n => ℝ)) :
    HasFDerivAt (fun z : PiLp p (fun _ : Fin n => ℝ) => ‖z‖ ^ 2) (lpDual u) u := by
  have hr : 0 < p.toReal := by linarith
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hbound : ∀ h : PiLp p (fun _ : Fin n => ℝ),
      ‖‖u + h‖ ^ 2 - ‖u‖ ^ 2 - lpDual u h‖ ≤ (p.toReal - 1) * ‖‖h‖ ^ 2‖ := by
    intro h
    have hup := lp_sq_smooth hp2 u h
    have hlow : lpDual u h ≤ ‖u + h‖ ^ 2 - ‖u‖ ^ 2 := by
      have h1 := lpDual_le hp2 u (u + h)
      have h2 := lpDual_self hr u
      rw [map_add] at h1
      nlinarith [sq_nonneg (‖u‖ - ‖u + h‖)]
    rw [Real.norm_of_nonneg (sq_nonneg ‖h‖), Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [sq_nonneg ‖h‖]
  have hO : (fun h : PiLp p (fun _ : Fin n => ℝ) => ‖u + h‖ ^ 2 - ‖u‖ ^ 2 - lpDual u h) =O[𝓝 0]
      (fun h => ‖h‖ ^ 2) :=
    Asymptotics.IsBigO.of_bound (p.toReal - 1) (Eventually.of_forall hbound)
  exact hO.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (by norm_num : 1 < 2))

theorem lpObjective_eq [Fact (1 ≤ p)] (xStar : PiLp p (fun _ : Fin n => ℝ)) :
    lpObjective xStar = fun z => (1 / 2 : ℝ) * ‖z - xStar‖ ^ 2 := by
  funext z; simp only [lpObjective]; ring

theorem hasFDerivAt_lpObjective [Fact (1 ≤ p)] (hp2 : 2 ≤ p.toReal)
    (xStar z : PiLp p (fun _ : Fin n => ℝ)) :
    HasFDerivAt (lpObjective xStar) ((1 / 2 : ℝ) • lpDual (z - xStar)) z := by
  rw [lpObjective_eq]
  have h1 := (hasFDerivAt_norm_sq hp2 (z - xStar)).comp z (hasFDerivAt_sub_const (𝕜 := ℝ) xStar)
  have h2 := h1.const_mul (1 / 2 : ℝ)
  simpa using h2

theorem fderiv_lpObjective [Fact (1 ≤ p)] (hp2 : 2 ≤ p.toReal)
    (xStar z : PiLp p (fun _ : Fin n => ℝ)) :
    fderiv ℝ (lpObjective xStar) z = (1 / 2 : ℝ) • lpDual (z - xStar) :=
  (hasFDerivAt_lpObjective hp2 xStar z).fderiv

/-- `‖f'(z)‖ = ‖z - x⋆‖`. -/
theorem norm_fderiv_lpObjective [Fact (1 ≤ p)] (hp2 : 2 ≤ p.toReal)
    (xStar z : PiLp p (fun _ : Fin n => ℝ)) :
    ‖fderiv ℝ (lpObjective xStar) z‖ = ‖z - xStar‖ := by
  have hr : 0 < p.toReal := by linarith
  rw [fderiv_lpObjective hp2]
  set u := z - xStar
  apply le_antisymm
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := norm_lpDual_le hp2 u
    linarith
  · have h1 : ((1 / 2 : ℝ) • lpDual u) u = ‖u‖ ^ 2 := by
      rw [FunLike.coe_smul, Pi.smul_apply, lpDual_self hr, smul_eq_mul]; ring
    have h2 := ((1 / 2 : ℝ) • lpDual u).le_opNorm u
    rw [h1, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h2
    rcases eq_or_lt_of_le (norm_nonneg u) with h0 | hpos
    · rw [← h0]; exact norm_nonneg _
    · have : ‖u‖ * ‖u‖ ≤ ‖(1 / 2 : ℝ) • lpDual u‖ * ‖u‖ := by nlinarith
      exact le_of_mul_le_mul_right this hpos

theorem lpObjective_props [Fact (1 ≤ p)] (hp2 : 2 ≤ p) (hpt : p ≠ ⊤)
    (xStar : PiLp p (fun _ : Fin n => ℝ)) :
    Differentiable ℝ (lpObjective xStar) ∧ ConvexOn ℝ Set.univ (lpObjective xStar) ∧
      (∀ x y, lpObjective xStar y ≤ lpObjective xStar x + fderiv ℝ (lpObjective xStar) x (y - x) +
        (p.toReal - 1) / 2 * ‖y - x‖ ^ 2) ∧
      LipschitzWith (Real.toNNReal (p.toReal - 1)) (fderiv ℝ (lpObjective xStar)) ∧
      (∀ z, ‖fderiv ℝ (lpObjective xStar) z‖ = ‖z - xStar‖) ∧
      ∀ C : Set (PiLp p (fun _ : Fin n => ℝ)), xStar ∈ C →
        IsHolderErrorBound C (lpObjective xStar) (Real.sqrt 2) (1 / 2) := by
  have hr2 : 2 ≤ p.toReal := by simpa using ENNReal.toReal_mono hpt hp2
  have hr : 0 < p.toReal := by linarith
  set f := lpObjective xStar with hf
  have hdiff : Differentiable ℝ f := fun z => (hasFDerivAt_lpObjective hr2 xStar z).differentiableAt
  have hconv : ConvexOn ℝ Set.univ f := by
    have h1 : ConvexOn ℝ Set.univ (fun z : PiLp p (fun _ : Fin n => ℝ) => ‖z - xStar‖) := by
      have := (convexOn_norm (convex_univ (𝕜 := ℝ)
        (E := PiLp p (fun _ : Fin n => ℝ)))).translate_right (-xStar)
      simp only [Set.preimage_univ] at this
      convert this using 1
      funext z; simp [Function.comp, sub_eq_neg_add]
    have h2 := ConvexOn.pow h1 (fun z _ => norm_nonneg _) 2
    have h3 := ConvexOn.smul (by norm_num : (0 : ℝ) ≤ 1 / 2) h2
    convert h3 using 1
    funext z; simp only [hf, lpObjective, Pi.pow_apply, smul_eq_mul]; ring
  have hquad : ∀ x y, f y ≤ f x + fderiv ℝ f x (y - x) + (p.toReal - 1) / 2 * ‖y - x‖ ^ 2 := by
    intro x y
    have h := lp_sq_smooth hr2 (x - xStar) (y - x)
    rw [show x - xStar + (y - x) = y - xStar by abel] at h
    rw [hf, fderiv_lpObjective hr2, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    simp only [lpObjective]
    linarith
  have hL : ((Real.toNNReal (p.toReal - 1) : NNReal) : ℝ) = p.toReal - 1 :=
    Real.coe_toNNReal _ (by linarith)
  have hlip : LipschitzWith (Real.toNNReal (p.toReal - 1)) (fderiv ℝ f) := by
    apply (Lemmata.CGBasics.Proof.smooth_iff_lipschitz f _ hconv hdiff).mp
    intro x y
    rw [hL]
    exact hquad x y
  refine ⟨hdiff, hconv, hquad, hlip, norm_fderiv_lpObjective hr2 xStar, ?_⟩
  intro C hxC x hx y hy
  have hf0 : ∀ z, 0 ≤ f z := fun z => by simp only [hf, lpObjective]; positivity
  have hfx : f xStar = 0 := by simp [hf, lpObjective]
  have hxsmin : xStar ∈ minimizers C f := ⟨hxC, fun z _ => by rw [hfx]; exact hf0 z⟩
  have hfy : f y = 0 := le_antisymm (by rw [← hfx]; exact hy.2 xStar hxC) (hf0 y)
  rw [hfy, sub_zero]
  calc Metric.infDist x (minimizers C f) ≤ dist x xStar := Metric.infDist_le_dist_of_mem hxsmin
    _ = ‖x - xStar‖ := dist_eq_norm _ _
    _ = Real.sqrt 2 * f x ^ (1 / 2 : ℝ) := by
        rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by norm_num)]
        simp only [hf, lpObjective]
        rw [show 2 * (‖x - xStar‖ ^ 2 / 2) = ‖x - xStar‖ ^ 2 by ring,
          Real.sqrt_sq (norm_nonneg _)]

namespace Proof

theorem lp_objective : LpObjective := by
  intro n p _ hp2 hpt xStar
  exact lpObjective_props hp2 hpt xStar

end Proof

end Lemmata.FWCaratheodory
