module

public import Lemmata.FrankWolfeIntro.Caratheodory.Smooth
public import Lemmata.FrankWolfeIntro.Statement
public import Lemmata.FrankWolfe.Proof.Rate
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Module.Convex

@[expose] public section

/-!
# The approximate Carathéodory theorem (Theorem 5.1)

Frank–Wolfe on `f(z) = ‖z - x*‖_p²` over the convex hull of `V`, with oracle answers in `V`. The
derivative of `‖·‖_p²` at `u` is the functional `lpDual u`; `‖·‖_p²` is `2(p - 1)`-smooth by
`lp_sq_smooth_fun`, and `lpDual u u = 2‖u‖²`. The open-loop rate gives
`‖x_t - x*‖² ≤ 4(p - 1)D²/(t + 2)`,
and `x_t` lies in the convex hull of `x₀` and the `t` oracle answers.
-/

namespace Lemmata.FrankWolfeIntro

open Lemmata.FrankWolfe

namespace Proof

variable {n : ℕ} {p : ENNReal}

/-- The derivative of `‖·‖_p²` at `u`, as a continuous linear functional on `ℓ_p^n`. -/
noncomputable def lpDual (u : PiLp p (fun _ : Fin n => ℝ)) :
    StrongDual ℝ (PiLp p (fun _ : Fin n => ℝ)) :=
  ∑ i, (2 * (∑ j, (u j ^ 2) ^ (p.toReal / 2)) ^ (2 / p.toReal - 1) *
    ((u i ^ 2) ^ (p.toReal / 2 - 1) * u i)) • PiLp.proj p (fun _ : Fin n => ℝ) i

theorem lpDual_apply (u h : PiLp p (fun _ : Fin n => ℝ)) :
    lpDual u h = lpJ p.toReal (fun i => u i) (fun i => h i) := by
  simp only [lpDual, lpJ, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, PiLp.proj_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem lp_norm_sq (hr : 0 < p.toReal) (x : PiLp p (fun _ : Fin n => ℝ)) :
    ‖x‖ ^ 2 = (∑ i, (x i ^ 2) ^ (p.toReal / 2)) ^ (2 / p.toReal) := by
  rw [PiLp.norm_eq_sum hr]
  have e : ∀ y : ℝ, ‖y‖ ^ p.toReal = (y ^ 2) ^ (p.toReal / 2) := by
    intro y
    rw [Real.norm_eq_abs, ← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    congr 1; push_cast; ring
  have key : ∀ S : ℝ, 0 ≤ S → (S ^ (1 / p.toReal)) ^ 2 = S ^ (2 / p.toReal) := by
    intro S hS
    rw [← Real.rpow_natCast, ← Real.rpow_mul hS]
    congr 1; push_cast; ring
  rw [key _ (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _))]
  simp only [e]

theorem lpDual_self (hr : 0 < p.toReal) (u : PiLp p (fun _ : Fin n => ℝ)) :
    lpDual u u = 2 * ‖u‖ ^ 2 := by
  rw [lpDual_apply, lp_norm_sq hr]
  unfold lpJ
  set S := ∑ i, (u i ^ 2) ^ (p.toReal / 2) with hS
  have hterm : ∀ i, (u i ^ 2) ^ (p.toReal / 2 - 1) * u i * u i = (u i ^ 2) ^ (p.toReal / 2) := by
    intro i
    by_cases hu : u i = 0
    · rw [hu]; simp [Real.zero_rpow (by positivity : p.toReal / 2 ≠ 0)]
    · have hpos : 0 < u i ^ 2 := by positivity
      rw [mul_assoc, ← sq, ← Real.rpow_add_one hpos.ne']
      congr 1; ring
  simp only [hterm]
  rw [← hS]
  rcases eq_or_lt_of_le (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (sq_nonneg (u i))
    (p.toReal / 2)) : (0 : ℝ) ≤ S) with h0 | hpos
  · have h0' : S = 0 := by rw [hS]; exact h0.symm
    rw [h0']; simp [Real.zero_rpow (by positivity : 2 / p.toReal ≠ 0)]
  · rw [mul_assoc, ← Real.rpow_add_one hpos.ne']
    congr 2; ring

theorem lp_sq_smooth (hp2 : 2 ≤ p.toReal) (u h : PiLp p (fun _ : Fin n => ℝ)) :
    ‖u + h‖ ^ 2 ≤ ‖u‖ ^ 2 + lpDual u h + (p.toReal - 1) * ‖h‖ ^ 2 := by
  have hr : 0 < p.toReal := by linarith
  rw [lp_norm_sq hr, lp_norm_sq hr, lp_norm_sq hr, lpDual_apply]
  simp only [PiLp.add_apply]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [lpJ, Real.zero_rpow (by positivity : 2 / p.toReal ≠ 0)]
  · exact lp_sq_smooth_fun hn hp2 (fun i => u i) (fun i => h i)

theorem approximate_caratheodory : ApproximateCaratheodory := by
  intro n p _ hp2 hpt V hV xStar hxs ε hε
  have hr2 : 2 ≤ p.toReal := by simpa using ENNReal.toReal_mono hpt hp2
  have hr0 : 0 < p.toReal := by linarith
  have hVne : V.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, convexHull_empty] at hxs
    exact hxs
  obtain ⟨x0, hx0⟩ := hVne
  -- a linear minimization oracle over `V`
  have hmin : ∀ g : StrongDual ℝ (PiLp p (fun _ : Fin n => ℝ)), ∃ v ∈ V, ∀ w ∈ V, g v ≤ g w := by
    intro g
    obtain ⟨v, hv, hvmin⟩ := hV.exists_isMinOn ⟨x0, hx0⟩ g.continuous.continuousOn
    exact ⟨v, hv, fun w hw => hvmin hw⟩
  choose lmo hlmoV hlmomin using hmin
  have hlmo_hull : ∀ g : StrongDual ℝ (PiLp p (fun _ : Fin n => ℝ)), ∀ y ∈ convexHull ℝ V,
      g (lmo g) ≤ g y := by
    intro g y hy
    have hsub : V ⊆ {w | g (lmo g) ≤ g w} := fun w hw => hlmomin g w hw
    exact convexHull_min hsub (convex_halfSpace_ge g.toLinearMap.isLinear _) hy
  -- diameter bound on the hull
  have hbdd : Bornology.IsBounded (convexHull ℝ V) := isBounded_convexHull.mpr hV.isBounded
  have hdiam : ∀ y ∈ convexHull ℝ V, ∀ z ∈ convexHull ℝ V, ‖y - z‖ ≤ Metric.diam V := by
    intro y hy z hz
    rw [← dist_eq_norm, ← convexHull_diam]
    exact Metric.dist_le_diam_of_mem hbdd hy hz
  -- the Frank–Wolfe iterates for `f z = ‖z - x*‖²`
  set f' : PiLp p (fun _ : Fin n => ℝ) → StrongDual ℝ (PiLp p (fun _ : Fin n => ℝ)) :=
    fun z => lpDual (z - xStar) with hf'
  set x := fwIterates lmo f' (openLoopStep 2) x0 with hx
  have hγI : ∀ k : ℕ, 0 ≤ (2 : ℝ) / ((k : ℝ) + 2) ∧ (2 : ℝ) / ((k : ℝ) + 2) ≤ 1 := by
    intro k
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hxsucc : ∀ k : ℕ, x (k + 1) = x k + (2 / ((k : ℝ) + 2)) • (lmo (f' (x k)) - x k) :=
    fun k => rfl
  -- the atoms used so far
  set S : ℕ → Finset (PiLp p (fun _ : Fin n => ℝ)) :=
    fun k => insert x0 ((Finset.range k).image (fun j => lmo (f' (x j)))) with hS
  have hS_sub : ∀ k, (↑(S k) : Set (PiLp p (fun _ : Fin n => ℝ))) ⊆ V := by
    intro k y hy
    simp only [hS, Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff, Set.mem_image,
      Finset.mem_coe, Finset.mem_range] at hy
    rcases hy with rfl | ⟨j, -, rfl⟩
    exacts [hx0, hlmoV _]
  have hS_card : ∀ k, (S k).card ≤ k + 1 := by
    intro k
    refine (Finset.card_insert_le _ _).trans ?_
    have := Finset.card_image_le (s := Finset.range k) (f := fun j => lmo (f' (x j)))
    rw [Finset.card_range] at this
    omega
  have hxS : ∀ k, x k ∈ convexHull ℝ (↑(S k) : Set (PiLp p (fun _ : Fin n => ℝ))) := by
    intro k
    induction k with
    | zero => exact subset_convexHull ℝ _ (by simp [hS]; rfl)
    | succ k ih =>
      have hmono : convexHull ℝ (↑(S k) : Set (PiLp p (fun _ : Fin n => ℝ))) ⊆
          convexHull ℝ ↑(S (k + 1)) := by
        apply convexHull_mono
        intro y hy
        simp only [hS, Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff, Set.mem_image,
          Finset.mem_coe, Finset.mem_range] at hy ⊢
        rcases hy with h | ⟨j, hj, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨j, by omega, h⟩
      have hv : lmo (f' (x k)) ∈ convexHull ℝ (↑(S (k + 1)) : Set (PiLp p (fun _ : Fin n => ℝ))) :=
        subset_convexHull ℝ _ (by simp [hS]; exact Or.inr ⟨k, le_rfl, rfl⟩)
      rw [hxsucc]
      exact (convex_convexHull ℝ _).add_smul_sub_mem (hmono ih) hv (hγI k)
  have hxV : ∀ k, x k ∈ convexHull ℝ V := fun k => convexHull_mono (hS_sub k) (hxS k)
  -- the recursion for `h k = ‖x k - x*‖²`
  have hrec : ∀ k : ℕ, ‖x (k + 1) - xStar‖ ^ 2 ≤ (1 - 2 / ((k : ℝ) + 2)) * ‖x k - xStar‖ ^ 2 +
      (2 / ((k : ℝ) + 2)) ^ 2 * (2 * (p.toReal - 1) * Metric.diam V ^ 2) / 2 := by
    intro k
    set γ := (2 : ℝ) / ((k : ℝ) + 2) with hγ
    set u := x k - xStar with hu
    set v := lmo (f' (x k)) with hv
    have hstep : x (k + 1) - xStar = u + γ • (v - x k) := by rw [hxsucc, hu]; abel
    have hsm := lp_sq_smooth hr2 u (γ • (v - x k))
    have hJ : lpDual u (γ • (v - x k)) ≤ -γ * (2 * ‖u‖ ^ 2) := by
      rw [map_smul, smul_eq_mul, map_sub]
      have h1 : lpDual u v ≤ lpDual u xStar := hlmo_hull (f' (x k)) xStar hxs
      have h2 : lpDual u (x k) - lpDual u xStar = 2 * ‖u‖ ^ 2 := by
        rw [← map_sub]; exact lpDual_self hr0 u
      have := mul_le_mul_of_nonneg_left
        (show lpDual u v - lpDual u (x k) ≤ -(2 * ‖u‖ ^ 2) by linarith) (hγI k).1
      linarith
    have hnorm : ‖γ • (v - x k)‖ ^ 2 ≤ γ ^ 2 * Metric.diam V ^ 2 := by
      rw [norm_smul, Real.norm_of_nonneg (hγI k).1, mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
        (hdiam _ (subset_convexHull ℝ V (hlmoV _)) _ (hxV k)) 2) (sq_nonneg γ)
    rw [hstep]
    have hu0 : 0 ≤ γ * ‖u‖ ^ 2 := mul_nonneg (hγI k).1 (sq_nonneg _)
    have hr1 : 0 ≤ p.toReal - 1 := by linarith
    have h3 := mul_le_mul_of_nonneg_left hnorm hr1
    nlinarith
  have hK : 0 ≤ 2 * (p.toReal - 1) * Metric.diam V ^ 2 := by
    have := Metric.diam_nonneg (s := V)
    have hr1 : 0 ≤ p.toReal - 1 := by linarith
    positivity
  have hrate := rate_of_recursion (h := fun k => ‖x k - xStar‖ ^ 2) hK hrec
  -- the number of steps
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = ⌈4 * (p.toReal - 1) * Metric.diam V ^ 2 / ε ^ 2⌉₊ + 1 := ⟨_, rfl⟩
  refine ⟨S t, hS_sub t, ?_, x t, hxS t, ?_⟩
  · have := hS_card t
    omega
  · have hxt : ‖x t - xStar‖ ^ 2 ≤ 2 * (2 * (p.toReal - 1) * Metric.diam V ^ 2) / ((t : ℝ) + 2) :=
      hrate t (by omega)
    have hceil : 4 * (p.toReal - 1) * Metric.diam V ^ 2 / ε ^ 2 ≤ (t : ℝ) + 2 := by
      have := Nat.le_ceil (4 * (p.toReal - 1) * Metric.diam V ^ 2 / ε ^ 2)
      have ht' : (t : ℝ) = (⌈4 * (p.toReal - 1) * Metric.diam V ^ 2 / ε ^ 2⌉₊ : ℝ) + 1 := by
        rw [ht]; push_cast; ring
      linarith
    have hbound : 2 * (2 * (p.toReal - 1) * Metric.diam V ^ 2) / ((t : ℝ) + 2) ≤ ε ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity)] at hceil
      linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).mp (le_trans hxt hbound)

end Proof

end Lemmata.FrankWolfeIntro
