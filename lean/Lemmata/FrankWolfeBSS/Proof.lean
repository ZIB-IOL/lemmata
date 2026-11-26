module

public import Lemmata.FrankWolfeBSS.Statement
public import Lemmata.FrankWolfe.Proof.Calculus

@[expose] public section

/-!
# Proofs

The lower bounds `L_t` are convex combinations of Frank–Wolfe lower bounds `f(x_ℓ) - g_ℓ ≤ f(y)`.
The recursion for `G_t` is an identity of the definitions. For the rate, each of the three step
rules gives `G_{t+1} ≤ (1 - s) G_t + s² L/2 D²` at `s = 2/(t+3)`, and the induction is the one of
the open-loop analysis.
-/

namespace Lemmata.FrankWolfeBSS

open Lemmata.FrankWolfe

universe u

namespace Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem run_mem {C : Set E} {f' : E → StrongDual ℝ E} {x v : ℕ → E} {γ : ℕ → ℝ}
    (hC : Convex ℝ C) (h : IsFWRun C f' x v γ) : ∀ t, x t ∈ C := by
  intro t
  induction t with
  | zero => exact h.1
  | succ t ih =>
    obtain ⟨hv, -, hγ, hx⟩ := h.2 t
    rw [hx]
    exact hC.add_smul_sub_mem ih hv hγ

theorem fw_lower_le {C : Set E} {f : E → ℝ} {x v : ℕ → E} {γ : ℕ → ℝ}
    (hconv : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f)
    (h : IsFWRun C (fderiv ℝ f) x v γ) {y : E} (hy : y ∈ C) (t : ℕ) :
    f (x t) - fderiv ℝ f (x t) (x t - v t) ≤ f y := by
  have h1 := add_fderiv_le_of_convexOn hconv hf (x t) y
  have h2 := (h.2 t).2.1 y hy
  rw [map_sub] at h1 ⊢
  linarith

theorem pdLower_le {C : Set E} {f : E → ℝ} {x v : ℕ → E} {γ : ℕ → ℝ}
    (hconv : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f)
    (h : IsFWRun C (fderiv ℝ f) x v γ) {y : E} (hy : y ∈ C) :
    ∀ t, pdLower f (fderiv ℝ f) x v γ t ≤ f y := by
  intro t
  induction t with
  | zero => exact fw_lower_le hconv hf h hy 0
  | succ t ih =>
    have hγ := (h.2 (t + 1)).2.2.1
    have hq := fw_lower_le hconv hf h hy (t + 1)
    show (1 - γ (t + 1)) * pdLower f (fderiv ℝ f) x v γ t +
      γ (t + 1) * (f (x (t + 1)) - fderiv ℝ f (x (t + 1)) (x (t + 1) - v (t + 1))) ≤ f y
    nlinarith [mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hγ.2),
      mul_le_mul_of_nonneg_left hq hγ.1]

theorem gap_bounds_primal : GapBoundsPrimal.{u} := by
  intro E _ _ C f x v γ hconv hf h y hy t
  have := pdLower_le hconv hf h hy t
  unfold pdGap
  linarith

theorem gap_recursion : GapRecursion.{u} := by
  intro E _ _ C f x v γ h t
  have hx := (h.2 (t + 1)).2.2.2
  have hL : pdLower f (fderiv ℝ f) x v γ (t + 1) =
      (1 - γ (t + 1)) * pdLower f (fderiv ℝ f) x v γ t +
        γ (t + 1) * (f (x (t + 1)) - fderiv ℝ f (x (t + 1)) (x (t + 1) - v (t + 1))) := rfl
  unfold pdGap pdBound
  rw [hL, hx]
  have e : fderiv ℝ f (x (t + 1)) (x (t + 1) - v (t + 1)) =
      -fderiv ℝ f (x (t + 1)) (v (t + 1) - x (t + 1)) := by rw [← map_neg, neg_sub]
  rw [e]
  ring

theorem gap_bound_convex : GapBoundConvex.{u} := by
  intro E _ _ f f' G x v hconv
  refine ⟨convex_univ, fun s1 _ s2 _ a b ha hb hab => ?_⟩
  obtain rfl : b = 1 - a := by linarith
  have key := hconv.2 (Set.mem_univ (x + s1 • (v - x))) (Set.mem_univ (x + s2 • (v - x))) ha hb
    hab
  have e : x + (a • s1 + (1 - a) • s2) • (v - x) =
      a • (x + s1 • (v - x)) + (1 - a) • (x + s2 • (v - x)) := by
    simp only [smul_eq_mul]
    module
  simp only [pdBound, smul_eq_mul] at key ⊢
  rw [show x + (a * s1 + (1 - a) * s2) • (v - x) =
      a • (x + s1 • (v - x)) + (1 - a) • (x + s2 • (v - x)) by simpa [smul_eq_mul] using e]
  linear_combination key

theorem pdBound_le_smooth {f : E → ℝ} {L : NNReal} (hsm : IsSmooth f L) (G : ℝ) (x v : E)
    (s : ℝ) : pdBound f (fderiv ℝ f) G x v s ≤ pdSmoothBound L G x v s := by
  have hd := hsm.le_quadratic x (x + s • (v - x))
  rw [add_sub_cancel_left, map_smul, smul_eq_mul, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs] at hd
  simp only [pdBound, pdSmoothBound]
  linear_combination hd

theorem rate_step (K : ℝ) (hK : 0 ≤ K) (t : ℝ) (ht : 0 ≤ t) :
    (1 - 2 / (t + 3)) * (2 * K / (t + 2)) + (2 / (t + 3)) ^ 2 * K / 2 ≤ 2 * K / (t + 3) := by
  have h2 : 0 < t + 2 := by linarith
  have h3 : 0 < t + 3 := by linarith
  have e : 2 * K / (t + 3) - ((1 - 2 / (t + 3)) * (2 * K / (t + 2)) + (2 / (t + 3)) ^ 2 * K / 2) =
      2 * K / ((t + 2) * (t + 3) ^ 2) := by
    field_simp
    ring
  have : 0 ≤ 2 * K / ((t + 2) * (t + 3) ^ 2) := by positivity
  linarith

/-- The rate from the gap inequality: any sequence `G` with `G₀ ≤ L/2 D²` and
`G_{t+1} ≤ pdBound (G_t) (γ_{t+1})`, whose steps follow one of the three rules, satisfies
`G_t ≤ 2 L D²/(t + 2)`. -/
theorem rate_of_gap_bound {f : E → ℝ} {L : NNReal} (hsm : IsSmooth f L) {x v : ℕ → E}
    {γ : ℕ → ℝ} {G : ℕ → ℝ} {D : ℝ}
    (hdist : ∀ t, ‖v t - x t‖ ^ 2 ≤ D ^ 2) (hbase : G 0 ≤ L / 2 * D ^ 2)
    (hrec : ∀ t, G (t + 1) ≤ pdBound f (fderiv ℝ f) (G t) (x (t + 1)) (v (t + 1)) (γ (t + 1)))
    (hrule : ∀ t : ℕ,
      γ (t + 1) = 2 / ((t : ℝ) + 3) ∨
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
        pdSmoothBound L (G t) (x (t + 1)) (v (t + 1)) (γ (t + 1)) ≤
          pdSmoothBound L (G t) (x (t + 1)) (v (t + 1)) s) ∨
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
        pdBound f (fderiv ℝ f) (G t) (x (t + 1)) (v (t + 1)) (γ (t + 1)) ≤
          pdBound f (fderiv ℝ f) (G t) (x (t + 1)) (v (t + 1)) s)) :
    ∀ t : ℕ, G t ≤ 2 * L * D ^ 2 / ((t : ℝ) + 2) := by
  have hL0 : (0 : ℝ) ≤ L := L.2
  have hK : 0 ≤ (L : ℝ) * D ^ 2 := mul_nonneg hL0 (sq_nonneg D)
  intro t
  induction t with
  | zero =>
    rw [Nat.cast_zero, zero_add]
    have e : (2 : ℝ) * L * D ^ 2 / 2 = L * D ^ 2 := by ring
    rw [e]
    linarith
  | succ t ih =>
    set s0 : ℝ := 2 / ((t : ℝ) + 3) with hs0
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have hs0I : s0 ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by positivity, by rw [hs0, div_le_one (by positivity)]; linarith⟩
    have hkey : G (t + 1) ≤ pdSmoothBound L (G t) (x (t + 1)) (v (t + 1)) s0 := by
      refine (hrec t).trans ?_
      rcases hrule t with h1 | h2 | h3
      · rw [h1]; exact pdBound_le_smooth hsm _ _ _ _
      · exact (pdBound_le_smooth hsm _ _ _ _).trans (h2 s0 hs0I)
      · exact (h3 s0 hs0I).trans (pdBound_le_smooth hsm _ _ _ _)
    simp only [pdSmoothBound] at hkey
    have hA : (1 - s0) * G t ≤ (1 - s0) * (2 * L * D ^ 2 / ((t : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hs0I.2)
    have hB : s0 ^ 2 * (L / 2) * ‖v (t + 1) - x (t + 1)‖ ^ 2 ≤ s0 ^ 2 * (L / 2) * D ^ 2 :=
      mul_le_mul_of_nonneg_left (hdist (t + 1)) (by positivity)
    have hstep := rate_step (L * D ^ 2) hK t ht0
    have ecast : ((t + 1 : ℕ) : ℝ) + 2 = (t : ℝ) + 3 := by push_cast; ring
    rw [ecast]
    have e1 : s0 ^ 2 * (L / 2) * D ^ 2 = (2 / ((t : ℝ) + 3)) ^ 2 * (L * D ^ 2) / 2 := by
      rw [hs0]; ring
    have e2 : (1 - s0) * (2 * L * D ^ 2 / ((t : ℝ) + 2)) =
        (1 - 2 / ((t : ℝ) + 3)) * (2 * (L * D ^ 2) / ((t : ℝ) + 2)) := by
      rw [hs0]; ring
    have e3 : 2 * (L * D ^ 2) / ((t : ℝ) + 3) = 2 * L * D ^ 2 / ((t : ℝ) + 3) := by ring
    linarith

theorem primal_dual_rate : PrimalDualRate.{u} := by
  intro E _ _ C f L x v γ hC hCc hconv hsm h hγ0 hrule
  have hbdd := hC.isBounded
  have hxC := run_mem hCc h
  have hdist : ∀ t, ‖v t - x t‖ ^ 2 ≤ Metric.diam C ^ 2 := fun t =>
    pow_le_pow_left₀ (norm_nonneg _)
      (by rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hbdd (h.2 t).1 (hxC t)) 2
  refine rate_of_gap_bound (G := pdGap f (fderiv ℝ f) x v γ) hsm hdist ?_
    (fun t => (gap_recursion C f x v γ h t).le) hrule
  have hx1 : x 1 = v 0 := by rw [(h.2 0).2.2.2, hγ0, one_smul, add_sub_cancel]
  have hd := hsm.le_quadratic (x 0) (v 0)
  have e : fderiv ℝ f (x 0) (x 0 - v 0) = -fderiv ℝ f (x 0) (v 0 - x 0) := by
    rw [← map_neg, neg_sub]
  show f (x (0 + 1)) - (f (x 0) - fderiv ℝ f (x 0) (x 0 - v 0)) ≤ L / 2 * Metric.diam C ^ 2
  rw [zero_add, hx1, e]
  have := mul_le_mul_of_nonneg_left (hdist 0) (by positivity : (0 : ℝ) ≤ L / 2)
  linarith

omit [NormedSpace ℝ E] in
theorem pdShortStep_min {L G : ℝ} (hL : 0 < L) (hG : 0 ≤ G) (x v : E) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1,
      pdSmoothBound L G x v (pdShortStep L G x v) ≤ pdSmoothBound L G x v s := by
  intro s hs
  unfold pdShortStep pdSmoothBound
  split_ifs with hvx
  · subst hvx
    simp only [sub_self, norm_zero]
    nlinarith [hs.1, hs.2]
  · have hd : 0 < ‖v - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hvx)
    set c := L * ‖v - x‖ ^ 2 with hc
    have hcpos : 0 < c := by positivity
    rcases le_total (G / c) 1 with hle | hle
    · rw [min_eq_right hle]
      have e : (1 - s) * G + s ^ 2 * (L / 2) * ‖v - x‖ ^ 2 -
          ((1 - G / c) * G + (G / c) ^ 2 * (L / 2) * ‖v - x‖ ^ 2) = c / 2 * (s - G / c) ^ 2 := by
        rw [hc]; field_simp; ring
      have := mul_nonneg (le_of_lt (half_pos hcpos)) (sq_nonneg (s - G / c))
      linarith
    · rw [min_eq_left hle]
      have hGc : c ≤ G := by rwa [le_div_iff₀ hcpos, one_mul] at hle
      have h1 : 0 ≤ G - (1 + s) * c / 2 := by nlinarith [hs.2]
      have := mul_nonneg (sub_nonneg.mpr hs.2) h1
      have e : (1 - s) * G + s ^ 2 * (L / 2) * ‖v - x‖ ^ 2 -
          ((1 - 1) * G + 1 ^ 2 * (L / 2) * ‖v - x‖ ^ 2) = (1 - s) * (G - (1 + s) * c / 2) := by
        rw [hc]; ring
      linarith

theorem primal_dual_short_step_rate : PrimalDualShortStepRate.{u} := by
  intro E _ _ C f L x v γ hC hCc hconv hsm hL h hγ0 hstep
  refine primal_dual_rate C f L x v γ hC hCc hconv hsm h hγ0 (fun t => Or.inr (Or.inl ?_))
  have hG : 0 ≤ pdGap f (fderiv ℝ f) x v γ t := by
    have := gap_bounds_primal C f x v γ hconv hsm.1 h (x (t + 1)) (run_mem hCc h (t + 1)) t
    linarith
  rw [hstep t]
  exact pdShortStep_min hL hG _ _

/-! ### Heavy-ball Frank–Wolfe -/

theorem hb_run_mem {C : Set E} {f' : E → StrongDual ℝ E} {x v : ℕ → E} {γ : ℕ → ℝ}
    (hC : Convex ℝ C) (h : IsHBRun C f' x v γ) : ∀ t, x t ∈ C := by
  intro t
  induction t with
  | zero => exact h.1
  | succ t ih =>
    obtain ⟨hv, -, hγ, hx⟩ := h.2 t
    rw [hx]
    exact hC.add_smul_sub_mem ih hv hγ

theorem hbDir_succ_apply (f' : E → StrongDual ℝ E) (x : ℕ → E) (γ : ℕ → ℝ) (t : ℕ) (y : E) :
    hbDir f' x γ (t + 1) y =
      (1 - γ (t + 1)) * hbDir f' x γ t y + γ (t + 1) * f' (x (t + 1)) y := by
  simp [hbDir]

theorem hb_model_le {C : Set E} {f : E → ℝ} {x v : ℕ → E} {γ : ℕ → ℝ}
    (hconv : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f)
    (h : IsHBRun C (fderiv ℝ f) x v γ) (y : E) :
    ∀ t, hbConst f (fderiv ℝ f) x γ t + hbDir (fderiv ℝ f) x γ t y ≤ f y := by
  intro t
  induction t with
  | zero =>
    have h1 := add_fderiv_le_of_convexOn hconv hf (x 0) y
    rw [map_sub] at h1
    show f (x 0) - fderiv ℝ f (x 0) (x 0) + fderiv ℝ f (x 0) y ≤ f y
    linarith
  | succ t ih =>
    have hγ := (h.2 (t + 1)).2.2.1
    have h1 := add_fderiv_le_of_convexOn hconv hf (x (t + 1)) y
    rw [map_sub] at h1
    rw [hbDir_succ_apply]
    show (1 - γ (t + 1)) * hbConst f (fderiv ℝ f) x γ t +
        γ (t + 1) * (f (x (t + 1)) - fderiv ℝ f (x (t + 1)) (x (t + 1))) +
        ((1 - γ (t + 1)) * hbDir (fderiv ℝ f) x γ t y + γ (t + 1) * fderiv ℝ f (x (t + 1)) y) ≤
      f y
    nlinarith [mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hγ.2),
      mul_le_mul_of_nonneg_left h1 hγ.1]

theorem hb_gap_bounds_primal : HeavyBallGapBoundsPrimal.{u} := by
  intro E _ _ C f x v γ hconv hf h y hy t
  have h1 := hb_model_le hconv hf h y t
  have h2 := (h.2 t).2.1 y hy
  unfold hbGap
  linarith

theorem hb_gap_recursion : HeavyBallGapRecursion.{u} := by
  intro E _ _ C f x v γ h t
  have hx := (h.2 (t + 1)).2.2.2
  have hγ := (h.2 (t + 1)).2.2.1
  have hmin := (h.2 t).2.1 (v (t + 1)) (h.2 (t + 1)).1
  have hc : hbConst f (fderiv ℝ f) x γ (t + 1) =
      (1 - γ (t + 1)) * hbConst f (fderiv ℝ f) x γ t +
        γ (t + 1) * (f (x (t + 1)) - fderiv ℝ f (x (t + 1)) (x (t + 1))) := rfl
  unfold hbGap pdBound
  rw [hc, hbDir_succ_apply, hx, map_sub]
  nlinarith [mul_le_mul_of_nonneg_left hmin (sub_nonneg.mpr hγ.2)]

theorem hb_rate : HeavyBallRate.{u} := by
  intro E _ _ C f L x v γ hC hCc hconv hsm h hγ0 hrule
  have hbdd := hC.isBounded
  have hxC := hb_run_mem hCc h
  have hdist : ∀ t, ‖v t - x t‖ ^ 2 ≤ Metric.diam C ^ 2 := fun t =>
    pow_le_pow_left₀ (norm_nonneg _)
      (by rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hbdd (h.2 t).1 (hxC t)) 2
  refine rate_of_gap_bound (G := hbGap f (fderiv ℝ f) x v γ) hsm hdist ?_
    (hb_gap_recursion C f x v γ h) hrule
  have hx1 : x 1 = v 0 := by rw [(h.2 0).2.2.2, hγ0, one_smul, add_sub_cancel]
  have hd := hsm.le_quadratic (x 0) (v 0)
  rw [map_sub] at hd
  show f (x (0 + 1)) - (f (x 0) - fderiv ℝ f (x 0) (x 0) + fderiv ℝ f (x 0) (v 0)) ≤
    L / 2 * Metric.diam C ^ 2
  rw [zero_add, hx1]
  have := mul_le_mul_of_nonneg_left (hdist 0) (by positivity : (0 : ℝ) ≤ L / 2)
  linarith

end Proof

end Lemmata.FrankWolfeBSS
