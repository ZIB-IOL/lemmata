module

public import Lemmata.FWOpenLoop.Interior

@[expose] public section

/-!
# Minimizers in the relative interior of a face: Lemmas 4.1–4.3

Strict complementarity and the Lipschitz derivative separate the vertices of the optimal face from
the others once the iterates are close to the minimizer, so from then on the atoms lie in the face
(Lemma 4.1). Lemma 4.2 is the scaling inequality of Lemma 3.2 relative to the affine hull of the
face, and the distance of the iterates to that affine hull contracts like
`∏ (1 - η_i) ≤ (η_t/η_S)⁴` (Lemma 4.3).
-/

namespace Lemmata.FWOpenLoop

open Lemmata.FrankWolfe

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Lemma 4.1.** -/
theorem active_set_bound {V F : Finset E} {f : E → ℝ} {L μ θ κ : ℝ} {x v : ℕ → E} {xStar : E}
    (hFV : F ⊆ V) (hconv : ConvexOn ℝ (convexHull ℝ (↑V : Set E)) f)
    (hdiff : ∀ y ∈ convexHull ℝ (↑V : Set E), DifferentiableAt ℝ f y)
    (hsm : IsSmoothOn (convexHull ℝ (↑V : Set E)) f L) (hL : 0 < L)
    (hlip : ∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E),
      ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖)
    (hdiam : 0 < Metric.diam (convexHull ℝ (↑V : Set E)))
    (huniq : minimizers (convexHull ℝ (↑V : Set E)) f = {xStar})
    (heb : IsHolderErrorBound (convexHull ℝ (↑V : Set E)) f μ θ) (hμ : 0 < μ)
    (hθ : θ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (hκ : 0 < κ)
    (hsc1 : ∀ p ∈ V, p ∉ F → κ ≤ fderiv ℝ f xStar (p - xStar))
    (hsc0 : ∀ p ∈ F, fderiv ℝ f xStar (p - xStar) = 0)
    (hrun : IsFWRun (convexHull ℝ (↑V : Set E)) (fderiv ℝ f) x v (fun t => eta 4 t)) :
    ∀ t : ℕ, ⌈8 * L * Metric.diam (convexHull ℝ (↑V : Set E)) ^ 2 *
        (2 * μ * L * Metric.diam (convexHull ℝ (↑V : Set E)) / κ) ^ (1 / θ)⌉₊ ≤ t →
      v t ∈ convexHull ℝ (↑F : Set E) := by
  classical
  intro t ht
  set C := convexHull ℝ (↑V : Set E) with hCdef
  set δ := Metric.diam C with hδ
  have hC : IsCompact C := V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hxs : xStar ∈ minimizers C f := by rw [huniq]; rfl
  have hθ0 := hθ.1
  set c := 2 * μ * L * δ / κ with hc
  have hcpos : 0 < c := by positivity
  have hS : 0 < 8 * L * δ ^ 2 * c ^ (1 / θ) := by positivity
  have ht1 : 1 ≤ t := le_trans (Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hS).ne') ht
  have hxC : x t ∈ C := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hconv.1 hrun t
  have hb := baseline_bound hC hconv hdiff hsm hL.le hrun hxs t ht1
  set h := f (x t) - f xStar with hh
  have hh0 : 0 ≤ h := sub_nonneg.mpr (hxs.2 _ hxC)
  have hlt : h < (1 / c) ^ (1 / θ) := by
    have h1 : 8 * L * δ ^ 2 * c ^ (1 / θ) ≤ t := le_trans (Nat.le_ceil _) (by exact_mod_cast ht)
    have hP : 0 < c ^ (1 / θ) := by positivity
    have hinv : (1 / c) ^ (1 / θ) * c ^ (1 / θ) = 1 := by
      rw [← Real.mul_rpow (by positivity) hcpos.le, one_div_mul_cancel hcpos.ne', Real.one_rpow]
    have h2 : 8 * L * δ ^ 2 / (t + 3) < (1 / c) ^ (1 / θ) := by
      rw [div_lt_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (1 / c) ^ (1 / θ))
      have e : (1 / c) ^ (1 / θ) * (8 * L * δ ^ 2 * c ^ (1 / θ)) = 8 * L * δ ^ 2 := by
        rw [mul_left_comm, hinv, mul_one]
      have hpos : 0 < (1 / c) ^ (1 / θ) := by positivity
      nlinarith
    linarith
  have hpow : h ^ θ < 1 / c := by
    have := Real.rpow_lt_rpow hh0 hlt hθ0
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hθ0.ne', Real.rpow_one] at this
  have hdist : ‖x t - xStar‖ ≤ μ * h ^ θ := by
    have := heb (x t) hxC xStar hxs
    rwa [huniq, Metric.infDist_singleton, dist_eq_norm] at this
  have hgrad := hlip (x t) hxC xStar hxs.1
  have hκ2 : L * δ * (μ * h ^ θ) < κ / 2 := by
    have : L * δ * (μ * h ^ θ) < L * δ * (μ * (1 / c)) :=
      mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hpow hμ) (by positivity)
    have e : L * δ * (μ * (1 / c)) = κ / 2 := by rw [hc]; field_simp
    linarith
  have hkey : ∀ p ∈ C, |(fderiv ℝ f (x t) - fderiv ℝ f xStar) (p - x t)| < κ / 2 := by
    intro p hp
    have hpd : ‖p - x t‖ ≤ δ := by
      rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hC.isBounded hp hxC
    calc |(fderiv ℝ f (x t) - fderiv ℝ f xStar) (p - x t)|
        ≤ ‖fderiv ℝ f (x t) - fderiv ℝ f xStar‖ * ‖p - x t‖ := by
          rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L * (μ * h ^ θ)) * δ := by
          apply mul_le_mul (le_trans hgrad (mul_le_mul_of_nonneg_left hdist hL.le)) hpd
            (norm_nonneg _) (by positivity)
      _ = L * δ * (μ * h ^ θ) := by ring
      _ < κ / 2 := hκ2
  set g := fderiv ℝ f (x t) with hg
  set gs := fderiv ℝ f xStar with hgs
  have hexpand : ∀ p : E, g p - g (x t) =
      (g - gs) (p - x t) + gs (p - xStar) + gs (xStar - x t) := by
    intro p
    simp only [sub_apply, map_sub]
    ring
  have hsep : ∀ p ∈ F, ∀ q ∈ V, q ∉ F → g p < g q := by
    intro p hp q hq hqF
    have h1 := abs_lt.mp (hkey p (subset_convexHull ℝ _ (Finset.mem_coe.mpr (hFV hp))))
    have h2 := abs_lt.mp (hkey q (subset_convexHull ℝ _ (Finset.mem_coe.mpr hq)))
    have h3 := hsc0 p hp
    have h4 := hsc1 q hq hqF
    have e1 := hexpand p
    have e2 := hexpand q
    linarith [h1.1, h1.2, h2.1, h2.2]
  -- the face is nonempty
  have hFne : F.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    obtain ⟨w, hw0, hw1, hwx⟩ := (Finset.mem_convexHull').mp hxs.1
    have hsum : ∑ y ∈ V, w y * gs (y - xStar) = 0 := by
      have : ∑ y ∈ V, w y * gs (y - xStar) = gs (∑ y ∈ V, w y • y) - gs xStar := by
        simp only [map_sub, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul,
          map_sum, map_smul, smul_eq_mul]
      rw [this, hwx, sub_self]
    have hge : ∑ y ∈ V, w y * κ ≤ ∑ y ∈ V, w y * gs (y - xStar) :=
      Finset.sum_le_sum (fun y hy => mul_le_mul_of_nonneg_left
        (hsc1 y hy (by rw [hemp]; exact Finset.notMem_empty y)) (hw0 y hy))
    rw [← Finset.sum_mul, hw1, one_mul, hsum] at hge
    linarith
  obtain ⟨p₀, hp₀⟩ := hFne
  -- the atom is a convex combination of vertices that all minimize `g`, hence lie in `F`
  obtain ⟨hvC, hvmin, -, -⟩ := hrun.2 t
  obtain ⟨w, hw0, hw1, hwv⟩ := (Finset.mem_convexHull').mp hvC
  have hmin : ∀ y ∈ V, g (v t) ≤ g y := fun y hy =>
    hvmin y (subset_convexHull ℝ _ (Finset.mem_coe.mpr hy))
  have hzero : ∑ y ∈ V, w y * (g y - g (v t)) = 0 := by
    have : ∑ y ∈ V, w y * (g y - g (v t)) = g (∑ y ∈ V, w y • y) - g (v t) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul, map_sum,
        map_smul, smul_eq_mul]
    rw [this, hwv, sub_self]
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun y hy =>
    mul_nonneg (hw0 y hy) (sub_nonneg.mpr (hmin y hy)))).mp hzero
  have hoff : ∀ q ∈ V \ F, w q = 0 := by
    intro q hq
    rw [Finset.mem_sdiff] at hq
    have hpos : 0 < g q - g (v t) := by
      have := hsep p₀ hp₀ q hq.1 hq.2
      have := hmin p₀ (hFV hp₀)
      linarith
    have := hterm q hq.1
    rcases mul_eq_zero.mp this with h0 | h0
    · exact h0
    · linarith
  refine (Finset.mem_convexHull').mpr ⟨w, fun y hy => hw0 y (hFV hy), ?_, ?_⟩
  · rw [← Finset.sum_sdiff hFV, Finset.sum_eq_zero hoff, zero_add] at hw1; exact hw1
  · rw [← Finset.sum_sdiff hFV, Finset.sum_eq_zero (fun q hq => by rw [hoff q hq, zero_smul]),
      zero_add] at hwv
    exact hwv

/-- **Lemma 4.2.** -/
theorem scaling_boundary_bound {V F : Finset E} {f : E → ℝ} {β : ℝ} {xStar : E}
    (hconv : ConvexOn ℝ (convexHull ℝ (↑V : Set E)) f)
    (hdiff : ∀ y ∈ convexHull ℝ (↑V : Set E), DifferentiableAt ℝ f y)
    (hxs : xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f)
    (hxF : xStar ∈ affineSpan ℝ (↑F : Set E)) (hβ : 0 < β)
    (hball : ∀ y ∈ affineSpan ℝ (↑F : Set E), ‖y - xStar‖ ≤ β → y ∈ convexHull ℝ (↑V : Set E))
    {x : E} (hx : x ∈ convexHull ℝ (↑V : Set E)) {p : E}
    (hpmin : ∀ y ∈ convexHull ℝ (↑V : Set E), fderiv ℝ f x p ≤ fderiv ℝ f x y)
    {u : E} (hu : u ∈ vectorSpan ℝ (↑F : Set E)) (hu1 : ‖u‖ ≤ 1) :
    β * fderiv ℝ f x u ≤ fderiv ℝ f x (x - p) := by
  have hmem : xStar - β • u ∈ convexHull ℝ (↑V : Set E) := by
    apply hball
    · have : xStar - β • u = (-(β • u)) +ᵥ xStar := by rw [vadd_eq_add]; abel
      rw [this]
      apply AffineSubspace.vadd_mem_of_mem_direction _ hxF
      rw [direction_affineSpan]; exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hu)
    · rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hβ]
      calc β * ‖u‖ ≤ β * 1 := mul_le_mul_of_nonneg_left hu1 hβ.le
        _ = β := mul_one β
  have h1 := hpmin _ hmem
  have h2 := convexOn_add_fderiv_le hconv hx (hdiff x hx) hxs.1
  have h3 := hxs.2 x hx
  have e1 : fderiv ℝ f x (xStar - β • u) = fderiv ℝ f x xStar - β * fderiv ℝ f x u := by
    rw [map_sub, map_smul, smul_eq_mul]
  have e2 : fderiv ℝ f x (xStar - x) = fderiv ℝ f x xStar - fderiv ℝ f x x := map_sub _ _ _
  have e3 : fderiv ℝ f x (x - p) = fderiv ℝ f x x - fderiv ℝ f x p := map_sub _ _ _
  linarith

/-- `t (t + 5)⁴ ≤ (t + 4)⁵`, the one-step decay of `(η_t/η_S)⁴`. -/
theorem fourth_power_step (t : ℝ) (ht : 0 ≤ t) :
    (1 - 4 / (t + 4)) * (4 / (t + 4)) ^ 4 ≤ (4 / (t + 5)) ^ 4 := by
  have h4 : 0 < t + 4 := by linarith
  have h5 : 0 < t + 5 := by linarith
  rw [show 1 - 4 / (t + 4) = t / (t + 4) by field_simp; ring, div_pow, div_pow,
    div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  have : t * (t + 5) ^ 4 ≤ (t + 4) ^ 5 := by
    nlinarith [sq_nonneg t, sq_nonneg (t + 4), mul_nonneg ht (sq_nonneg t),
      mul_nonneg ht (mul_nonneg ht (sq_nonneg t)), pow_nonneg ht 4, pow_nonneg ht 3]
  have e1 : t * 4 ^ 4 * (t + 5) ^ 4 = 4 ^ 4 * (t * (t + 5) ^ 4) := by ring
  have e2 : 4 ^ 4 * ((t + 4) * (t + 4) ^ 4) = 4 ^ 4 * (t + 4) ^ 5 := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left this (by norm_num)

/-- **Lemma 4.3.** -/
theorem distance_to_face_bound {V F : Finset E} {f : E → ℝ} {L μ θ β κ : ℝ} {x v : ℕ → E}
    {xStar : E} (hFV : F ⊆ V) (hconv : ConvexOn ℝ (convexHull ℝ (↑V : Set E)) f)
    (hdiff : ∀ y ∈ convexHull ℝ (↑V : Set E), DifferentiableAt ℝ f y)
    (hsm : IsSmoothOn (convexHull ℝ (↑V : Set E)) f L) (hL : 0 < L)
    (hlip : ∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E),
      ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖)
    (hdiam : 0 < Metric.diam (convexHull ℝ (↑V : Set E)))
    (huniq : minimizers (convexHull ℝ (↑V : Set E)) f = {xStar})
    (hxF : xStar ∈ affineSpan ℝ (↑F : Set E))
    (heb : IsHolderErrorBound (convexHull ℝ (↑V : Set E)) f μ θ) (hμ : 0 < μ)
    (hθ : θ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (hβ : 0 < β) (hκ : 0 < κ)
    (hsc1 : ∀ p ∈ V, p ∉ F → κ ≤ fderiv ℝ f xStar (p - xStar))
    (hsc0 : ∀ p ∈ F, fderiv ℝ f xStar (p - xStar) = 0)
    (hrun : IsFWRun (convexHull ℝ (↑V : Set E)) (fderiv ℝ f) x v (fun t => eta 4 t))
    (S : ℕ) (hS : S = max ⌈8 * L * Metric.diam (convexHull ℝ (↑V : Set E)) ^ 2 *
        (μ / β) ^ (1 / θ)⌉₊ ⌈8 * L * Metric.diam (convexHull ℝ (↑V : Set E)) ^ 2 *
          (2 * μ * L * Metric.diam (convexHull ℝ (↑V : Set E)) / κ) ^ (1 / θ)⌉₊) :
    ∀ t : ℕ, S ≤ t →
      Metric.infDist (x t) (affineSpan ℝ (↑F : Set E)) ≤ (eta 4 t / eta 4 S) ^ 4 * β := by
  set A := affineSpan ℝ (↑F : Set E) with hA
  have hAne : (A : Set E).Nonempty := ⟨xStar, hxF⟩
  have hactive := active_set_bound hFV hconv hdiff hsm hL hlip hdiam huniq heb hμ hθ hκ hsc1 hsc0
    hrun
  have hηS : 0 < eta 4 S := by simp only [eta]; push_cast; positivity
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    rw [div_self hηS.ne', one_pow, one_mul]
    have hnear := near_optimum_bound (V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)) hconv hdiff
      hsm hL hdiam heb hμ hθ.1 hβ hrun S (by rw [hS]; exact le_max_left _ _)
    rw [huniq, Metric.infDist_singleton] at hnear
    exact le_trans (Metric.infDist_le_dist_of_mem hxF) hnear
  | succ t ht ih =>
    obtain ⟨-, -, hγ, hx'⟩ := hrun.2 t
    have hvF : v t ∈ (A : Set E) :=
      convexHull_subset_affineSpan _ (hactive t (le_trans (by rw [hS]; exact le_max_right _ _) ht))
    have hη : 0 < eta 4 t := by simp only [eta]; push_cast; positivity
    have hη1 : eta 4 t < 1 := by
      have hS1 : 1 ≤ S := by
        have : 0 < 8 * L * Metric.diam (convexHull ℝ (↑V : Set E)) ^ 2 *
            (2 * μ * L * Metric.diam (convexHull ℝ (↑V : Set E)) / κ) ^ (1 / θ) := by
          have := hθ.1; positivity
        have := Nat.ceil_pos.mpr this
        rw [hS]; omega
      have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast le_trans hS1 ht
      simp only [eta]; push_cast
      rw [div_lt_one (by linarith)]; linarith
    -- one step contracts the distance to the affine hull by `1 - η_t`
    have hstep : Metric.infDist (x (t + 1)) A ≤ (1 - eta 4 t) * Metric.infDist (x t) A := by
      have hpos : 0 < 1 - eta 4 t := by linarith
      rw [mul_comm, ← div_le_iff₀ hpos, Metric.le_infDist hAne]
      intro z hz
      rw [div_le_iff₀ hpos]
      have hw : AffineMap.lineMap z (v t) (eta 4 t) ∈ A := AffineMap.lineMap_mem _ hz hvF
      calc Metric.infDist (x (t + 1)) A ≤ dist (x (t + 1)) (AffineMap.lineMap z (v t) (eta 4 t)) :=
            Metric.infDist_le_dist_of_mem hw
        _ = (1 - eta 4 t) * dist (x t) z := by
            rw [hx', AffineMap.lineMap_apply, dist_eq_norm, dist_eq_norm, vsub_eq_sub, vadd_eq_add]
            have : x t + eta 4 t • (v t - x t) - (eta 4 t • (v t - z) + z) =
                (1 - eta 4 t) • (x t - z) := by module
            rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
        _ = dist (x t) z * (1 - eta 4 t) := by ring
    have hdecay : (1 - eta 4 t) * (eta 4 t / eta 4 S) ^ 4 ≤ (eta 4 (t + 1 : ℕ) / eta 4 S) ^ 4 := by
      have h1 : eta 4 (t : ℤ) = 4 / ((t : ℝ) + 4) := by simp [eta]
      have h2 : eta 4 ((t + 1 : ℕ) : ℤ) = 4 / ((t : ℝ) + 5) := by simp [eta]; ring
      rw [div_pow, div_pow, ← mul_div_assoc, div_le_div_iff_of_pos_right (by positivity), h1, h2]
      exact fourth_power_step t (by positivity)
    calc Metric.infDist (x (t + 1)) A ≤ (1 - eta 4 t) * Metric.infDist (x t) A := hstep
      _ ≤ (1 - eta 4 t) * ((eta 4 t / eta 4 S) ^ 4 * β) :=
          mul_le_mul_of_nonneg_left ih (by linarith)
      _ = ((1 - eta 4 t) * (eta 4 t / eta 4 S) ^ 4) * β := by ring
      _ ≤ (eta 4 (t + 1 : ℕ) / eta 4 S) ^ 4 * β := mul_le_mul_of_nonneg_right hdecay hβ.le

end Lemmata.FWOpenLoop
