module

public import Lemmata.FWOpenLoop.Face
public import Lemmata.FWOpenLoop.SeqGen
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

@[expose] public section

/-!
# Minimizers in the relative interior of a face: Lemma 4.4 and Theorem 4.5

In an inner product space, the orthogonal projection `y_t` of the iterate onto the affine hull of
the optimal face is close to `x_t` (Lemma 4.3) and within `β` of `x⋆`, hence in `C`. Strong
convexity at `y_t` gives the gradient lower bound `√(α/2) √(f(y_t) - f(x⋆))` in the direction of
`y_t - x⋆`, and the Lipschitz derivative carries it back to `x_t` (Lemma 4.4). Theorem 4.5 runs the
induction of Lemma 3.5 with `ψ = 1/2` and a third case for iterates that are already very good.
-/

namespace Lemmata.FWOpenLoop

open Lemmata.FrankWolfe

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The thresholds of Lemma 4.4 are those of Lemmas 3.3 and 4.1 for the error bound
`(√(2/α), 1/2)` of an `α`-strongly convex function. -/
theorem thresholds_eq {L α β κ δ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hκ : 0 < κ) :
    max ⌈16 * L * δ ^ 2 / (α * β ^ 2)⌉₊ ⌈64 * L ^ 3 * δ ^ 4 / (α * κ ^ 2)⌉₊ =
      max ⌈8 * L * δ ^ 2 * (Real.sqrt (2 / α) / β) ^ (1 / (1 / 2 : ℝ))⌉₊
        ⌈8 * L * δ ^ 2 * (2 * Real.sqrt (2 / α) * L * δ / κ) ^ (1 / (1 / 2 : ℝ))⌉₊ := by
  have h2 : (1 / (1 / 2 : ℝ)) = 2 := by norm_num
  have hs : Real.sqrt (2 / α) ^ 2 = 2 / α := Real.sq_sqrt (by positivity)
  rw [h2, Real.rpow_two, Real.rpow_two]
  congr 2
  · rw [div_pow, hs]; field_simp; ring
  · rw [div_pow, mul_pow, mul_pow, mul_pow, hs]; field_simp; ring

/-- **Lemma 4.4.** -/
theorem scaling_cvx_bound {V F : Finset E} {f : E → ℝ} {L α β κ : ℝ} {x v : ℕ → E} {xStar : E}
    (hFV : F ⊆ V) (hsc : StrongConvexOn (convexHull ℝ (↑V : Set E)) α f) (hα : 0 < α)
    (hdiff : ∀ y ∈ convexHull ℝ (↑V : Set E), DifferentiableAt ℝ f y)
    (hsm : IsSmoothOn (convexHull ℝ (↑V : Set E)) f L) (hL : 0 < L)
    (hlip : ∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E),
      ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖)
    (hdiam : 0 < Metric.diam (convexHull ℝ (↑V : Set E)))
    (huniq : minimizers (convexHull ℝ (↑V : Set E)) f = {xStar})
    (hxF : xStar ∈ affineSpan ℝ (↑F : Set E)) (hβ : 0 < β)
    (hball : ∀ y ∈ affineSpan ℝ (↑F : Set E), ‖y - xStar‖ ≤ β → y ∈ convexHull ℝ (↑V : Set E))
    (hκ : 0 < κ) (hsc1 : ∀ p ∈ V, p ∉ F → κ ≤ fderiv ℝ f xStar (p - xStar))
    (hsc0 : ∀ p ∈ F, fderiv ℝ f xStar (p - xStar) = 0)
    (hrun : IsFWRun (convexHull ℝ (↑V : Set E)) (fderiv ℝ f) x v (fun t => eta 4 t))
    (S : ℕ) (hS : S = max ⌈16 * L * Metric.diam (convexHull ℝ (↑V : Set E)) ^ 2 / (α * β ^ 2)⌉₊
      ⌈64 * L ^ 3 * Metric.diam (convexHull ℝ (↑V : Set E)) ^ 4 / (α * κ ^ 2)⌉₊) :
    ∀ t : ℕ, S ≤ t → f (x t) - f xStar ≤ (eta 4 t / eta 4 S) ^ 4 * β *
        sSup ((fun y => ‖fderiv ℝ f y‖) '' convexHull ℝ (↑V : Set E)) ∨
      ∃ u ∈ vectorSpan ℝ (↑F : Set E), ‖u‖ ≤ 1 ∧
        √(α / 2) * √(f (x t) - f xStar) - (eta 4 t / eta 4 S) ^ 2 *
          √(α * β * sSup ((fun y => ‖fderiv ℝ f y‖) '' convexHull ℝ (↑V : Set E)) / 2) -
          (eta 4 t / eta 4 S) ^ 4 * L * β ≤ fderiv ℝ f (x t) u := by
  classical
  intro t ht
  set C := convexHull ℝ (↑V : Set E) with hCdef
  set δ := Metric.diam C with hδ
  set M := sSup ((fun y => ‖fderiv ℝ f y‖) '' C) with hM
  set A := affineSpan ℝ (↑F : Set E) with hA
  set K := vectorSpan ℝ (↑F : Set E) with hK
  have hCc : IsCompact C := V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hxs : xStar ∈ minimizers C f := by rw [huniq]; rfl
  have hconv : ConvexOn ℝ C f := strongConvexOn_zero.mp (hsc.mono hα.le)
  have heb := (Lemmata.FrankWolfe.Proof.strongConvex_heb C f α hsc hα).2
  have hθ : (1 / 2 : ℝ) ∈ Set.Ioc (0 : ℝ) (1 / 2) := ⟨by norm_num, le_rfl⟩
  have hμ : 0 < Real.sqrt (2 / α) := Real.sqrt_pos.mpr (by positivity)
  have hS' := hS.trans (thresholds_eq (L := L) (δ := δ) hα hβ hκ)
  have hxC : x t ∈ C := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hconv.1 hrun t
  set h := f (x t) - f xStar with hh
  have hh0 : 0 ≤ h := sub_nonneg.mpr (hxs.2 _ hxC)
  set r4 := (eta 4 t / eta 4 S) ^ 4 with hr4
  have hηS : 0 < eta 4 S := by simp only [eta]; push_cast; positivity
  have hηt : 0 < eta 4 t := by simp only [eta]; push_cast; positivity
  -- the gradient is bounded on `C`
  have hbdd : BddAbove ((fun y => ‖fderiv ℝ f y‖) '' C) := by
    refine ⟨‖fderiv ℝ f xStar‖ + L * δ, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have h1 := hlip z hz xStar hxs.1
    have h2 : ‖z - xStar‖ ≤ δ := by
      rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hCc.isBounded hz hxs.1
    have h3 : ‖fderiv ℝ f z‖ ≤ ‖fderiv ℝ f xStar‖ + ‖fderiv ℝ f z - fderiv ℝ f xStar‖ := by
      have := norm_add_le (fderiv ℝ f xStar) (fderiv ℝ f z - fderiv ℝ f xStar)
      rwa [add_sub_cancel] at this
    nlinarith
  have hMx : ‖fderiv ℝ f (x t)‖ ≤ M := le_csSup hbdd ⟨x t, hxC, rfl⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hMx
  by_cases hD : h ≤ r4 * β * M
  · exact Or.inl hD
  right
  replace hD := lt_of_not_ge hD
  -- the distance to the affine hull of the face, and to the minimizer
  have hdist := distance_to_face_bound hFV hconv hdiff hsm hL hlip hdiam huniq hxF heb hμ hθ hβ hκ
    hsc1 hsc0 hrun S hS' t ht
  have hnear := near_optimum_bound hCc hconv hdiff hsm hL hdiam heb hμ hθ.1 hβ hrun t
    (le_trans (by rw [hS']; exact le_max_left _ _) ht)
  rw [huniq, Metric.infDist_singleton, dist_eq_norm] at hnear
  -- the orthogonal projection onto the affine hull of the face
  have : FiniteDimensional ℝ K := finiteDimensional_vectorSpan_of_finite ℝ F.finite_toSet
  have : CompleteSpace K := FiniteDimensional.complete ℝ K
  set w := x t - xStar with hw
  set y := xStar + K.starProjection w with hy
  have hPw : K.starProjection w ∈ K := K.starProjection_apply_mem w
  have hyA : y ∈ A := by
    have : y = K.starProjection w +ᵥ xStar := by rw [hy, vadd_eq_add, add_comm]
    rw [this]
    apply AffineSubspace.vadd_mem_of_mem_direction _ hxF
    rw [hA, direction_affineSpan]; exact hPw
  have hyx : ‖y - xStar‖ ≤ β := by
    rw [hy, add_sub_cancel_left]
    exact le_trans (K.norm_starProjection_apply_le w) hnear
  have hyC : y ∈ C := hball y hyA hyx
  have hxy : ‖x t - y‖ ≤ r4 * β := by
    have e : x t - y = w - K.starProjection w := by rw [hy, hw]; abel
    rw [e, ← dist_eq_norm, K.dist_starProjection_eq_infDist]
    refine le_trans ?_ hdist
    have hAne : (A : Set E).Nonempty := ⟨xStar, hxF⟩
    rw [Metric.le_infDist hAne]
    intro a ha
    have hav : a - xStar ∈ K := by
      have := AffineSubspace.vsub_mem_direction ha hxF
      rwa [hA, direction_affineSpan, vsub_eq_sub] at this
    calc Metric.infDist w (K : Set E) ≤ dist w (a - xStar) := Metric.infDist_le_dist_of_mem hav
      _ = dist (x t) a := by rw [hw, dist_eq_norm, dist_eq_norm]; congr 1; abel
  -- the function value at the projection
  have hfy : h - r4 * β * M ≤ f y - f xStar := by
    have h1 := convexOn_add_fderiv_le hconv hxC (hdiff _ hxC) hyC
    have h2 : fderiv ℝ f (x t) (x t - y) ≤ M * (r4 * β) := by
      calc fderiv ℝ f (x t) (x t - y) ≤ ‖fderiv ℝ f (x t)‖ * ‖x t - y‖ :=
            le_trans (le_abs_self _) (by
              rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _)
        _ ≤ M * (r4 * β) := mul_le_mul hMx hxy (norm_nonneg _) hM0
    have e : fderiv ℝ f (x t) (y - x t) = -fderiv ℝ f (x t) (x t - y) := by
      rw [← map_neg, neg_sub]
    rw [e] at h1
    nlinarith
  set G := f y - f xStar with hG
  have hGpos : 0 < G := by nlinarith
  have hyne : y ≠ xStar := by
    intro e; rw [hG, e, sub_self] at hGpos; exact lt_irrefl _ hGpos
  set ρ := ‖y - xStar‖ with hρ
  have hρpos : 0 < ρ := norm_pos_iff.mpr (sub_ne_zero.mpr hyne)
  set u := ρ⁻¹ • (y - xStar) with hu
  have hyK : y - xStar ∈ K := by rw [hy, add_sub_cancel_left]; exact hPw
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hρpos.ne']
  refine ⟨u, Submodule.smul_mem _ _ hyK, hu1.le, ?_⟩
  -- strong convexity at `y`
  have hsy := strongConvexOn_add_fderiv_le hsc hyC (hdiff y hyC) hxs.1
  have e1 : fderiv ℝ f y (xStar - y) = -fderiv ℝ f y (y - xStar) := by rw [← map_neg, neg_sub]
  rw [e1, norm_sub_rev] at hsy
  have hgy : √(α / 2) * √G * ρ ≤ fderiv ℝ f y (y - xStar) := by
    have hsq : 0 ≤ (√G - √(α / 2) * ρ) ^ 2 := sq_nonneg _
    have h1 : (√G) ^ 2 = G := Real.sq_sqrt hGpos.le
    have h2 : (√(α / 2)) ^ 2 = α / 2 := Real.sq_sqrt (by positivity)
    have h3 : 0 ≤ √(α / 2) * √G * ρ := by positivity
    nlinarith
  have hgu : √(α / 2) * √G ≤ fderiv ℝ f y u := by
    rw [hu, map_smul, smul_eq_mul, le_inv_mul_iff₀ hρpos]
    linarith
  -- back to `x_t`
  have hlipxy := hlip (x t) hxC y hyC
  have hgxu : fderiv ℝ f y u - L * (r4 * β) ≤ fderiv ℝ f (x t) u := by
    have h1 : |(fderiv ℝ f (x t) - fderiv ℝ f y) u| ≤ L * (r4 * β) := by
      calc |(fderiv ℝ f (x t) - fderiv ℝ f y) u| ≤ ‖fderiv ℝ f (x t) - fderiv ℝ f y‖ * ‖u‖ := by
            rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ L * (r4 * β) := by
            rw [hu1, mul_one]
            exact le_trans hlipxy (mul_le_mul_of_nonneg_left hxy hL.le)
    rw [sub_apply] at h1
    linarith [(abs_le.mp h1).1]
  -- `√G ≥ √h - (η_t/η_S)² √(βM)`
  have hsqrtG : √h - (eta 4 t / eta 4 S) ^ 2 * √(β * M) ≤ √G := by
    have hb : √(r4 * β * M) = (eta 4 t / eta 4 S) ^ 2 * √(β * M) := by
      rw [hr4, show (eta 4 t / eta 4 S) ^ 4 * β * M = ((eta 4 t / eta 4 S) ^ 2) ^ 2 * (β * M) by
        ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [← hb]
    have h1 : √h ≤ √(h - r4 * β * M) + √(r4 * β * M) := by
      have ha0 : 0 ≤ h - r4 * β * M := by linarith
      have hb0 : 0 ≤ r4 * β * M := by positivity
      have hs0 : 0 ≤ √(h - r4 * β * M) + √(r4 * β * M) := by positivity
      calc √h ≤ √((√(h - r4 * β * M) + √(r4 * β * M)) ^ 2) := by
            apply Real.sqrt_le_sqrt
            nlinarith [Real.sq_sqrt ha0, Real.sq_sqrt hb0,
              mul_nonneg (Real.sqrt_nonneg (h - r4 * β * M)) (Real.sqrt_nonneg (r4 * β * M))]
        _ = √(h - r4 * β * M) + √(r4 * β * M) := Real.sqrt_sq hs0
    have h2 : √(h - r4 * β * M) ≤ √G := Real.sqrt_le_sqrt hfy
    linarith
  have hfin : √(α / 2) * (√h - (eta 4 t / eta 4 S) ^ 2 * √(β * M)) ≤ √(α / 2) * √G :=
    mul_le_mul_of_nonneg_left hsqrtG (by positivity)
  have e2 : √(α / 2) * √(β * M) = √(α * β * M / 2) := by
    rw [← Real.sqrt_mul (by positivity)]; congr 1; ring
  have e3 : (eta 4 t / eta 4 S) ^ 4 * L * β = L * (r4 * β) := by rw [hr4]; ring
  rw [e3]
  have : √(α / 2) * (√h - (eta 4 t / eta 4 S) ^ 2 * √(β * M)) =
      √(α / 2) * √h - (eta 4 t / eta 4 S) ^ 2 * √(α * β * M / 2) := by
    rw [← e2]; ring
  linarith

/-- The step sizes `η_t = 4/(t + 4)` decrease. -/
theorem eta4_le_of_le {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) : eta 4 (k₂ : ℤ) ≤ eta 4 (k₁ : ℤ) := by
  unfold eta
  push_cast
  have : (k₁ : ℝ) ≤ k₂ := by exact_mod_cast h
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)

set_option maxHeartbeats 1000000 in
/-- **Theorem 4.5.** -/
theorem polytope_face_bound {V F : Finset E} {f : E → ℝ} {L α β κ : ℝ} {x v : ℕ → E} {xStar : E}
    (hFV : F ⊆ V) (hsc : StrongConvexOn (convexHull ℝ (↑V : Set E)) α f) (hα : 0 < α)
    (hdiff : ∀ y ∈ convexHull ℝ (↑V : Set E), DifferentiableAt ℝ f y)
    (hsm : IsSmoothOn (convexHull ℝ (↑V : Set E)) f L) (hL : 0 < L)
    (hlip : ∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E),
      ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖)
    (hdiam : 0 < Metric.diam (convexHull ℝ (↑V : Set E)))
    (huniq : minimizers (convexHull ℝ (↑V : Set E)) f = {xStar})
    (hxF : xStar ∈ affineSpan ℝ (↑F : Set E)) (hβ : 0 < β)
    (hball : ∀ y ∈ affineSpan ℝ (↑F : Set E), ‖y - xStar‖ ≤ β → y ∈ convexHull ℝ (↑V : Set E))
    (hκ : 0 < κ) (hsc1 : ∀ p ∈ V, p ∉ F → κ ≤ fderiv ℝ f xStar (p - xStar))
    (hsc0 : ∀ p ∈ F, fderiv ℝ f xStar (p - xStar) = 0)
    (hrun : IsFWRun (convexHull ℝ (↑V : Set E)) (fderiv ℝ f) x v (fun t => eta 4 t))
    (S : ℕ) (hS : S = max ⌈16 * L * Metric.diam (convexHull ℝ (↑V : Set E)) ^ 2 / (α * β ^ 2)⌉₊
      ⌈64 * L ^ 3 * Metric.diam (convexHull ℝ (↑V : Set E)) ^ 4 / (α * κ ^ 2)⌉₊)
    (M : ℝ) (hM : M = sSup ((fun y => ‖fderiv ℝ f y‖) '' convexHull ℝ (↑V : Set E))) :
    ∀ t : ℕ, S ≤ t → f (x t) - f xStar ≤ eta 4 ((t : ℤ) - 2) ^ 2 *
      max (max ((f (x S) - f xStar) / eta 4 ((S : ℤ) - 1) ^ 2)
        ((L * Metric.diam (convexHull ℝ (↑V : Set E)) ^ 2 / 2 +
            β * √(α * β * M) / (eta 4 S * 2 * √2) + L * β ^ 2 / (eta 4 S * 2)) ^ 2 /
          (√α * β / (2 * √2)) ^ 2 +
          (L * Metric.diam (convexHull ℝ (↑V : Set E)) ^ 2 / 2 +
            β * √(α * β * M) / (eta 4 S * 2 * √2) + L * β ^ 2 / (eta 4 S * 2))))
        (β * M / eta 4 S ^ 2 + L * Metric.diam (convexHull ℝ (↑V : Set E)) ^ 2 / 2) := by
  classical
  set C := convexHull ℝ (↑V : Set E) with hCdef
  set δ := Metric.diam C with hδ
  have hCc : IsCompact C := V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hxs : xStar ∈ minimizers C f := by rw [huniq]; rfl
  have hconv : ConvexOn ℝ C f := strongConvexOn_zero.mp (hsc.mono hα.le)
  have hmem : ∀ τ, x τ ∈ C := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hconv.1 hrun
  have hh0 : ∀ τ, 0 ≤ f (x τ) - f xStar := fun τ => sub_nonneg.mpr (hxs.2 _ (hmem τ))
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact Real.sSup_nonneg (fun _ ⟨z, _, hz⟩ => hz ▸ norm_nonneg _)
  set cA := √α * β / (2 * √2) with hcA
  set cB := L * δ ^ 2 / 2 + β * √(α * β * M) / (eta 4 S * 2 * √2) + L * β ^ 2 / (eta 4 S * 2)
    with hcB
  set cD := β * M with hcD
  set cE := L * δ ^ 2 / 2 with hcE
  have hηS : 0 < eta 4 S := by simp only [eta]; push_cast; positivity
  have hcApos : 0 < cA := by positivity
  have hcB0 : 0 ≤ cB := by positivity
  have hcE0 : 0 ≤ cE := by positivity
  set P : ℕ → ℝ := fun τ => eta 4 ((τ : ℤ) - 2) * eta 4 ((τ : ℤ) - 1) with hP
  have hPpos : ∀ τ, 0 < P τ := fun τ => mul_pos (etaL_pos (by norm_num) _ (by omega))
    (etaL_pos (by norm_num) _ (by omega))
  set hS0 := f (x S) - f xStar with hhS
  have hinv : ∀ t, S ≤ t → f (x t) - f xStar ≤
      max (max (P t / P S * hS0) (P t * cB ^ 2 / cA ^ 2 + P t * cB)) (P t * (cD / eta 4 S ^ 2 + cE))
      := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
      refine le_max_of_le_left (le_max_of_le_left ?_)
      rw [div_self (hPpos S).ne', one_mul]
    | succ t ht ih =>
      set η := eta 4 (t : ℤ) with hη
      have hηpos : 0 < η := etaL_pos (by norm_num) _ (by omega)
      have hη1 : η ≤ eta 4 ((t : ℤ) - 1) := etaL_anti (by norm_num) _ (by omega)
      have hη2pos : 0 < eta 4 ((t : ℤ) - 2) := etaL_pos (by norm_num) _ (by omega)
      have hηS' : η ≤ eta 4 S := eta4_le_of_le ht
      have hPt1 : P (t + 1) = eta 4 ((t : ℤ) - 1) * η := by
        rw [hη]
        simp only [hP]
        rw [show ((t + 1 : ℕ) : ℤ) - 2 = (t : ℤ) - 1 by push_cast; ring,
          show ((t + 1 : ℕ) : ℤ) - 1 = (t : ℤ) by push_cast; ring]
      have hshift : P (t + 1) = η / eta 4 ((t : ℤ) - 2) * P t := by
        rw [hPt1]
        simp only [hP]
        rw [div_mul_eq_mul_div, eq_div_iff hη2pos.ne']
        ring
      have hsq : η ^ 2 ≤ P (t + 1) := by
        rw [hPt1, sq]; exact mul_le_mul_of_nonneg_right hη1 hηpos.le
      obtain ⟨hstep, hgap, -, -, -⟩ := basic_step hCc hconv hdiff hsm hrun hxs t
      obtain ⟨hvC, hvmin, -, -⟩ := hrun.2 t
      have hvd : ‖v t - x t‖ ^ 2 ≤ δ ^ 2 := by
        apply pow_le_pow_left₀ (norm_nonneg _)
        rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hCc.isBounded hvC (hmem t)
      set g := fderiv ℝ f (x t) (x t - v t) with hg
      set h := f (x t) - f xStar with hh
      have hprog : f (x (t + 1)) - f xStar ≤ h - η * g + η ^ 2 * cE := by
        have := mul_le_mul_of_nonneg_left hvd (by positivity : (0 : ℝ) ≤ η ^ 2 * L / 2)
        rw [hcE]; nlinarith
      have hhτ : 0 ≤ h := hh0 t
      by_cases hD : h ≤ (η / eta 4 S) ^ 4 * β * M
      · -- the iterate is already very good
        refine le_max_of_le_right ?_
        have h1 : f (x (t + 1)) - f xStar ≤ h + η ^ 2 * cE := by
          have := mul_le_mul_of_nonneg_left hgap hηpos.le; nlinarith
        have h2 : (η / eta 4 S) ^ 4 * β * M ≤ P (t + 1) * (cD / eta 4 S ^ 2) := by
          rw [hPt1, hcD]
          have h3 : η ^ 3 ≤ eta 4 ((t : ℤ) - 1) * eta 4 S ^ 2 := by
            calc η ^ 3 = η * (η * η) := by ring
              _ ≤ eta 4 ((t : ℤ) - 1) * (eta 4 S * eta 4 S) :=
                mul_le_mul hη1 (mul_le_mul hηS' hηS' hηpos.le hηS.le) (by positivity)
                  (by linarith)
              _ = eta 4 ((t : ℤ) - 1) * eta 4 S ^ 2 := by ring
          have e : (η / eta 4 S) ^ 4 * β * M =
              η ^ 3 * (η * (β * M) / eta 4 S ^ 4) := by field_simp
          rw [e]
          have e2 : eta 4 ((t : ℤ) - 1) * η * (β * M / eta 4 S ^ 2) =
              (eta 4 ((t : ℤ) - 1) * eta 4 S ^ 2) * (η * (β * M) / eta 4 S ^ 4) := by
            field_simp
          rw [e2]
          exact mul_le_mul_of_nonneg_right h3 (by positivity)
        have h3 : η ^ 2 * cE ≤ P (t + 1) * cE := mul_le_mul_of_nonneg_right hsq hcE0
        nlinarith
      · replace hD := lt_of_not_ge hD
        -- the scaling inequalities
        rcases scaling_cvx_bound hFV hsc hα hdiff hsm hL hlip hdiam huniq hxF hβ hball hκ hsc1
            hsc0 hrun S hS t ht with hD' | ⟨u, huK, hu1, hu⟩
        · rw [← hM] at hD'; linarith
        rw [← hM] at hu
        have hbor := scaling_boundary_bound hconv hdiff hxs hxF hβ hball (hmem t) hvmin huK hu1
        have hrec : f (x (t + 1)) - f xStar ≤ (1 - η / 2) * h - η * cA * √h + η ^ 2 * cB := by
          have hr : η / eta 4 S ≤ 1 := by rw [div_le_one hηS]; exact hηS'
          have hr0 : 0 ≤ η / eta 4 S := by positivity
          -- `g ≥ β f'(x_t)(u)` and the lower bound on `f'(x_t)(u)`
          have hgu : β * (√(α / 2) * √h - (η / eta 4 S) ^ 2 * √(α * β * M / 2) -
              (η / eta 4 S) ^ 4 * L * β) ≤ g := le_trans (mul_le_mul_of_nonneg_left hu hβ.le) hbor
          have hsqrt2 : √(α * β * M / 2) = √(α * β * M) / √2 := by
            rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 2)]
          have hA2 : β * √(α / 2) / 2 = cA := by
            rw [hcA, Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 2)]; ring
          have hb1 : η * β / 2 * ((η / eta 4 S) ^ 2 * √(α * β * M / 2)) ≤
              η ^ 2 * (β * √(α * β * M) / (eta 4 S * 2 * √2)) := by
            rw [hsqrt2]
            have h2pos : 0 < √2 := by positivity
            have hq : (η / eta 4 S) ^ 2 ≤ η / eta 4 S := by
              rw [sq]; exact mul_le_of_le_one_left hr0 hr
            have e : η * β / 2 * ((η / eta 4 S) ^ 2 * (√(α * β * M) / √2)) =
                (η / eta 4 S) ^ 2 * (η * β * √(α * β * M) / (2 * √2)) := by ring
            have e2 : η ^ 2 * (β * √(α * β * M) / (eta 4 S * 2 * √2)) =
                (η / eta 4 S) * (η * β * √(α * β * M) / (2 * √2)) := by field_simp
            rw [e, e2]
            exact mul_le_mul_of_nonneg_right hq (by positivity)
          have hb2 : η * β / 2 * ((η / eta 4 S) ^ 4 * L * β) ≤
              η ^ 2 * (L * β ^ 2 / (eta 4 S * 2)) := by
            have hq : (η / eta 4 S) ^ 4 ≤ η / eta 4 S := by
              calc (η / eta 4 S) ^ 4 = (η / eta 4 S) * (η / eta 4 S) ^ 3 := by ring
                _ ≤ (η / eta 4 S) * 1 :=
                    mul_le_mul_of_nonneg_left (pow_le_one₀ hr0 hr) hr0
                _ = η / eta 4 S := mul_one _
            have e : η * β / 2 * ((η / eta 4 S) ^ 4 * L * β) =
                (η / eta 4 S) ^ 4 * (η * L * β ^ 2 / 2) := by ring
            have e2 : η ^ 2 * (L * β ^ 2 / (eta 4 S * 2)) =
                (η / eta 4 S) * (η * L * β ^ 2 / 2) := by field_simp
            rw [e, e2]
            exact mul_le_mul_of_nonneg_right hq (by positivity)
          have hhg : h ≤ g := hgap
          have hmix : h / 2 + g / 2 ≤ g := by linarith
          have := mul_le_mul_of_nonneg_left hmix hηpos.le
          have h4 : η * β / 2 * (√(α / 2) * √h) = η * cA * √h := by rw [← hA2]; ring
          rw [hcB]
          nlinarith [hb1, hb2, h4, hgu]
        by_cases hsmall : h ≤ (η * cB / cA) ^ 2
        · refine le_max_of_le_left (le_max_of_le_right ?_)
          have h1 : f (x (t + 1)) - f xStar ≤ h + η ^ 2 * cB := by
            have : 0 ≤ η * cA * √h := by positivity
            nlinarith
          have h2 : (η * cB / cA) ^ 2 = η ^ 2 * cB ^ 2 / cA ^ 2 := by ring
          have h3 : η ^ 2 * cB ^ 2 / cA ^ 2 ≤ P (t + 1) * cB ^ 2 / cA ^ 2 :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsq (by positivity))
              (by positivity)
          have h4 : η ^ 2 * cB ≤ P (t + 1) * cB := mul_le_mul_of_nonneg_right hsq hcB0
          linarith
        · replace hsmall := lt_of_not_ge hsmall
          have hroot : η * cB / cA ≤ √h := by
            rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ η * cB / cA)]
            exact Real.sqrt_le_sqrt hsmall.le
          have hcancel : η ^ 2 * cB ≤ η * cA * √h := by
            have := mul_le_mul_of_nonneg_left hroot (by positivity : (0 : ℝ) ≤ η * cA)
            have e : η * cA * (η * cB / cA) = η ^ 2 * cB := by field_simp
            linarith
          have hcontr : f (x (t + 1)) - f xStar ≤ η / eta 4 ((t : ℤ) - 2) * h := by
            have := one_sub_etaL (ℓ := 4) (by norm_num) (t : ℤ) (by omega)
            have e : 1 - η / 2 = η / eta 4 ((t : ℤ) - 2) := by rw [← this]; ring
            rw [← e]; linarith
          set r := η / eta 4 ((t : ℤ) - 2) with hr
          have hr0 : 0 ≤ r := by positivity
          calc f (x (t + 1)) - f xStar ≤ r * h := hcontr
            _ ≤ r * max (max (P t / P S * hS0) (P t * cB ^ 2 / cA ^ 2 + P t * cB))
                (P t * (cD / eta 4 S ^ 2 + cE)) := mul_le_mul_of_nonneg_left ih hr0
            _ = max (max (P (t + 1) / P S * hS0) (P (t + 1) * cB ^ 2 / cA ^ 2 + P (t + 1) * cB))
                (P (t + 1) * (cD / eta 4 S ^ 2 + cE)) := by
              rw [mul_max_of_nonneg _ _ hr0, mul_max_of_nonneg _ _ hr0, hshift]
              congr 1
              · congr 1 <;> ring
              · ring
            _ ≤ _ := le_rfl
  -- the bound in the form of the theorem
  intro t ht
  refine le_trans (hinv t ht) ?_
  have hη2 : 0 < eta 4 ((t : ℤ) - 2) := etaL_pos (by norm_num) _ (by omega)
  have hanti_t : eta 4 ((t : ℤ) - 1) ≤ eta 4 ((t : ℤ) - 2) := by
    have := etaL_anti (ℓ := 4) (by norm_num) ((t : ℤ) - 1) (by omega)
    rwa [show (t : ℤ) - 1 - 1 = (t : ℤ) - 2 by ring] at this
  have hanti_S : eta 4 ((S : ℤ) - 1) ≤ eta 4 ((S : ℤ) - 2) := by
    have := etaL_anti (ℓ := 4) (by norm_num) ((S : ℤ) - 1) (by omega)
    rwa [show (S : ℤ) - 1 - 1 = (S : ℤ) - 2 by ring] at this
  have hS1 : 0 < eta 4 ((S : ℤ) - 1) := etaL_pos (by norm_num) _ (by omega)
  have hPt : P t ≤ eta 4 ((t : ℤ) - 2) ^ 2 := by
    simp only [hP]; rw [sq]; exact mul_le_mul_of_nonneg_left hanti_t hη2.le
  have hPS : eta 4 ((S : ℤ) - 1) ^ 2 ≤ P S := by
    simp only [hP]; rw [sq]; exact mul_le_mul_of_nonneg_right hanti_S hS1.le
  have hX : P t / P S * hS0 ≤ eta 4 ((t : ℤ) - 2) ^ 2 * (hS0 / eta 4 ((S : ℤ) - 1) ^ 2) := by
    have hS00 : 0 ≤ hS0 := hh0 S
    rw [div_mul_eq_mul_div, mul_div_assoc', div_le_div_iff₀ (hPpos S) (by positivity)]
    calc P t * hS0 * eta 4 ((S : ℤ) - 1) ^ 2 ≤ eta 4 ((t : ℤ) - 2) ^ 2 * hS0 * P S := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hPt hS00) hPS (by positivity)
            (by positivity)
      _ = _ := by ring
  rw [mul_max_of_nonneg _ _ (by positivity), mul_max_of_nonneg _ _ (by positivity)]
  apply max_le_max (max_le_max hX ?_) ?_
  · have : P t * cB ^ 2 / cA ^ 2 + P t * cB = P t * (cB ^ 2 / cA ^ 2 + cB) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hPt (by positivity)
  · exact mul_le_mul_of_nonneg_right hPt (by positivity)

end

namespace Proof

theorem active_set_identification : ActiveSetIdentification.{u} := by
  intro E _ _ V F f L μ θ κ x v xStar hFV hconv hdiff hsm hL hlip hdiam huniq heb hμ hθ hκ hsc1
    hsc0 hrun t ht
  exact active_set_bound hFV hconv hdiff hsm hL hlip hdiam huniq heb hμ hθ hκ hsc1 hsc0 hrun t ht

theorem scaling_boundary : ScalingBoundary.{u} := by
  intro E _ _ V F f β xStar hconv hdiff hxs hxF hβ hball x hx p _ hpmin u hu hu1
  exact scaling_boundary_bound hconv hdiff hxs hxF hβ hball hx hpmin hu hu1

theorem distance_to_face : DistanceToFace.{u} := by
  intro E _ _ V F f L μ θ β κ x v xStar hFV hconv hdiff hsm hL hlip hdiam huniq hxF heb hμ hθ hβ
    hκ hsc1 hsc0 hrun δ S t ht
  exact distance_to_face_bound hFV hconv hdiff hsm hL hlip hdiam huniq hxF heb hμ hθ hβ hκ hsc1
    hsc0 hrun S rfl t ht

theorem scaling_cvx : ScalingCVX.{u} := by
  intro E _ _ V F f L α β κ x v xStar hFV hsc hα hdiff hsm hL hlip hdiam huniq hxF hβ hball hκ
    hsc1 hsc0 hrun δ M S t ht
  exact scaling_cvx_bound hFV hsc hα hdiff hsm hL hlip hdiam huniq hxF hβ hball hκ hsc1 hsc0 hrun
    S rfl t ht

theorem polytope_face_rate : PolytopeFaceRate.{u} := by
  intro E _ _ V F f L α β κ x v xStar hFV hsc hα hdiff hsm hL hlip hdiam huniq hxF hβ hball hκ
    hsc1 hsc0 hrun δ M S cA cB cD cE t ht
  exact polytope_face_bound hFV hsc hα hdiff hsm hL hlip hdiam huniq hxF hβ hball hκ hsc1 hsc0
    hrun S rfl M rfl t ht

end Proof

end Lemmata.FWOpenLoop
