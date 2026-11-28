module

public import Lemmata.FWProduct.Width
public import Lemmata.AwayStepFW.Main
public import Lemmata.CGImprovements.Main

@[expose] public section

/-!
# The pyramidal width of a product, upper bound (Theorem 4.5), and linear rates (Proposition 4.8)

The facial distance of a polytope with at least two vertices is attained: it is an infimum over
finitely many faces of compact sets of distances. For minimizing pairs `(p₁, q₁)` and `(p₂, q₂)` of
the factors, at distances `δ₁, δ₂`, the points `p = (p₁, p₂)` and
`q = θ (p₁, q₂) + (1 - θ) (q₁, p₂)` with `θ = δ₁²/(δ₁² + δ₂²)` lie in the face exposed by
`(ψ₁, ψ₂)` and in the hull of the remaining vertices, at distance `√(δ₁² δ₂²/(δ₁² + δ₂²))`.

The lower bound and the facial distance scaling of the away-step entry give a scaling constant
for the product, and the sharpness rate of away-step Frank–Wolfe applies under quadratic growth.
-/

namespace Lemmata.FWProduct

open Lemmata.FrankWolfe Lemmata.AwayStepFW Lemmata.CGImprovements

universe u

section Generic

variable {E : Type u} [NormedAddCommGroup E]

/-- Two distinct points give a proper exposed face. -/
theorem exists_proper_face [InnerProductSpace ℝ E] {V : Finset E} (h : 1 < V.card) :
    ∃ ψ : StrongDual ℝ E, exposedFace V ψ ≠ V := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h
  refine ⟨innerSL ℝ (a - b), fun heq => ?_⟩
  have hbF : b ∈ exposedFace V (innerSL ℝ (a - b)) := by rw [heq]; exact hb
  simp only [exposedFace, Finset.mem_filter] at hbF
  have h1 := hbF.2 a ha
  simp only [innerSL_apply_apply] at h1
  have h2 : ‖a - b‖ ^ 2 ≤ 0 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_right]; linarith
  have h3 : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
  exact hab (sub_eq_zero.mp (norm_eq_zero.mp h3))

variable [NormedSpace ℝ E]

open Classical in
/-- The facial distance of a polytope with a proper face is attained. -/
theorem facialDistance_attained {V : Finset E} (hex : ∃ ψ : StrongDual ℝ E, exposedFace V ψ ≠ V) :
    ∃ ψ : StrongDual ℝ E, exposedFace V ψ ≠ V ∧
      ∃ p ∈ convexHull ℝ (↑(exposedFace V ψ) : Set E),
        ∃ q ∈ convexHull ℝ (↑(V \ exposedFace V ψ) : Set E), ‖p - q‖ = facialDistance V := by
  set S : Set ℝ := {r : ℝ | ∃ ψ : StrongDual ℝ E, exposedFace V ψ ≠ V ∧
    ∃ p ∈ convexHull ℝ (↑(exposedFace V ψ) : Set E),
      ∃ q ∈ convexHull ℝ (↑(V \ exposedFace V ψ) : Set E), r = ‖p - q‖} with hS
  have hfd : facialDistance V = sInf S := rfl
  set 𝓕 : Finset (Finset E) :=
    V.powerset.filter (fun F => ∃ ψ : StrongDual ℝ E, exposedFace V ψ = F ∧ F ≠ V) with h𝓕
  set T : Finset E → Set ℝ := fun F => (fun z : E × E => ‖z.1 - z.2‖) ''
    (convexHull ℝ (↑F : Set E) ×ˢ convexHull ℝ (↑(V \ F) : Set E)) with hT
  have hS' : S = ⋃ F ∈ 𝓕, T F := by
    ext r
    constructor
    · rintro ⟨ψ, hψ, p, hp, q, hq, rfl⟩
      refine Set.mem_iUnion₂.mpr ⟨exposedFace V ψ, ?_, (p, q), ⟨hp, hq⟩, rfl⟩
      rw [h𝓕, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨exposedFace_subset V ψ, ψ, rfl, hψ⟩
    · intro hr
      obtain ⟨F, hF, z, ⟨hp, hq⟩, rfl⟩ := Set.mem_iUnion₂.mp hr
      rw [h𝓕, Finset.mem_filter] at hF
      obtain ⟨-, ψ, rfl, hψ⟩ := hF
      exact ⟨ψ, hψ, z.1, hp, z.2, hq, rfl⟩
  have hcpt : IsCompact S := by
    rw [hS']
    refine Finset.isCompact_biUnion 𝓕 (fun F _ => ?_)
    exact ((Set.Finite.isCompact_convexHull (𝕜 := ℝ) F.finite_toSet).prod
      (Set.Finite.isCompact_convexHull (𝕜 := ℝ) (V \ F).finite_toSet)).image
      (continuous_norm.comp (continuous_fst.sub continuous_snd))
  obtain ⟨ψ, hψ⟩ := hex
  have hV : V.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    exact hψ (Finset.subset_empty.mp (exposedFace_subset _ ψ))
  obtain ⟨p, hp⟩ := Proof.exposedFace_nonempty hV ψ
  obtain ⟨q, hq⟩ := sdiff_exposedFace_nonempty hψ
  have hne : S.Nonempty := ⟨_, ψ, hψ, p, subset_convexHull ℝ _ (Finset.mem_coe.mpr hp), q,
    subset_convexHull ℝ _ (Finset.mem_coe.mpr hq), rfl⟩
  obtain ⟨φ, hφ, p', hp', q', hq', heq⟩ := hcpt.sInf_mem hne
  exact ⟨φ, hφ, p', hp', q', hq', by rw [hfd, heq]⟩

/-- A scaling constant can be decreased. -/
theorem isScaling_mono {V : Finset E} {δ δ' : ℝ} (h : IsScaling V δ) (h0 : 0 ≤ δ')
    (hle : δ' ≤ δ) : IsScaling V δ' := by
  intro S hS x hx y hy ψ a ha hamax v hv hvmin
  have key := h S hS x hx y hy ψ a ha hamax v hv hvmin
  rcases le_total 0 (ψ (x - y)) with hpos | hneg
  · calc δ' * ψ (x - y) ≤ δ * ψ (x - y) := mul_le_mul_of_nonneg_right hle hpos
      _ ≤ ψ (a - v) * ‖x - y‖ := key
  · have h1 : δ' * ψ (x - y) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h0 hneg
    have hxa : ψ x ≤ ψ a := le_on_hull ψ (fun w hw => hamax w hw) x hx
    have hxv : ψ v ≤ ψ x := ge_on_hull' ψ (fun w hw => hvmin w hw) x
      (convexHull_mono (Finset.coe_subset.mpr hS) hx)
    have h2 : 0 ≤ ψ (a - v) * ‖x - y‖ := by
      rw [map_sub]; exact mul_nonneg (by linarith) (norm_nonneg _)
    linarith

end Generic

section Product

variable {E₁ E₂ : Type u} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [NormedAddCommGroup E₂]
  [InnerProductSpace ℝ E₂]

/-- Products of convex combinations are convex combinations of products. -/
theorem toLp_mem_convexHull {A : Finset E₁} {B : Finset E₂} {T : Set (WithLp 2 (E₁ × E₂))}
    (hT : ∀ a ∈ A, ∀ b ∈ B, WithLp.toLp 2 (a, b) ∈ T) {x : E₁} {y : E₂}
    (hx : x ∈ convexHull ℝ (↑A : Set E₁)) (hy : y ∈ convexHull ℝ (↑B : Set E₂)) :
    WithLp.toLp 2 (x, y) ∈ convexHull ℝ T := by
  have h1 : (x, y) ∈ convexHull ℝ ((↑A : Set E₁) ×ˢ (↑B : Set E₂)) := by
    rw [convexHull_prod]; exact ⟨hx, hy⟩
  have h2 := Set.mem_image_of_mem (WithLp.linearEquiv 2 ℝ (E₁ × E₂)).symm.toLinearMap h1
  rw [LinearMap.image_convexHull] at h2
  refine convexHull_mono ?_ h2
  rintro z ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
  exact hT a ha b hb

open Classical in
theorem product_width_upper_bound {V₁ : Finset E₁} {V₂ : Finset E₂} (h1 : 1 < V₁.card)
    (h2 : 1 < V₂.card) :
    facialDistance (productVertices V₁ V₂) ≤
      Real.sqrt (facialDistance V₁ ^ 2 * facialDistance V₂ ^ 2 /
        (facialDistance V₁ ^ 2 + facialDistance V₂ ^ 2)) := by
  obtain ⟨ψ₁, hψ₁, p₁, hp₁, q₁, hq₁, hd₁⟩ := facialDistance_attained (exists_proper_face h1)
  obtain ⟨ψ₂, hψ₂, p₂, hp₂, q₂, hq₂, hd₂⟩ := facialDistance_attained (exists_proper_face h2)
  set w₁ := facialDistance V₁ with hw₁
  set w₂ := facialDistance V₂ with hw₂
  set V := productVertices V₁ V₂ with hV
  set Ψ : StrongDual ℝ (WithLp 2 (E₁ × E₂)) := fstL ψ₁ + sndL ψ₂ with hΨ
  have hc1 : Ψ.comp inl₁ = ψ₁ := by
    ext a; simp [hΨ, fstL, sndL, inl₁]
  have hc2 : Ψ.comp inr₂ = ψ₂ := by
    ext b; simp [hΨ, fstL, sndL, inr₂]
  set F₁ := exposedFace V₁ ψ₁ with hF₁
  set F₂ := exposedFace V₂ ψ₂ with hF₂
  set F := exposedFace V Ψ with hF
  have hmem : ∀ a ∈ V₁, ∀ b ∈ V₂, WithLp.toLp 2 (a, b) ∈ F ↔ a ∈ F₁ ∧ b ∈ F₂ := by
    intro a ha b hb
    rw [hF, mem_face_iff Ψ ha hb, hc1, hc2]
  have hFV : F ≠ V := by
    obtain ⟨a, ha⟩ := sdiff_exposedFace_nonempty hψ₁
    rw [Finset.mem_sdiff] at ha
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < V₂.card)
    intro h
    have hab : WithLp.toLp 2 (a, b) ∈ F := by
      rw [h]; exact mem_productVertices.mpr ⟨a, ha.1, b, hb, rfl⟩
    exact ha.2 ((hmem a ha.1 b hb).mp hab).1
  -- the points
  have hp : WithLp.toLp 2 (p₁, p₂) ∈ convexHull ℝ (↑F : Set (WithLp 2 (E₁ × E₂))) := by
    refine toLp_mem_convexHull (A := F₁) (B := F₂) (fun a ha b hb => ?_) hp₁ hp₂
    have ha' := exposedFace_subset V₁ ψ₁ ha
    have hb' := exposedFace_subset V₂ ψ₂ hb
    exact Finset.mem_coe.mpr ((hmem a ha' b hb').mpr ⟨ha, hb⟩)
  have hqa : WithLp.toLp 2 (p₁, q₂) ∈ convexHull ℝ (↑(V \ F) : Set (WithLp 2 (E₁ × E₂))) := by
    refine toLp_mem_convexHull (A := F₁) (B := V₂ \ F₂) (fun a ha b hb => ?_) hp₁ hq₂
    rw [Finset.mem_sdiff] at hb
    have ha' := exposedFace_subset V₁ ψ₁ ha
    refine Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨mem_productVertices.mpr
      ⟨a, ha', b, hb.1, rfl⟩, fun h => hb.2 ((hmem a ha' b hb.1).mp h).2⟩)
  have hqb : WithLp.toLp 2 (q₁, p₂) ∈ convexHull ℝ (↑(V \ F) : Set (WithLp 2 (E₁ × E₂))) := by
    refine toLp_mem_convexHull (A := V₁ \ F₁) (B := F₂) (fun a ha b hb => ?_) hq₁ hp₂
    rw [Finset.mem_sdiff] at ha
    have hb' := exposedFace_subset V₂ ψ₂ hb
    refine Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨mem_productVertices.mpr
      ⟨a, ha.1, b, hb', rfl⟩, fun h => ha.2 ((hmem a ha.1 b hb').mp h).1⟩)
  set s := w₁ ^ 2 + w₂ ^ 2 with hs
  set θ := w₁ ^ 2 / s with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by
    rcases (show (0 : ℝ) ≤ s by positivity).eq_or_lt with h0 | hpos
    · rw [hθ, ← h0, div_zero]; norm_num
    · rw [hθ, div_le_one hpos]; nlinarith [sq_nonneg w₂]
  set q : WithLp 2 (E₁ × E₂) :=
    θ • WithLp.toLp 2 (p₁, q₂) + (1 - θ) • WithLp.toLp 2 (q₁, p₂) with hq
  have hqmem : q ∈ convexHull ℝ (↑(V \ F) : Set (WithLp 2 (E₁ × E₂))) :=
    convex_convexHull ℝ _ hqa hqb hθ0 (by linarith) (by ring)
  -- the distance
  have hfst : (WithLp.toLp 2 (p₁, p₂) - q).fst = (1 - θ) • (p₁ - q₁) := by
    simp only [hq, WithLp.sub_fst, WithLp.add_fst, WithLp.smul_fst, WithLp.toLp_fst, smul_sub,
      sub_smul, one_smul]
    abel
  have hsnd : (WithLp.toLp 2 (p₁, p₂) - q).snd = θ • (p₂ - q₂) := by
    simp only [hq, WithLp.sub_snd, WithLp.add_snd, WithLp.smul_snd, WithLp.toLp_snd, smul_sub,
      sub_smul, one_smul]
    abel
  have hsq : ‖WithLp.toLp 2 (p₁, p₂) - q‖ ^ 2 = w₁ ^ 2 * w₂ ^ 2 / (w₁ ^ 2 + w₂ ^ 2) := by
    rw [WithLp.prod_norm_sq_eq_of_L2, hfst, hsnd, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - θ), abs_of_nonneg hθ0, hd₁,
      hd₂]
    rcases (show (0 : ℝ) ≤ s by positivity).eq_or_lt with h0 | hpos
    · have hw1 : w₁ = 0 := by nlinarith [sq_nonneg w₁, sq_nonneg w₂]
      have hw2 : w₂ = 0 := by nlinarith [sq_nonneg w₁, sq_nonneg w₂]
      rw [hw1, hw2]; simp
    · have hs0 : w₁ ^ 2 + w₂ ^ 2 ≠ 0 := by rw [← hs]; exact hpos.ne'
      rw [hθ, hs]
      field_simp
      ring
  have hnorm : ‖WithLp.toLp 2 (p₁, p₂) - q‖ =
      Real.sqrt (w₁ ^ 2 * w₂ ^ 2 / (w₁ ^ 2 + w₂ ^ 2)) := by
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  calc facialDistance V ≤ ‖WithLp.toLp 2 (p₁, p₂) - q‖ :=
        Proof.facialDistance_le hFV hp (by convert hqmem)
    _ = _ := hnorm

end Product

section Rate

variable {E₁ E₂ : Type u} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]

instance : FiniteDimensional ℝ (WithLp 2 (E₁ × E₂)) :=
  LinearEquiv.finiteDimensional (WithLp.linearEquiv 2 ℝ (E₁ × E₂)).symm

omit [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁] [InnerProductSpace ℝ E₂]
  [FiniteDimensional ℝ E₂] in
theorem nonempty_of_width_pos {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : Finset E} (hw : 0 < affinePyramidalWidth V) : V.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  subst h
  rw [affinePyramidalWidth_eq_zero (fun φ => Finset.subset_empty.mp (exposedFace_subset _ φ))]
    at hw
  exact lt_irrefl 0 hw

theorem product_away_linear_bound (V₁ : Finset E₁) (V₂ : Finset E₂) (f : WithLp 2 (E₁ × E₂) → ℝ)
    (L : NNReal) (μ : ℝ) (x : ℕ → WithLp 2 (E₁ × E₂)) (S : ℕ → Finset (WithLp 2 (E₁ × E₂)))
    (lam : ℕ → WithLp 2 (E₁ × E₂) → ℝ) (hL : 0 < (L : ℝ)) (hμ : 0 < μ)
    (hw₁ : 0 < affinePyramidalWidth V₁) (hw₂ : 0 < affinePyramidalWidth V₂)
    (hconv : ConvexOn ℝ Set.univ f) (hsm : IsSmooth f L)
    (hqg : ∀ y ∈ convexHull ℝ (↑(productVertices V₁ V₂) : Set (WithLp 2 (E₁ × E₂))),
      ∀ xStar ∈ minimizers (convexHull ℝ (↑(productVertices V₁ V₂) : Set (WithLp 2 (E₁ × E₂)))) f,
        μ / 2 * Metric.infDist y
          (minimizers (convexHull ℝ (↑(productVertices V₁ V₂) : Set (WithLp 2 (E₁ × E₂)))) f) ^ 2 ≤
          f y - f xStar)
    (hrun : IsAFWRun (productVertices V₁ V₂) f L x S lam) :
    ∀ xStar ∈ minimizers (convexHull ℝ (↑(productVertices V₁ V₂) : Set (WithLp 2 (E₁ × E₂)))) f,
    ∀ t : ℕ, 1 ≤ t →
      f (x t) - f xStar ≤
        (1 - min (1 / 2) (μ * (affinePyramidalWidth V₁ ^ 2 * affinePyramidalWidth V₂ ^ 2 /
            (affinePyramidalWidth V₁ ^ 2 + affinePyramidalWidth V₂ ^ 2)) /
          (16 * L * Metric.diam (↑(productVertices V₁ V₂) : Set (WithLp 2 (E₁ × E₂))) ^ 2))) ^
            ((t - 1) / 2) *
          (L * Metric.diam (↑(productVertices V₁ V₂) : Set (WithLp 2 (E₁ × E₂))) ^ 2 / 2) := by
  intro xStar hxs t ht
  set V := productVertices V₁ V₂ with hV
  set C := convexHull ℝ (↑V : Set (WithLp 2 (E₁ × E₂))) with hC
  set D := Metric.diam (↑V : Set (WithLp 2 (E₁ × E₂))) with hD
  set α2 := affinePyramidalWidth V₁ ^ 2 * affinePyramidalWidth V₂ ^ 2 /
    (affinePyramidalWidth V₁ ^ 2 + affinePyramidalWidth V₂ ^ 2) with hα2
  have hα20 : 0 < α2 := by positivity
  set α := Real.sqrt α2 with hα
  have hα0 : 0 < α := Real.sqrt_pos.mpr hα20
  have hαsq : α ^ 2 = α2 := Real.sq_sqrt hα20.le
  have hlow : α ≤ facialDistance V :=
    product_width_lower_bound (nonempty_of_width_pos hw₁) (nonempty_of_width_pos hw₂)
  have hscal : IsScaling V α := isScaling_mono (facial_distance_is_scaling V) hα0.le hlow
  set c := Real.sqrt (2 / μ) with hc
  have hc0 : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hsharp : IsSharp C f c (1 / 2) := by
    intro y hy z hz
    have hq := hqg y hy z hz
    have hd0 : 0 ≤ Metric.infDist y (minimizers C f) := Metric.infDist_nonneg
    have hh0 : 0 ≤ f y - f z := sub_nonneg.mpr (hz.2 y hy)
    rw [← Real.sqrt_eq_rpow, hc, ← Real.sqrt_mul (by positivity)]
    rw [Real.le_sqrt hd0 (by positivity)]
    have : Metric.infDist y (minimizers C f) ^ 2 ≤ 2 / μ * (f y - f z) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hμ]; linarith
    exact this
  have h := sharp_away_linear V f L c α x S lam hL hc0 hα0 hscal hconv hsm hsharp hrun xStar hxs t
    ht
  have e : α ^ 2 / (8 * c ^ 2 * L * D ^ 2) = μ * α2 / (16 * L * D ^ 2) := by
    rw [hαsq, hc, Real.sq_sqrt (show (0 : ℝ) ≤ 2 / μ by positivity)]
    rcases eq_or_ne D 0 with hD0 | hD0
    · rw [hD0]; simp
    · field_simp
      ring
  rw [e] at h
  exact h

end Rate

namespace Proof

theorem product_width_upper : ProductWidthUpperBound.{u} := by
  intro E₁ E₂ _ _ _ _ V₁ V₂ h1 h2
  exact product_width_upper_bound h1 h2

theorem product_away_linear : ProductAwayLinear.{u} := by
  intro E₁ E₂ _ _ _ _ _ _ V₁ V₂ f L μ x S lam hL hμ hw₁ hw₂ hconv hsm hqg hrun
  exact product_away_linear_bound V₁ V₂ f L μ x S lam hL hμ hw₁ hw₂ hconv hsm hqg hrun

end Proof

end Lemmata.FWProduct
