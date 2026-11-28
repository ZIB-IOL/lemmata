module

public import Lemmata.FWProduct.Separation
public import Lemmata.AwayStepFW.PyramidalEq
public import Lemmata.AwayStepFW.FacialDistance

@[expose] public section

/-!
# The pyramidal width of a product (Theorem 4.5, lower bound)

An exposed face of the product `conv V₁ × conv V₂` for a functional `ψ = (ψ₁, ψ₂)` is the product
`F₁ × F₂` of the exposed faces of the factors. For each proper factor face, the separation lemma
gives a unit vector separating its affine hull from the remaining vertices with margin at least the
affine pyramidal width `ŵᵢ`, and it is constant on the face. If both factor faces are proper, the
normalized combination `((π₁/γ₁ + π₂/γ₂) - 1)/√(1/γ₁² + 1/γ₂²)` of the two separating functionals
equals `1/√(1/γ₁² + 1/γ₂²)` on the face and is nonpositive on the remaining vertices; if one factor
face is the whole factor, the other separating functional alone gives the margin `ŵᵢ`.
-/

namespace Lemmata.FWProduct

open Lemmata.FrankWolfe Lemmata.AwayStepFW

universe u

section Generic

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affinePyramidalWidth_nonneg (V : Finset E) : 0 ≤ affinePyramidalWidth V := by
  unfold affinePyramidalWidth
  exact Real.sInf_nonneg (fun r ⟨_, _, _, _, _, _, hr⟩ => hr ▸ norm_nonneg _)

open Classical in
theorem affinePyramidalWidth_le {V : Finset E} {ψ : StrongDual ℝ E} (hF : exposedFace V ψ ≠ V)
    {a q : E} (ha : a ∈ affineSpan ℝ (↑(exposedFace V ψ) : Set E))
    (hq : q ∈ convexHull ℝ (↑(V \ exposedFace V ψ) : Set E)) :
    affinePyramidalWidth V ≤ ‖a - q‖ := by
  classical
  unfold affinePyramidalWidth
  refine csInf_le ⟨0, fun r ⟨_, _, _, _, _, _, hr⟩ => hr ▸ norm_nonneg _⟩ ?_
  exact ⟨ψ, hF, a, ha, q, hq, rfl⟩

open Classical in
theorem sdiff_exposedFace_nonempty {V : Finset E} {ψ : StrongDual ℝ E}
    (hF : exposedFace V ψ ≠ V) : (V \ exposedFace V ψ).Nonempty := by
  rw [Finset.sdiff_nonempty]
  intro h
  exact hF (Finset.Subset.antisymm (exposedFace_subset V ψ) h)

theorem affine_le_facial (V : Finset E) : affinePyramidalWidth V ≤ facialDistance V := by
  classical
  by_cases hex : ∃ ψ : StrongDual ℝ E, exposedFace V ψ ≠ V
  · obtain ⟨ψ, hF⟩ := hex
    have hV : V.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      subst h
      exact hF (Finset.subset_empty.mp (exposedFace_subset _ ψ))
    obtain ⟨p, hp⟩ := Proof.exposedFace_nonempty hV ψ
    obtain ⟨q, hq⟩ := sdiff_exposedFace_nonempty hF
    unfold facialDistance
    refine le_csInf ⟨‖p - q‖, ψ, hF, p, subset_convexHull ℝ _ (Finset.mem_coe.mpr hp), q,
      subset_convexHull ℝ _ (Finset.mem_coe.mpr hq), rfl⟩ ?_
    rintro r ⟨φ, hφ, p', hp', q', hq', rfl⟩
    exact affinePyramidalWidth_le hφ (convexHull_subset_affineSpan _ hp') hq'
  · push Not at hex
    have : affinePyramidalWidth V = 0 := by
      unfold affinePyramidalWidth
      have hempty : {r : ℝ | ∃ ψ : StrongDual ℝ E, exposedFace V ψ ≠ V ∧
          ∃ a ∈ affineSpan ℝ (↑(exposedFace V ψ) : Set E),
            ∃ q ∈ convexHull ℝ (↑(V \ exposedFace V ψ) : Set E), r = ‖a - q‖} = ∅ := by
        apply Set.eq_empty_of_forall_notMem
        rintro r ⟨ψ, hψ, -⟩
        exact hψ (hex ψ)
      rw [hempty, Real.sInf_empty]
    rw [this]
    exact Proof.facialDistance_nonneg V

/-- An affine functional bounded on a finite set is bounded on its convex hull. -/
theorem le_on_hull {S : Finset E} (g : StrongDual ℝ E) {c : ℝ} (h : ∀ x ∈ S, g x ≤ c) :
    ∀ x ∈ convexHull ℝ (↑S : Set E), g x ≤ c := fun _ hx =>
  convexHull_min (fun y hy => h y hy) (convex_halfSpace_le g.toLinearMap.isLinear c) hx

theorem ge_on_hull' {S : Finset E} (g : StrongDual ℝ E) {c : ℝ} (h : ∀ x ∈ S, c ≤ g x) :
    ∀ x ∈ convexHull ℝ (↑S : Set E), c ≤ g x := fun _ hx =>
  convexHull_min (fun y hy => h y hy) (convex_halfSpace_ge g.toLinearMap.isLinear c) hx

end Generic

section Factor

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open Classical in
/-- The separating data of a proper face: `⟨w, ·⟩ - β` equals `γ ≥ ŵ` on the face and is
nonpositive on the remaining vertices. -/
theorem factor_data {V : Finset E} {φ : StrongDual ℝ E} (hV : V.Nonempty)
    (hF : exposedFace V φ ≠ V) :
    ∃ w : E, ‖w‖ ≤ 1 ∧ ∃ β γ : ℝ, affinePyramidalWidth V ≤ γ ∧
      (∀ a ∈ exposedFace V φ, inner ℝ w a - β = γ) ∧
      ∀ q ∈ V \ exposedFace V φ, inner ℝ w q - β ≤ 0 := by
  classical
  set F := exposedFace V φ with hFdef
  have hFne : F.Nonempty := Proof.exposedFace_nonempty hV φ
  have hK : (V \ F).Nonempty := sdiff_exposedFace_nonempty hF
  set wd := affinePyramidalWidth V with hwd
  obtain ⟨w, hw1, hsep⟩ := exists_separation hFne hK (δ := wd)
    (fun a ha q hq => affinePyramidalWidth_le hF ha hq)
  obtain ⟨q₀, hq₀⟩ := hK
  have hq₀c : q₀ ∈ convexHull ℝ (↑(V \ F) : Set E) := subset_convexHull ℝ _ (Finset.mem_coe.mpr hq₀)
  -- `⟨w, ·⟩` is constant on the face
  have hconst : ∀ a ∈ F, ∀ a' ∈ F, inner ℝ w a = inner ℝ w a' := by
    intro a ha a' ha'
    by_contra hne
    set c := inner ℝ w (a - a') with hc
    have hc0 : c ≠ 0 := by rw [hc, inner_sub_right]; exact sub_ne_zero.mpr hne
    have haA : a ∈ affineSpan ℝ (↑F : Set E) := subset_affineSpan ℝ _ (Finset.mem_coe.mpr ha)
    have ha'A : a' ∈ affineSpan ℝ (↑F : Set E) := subset_affineSpan ℝ _ (Finset.mem_coe.mpr ha')
    set s := (wd - inner ℝ w (a - q₀) - 1) / c with hs
    have hmem := AffineSubspace.smul_vsub_vadd_mem _ s haA ha'A haA
    have h := hsep _ hmem q₀ hq₀c
    have e : inner ℝ w ((s • (a -ᵥ a') +ᵥ a) - q₀) = inner ℝ w (a - q₀) + s * c := by
      rw [vsub_eq_sub, vadd_eq_add, show s • (a - a') + a - q₀ = (a - q₀) + s • (a - a') by abel,
        inner_add_right, inner_smul_right]
    rw [e, hs, div_mul_cancel₀ _ hc0] at h
    linarith
  obtain ⟨a₀, ha₀⟩ := hFne
  set β := (V \ F).sup' ⟨q₀, hq₀⟩ (fun q => inner ℝ w q) with hβ
  obtain ⟨qm, hqm, hqmeq⟩ := Finset.exists_mem_eq_sup' ⟨q₀, hq₀⟩ (fun q => inner ℝ w q)
  refine ⟨w, hw1, β, inner ℝ w a₀ - β, ?_, fun a ha => by rw [hconst a ha a₀ ha₀], fun q hq => ?_⟩
  · have h := hsep a₀ (subset_affineSpan ℝ _ (Finset.mem_coe.mpr ha₀)) qm
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr hqm))
    rw [inner_sub_right, ← hqmeq] at h
    exact h
  · have := Finset.le_sup' (fun q => inner ℝ w q) hq
    rw [← hβ] at this
    linarith

end Factor

section Product

variable {E₁ E₂ : Type u} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [NormedAddCommGroup E₂]
  [InnerProductSpace ℝ E₂]

/-- The inclusion of the first factor. -/
noncomputable def inl₁ : E₁ →L[ℝ] WithLp 2 (E₁ × E₂) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ E₁ E₂)

/-- The inclusion of the second factor. -/
noncomputable def inr₂ : E₂ →L[ℝ] WithLp 2 (E₁ × E₂) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ E₁ E₂)

/-- The first coordinate. -/
noncomputable def fstL : StrongDual ℝ E₁ → StrongDual ℝ (WithLp 2 (E₁ × E₂)) := fun g =>
  g.comp ((ContinuousLinearMap.fst ℝ E₁ E₂).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).toContinuousLinearMap)

/-- The second coordinate. -/
noncomputable def sndL : StrongDual ℝ E₂ → StrongDual ℝ (WithLp 2 (E₁ × E₂)) := fun g =>
  g.comp ((ContinuousLinearMap.snd ℝ E₁ E₂).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).toContinuousLinearMap)

theorem fstL_apply (g : StrongDual ℝ E₁) (x : WithLp 2 (E₁ × E₂)) : fstL g x = g x.fst := rfl

theorem sndL_apply (g : StrongDual ℝ E₂) (x : WithLp 2 (E₁ × E₂)) : sndL g x = g x.snd := rfl

theorem split (ψ : StrongDual ℝ (WithLp 2 (E₁ × E₂))) (a : E₁) (b : E₂) :
    ψ (WithLp.toLp 2 (a, b)) = ψ.comp inl₁ a + ψ.comp inr₂ b := by
  have : WithLp.toLp 2 (a, b) = inl₁ a + inr₂ b := by
    show WithLp.toLp 2 (a, b) = WithLp.toLp 2 (a, 0) + WithLp.toLp 2 (0, b)
    rw [← WithLp.toLp_add]; simp
  rw [this, map_add]; rfl

omit [InnerProductSpace ℝ E₁] [InnerProductSpace ℝ E₂] in
theorem mem_productVertices {V₁ : Finset E₁} {V₂ : Finset E₂} {x : WithLp 2 (E₁ × E₂)} :
    x ∈ productVertices V₁ V₂ ↔ ∃ a ∈ V₁, ∃ b ∈ V₂, WithLp.toLp 2 (a, b) = x := by
  classical
  simp only [productVertices, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, b, ⟨ha, hb⟩, rfl⟩

theorem mem_face_iff {V₁ : Finset E₁} {V₂ : Finset E₂} (ψ : StrongDual ℝ (WithLp 2 (E₁ × E₂)))
    {a : E₁} {b : E₂} (ha : a ∈ V₁) (hb : b ∈ V₂) :
    WithLp.toLp 2 (a, b) ∈ exposedFace (productVertices V₁ V₂) ψ ↔
      a ∈ exposedFace V₁ (ψ.comp inl₁) ∧ b ∈ exposedFace V₂ (ψ.comp inr₂) := by
  classical
  simp only [exposedFace, Finset.mem_filter]
  constructor
  · rintro ⟨-, h⟩
    refine ⟨⟨ha, fun u hu => ?_⟩, ⟨hb, fun u hu => ?_⟩⟩
    · have := h (WithLp.toLp 2 (u, b)) (mem_productVertices.mpr ⟨u, hu, b, hb, rfl⟩)
      rw [split, split] at this; linarith
    · have := h (WithLp.toLp 2 (a, u)) (mem_productVertices.mpr ⟨a, ha, u, hu, rfl⟩)
      rw [split, split] at this; linarith
  · rintro ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
    refine ⟨mem_productVertices.mpr ⟨a, ha, b, hb, rfl⟩, fun x hx => ?_⟩
    obtain ⟨u, hu, w, hw, rfl⟩ := mem_productVertices.mp hx
    rw [split, split]; linarith [h1 u hu, h2 w hw]

omit [InnerProductSpace ℝ E₁] [InnerProductSpace ℝ E₂] in
theorem norm_fst_le (x : WithLp 2 (E₁ × E₂)) : ‖x.fst‖ ≤ ‖x‖ := by
  have h := WithLp.prod_norm_sq_eq_of_L2 x
  have : ‖x.fst‖ ^ 2 ≤ ‖x‖ ^ 2 := by rw [h]; nlinarith [sq_nonneg ‖x.snd‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp this

omit [InnerProductSpace ℝ E₁] [InnerProductSpace ℝ E₂] in
theorem norm_snd_le (x : WithLp 2 (E₁ × E₂)) : ‖x.snd‖ ≤ ‖x‖ := by
  have h := WithLp.prod_norm_sq_eq_of_L2 x
  have : ‖x.snd‖ ^ 2 ≤ ‖x‖ ^ 2 := by rw [h]; nlinarith [sq_nonneg ‖x.fst‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp this

end Product

section Main

variable {E₁ E₂ : Type u} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [NormedAddCommGroup E₂]
  [InnerProductSpace ℝ E₂]

/-- The value of the width formula is symmetric. -/
theorem formula_comm (a b : ℝ) :
    Real.sqrt (a ^ 2 * b ^ 2 / (a ^ 2 + b ^ 2)) = Real.sqrt (b ^ 2 * a ^ 2 / (b ^ 2 + a ^ 2)) := by
  congr 1; ring

/-- `1/√(1/a² + 1/b²) = √(a²b²/(a² + b²))`. -/
theorem formula_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1 / Real.sqrt (1 / a ^ 2 + 1 / b ^ 2) = Real.sqrt (a ^ 2 * b ^ 2 / (a ^ 2 + b ^ 2)) := by
  rw [one_div, ← Real.sqrt_inv]
  congr 1
  field_simp
  ring

open Classical in
theorem element_bound {V₁ : Finset E₁} {V₂ : Finset E₂} (hV₁ : V₁.Nonempty) (hV₂ : V₂.Nonempty)
    (hw₁ : 0 < affinePyramidalWidth V₁) (hw₂ : 0 < affinePyramidalWidth V₂)
    {ψ : StrongDual ℝ (WithLp 2 (E₁ × E₂))}
    (hF : exposedFace (productVertices V₁ V₂) ψ ≠ productVertices V₁ V₂)
    {p q : WithLp 2 (E₁ × E₂)}
    (hp : p ∈ convexHull ℝ (↑(exposedFace (productVertices V₁ V₂) ψ) : Set (WithLp 2 (E₁ × E₂))))
    (hq : q ∈ convexHull ℝ (↑(productVertices V₁ V₂ \ exposedFace (productVertices V₁ V₂) ψ) :
      Set (WithLp 2 (E₁ × E₂)))) :
    Real.sqrt (affinePyramidalWidth V₁ ^ 2 * affinePyramidalWidth V₂ ^ 2 /
      (affinePyramidalWidth V₁ ^ 2 + affinePyramidalWidth V₂ ^ 2)) ≤ ‖p - q‖ := by
  set V := productVertices V₁ V₂ with hVdef
  set F := exposedFace V ψ with hFdef
  set F₁ := exposedFace V₁ (ψ.comp inl₁) with hF₁
  set F₂ := exposedFace V₂ (ψ.comp inr₂) with hF₂
  set w₁ := affinePyramidalWidth V₁ with hw₁def
  set w₂ := affinePyramidalWidth V₂ with hw₂def
  have hmemF : ∀ x ∈ F, ∃ a ∈ F₁, ∃ b ∈ F₂, WithLp.toLp 2 (a, b) = x := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_productVertices.mp (exposedFace_subset V ψ hx)
    exact ⟨a, ((mem_face_iff ψ ha hb).mp hx).1, b, ((mem_face_iff ψ ha hb).mp hx).2, rfl⟩
  have hmemK : ∀ x ∈ V \ F, ∃ a ∈ V₁, ∃ b ∈ V₂, WithLp.toLp 2 (a, b) = x ∧ (a ∉ F₁ ∨ b ∉ F₂) := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_productVertices.mp hx.1
    refine ⟨a, ha, b, hb, rfl, ?_⟩
    by_contra h
    push Not at h
    exact hx.2 ((mem_face_iff ψ ha hb).mpr h)
  have hlt := (prep_bounds.1 w₁ w₂ hw₁ hw₂).2
  by_cases h1 : F₁ = V₁ <;> by_cases h2 : F₂ = V₂
  · exfalso
    apply hF
    apply Finset.Subset.antisymm (exposedFace_subset V ψ)
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_productVertices.mp hx
    exact (mem_face_iff ψ ha hb).mpr ⟨by rw [← hF₁, h1]; exact ha, by rw [← hF₂, h2]; exact hb⟩
  · -- the first factor face is improper
    obtain ⟨w, hw, β, γ, hγ, hFw, hKw⟩ := factor_data hV₂ h2
    set g : StrongDual ℝ (WithLp 2 (E₁ × E₂)) := sndL (innerSL ℝ w) with hg
    have hgF : ∀ x ∈ F, β + γ ≤ g x := by
      intro x hx
      obtain ⟨a, -, b, hb, rfl⟩ := hmemF x hx
      rw [hg, sndL_apply, innerSL_apply_apply, WithLp.toLp_snd]
      linarith [hFw b hb]
    have hgK : ∀ x ∈ V \ F, g x ≤ β := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl, hab⟩ := hmemK x hx
      have hbF : b ∉ F₂ := by
        rcases hab with h | h
        · exact absurd (by rw [h1]; exact ha) h
        · exact h
      rw [hg, sndL_apply, innerSL_apply_apply, WithLp.toLp_snd]
      linarith [hKw b (Finset.mem_sdiff.mpr ⟨hb, hbF⟩)]
    have hp' := ge_on_hull' g hgF p hp
    have hq' := le_on_hull g hgK q hq
    have hgpq : g (p - q) ≤ ‖p - q‖ := by
      rw [hg, sndL_apply, innerSL_apply_apply]
      calc inner ℝ w (p - q).snd ≤ ‖w‖ * ‖(p - q).snd‖ := real_inner_le_norm _ _
        _ ≤ 1 * ‖p - q‖ := mul_le_mul hw (norm_snd_le _) (norm_nonneg _) zero_le_one
        _ = ‖p - q‖ := one_mul _
    rw [map_sub] at hgpq
    have := min_le_right w₁ w₂
    linarith
  · -- the second factor face is improper
    obtain ⟨w, hw, β, γ, hγ, hFw, hKw⟩ := factor_data hV₁ h1
    set g : StrongDual ℝ (WithLp 2 (E₁ × E₂)) := fstL (innerSL ℝ w) with hg
    have hgF : ∀ x ∈ F, β + γ ≤ g x := by
      intro x hx
      obtain ⟨a, ha, b, -, rfl⟩ := hmemF x hx
      rw [hg, fstL_apply, innerSL_apply_apply, WithLp.toLp_fst]
      linarith [hFw a ha]
    have hgK : ∀ x ∈ V \ F, g x ≤ β := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl, hab⟩ := hmemK x hx
      have haF : a ∉ F₁ := by
        rcases hab with h | h
        · exact h
        · exact absurd (by rw [h2]; exact hb) h
      rw [hg, fstL_apply, innerSL_apply_apply, WithLp.toLp_fst]
      linarith [hKw a (Finset.mem_sdiff.mpr ⟨ha, haF⟩)]
    have hp' := ge_on_hull' g hgF p hp
    have hq' := le_on_hull g hgK q hq
    have hgpq : g (p - q) ≤ ‖p - q‖ := by
      rw [hg, fstL_apply, innerSL_apply_apply]
      calc inner ℝ w (p - q).fst ≤ ‖w‖ * ‖(p - q).fst‖ := real_inner_le_norm _ _
        _ ≤ 1 * ‖p - q‖ := mul_le_mul hw (norm_fst_le _) (norm_nonneg _) zero_le_one
        _ = ‖p - q‖ := one_mul _
    rw [map_sub] at hgpq
    have := min_le_left w₁ w₂
    linarith
  · -- both factor faces are proper
    obtain ⟨u₁, hu₁, β₁, γ₁, hγ₁, hF1, hK1⟩ := factor_data hV₁ h1
    obtain ⟨u₂, hu₂, β₂, γ₂, hγ₂, hF2, hK2⟩ := factor_data hV₂ h2
    have hγ₁0 : 0 < γ₁ := lt_of_lt_of_le hw₁ hγ₁
    have hγ₂0 : 0 < γ₂ := lt_of_lt_of_le hw₂ hγ₂
    set N := Real.sqrt (1 / γ₁ ^ 2 + 1 / γ₂ ^ 2) with hN
    have hN0 : 0 < N := Real.sqrt_pos.mpr (by positivity)
    set g : StrongDual ℝ (WithLp 2 (E₁ × E₂)) :=
      (1 / (γ₁ * N)) • fstL (innerSL ℝ u₁) + (1 / (γ₂ * N)) • sndL (innerSL ℝ u₂) with hg
    have hgv : ∀ x : WithLp 2 (E₁ × E₂),
        g x = inner ℝ u₁ x.fst / (γ₁ * N) + inner ℝ u₂ x.snd / (γ₂ * N) := by
      intro x
      rw [hg, FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, Pi.smul_apply, FunLike.coe_smul,
        Pi.smul_apply, fstL_apply, sndL_apply, innerSL_apply_apply, innerSL_apply_apply,
        smul_eq_mul, smul_eq_mul]
      ring
    set c₀ := β₁ / (γ₁ * N) + β₂ / (γ₂ * N) with hc₀
    have hub1 : ∀ a ∈ V₁, inner ℝ u₁ a ≤ β₁ + γ₁ := by
      intro a ha
      by_cases haF : a ∈ F₁
      · linarith [hF1 a haF]
      · linarith [hK1 a (Finset.mem_sdiff.mpr ⟨ha, haF⟩)]
    have hub2 : ∀ b ∈ V₂, inner ℝ u₂ b ≤ β₂ + γ₂ := by
      intro b hb
      by_cases hbF : b ∈ F₂
      · linarith [hF2 b hbF]
      · linarith [hK2 b (Finset.mem_sdiff.mpr ⟨hb, hbF⟩)]
    have hgF : ∀ x ∈ F, c₀ + 2 / N ≤ g x := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hmemF x hx
      rw [hgv, WithLp.toLp_fst, WithLp.toLp_snd]
      have e1 : inner ℝ u₁ a = β₁ + γ₁ := by linarith [hF1 a ha]
      have e2 : inner ℝ u₂ b = β₂ + γ₂ := by linarith [hF2 b hb]
      rw [e1, e2, hc₀]
      apply le_of_eq
      field_simp
      ring
    have hgK : ∀ x ∈ V \ F, g x ≤ c₀ + 1 / N := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl, hab⟩ := hmemK x hx
      rw [hgv, WithLp.toLp_fst, WithLp.toLp_snd, hc₀]
      have hd1 : 0 < γ₁ * N := by positivity
      have hd2 : 0 < γ₂ * N := by positivity
      rcases hab with haF | hbF
      · have i1 : inner ℝ u₁ a ≤ β₁ := by linarith [hK1 a (Finset.mem_sdiff.mpr ⟨ha, haF⟩)]
        have i2 := hub2 b hb
        have j1 : inner ℝ u₁ a / (γ₁ * N) ≤ β₁ / (γ₁ * N) := div_le_div_of_nonneg_right i1 hd1.le
        have j2 : inner ℝ u₂ b / (γ₂ * N) ≤ (β₂ + γ₂) / (γ₂ * N) :=
          div_le_div_of_nonneg_right i2 hd2.le
        have e : (β₂ + γ₂) / (γ₂ * N) = β₂ / (γ₂ * N) + 1 / N := by field_simp
        linarith
      · have i1 := hub1 a ha
        have i2 : inner ℝ u₂ b ≤ β₂ := by linarith [hK2 b (Finset.mem_sdiff.mpr ⟨hb, hbF⟩)]
        have j1 : inner ℝ u₁ a / (γ₁ * N) ≤ (β₁ + γ₁) / (γ₁ * N) :=
          div_le_div_of_nonneg_right i1 hd1.le
        have j2 : inner ℝ u₂ b / (γ₂ * N) ≤ β₂ / (γ₂ * N) := div_le_div_of_nonneg_right i2 hd2.le
        have e : (β₁ + γ₁) / (γ₁ * N) = β₁ / (γ₁ * N) + 1 / N := by field_simp
        linarith
    have hp' := ge_on_hull' g hgF p hp
    have hq' := le_on_hull g hgK q hq
    -- `g(p - q) ≤ ‖p - q‖`
    have hgpq : g (p - q) ≤ ‖p - q‖ := by
      set d := p - q with hd
      set X := ‖d.fst‖ with hX
      set Y := ‖d.snd‖ with hY
      have hX0 : 0 ≤ X := norm_nonneg _
      have hY0 : 0 ≤ Y := norm_nonneg _
      have hnd : ‖d‖ ^ 2 = X ^ 2 + Y ^ 2 := WithLp.prod_norm_sq_eq_of_L2 d
      have i1 : inner ℝ u₁ d.fst ≤ X :=
        le_trans (real_inner_le_norm _ _) (by nlinarith [norm_nonneg u₁])
      have i2 : inner ℝ u₂ d.snd ≤ Y :=
        le_trans (real_inner_le_norm _ _) (by nlinarith [norm_nonneg u₂])
      have hS : X / γ₁ + Y / γ₂ ≤ N * ‖d‖ := by
        have hsq : (X / γ₁ + Y / γ₂) ^ 2 ≤ (N * ‖d‖) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity), hnd]
          have : (1 / γ₁ ^ 2 + 1 / γ₂ ^ 2) * (X ^ 2 + Y ^ 2) - (X / γ₁ + Y / γ₂) ^ 2 =
              (X / γ₂ - Y / γ₁) ^ 2 := by field_simp; ring
          nlinarith [sq_nonneg (X / γ₂ - Y / γ₁)]
        exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp hsq
      rw [hgv]
      calc inner ℝ u₁ d.fst / (γ₁ * N) + inner ℝ u₂ d.snd / (γ₂ * N)
          ≤ X / (γ₁ * N) + Y / (γ₂ * N) := by
            have := div_le_div_of_nonneg_right i1 (by positivity : (0 : ℝ) ≤ γ₁ * N)
            have := div_le_div_of_nonneg_right i2 (by positivity : (0 : ℝ) ≤ γ₂ * N)
            linarith
        _ = (X / γ₁ + Y / γ₂) / N := by field_simp
        _ ≤ N * ‖d‖ / N := div_le_div_of_nonneg_right hS hN0.le
        _ = ‖d‖ := by field_simp
    rw [map_sub] at hgpq
    have h1N : 1 / N ≤ ‖p - q‖ := by
      have : 1 / N = (c₀ + 2 / N) - (c₀ + 1 / N) := by ring
      linarith
    -- monotonicity of the formula
    have hmono1 := prep_bounds.2 w₁ γ₁ w₂ hw₁ hγ₁ hw₂
    have hmono2 := prep_bounds.2 w₂ γ₂ γ₁ hw₂ hγ₂ hγ₁0
    rw [formula_comm w₂ γ₁, formula_comm γ₂ γ₁] at hmono2
    calc Real.sqrt (w₁ ^ 2 * w₂ ^ 2 / (w₁ ^ 2 + w₂ ^ 2))
        ≤ Real.sqrt (γ₁ ^ 2 * w₂ ^ 2 / (γ₁ ^ 2 + w₂ ^ 2)) := hmono1
      _ ≤ Real.sqrt (γ₁ ^ 2 * γ₂ ^ 2 / (γ₁ ^ 2 + γ₂ ^ 2)) := hmono2
      _ = 1 / N := (formula_eq hγ₁0 hγ₂0).symm
      _ ≤ ‖p - q‖ := h1N

open Classical in
/-- No proper face means affine pyramidal width zero. -/
theorem affinePyramidalWidth_eq_zero {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : Finset E} (h : ∀ φ : StrongDual ℝ E, exposedFace V φ = V) :
    affinePyramidalWidth V = 0 := by
  unfold affinePyramidalWidth
  have hempty : {r : ℝ | ∃ ψ : StrongDual ℝ E, exposedFace V ψ ≠ V ∧
      ∃ a ∈ affineSpan ℝ (↑(exposedFace V ψ) : Set E),
        ∃ q ∈ convexHull ℝ (↑(V \ exposedFace V ψ) : Set E), r = ‖a - q‖} = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    rintro r ⟨ψ, hψ, -⟩
    exact hψ (h ψ)
  rw [hempty, Real.sInf_empty]

theorem product_width_lower_bound {V₁ : Finset E₁} {V₂ : Finset E₂} (_hV₁ : V₁.Nonempty)
    (hV₂ : V₂.Nonempty) :
    Real.sqrt (affinePyramidalWidth V₁ ^ 2 * affinePyramidalWidth V₂ ^ 2 /
      (affinePyramidalWidth V₁ ^ 2 + affinePyramidalWidth V₂ ^ 2)) ≤
      facialDistance (productVertices V₁ V₂) := by
  classical
  rcases (affinePyramidalWidth_nonneg V₁).eq_or_lt with h0 | hw₁
  · rw [← h0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      zero_div, Real.sqrt_zero]
    exact Proof.facialDistance_nonneg _
  rcases (affinePyramidalWidth_nonneg V₂).eq_or_lt with h0 | hw₂
  · rw [← h0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      zero_div, Real.sqrt_zero]
    exact Proof.facialDistance_nonneg _
  -- a proper face of the first factor
  have hex : ∃ φ : StrongDual ℝ E₁, exposedFace V₁ φ ≠ V₁ := by
    by_contra h
    push Not at h
    rw [affinePyramidalWidth_eq_zero h] at hw₁
    exact lt_irrefl 0 hw₁
  obtain ⟨φ, hφ⟩ := hex
  obtain ⟨a, ha⟩ := sdiff_exposedFace_nonempty hφ
  rw [Finset.mem_sdiff] at ha
  obtain ⟨b, hb⟩ := hV₂
  set ψ : StrongDual ℝ (WithLp 2 (E₁ × E₂)) := fstL φ with hψ
  have hcomp : ∀ u : E₁, ψ.comp inl₁ u = φ u := fun u => by
    simp [hψ, fstL, inl₁]
  have heq : ψ.comp inl₁ = φ := ContinuousLinearMap.ext hcomp
  have hab : WithLp.toLp 2 (a, b) ∉ exposedFace (productVertices V₁ V₂) ψ := by
    intro h
    have h' := ((mem_face_iff ψ ha.1 hb).mp h).1
    rw [heq] at h'
    exact ha.2 h'
  have hmemV : WithLp.toLp 2 (a, b) ∈ productVertices V₁ V₂ :=
    mem_productVertices.mpr ⟨a, ha.1, b, hb, rfl⟩
  have hψF : exposedFace (productVertices V₁ V₂) ψ ≠ productVertices V₁ V₂ := by
    intro h; rw [h] at hab; exact hab hmemV
  have hVne : (productVertices V₁ V₂).Nonempty := ⟨_, hmemV⟩
  obtain ⟨p, hp⟩ := Proof.exposedFace_nonempty hVne ψ
  unfold facialDistance
  have hqmem := subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨hmemV, hab⟩))
  refine le_csInf ⟨_, ψ, hψF, p, subset_convexHull ℝ _ (Finset.mem_coe.mpr hp),
    WithLp.toLp 2 (a, b), by convert hqmem, rfl⟩ ?_
  rintro r ⟨ψ', hψ', p', hp', q', hq', rfl⟩
  exact element_bound ⟨a, ha.1⟩ ⟨b, hb⟩ hw₁ hw₂ hψ' hp' (by convert hq')

end Main

namespace Proof

theorem affine_width_le_facial : AffineWidthLeFacial.{u} := fun V => affine_le_facial V

theorem product_width_lower : ProductWidthLowerBound.{u} := by
  intro E₁ E₂ _ _ _ _ V₁ V₂ hV₁ hV₂
  exact product_width_lower_bound hV₁ hV₂

end Proof

end Lemmata.FWProduct
