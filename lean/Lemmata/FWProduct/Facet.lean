module

public import Lemmata.FWProduct.Upper

@[expose] public section

/-!
# The vertex-facet distance of a product (Proposition 4.7)

Exposed faces of the product `conv V₁ × conv V₂` are products `F₁ × F₂` of exposed faces of the
factors (the improper face `Vᵢ` included, exposed by the zero functional). A facet, a maximal proper
exposed face, is therefore `F₁ × V₂` for a facet `F₁` of the first factor or `V₁ × F₂` for a facet
`F₂` of the second: if both factor faces were proper, `F₁ × V₂` would be a larger proper face. The
affine hull of `F₁ × V₂` projects into the affine hull of `F₁`, and contains `(a₁, b)` for `a₁` in
the affine hull of `F₁` and `b ∈ V₂`, so its distances to the remaining vertices are those of
`F₁`.
-/

namespace Lemmata.FWProduct

open Lemmata.FrankWolfe Lemmata.AwayStepFW

universe u

section Generic

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The values defining the vertex-facet distance. -/
def vfValues (V : Finset E) : Set ℝ :=
  {r : ℝ | ∃ F : Finset E, IsFacet V F ∧ ∃ a ∈ affineSpan ℝ (↑F : Set E), ∃ v ∈ V, v ∉ F ∧
    r = ‖a - v‖}

theorem vertexFacetDistance_eq (V : Finset E) : vertexFacetDistance V = sInf (vfValues V) := by
  classical
  unfold vertexFacetDistance vfValues
  congr 1
  ext r
  constructor
  · rintro ⟨F, hF, a, ha, v, hv, rfl⟩
    rw [Finset.mem_sdiff] at hv
    exact ⟨F, hF, a, ha, v, hv.1, hv.2, rfl⟩
  · rintro ⟨F, hF, a, ha, v, hv, hvF, rfl⟩
    exact ⟨F, hF, a, ha, v, Finset.mem_sdiff.mpr ⟨hv, hvF⟩, rfl⟩

theorem vfValues_nonneg {V : Finset E} : ∀ r ∈ vfValues V, 0 ≤ r := by
  rintro r ⟨_, _, _, _, _, _, _, rfl⟩; exact norm_nonneg _

theorem exposedFace_zero (V : Finset E) : exposedFace V 0 = V := by
  classical
  ext w
  simp [exposedFace]

open Classical in
/-- A polytope with a proper exposed face has a facet. -/
theorem exists_facet {V : Finset E} (hex : ∃ ψ : StrongDual ℝ E, exposedFace V ψ ≠ V) :
    ∃ F, IsFacet V F := by
  set 𝓟 : Finset (Finset E) :=
    V.powerset.filter (fun F => ∃ ψ : StrongDual ℝ E, exposedFace V ψ = F ∧ F ≠ V) with h𝓟
  obtain ⟨ψ, hψ⟩ := hex
  have hne : 𝓟.Nonempty := ⟨exposedFace V ψ, by
    rw [h𝓟, Finset.mem_filter, Finset.mem_powerset]; exact ⟨exposedFace_subset V ψ, ψ, rfl, hψ⟩⟩
  obtain ⟨F, hF, hmax⟩ := 𝓟.exists_max_image Finset.card hne
  rw [h𝓟, Finset.mem_filter, Finset.mem_powerset] at hF
  obtain ⟨-, φ, rfl, hφ⟩ := hF
  refine ⟨exposedFace V φ, ⟨φ, rfl⟩, hφ, fun φ' hsub hne' => ?_⟩
  have hmem : exposedFace V φ' ∈ 𝓟 := by
    rw [h𝓟, Finset.mem_filter, Finset.mem_powerset]; exact ⟨exposedFace_subset V φ', φ', rfl, hne'⟩
  exact (Finset.eq_of_subset_of_card_le hsub (hmax _ hmem)).symm

theorem isFacet_nonempty {V F : Finset E} (hV : V.Nonempty) (h : IsFacet V F) : F.Nonempty := by
  obtain ⟨⟨ψ, rfl⟩, -, -⟩ := h
  exact Proof.exposedFace_nonempty hV ψ

theorem isFacet_subset {V F : Finset E} (h : IsFacet V F) : F ⊆ V := by
  obtain ⟨⟨ψ, rfl⟩, -, -⟩ := h
  exact exposedFace_subset V ψ

theorem isFacet_exists_out {V F : Finset E} (h : IsFacet V F) : ∃ v ∈ V, v ∉ F := by
  by_contra hc
  push Not at hc
  exact h.2.1 (Finset.Subset.antisymm (isFacet_subset h) hc)

end Generic

section Product

variable {E₁ E₂ : Type u} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [NormedAddCommGroup E₂]
  [InnerProductSpace ℝ E₂]

omit [InnerProductSpace ℝ E₁] [InnerProductSpace ℝ E₂] in
theorem mem_productVertices_iff {A : Finset E₁} {B : Finset E₂} {a : E₁} {b : E₂} :
    WithLp.toLp 2 (a, b) ∈ productVertices A B ↔ a ∈ A ∧ b ∈ B := by
  constructor
  · intro h
    obtain ⟨a', ha', b', hb', he⟩ := mem_productVertices.mp h
    have h1 := congrArg WithLp.ofLp he
    simp only [Prod.mk.injEq] at h1
    exact ⟨h1.1 ▸ ha', h1.2 ▸ hb'⟩
  · rintro ⟨ha, hb⟩
    exact mem_productVertices.mpr ⟨a, ha, b, hb, rfl⟩

omit [InnerProductSpace ℝ E₁] [InnerProductSpace ℝ E₂] in
theorem productVertices_mono {A A' : Finset E₁} {B B' : Finset E₂} (hA : A ⊆ A') (hB : B ⊆ B') :
    productVertices A B ⊆ productVertices A' B' := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_productVertices.mp hx
  exact mem_productVertices_iff.mpr ⟨hA ha, hB hb⟩

omit [InnerProductSpace ℝ E₁] [InnerProductSpace ℝ E₂] in
theorem productVertices_left_inj {A A' : Finset E₁} {B : Finset E₂} (hB : B.Nonempty)
    (h : productVertices A B = productVertices A' B) : A = A' := by
  obtain ⟨b, hb⟩ := hB
  ext a
  have := congrArg (fun T => WithLp.toLp 2 (a, b) ∈ T) h
  simp only [mem_productVertices_iff, eq_iff_iff] at this
  constructor
  · intro ha; exact (this.mp ⟨ha, hb⟩).1
  · intro ha; exact (this.mpr ⟨ha, hb⟩).1

omit [InnerProductSpace ℝ E₁] [InnerProductSpace ℝ E₂] in
theorem productVertices_right_inj {A : Finset E₁} {B B' : Finset E₂} (hA : A.Nonempty)
    (h : productVertices A B = productVertices A B') : B = B' := by
  obtain ⟨a, ha⟩ := hA
  ext b
  have := congrArg (fun T => WithLp.toLp 2 (a, b) ∈ T) h
  simp only [mem_productVertices_iff, eq_iff_iff] at this
  constructor
  · intro hb; exact (this.mp ⟨ha, hb⟩).2
  · intro hb; exact (this.mpr ⟨ha, hb⟩).2

theorem fstL_add_comp_inl (φ₁ : StrongDual ℝ E₁) (φ₂ : StrongDual ℝ E₂) :
    (fstL φ₁ + sndL φ₂ : StrongDual ℝ (WithLp 2 (E₁ × E₂))).comp inl₁ = φ₁ := by
  ext a; simp [fstL, sndL, inl₁]

theorem fstL_add_comp_inr (φ₁ : StrongDual ℝ E₁) (φ₂ : StrongDual ℝ E₂) :
    (fstL φ₁ + sndL φ₂ : StrongDual ℝ (WithLp 2 (E₁ × E₂))).comp inr₂ = φ₂ := by
  ext b; simp [fstL, sndL, inr₂]

/-- Products of exposed faces are exposed faces. -/
theorem exposedFace_prod (V₁ : Finset E₁) (V₂ : Finset E₂) (φ₁ : StrongDual ℝ E₁)
    (φ₂ : StrongDual ℝ E₂) :
    exposedFace (productVertices V₁ V₂) (fstL φ₁ + sndL φ₂) =
      productVertices (exposedFace V₁ φ₁) (exposedFace V₂ φ₂) := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_productVertices.mp (exposedFace_subset _ _ hx)
    rw [mem_face_iff _ ha hb, fstL_add_comp_inl, fstL_add_comp_inr] at hx
    exact mem_productVertices_iff.mpr hx
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_productVertices.mp hx
    rw [mem_face_iff _ (exposedFace_subset _ _ ha) (exposedFace_subset _ _ hb), fstL_add_comp_inl,
      fstL_add_comp_inr]
    exact ⟨ha, hb⟩

/-- Every exposed face of the product is a product of exposed faces. -/
theorem exposedFace_eq_prod (V₁ : Finset E₁) (V₂ : Finset E₂)
    (ψ : StrongDual ℝ (WithLp 2 (E₁ × E₂))) :
    exposedFace (productVertices V₁ V₂) ψ =
      productVertices (exposedFace V₁ (ψ.comp inl₁)) (exposedFace V₂ (ψ.comp inr₂)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_productVertices.mp (exposedFace_subset _ _ hx)
    exact mem_productVertices_iff.mpr ((mem_face_iff ψ ha hb).mp hx)
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_productVertices.mp hx
    exact (mem_face_iff ψ (exposedFace_subset _ _ ha) (exposedFace_subset _ _ hb)).mpr ⟨ha, hb⟩

theorem isFacet_prod_left {V₁ : Finset E₁} {V₂ : Finset E₂} (hV₁ : V₁.Nonempty)
    (hV₂ : V₂.Nonempty) {F₁ : Finset E₁} (h : IsFacet V₁ F₁) :
    IsFacet (productVertices V₁ V₂) (productVertices F₁ V₂) := by
  obtain ⟨⟨φ₁, rfl⟩, hne, hmax⟩ := h
  have hface : exposedFace (productVertices V₁ V₂) (fstL φ₁ + sndL 0) =
      productVertices (exposedFace V₁ φ₁) V₂ := by rw [exposedFace_prod, exposedFace_zero]
  refine ⟨⟨_, hface⟩, fun heq => hne (productVertices_left_inj hV₂ heq), fun Φ hsub hΦ => ?_⟩
  rw [exposedFace_eq_prod] at hsub hΦ ⊢
  have hF₁ : (exposedFace V₁ φ₁).Nonempty := Proof.exposedFace_nonempty hV₁ φ₁
  have hG₁ : exposedFace V₁ φ₁ ⊆ exposedFace V₁ (Φ.comp inl₁) := by
    intro a ha
    obtain ⟨b, hb⟩ := hV₂
    exact (mem_productVertices_iff.mp (hsub (mem_productVertices_iff.mpr ⟨ha, hb⟩))).1
  have hG₂ : exposedFace V₂ (Φ.comp inr₂) = V₂ := by
    apply Finset.Subset.antisymm (exposedFace_subset _ _)
    intro b hb
    obtain ⟨a, ha⟩ := hF₁
    exact (mem_productVertices_iff.mp (hsub (mem_productVertices_iff.mpr ⟨ha, hb⟩))).2
  have hG₁ne : exposedFace V₁ (Φ.comp inl₁) ≠ V₁ := fun h => hΦ (by rw [h, hG₂])
  rw [hmax _ hG₁ hG₁ne, hG₂]

theorem isFacet_prod_right {V₁ : Finset E₁} {V₂ : Finset E₂} (hV₁ : V₁.Nonempty)
    (hV₂ : V₂.Nonempty) {F₂ : Finset E₂} (h : IsFacet V₂ F₂) :
    IsFacet (productVertices V₁ V₂) (productVertices V₁ F₂) := by
  obtain ⟨⟨φ₂, rfl⟩, hne, hmax⟩ := h
  have hface : exposedFace (productVertices V₁ V₂) (fstL 0 + sndL φ₂) =
      productVertices V₁ (exposedFace V₂ φ₂) := by rw [exposedFace_prod, exposedFace_zero]
  refine ⟨⟨_, hface⟩, fun heq => hne (productVertices_right_inj hV₁ heq), fun Φ hsub hΦ => ?_⟩
  rw [exposedFace_eq_prod] at hsub hΦ ⊢
  have hF₂ : (exposedFace V₂ φ₂).Nonempty := Proof.exposedFace_nonempty hV₂ φ₂
  have hG₂ : exposedFace V₂ φ₂ ⊆ exposedFace V₂ (Φ.comp inr₂) := by
    intro b hb
    obtain ⟨a, ha⟩ := hV₁
    exact (mem_productVertices_iff.mp (hsub (mem_productVertices_iff.mpr ⟨ha, hb⟩))).2
  have hG₁ : exposedFace V₁ (Φ.comp inl₁) = V₁ := by
    apply Finset.Subset.antisymm (exposedFace_subset _ _)
    intro a ha
    obtain ⟨b, hb⟩ := hF₂
    exact (mem_productVertices_iff.mp (hsub (mem_productVertices_iff.mpr ⟨ha, hb⟩))).1
  have hG₂ne : exposedFace V₂ (Φ.comp inr₂) ≠ V₂ := fun h => hΦ (by rw [h, hG₁])
  rw [hmax _ hG₂ hG₂ne, hG₁]

/-- The facets of the product. -/
theorem isFacet_prod_cases {V₁ : Finset E₁} {V₂ : Finset E₂} (hV₁ : V₁.Nonempty)
    (hV₂ : V₂.Nonempty) {F : Finset (WithLp 2 (E₁ × E₂))} (h : IsFacet (productVertices V₁ V₂) F) :
    (∃ F₁, IsFacet V₁ F₁ ∧ F = productVertices F₁ V₂) ∨
      ∃ F₂, IsFacet V₂ F₂ ∧ F = productVertices V₁ F₂ := by
  obtain ⟨⟨ψ, rfl⟩, hne, hmax⟩ := h
  set F₁ := exposedFace V₁ (ψ.comp inl₁) with hF₁
  set F₂ := exposedFace V₂ (ψ.comp inr₂) with hF₂
  have hF : exposedFace (productVertices V₁ V₂) ψ = productVertices F₁ F₂ :=
    exposedFace_eq_prod V₁ V₂ ψ
  have hF₁ne : F₁.Nonempty := Proof.exposedFace_nonempty hV₁ _
  have hF₂ne : F₂.Nonempty := Proof.exposedFace_nonempty hV₂ _
  by_cases h1 : F₁ = V₁ <;> by_cases h2 : F₂ = V₂
  · exact absurd (by rw [hF, h1, h2]) hne
  · -- the first factor face is improper
    right
    refine ⟨F₂, ⟨⟨_, rfl⟩, h2, fun φ hsub hφ => ?_⟩, by rw [hF, h1]⟩
    have hface : exposedFace (productVertices V₁ V₂) (fstL 0 + sndL φ) =
        productVertices V₁ (exposedFace V₂ φ) := by rw [exposedFace_prod, exposedFace_zero]
    have hsub' : exposedFace (productVertices V₁ V₂) ψ ⊆
        exposedFace (productVertices V₁ V₂) (fstL 0 + sndL φ) := by
      rw [hF, hface, h1]; exact productVertices_mono subset_rfl hsub
    have hne' : exposedFace (productVertices V₁ V₂) (fstL 0 + sndL φ) ≠ productVertices V₁ V₂ := by
      rw [hface]; intro heq; exact hφ (productVertices_right_inj hV₁ heq)
    have := hmax _ hsub' hne'
    rw [hface, hF, h1] at this
    exact productVertices_right_inj hV₁ this
  · -- the second factor face is improper
    left
    refine ⟨F₁, ⟨⟨_, rfl⟩, h1, fun φ hsub hφ => ?_⟩, by rw [hF, h2]⟩
    have hface : exposedFace (productVertices V₁ V₂) (fstL φ + sndL 0) =
        productVertices (exposedFace V₁ φ) V₂ := by rw [exposedFace_prod, exposedFace_zero]
    have hsub' : exposedFace (productVertices V₁ V₂) ψ ⊆
        exposedFace (productVertices V₁ V₂) (fstL φ + sndL 0) := by
      rw [hF, hface, h2]; exact productVertices_mono hsub subset_rfl
    have hne' : exposedFace (productVertices V₁ V₂) (fstL φ + sndL 0) ≠ productVertices V₁ V₂ := by
      rw [hface]; intro heq; exact hφ (productVertices_left_inj hV₂ heq)
    have := hmax _ hsub' hne'
    rw [hface, hF, h2] at this
    exact productVertices_left_inj hV₂ this
  · -- both proper: `F₁ × V₂` is a larger proper face
    exfalso
    have hface : exposedFace (productVertices V₁ V₂) (fstL (ψ.comp inl₁) + sndL 0) =
        productVertices F₁ V₂ := by rw [exposedFace_prod, exposedFace_zero]
    have hsub' : exposedFace (productVertices V₁ V₂) ψ ⊆
        exposedFace (productVertices V₁ V₂) (fstL (ψ.comp inl₁) + sndL 0) := by
      rw [hF, hface]; exact productVertices_mono subset_rfl (exposedFace_subset _ _)
    have hne' : exposedFace (productVertices V₁ V₂) (fstL (ψ.comp inl₁) + sndL 0) ≠
        productVertices V₁ V₂ := by
      rw [hface]; intro heq; exact h1 (productVertices_left_inj hV₂ heq)
    have := hmax _ hsub' hne'
    rw [hface, hF] at this
    exact h2 (productVertices_right_inj hF₁ne this).symm

end Product

section Distance

variable {E₁ E₂ : Type u} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [NormedAddCommGroup E₂]
  [InnerProductSpace ℝ E₂]

omit [InnerProductSpace ℝ E₁] [InnerProductSpace ℝ E₂] in
theorem vfValues_nonempty' {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {V : Finset E} (h : 1 < V.card) : (vfValues V).Nonempty := by
  obtain ⟨F, hF⟩ := exists_facet (exists_proper_face h)
  obtain ⟨a, ha⟩ := isFacet_nonempty (Finset.card_pos.mp (by omega)) hF
  obtain ⟨v, hv, hvF⟩ := isFacet_exists_out hF
  exact ⟨_, F, hF, a, subset_affineSpan ℝ _ (Finset.mem_coe.mpr ha), v, hv, hvF, rfl⟩

/-- The first coordinate, as an affine map. -/
noncomputable def fstA : WithLp 2 (E₁ × E₂) →ᵃ[ℝ] E₁ :=
  ((ContinuousLinearMap.fst ℝ E₁ E₂).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).toContinuousLinearMap).toLinearMap.toAffineMap

/-- The second coordinate, as an affine map. -/
noncomputable def sndA : WithLp 2 (E₁ × E₂) →ᵃ[ℝ] E₂ :=
  ((ContinuousLinearMap.snd ℝ E₁ E₂).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).toContinuousLinearMap).toLinearMap.toAffineMap

theorem fst_mem_affineSpan {F₁ : Finset E₁} {V₂ : Finset E₂} {a : WithLp 2 (E₁ × E₂)}
    (ha : a ∈ affineSpan ℝ (↑(productVertices F₁ V₂) : Set (WithLp 2 (E₁ × E₂)))) :
    a.fst ∈ affineSpan ℝ (↑F₁ : Set E₁) := by
  have h1 : fstA a ∈
      (affineSpan ℝ (↑(productVertices F₁ V₂) : Set (WithLp 2 (E₁ × E₂)))).map fstA :=
    AffineSubspace.mem_map.mpr ⟨a, ha, rfl⟩
  rw [AffineSubspace.map_span] at h1
  refine affineSpan_mono ℝ ?_ h1
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨a', ha', b', hb', rfl⟩ := mem_productVertices.mp hx
  exact ha'

theorem snd_mem_affineSpan {V₁ : Finset E₁} {F₂ : Finset E₂} {a : WithLp 2 (E₁ × E₂)}
    (ha : a ∈ affineSpan ℝ (↑(productVertices V₁ F₂) : Set (WithLp 2 (E₁ × E₂)))) :
    a.snd ∈ affineSpan ℝ (↑F₂ : Set E₂) := by
  have h1 : sndA a ∈
      (affineSpan ℝ (↑(productVertices V₁ F₂) : Set (WithLp 2 (E₁ × E₂)))).map sndA :=
    AffineSubspace.mem_map.mpr ⟨a, ha, rfl⟩
  rw [AffineSubspace.map_span] at h1
  refine affineSpan_mono ℝ ?_ h1
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨a', ha', b', hb', rfl⟩ := mem_productVertices.mp hx
  exact hb'

theorem toLp_left_mem_affineSpan {F₁ : Finset E₁} {V₂ : Finset E₂} {a₁ : E₁}
    (ha₁ : a₁ ∈ affineSpan ℝ (↑F₁ : Set E₁)) {b : E₂} (hb : b ∈ V₂) :
    WithLp.toLp 2 (a₁, b) ∈
      affineSpan ℝ (↑(productVertices F₁ V₂) : Set (WithLp 2 (E₁ × E₂))) := by
  set g : E₁ →ᵃ[ℝ] WithLp 2 (E₁ × E₂) :=
    (AffineEquiv.constVAdd ℝ (WithLp 2 (E₁ × E₂)) (WithLp.toLp 2 (0, b))).toAffineMap.comp
      inl₁.toLinearMap.toAffineMap with hgdef
  have hg : ∀ x, g x = WithLp.toLp 2 (x, b) := by
    intro x
    show WithLp.toLp 2 (0, b) + WithLp.toLp 2 (x, 0) = WithLp.toLp 2 (x, b)
    rw [← WithLp.toLp_add]; simp
  have h1 : g a₁ ∈ (affineSpan ℝ (↑F₁ : Set E₁)).map g := AffineSubspace.mem_map.mpr ⟨a₁, ha₁, rfl⟩
  rw [AffineSubspace.map_span, hg] at h1
  refine affineSpan_mono ℝ ?_ h1
  rintro y ⟨x, hx, rfl⟩
  rw [hg]
  exact mem_productVertices_iff.mpr ⟨hx, hb⟩

theorem toLp_right_mem_affineSpan {V₁ : Finset E₁} {F₂ : Finset E₂} {a₂ : E₂}
    (ha₂ : a₂ ∈ affineSpan ℝ (↑F₂ : Set E₂)) {b : E₁} (hb : b ∈ V₁) :
    WithLp.toLp 2 (b, a₂) ∈
      affineSpan ℝ (↑(productVertices V₁ F₂) : Set (WithLp 2 (E₁ × E₂))) := by
  set g : E₂ →ᵃ[ℝ] WithLp 2 (E₁ × E₂) :=
    (AffineEquiv.constVAdd ℝ (WithLp 2 (E₁ × E₂)) (WithLp.toLp 2 (b, 0))).toAffineMap.comp
      inr₂.toLinearMap.toAffineMap with hgdef
  have hg : ∀ x, g x = WithLp.toLp 2 (b, x) := by
    intro x
    show WithLp.toLp 2 (b, 0) + WithLp.toLp 2 (0, x) = WithLp.toLp 2 (b, x)
    rw [← WithLp.toLp_add]; simp
  have h1 : g a₂ ∈ (affineSpan ℝ (↑F₂ : Set E₂)).map g := AffineSubspace.mem_map.mpr ⟨a₂, ha₂, rfl⟩
  rw [AffineSubspace.map_span, hg] at h1
  refine affineSpan_mono ℝ ?_ h1
  rintro y ⟨x, hx, rfl⟩
  rw [hg]
  exact mem_productVertices_iff.mpr ⟨hb, hx⟩

omit [InnerProductSpace ℝ E₁] [InnerProductSpace ℝ E₂] in
theorem norm_toLp_sub_left (a v : E₁) (b : E₂) :
    ‖WithLp.toLp 2 (a, b) - WithLp.toLp 2 (v, b)‖ = ‖a - v‖ := by
  rw [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self, WithLp.prod_norm_eq_of_L2]
  simp [Real.sqrt_sq (norm_nonneg _)]

omit [InnerProductSpace ℝ E₁] [InnerProductSpace ℝ E₂] in
theorem norm_toLp_sub_right (b : E₁) (a v : E₂) :
    ‖WithLp.toLp 2 (b, a) - WithLp.toLp 2 (b, v)‖ = ‖a - v‖ := by
  rw [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self, WithLp.prod_norm_eq_of_L2]
  simp [Real.sqrt_sq (norm_nonneg _)]

theorem product_vertex_facet_eq {V₁ : Finset E₁} {V₂ : Finset E₂} (h1 : 1 < V₁.card)
    (h2 : 1 < V₂.card) :
    vertexFacetDistance (productVertices V₁ V₂) =
      min (vertexFacetDistance V₁) (vertexFacetDistance V₂) := by
  have hV₁ : V₁.Nonempty := Finset.card_pos.mp (by omega)
  have hV₂ : V₂.Nonempty := Finset.card_pos.mp (by omega)
  rw [vertexFacetDistance_eq, vertexFacetDistance_eq, vertexFacetDistance_eq]
  set S := vfValues (productVertices V₁ V₂) with hS
  set S₁ := vfValues V₁ with hS₁def
  set S₂ := vfValues V₂ with hS₂def
  have hS₁ : S₁.Nonempty := vfValues_nonempty' h1
  have hS₂ : S₂.Nonempty := vfValues_nonempty' h2
  have hsub1 : S₁ ⊆ S := by
    rintro r ⟨F₁, hF₁, a₁, ha₁, v₁, hv₁, hv₁F, rfl⟩
    obtain ⟨b, hb⟩ := hV₂
    exact ⟨productVertices F₁ V₂, isFacet_prod_left hV₁ ⟨b, hb⟩ hF₁, WithLp.toLp 2 (a₁, b),
      toLp_left_mem_affineSpan ha₁ hb, WithLp.toLp 2 (v₁, b),
      mem_productVertices_iff.mpr ⟨hv₁, hb⟩,
      fun h => hv₁F (mem_productVertices_iff.mp h).1, (norm_toLp_sub_left a₁ v₁ b).symm⟩
  have hsub2 : S₂ ⊆ S := by
    rintro r ⟨F₂, hF₂, a₂, ha₂, v₂, hv₂, hv₂F, rfl⟩
    obtain ⟨b, hb⟩ := hV₁
    exact ⟨productVertices V₁ F₂, isFacet_prod_right ⟨b, hb⟩ hV₂ hF₂, WithLp.toLp 2 (b, a₂),
      toLp_right_mem_affineSpan ha₂ hb, WithLp.toLp 2 (b, v₂),
      mem_productVertices_iff.mpr ⟨hb, hv₂⟩,
      fun h => hv₂F (mem_productVertices_iff.mp h).2, (norm_toLp_sub_right b a₂ v₂).symm⟩
  have hdom : ∀ r ∈ S, ∃ r' ∈ S₁ ∪ S₂, r' ≤ r := by
    rintro r ⟨F, hF, a, ha, v, hv, hvF, rfl⟩
    obtain ⟨v₁, hv₁, w, hw, rfl⟩ := mem_productVertices.mp hv
    rcases isFacet_prod_cases hV₁ hV₂ hF with ⟨F₁, hF₁, rfl⟩ | ⟨F₂, hF₂, rfl⟩
    · have hv₁F : v₁ ∉ F₁ := fun h => hvF (mem_productVertices_iff.mpr ⟨h, hw⟩)
      refine ⟨‖a.fst - v₁‖, Or.inl ⟨F₁, hF₁, a.fst, fst_mem_affineSpan ha, v₁, hv₁, hv₁F, rfl⟩,
        ?_⟩
      have := norm_fst_le (a - WithLp.toLp 2 (v₁, w))
      rwa [WithLp.sub_fst, WithLp.toLp_fst] at this
    · have hwF : w ∉ F₂ := fun h => hvF (mem_productVertices_iff.mpr ⟨hv₁, h⟩)
      refine ⟨‖a.snd - w‖, Or.inr ⟨F₂, hF₂, a.snd, snd_mem_affineSpan ha, w, hw, hwF, rfl⟩, ?_⟩
      have := norm_snd_le (a - WithLp.toLp 2 (v₁, w))
      rwa [WithLp.sub_snd, WithLp.toLp_snd] at this
  have hb1 : BddBelow S₁ := ⟨0, vfValues_nonneg⟩
  have hb2 : BddBelow S₂ := ⟨0, vfValues_nonneg⟩
  have hbS : BddBelow S := ⟨0, vfValues_nonneg⟩
  have hU : BddBelow (S₁ ∪ S₂) :=
    ⟨0, fun x hx => hx.elim (vfValues_nonneg x) (vfValues_nonneg x)⟩
  rw [← csInf_union hb1 hS₁ hb2 hS₂]
  apply le_antisymm
  · exact csInf_le_csInf hbS (hS₁.mono Set.subset_union_left) (Set.union_subset hsub1 hsub2)
  · apply le_csInf (hS₁.mono hsub1)
    intro r hr
    obtain ⟨r', hr', hle⟩ := hdom r hr
    exact le_trans (csInf_le hU hr') hle

end Distance

namespace Proof

theorem product_vertex_facet : ProductVertexFacet.{u} := by
  intro E₁ E₂ _ _ _ _ V₁ V₂ h1 h2
  exact product_vertex_facet_eq h1 h2

end Proof

end Lemmata.FWProduct
