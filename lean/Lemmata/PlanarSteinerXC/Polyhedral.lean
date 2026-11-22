module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Data.ENat.Lattice
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
# Extension complexity

An *LP extension* of a set `P ⊆ ℝ^ι` with `m` inequalities is a polyhedron
`{y ∈ ℝ^d | g(y) = 0 for finitely many affine g, ℓ_j(y) ≥ 0 for j < m}` together with an affine
map whose image is exactly `P`. Equations are free; only inequalities are counted.
The extension complexity `xc P` is the least such `m` (and `⊤` if there is none).

We prove the two monotonicity properties used throughout: affine images and intersections with
affine hyperplanes cannot increase `xc`. We also prove the face lemma for convex hulls.
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

open Set

/-- An LP extension of `P ⊆ ℝ^ι` with `m` inequalities: finitely many affine equations (free),
`m` affine inequalities `ℓ_j(y) ≥ 0` on `ℝ^dim`, and an affine map onto `P`. -/
structure LPExtension.{u} {ι : Type u} (P : Set (ι → ℝ)) (m : ℕ) : Type u where
  /-- Dimension of the auxiliary space. -/
  dim : ℕ
  /-- Affine equations `g(y) = 0`; they are not counted. -/
  eqns : List ((Fin dim → ℝ) →ᵃ[ℝ] ℝ)
  /-- The `m` affine inequalities `ℓ_j(y) ≥ 0`. -/
  ineqs : Fin m → (Fin dim → ℝ) →ᵃ[ℝ] ℝ
  /-- The affine projection. -/
  proj : (Fin dim → ℝ) →ᵃ[ℝ] (ι → ℝ)
  /-- The projection of the polyhedron is exactly `P`. -/
  image_eq : proj '' {y | (∀ g ∈ eqns, g y = 0) ∧ ∀ j, 0 ≤ ineqs j y} = P

/-- Linear extension complexity: the fewest inequalities of a polyhedron (equations free) that has
`P` as an affine image; `⊤` if no such polyhedron exists. -/
noncomputable def xc {ι : Type*} (P : Set (ι → ℝ)) : ℕ∞ :=
  ⨅ (m : ℕ) (_ : Nonempty (LPExtension P m)), (m : ℕ∞)

variable {ι κ : Type*}

theorem xc_le_of_extension {P : Set (ι → ℝ)} {m : ℕ} (E : LPExtension P m) : xc P ≤ m :=
  iInf₂_le m ⟨E⟩

/-- To compare extension complexities it suffices to transform extensions. -/
theorem xc_le_xc_of {P : Set (ι → ℝ)} {Q : Set (κ → ℝ)}
    (h : ∀ m, LPExtension P m → Nonempty (LPExtension Q m)) : xc Q ≤ xc P := by
  refine le_iInf₂ fun m hm => ?_
  obtain ⟨E⟩ := hm
  obtain ⟨E'⟩ := h m E
  exact xc_le_of_extension E'

/-- Affine images cannot increase extension complexity. -/
theorem xc_image_le (f : (ι → ℝ) →ᵃ[ℝ] (κ → ℝ)) (P : Set (ι → ℝ)) : xc (f '' P) ≤ xc P := by
  refine xc_le_xc_of fun m E => ⟨?_⟩
  exact
    { dim := E.dim
      eqns := E.eqns
      ineqs := E.ineqs
      proj := f.comp E.proj
      image_eq := by
        rw [AffineMap.coe_comp, Set.image_comp, E.image_eq] }

theorem xc_le_of_image_eq (f : (ι → ℝ) →ᵃ[ℝ] (κ → ℝ)) {P : Set (ι → ℝ)} {Q : Set (κ → ℝ)}
    (h : f '' P = Q) : xc Q ≤ xc P :=
  h ▸ xc_image_le f P

/-- Intersecting with an affine hyperplane cannot increase extension complexity
(the hyperplane is added as a free equation). -/
theorem xc_inter_hyperplane_le (c : (ι → ℝ) →ₗ[ℝ] ℝ) (δ : ℝ) (P : Set (ι → ℝ)) :
    xc (P ∩ {x | c x = δ}) ≤ xc P := by
  refine xc_le_xc_of fun m E => ⟨?_⟩
  obtain ⟨d, eqns, ineqs, proj, rfl⟩ := E
  let g : (Fin d → ℝ) →ᵃ[ℝ] ℝ :=
    c.toAffineMap.comp proj - AffineMap.const ℝ (Fin d → ℝ) δ
  have hg : ∀ y, g y = c (proj y) - δ := fun y => by
    simp [g]
  exact
    { dim := d
      eqns := g :: eqns
      ineqs := ineqs
      proj := proj
      image_eq := by
        ext x
        simp only [List.mem_cons, forall_eq_or_imp, mem_image, mem_ofPred_eq, mem_inter_iff, hg,
          sub_eq_zero]
        constructor
        · rintro ⟨y, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
          exact ⟨⟨y, ⟨h2, h3⟩, rfl⟩, h1⟩
        · rintro ⟨⟨y, ⟨h2, h3⟩, rfl⟩, h1⟩
          exact ⟨y, ⟨⟨h1, h2⟩, h3⟩, rfl⟩ }

/-- A linear functional on `ℝ^ι` that sums the coordinates in a finite set. -/
noncomputable def sumOver (B : Finset ι) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i ∈ B, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.mul_sum]

@[simp] theorem sumOver_apply (B : Finset ι) (x : ι → ℝ) : sumOver B x = ∑ i ∈ B, x i := rfl

/-! ### Faces of convex hulls -/

/-- If `c ≤ δ` on `X`, then the hyperplane section `{c = δ}` of `conv X` is the convex hull of the
points of `X` on that hyperplane. -/
theorem convexHull_inter_hyperplane_of_le {E : Type*} [AddCommGroup E] [Module ℝ E]
    {X : Set E} (c : E →ₗ[ℝ] ℝ) (δ : ℝ) (hX : ∀ x ∈ X, c x ≤ δ) :
    convexHull ℝ X ∩ {x | c x = δ} = convexHull ℝ (X ∩ {x | c x = δ}) := by
  classical
  apply Subset.antisymm
  · rintro x ⟨hx, hcx⟩
    rw [convexHull_eq] at hx
    obtain ⟨κ, t, w, z, hw0, hw1, hz, rfl⟩ := hx
    simp only [mem_ofPred_eq] at hcx
    have hsum : t.centerMass w z = ∑ i ∈ t, w i • z i := Finset.centerMass_eq_of_sum_1 _ _ hw1
    -- the slack `δ - c (z i)` vanishes wherever the weight is positive
    have hslack : ∑ i ∈ t, w i * (δ - c (z i)) = 0 := by
      have : c (t.centerMass w z) = ∑ i ∈ t, w i * c (z i) := by
        rw [hsum, map_sum]; simp [map_smul, smul_eq_mul]
      rw [hcx] at this
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
      linarith
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun i hi =>
      mul_nonneg (hw0 i hi) (sub_nonneg.mpr (hX _ (hz i hi))))).mp hslack
    rw [← Finset.centerMass_filter_ne_zero]
    apply Finset.centerMass_mem_convexHull
    · intro i hi
      exact hw0 i (Finset.mem_filter.mp hi).1
    · rw [Finset.sum_filter_ne_zero, hw1]; exact one_pos
    · intro i hi
      obtain ⟨hit, hwi⟩ := Finset.mem_filter.mp hi
      refine ⟨hz i hit, ?_⟩
      have := hterm i hit
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hwi
      · simp only [mem_ofPred_eq]; linarith
  · apply subset_inter
    · exact convexHull_mono inter_subset_left
    · apply convexHull_min inter_subset_right
      intro a ha b hb s t hs ht hst
      simp only [mem_ofPred_eq] at ha hb ⊢
      rw [map_add, map_smul, map_smul, ha, hb, smul_eq_mul, smul_eq_mul, ← add_mul, hst, one_mul]

/-- The `≥` version of `convexHull_inter_hyperplane_of_le`. -/
theorem convexHull_inter_hyperplane_of_ge {E : Type*} [AddCommGroup E] [Module ℝ E]
    {X : Set E} (c : E →ₗ[ℝ] ℝ) (δ : ℝ) (hX : ∀ x ∈ X, δ ≤ c x) :
    convexHull ℝ X ∩ {x | c x = δ} = convexHull ℝ (X ∩ {x | c x = δ}) := by
  have h := convexHull_inter_hyperplane_of_le (X := X) (-c) (-δ)
    (fun x hx => by simpa using hX x hx)
  have hs : {x | (-c) x = -δ} = {x | c x = δ} := by
    ext x; simp [neg_inj]
  rwa [hs] at h

/-- The image of a convex hull under an affine map is the convex hull of the image. -/
theorem image_convexHull_eq {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] (f : E →ᵃ[ℝ] F) (X : Set E) :
    f '' convexHull ℝ X = convexHull ℝ (f '' X) :=
  f.image_convexHull X

end Lemmata.PlanarSteinerXC
