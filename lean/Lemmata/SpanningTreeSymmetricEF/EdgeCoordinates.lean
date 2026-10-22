module

public import Lemmata.SpanningTreeSymmetricEF.Models
public import Lemmata.SpanningTreeSymmetricEF.FormulationAffine

@[expose] public section

namespace Lemmata.SpanningTreeSymmetricEF.EdgeCoordinates

open scoped BigOperators Classical
open Approximation
noncomputable section

/-- Ordinary loopless edges of the complete graph. -/
abbrev Edge (n : ℕ) := FormulationStructure.Edge (Fin n)

/-- Restriction to ordinary edges. -/
def restrict {n : ℕ} (x : Sym2 (Fin n) → ℝ) : Edge n → ℝ := fun e => x e.val

/-- Canonical zero-padding is linear, so it does not introduce inequalities. -/
def zeroPad (n : ℕ) : (Edge n → ℝ) →ₗ[ℝ] (Sym2 (Fin n) → ℝ) where
  toFun x e := if h : ¬e.IsDiag then x ⟨e,h⟩ else 0
  map_add' x y := by
    funext e
    by_cases h : e.IsDiag <;> simp [h]
  map_smul' a x := by
    funext e
    by_cases h : e.IsDiag <;> simp [h]

@[simp] theorem restrict_zeroPad {n : ℕ} (x : Edge n → ℝ) :
    restrict (zeroPad n x) = x := by
  funext e
  simp [restrict, zeroPad, e.property]

theorem zeroPad_restrict {n : ℕ} (x : Sym2 (Fin n) → ℝ)
    (h : ∀ e, e.IsDiag → x e = 0) : zeroPad n (restrict x) = x := by
  funext e
  by_cases he : e.IsDiag <;> simp [zeroPad, restrict, he, h e]

/-- Actual incidence vectors expressed on ordinary edges. -/
def incidence {n : ℕ} (T : Tree n) : Edge n → ℝ :=
  restrict (SpanningTreeMinSplit.edgeValue T)

@[simp] theorem zeroPad_incidence {n : ℕ} (T : Tree n) :
    zeroPad n (incidence T) = SpanningTreeMinSplit.edgeValue T := by
  apply zeroPad_restrict
  intro e he
  rw [GraphBridge.published_edgeValue_eq]
  have hn : e ∉ T.val.edgeSet := fun h => (SimpleGraph.not_isDiag_of_mem_edgeSet T.val h) he
  simp [hn]

/-- Padding does not change any objective, including arbitrary signed costs. -/
theorem objective_zeroPad {n : ℕ} (c : Sym2 (Fin n) → ℝ) (x : Edge n → ℝ) :
    objective c (zeroPad n x) = objective (restrict c) x := by
  unfold objective
  calc
    _ = ∑ e ∈ Finset.univ.filter (fun e : Sym2 (Fin n) => ¬e.IsDiag),
        c e * zeroPad n x e := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro e _ he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at he
      simp [zeroPad, he]
    _ = ∑ e : Edge n, c e.val * zeroPad n x e.val :=
      Finset.sum_subtype _ (by simp) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      simp [restrict, zeroPad, e.property]

/-- Inverse reindexing on ordinary edges is the same vertex action. -/
def relabel {n : ℕ} (g : Equiv.Perm (Fin n)) (x : Edge n → ℝ) : Edge n → ℝ :=
  fun e => x (FormulationAffine.edgeEquiv g.symm e)

theorem zeroPad_relabel {n : ℕ} (g : Equiv.Perm (Fin n)) (x : Edge n → ℝ) :
    zeroPad n (relabel g x) = CoordinateLowerBounds.edgeAction n g (zeroPad n x) := by
  funext e
  by_cases he : e.IsDiag
  · have hm : (e.map g.symm).IsDiag := (Sym2.isDiag_map g.symm.injective).mpr he
    simp [zeroPad, CoordinateLowerBounds.edgeAction,
      CoordinateLowerBounds.edgeRelabel, he, hm]
  · have hm : ¬(e.map g.symm).IsDiag :=
      fun h => he ((Sym2.isDiag_map g.symm.injective).mp h)
    simp [zeroPad, relabel, FormulationAffine.edgeEquiv,
      CoordinateLowerBounds.edgeAction, CoordinateLowerBounds.edgeRelabel, he, hm]

/-- Every ordinary-edge approximation yields the full-coordinate approximation
used by the lower theorem. No condition is added to the original feasible set. -/
theorem maxApproximation_zeroPad {n : ℕ} {R : Set (Edge n → ℝ)} {β : ℝ}
    (h : MaxApproximation (incidence (n := n)) R β) :
    MaxApproximation (SpanningTreeMinSplit.edgeValue (n := n)) (zeroPad n '' R) β := by
  refine ⟨h.factor_ge_one, fun T => ⟨incidence T, h.contains T, zeroPad_incidence T⟩, ?_⟩
  rintro c hc _ ⟨x, hx, rfl⟩
  obtain ⟨T, hT⟩ := h.bound (restrict c) (fun e => hc e.val) x hx
  refine ⟨T, ?_⟩
  rw [objective_zeroPad]
  have he := objective_zeroPad c (incidence T)
  rw [zeroPad_incidence] at he
  rw [he]
  exact hT

/-- The two ambient conventions represent exactly the same convex hull. -/
theorem zeroPad_treePolytope (n : ℕ) :
    zeroPad n '' convexHull ℝ (Set.range (incidence (n := n))) = treePolytope n := by
  rw [(zeroPad n).image_convexHull, ← Set.range_comp]
  simp only [Function.comp_def, zeroPad_incidence, treePolytope]

section Presentation
variable {n : ℕ} {E J : Type*} [AddCommGroup E] [Module ℝ E] [Fintype J]
variable (Q : AffineSubspace ℝ E) (a : J → E →ᵃ[ℝ] ℝ)
  (p : E →ᵃ[ℝ] (Edge n → ℝ))
  (ρ : Equiv.Perm (Fin n) →* (E ≃ᵃ[ℝ] E))
  (hstable : ∀ g z, z ∈ CoordinateLowerBounds.feasible Q a →
    ρ g z ∈ CoordinateLowerBounds.feasible Q a)
  (hcov : ∀ g z, z ∈ CoordinateLowerBounds.feasible Q a →
    p (ρ g z) = relabel g (p z))

/-- A loopless LP becomes a `SymmetricLP` with exactly the SAME row index type,
affine slice, slacks and auxiliary action. -/
def padLP : SymmetricLP n E J where
  slice := Q
  slack := a
  project := (zeroPad n).toAffineMap.comp p
  action := ρ
  stable := hstable
  covariant := by
    intro g z hz
    change zeroPad n (p (ρ g z)) = _
    rw [hcov g z hz]
    exact zeroPad_relabel g (p z)

theorem padLP_image : (padLP Q a p ρ hstable hcov).image =
    zeroPad n '' SignedLift.lpImage Q a p := by
  ext x
  constructor
  · rintro ⟨z, hz, ha, hp⟩
    exact ⟨p z, ⟨z, hz, ha, rfl⟩, hp⟩
  · rintro ⟨_, ⟨z, hz, ha, rfl⟩, hp⟩
    exact ⟨z, hz, ha, hp⟩

theorem padLP_approximates {β : ℝ}
    (h : MaxApproximation (incidence (n := n)) (SignedLift.lpImage Q a p) β) :
    (padLP Q a p ρ hstable hcov).Approximates β := by
  unfold SymmetricLP.Approximates
  rw [padLP_image]
  exact maxApproximation_zeroPad h

theorem padLP_exact
    (h : SignedLift.lpImage Q a p = convexHull ℝ (Set.range (incidence (n := n)))) :
    (padLP Q a p ρ hstable hcov).Exact := by
  unfold SymmetricLP.Exact
  rw [padLP_image, h, zeroPad_treePolytope]

end Presentation

section PSD
variable {n : ℕ} {E B : Type*} {K : B → Type*}
  [AddCommGroup E] [Module ℝ E] [Fintype B] [∀ b, Fintype (K b)]
variable (S : AffineSubspace ℝ E) (M : ∀ b, E →ᵃ[ℝ] Matrix (K b) (K b) ℝ)
  (p : E →ᵃ[ℝ] (Edge n → ℝ))

/-- Padding changes neither PSD blocks nor affine equations, hence not size. -/
def padPSD : PSDPresentation n E B K where
  slice := S
  block := M
  project := (zeroPad n).toAffineMap.comp p

theorem padPSD_image : (padPSD S M p).image = zeroPad n '' SignedLift.psdImage S M p := by
  ext x
  constructor
  · rintro ⟨z, hz, hM, hp⟩
    exact ⟨p z, ⟨z, hz, hM, rfl⟩, hp⟩
  · rintro ⟨_, ⟨z, hz, hM, rfl⟩, hp⟩
    exact ⟨z, hz, hM, hp⟩

theorem padPSD_contains
    (h : convexHull ℝ (Set.range (incidence (n := n))) ⊆ SignedLift.psdImage S M p) :
    treePolytope n ⊆ (padPSD S M p).image := by
  rw [← zeroPad_treePolytope, padPSD_image]
  exact Set.image_mono h

theorem padPSD_nonnegative
    (h : ∀ x ∈ SignedLift.psdImage S M p, ∀ e, 0 ≤ x e) :
    ∀ x ∈ (padPSD S M p).image, ∀ e, 0 ≤ x e := by
  intro x hx e
  rw [padPSD_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  by_cases he : e.IsDiag
  · simp [zeroPad, he]
  · simpa [zeroPad, he] using h y hy ⟨e, he⟩

end PSD
end
end Lemmata.SpanningTreeSymmetricEF.EdgeCoordinates
