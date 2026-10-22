module

public import Lemmata.SpanningTreeMinSplit.Main
public import Lemmata.SpanningTreeSymmetricEF.PolyhedralNormalForm
public import Lemmata.SpanningTreeSymmetricEF.OrbitCriterion

@[expose] public section

namespace Lemmata.SpanningTreeSymmetricEF

open scoped BigOperators
noncomputable section

/-- The same actual tree type as in the published full-slack entry. -/
abbrev Tree (n : ℕ) := SpanningTreeMinSplit.Tree n

/-- The actual spanning-tree polytope, embedded with zero diagonal coordinates. -/
def treePolytope (n : ℕ) : Set (Sym2 (Fin n) → ℝ) :=
  convexHull ℝ (Set.range (SpanningTreeMinSplit.edgeValue (n := n)))

/-- The generic formulation library and the published graph model have identical
scalar incidence vectors; this is a proved identity, not an interface input. -/
theorem incidence_eq_source {n : ℕ} (T : Tree n) :
    SpanningTreeMinSplit.edgeValue T = ApproximationUpper.treeIncidence T := by
  classical
  funext e
  rw [GraphBridge.published_edgeValue_eq]
  rfl

theorem treePolytope_eq_source (n : ℕ) :
    treePolytope n = convexHull ℝ
      (Set.range (ApproximationUpper.treeIncidence (V := Fin n))) := by
  unfold treePolytope
  congr 2
  funext T
  exact incidence_eq_source T

/-- A finite affine LP presentation with a genuine vertex-group action.
Only feasibility-level covariance is required; lineality, redundant rows and
implicit equations are allowed. Equations in `slice` do not count as rows. -/
structure SymmetricLP (n : ℕ) (E J : Type*) [AddCommGroup E] [Module ℝ E]
    [Fintype J] where
  slice : AffineSubspace ℝ E
  slack : J → E →ᵃ[ℝ] ℝ
  project : E →ᵃ[ℝ] (Sym2 (Fin n) → ℝ)
  action : Equiv.Perm (Fin n) →* (E ≃ᵃ[ℝ] E)
  stable : ∀ g z, z ∈ CoordinateLowerBounds.feasible slice slack →
    action g z ∈ CoordinateLowerBounds.feasible slice slack
  covariant : ∀ g z, z ∈ CoordinateLowerBounds.feasible slice slack →
    project (action g z) = CoordinateLowerBounds.edgeAction n g (project z)

namespace SymmetricLP
variable {n : ℕ} {E J : Type*} [AddCommGroup E] [Module ℝ E] [Fintype J]

/-- Image of the actual feasible auxiliary points, not a supplied polytope. -/
def image (L : SymmetricLP n E J) : Set (Sym2 (Fin n) → ℝ) :=
  SignedLift.lpImage L.slice L.slack L.project

/-- Approximation means nonnegative-objective maximization and tree containment. -/
def Approximates (L : SymmetricLP n E J) (β : ℝ) : Prop :=
  Approximation.MaxApproximation (SpanningTreeMinSplit.edgeValue (n := n)) L.image β

def Exact (L : SymmetricLP n E J) : Prop := L.image = treePolytope n

theorem approximates_iff_source (L : SymmetricLP n E J) (β : ℝ) :
    L.Approximates β ↔ Approximation.MaxApproximation
      (ApproximationUpper.treeIncidence (V := Fin n)) L.image β := by
  have h : SpanningTreeMinSplit.edgeValue (n := n) =
      ApproximationUpper.treeIncidence (V := Fin n) := funext incidence_eq_source
  simp only [Approximates, h]

end SymmetricLP

/-- An arbitrary finite product-PSD presentation. Scalar inequalities may be
represented as order-one blocks; affine equations are free. -/
structure PSDPresentation (n : ℕ) (E B : Type*) (K : B → Type*)
    [AddCommGroup E] [Module ℝ E] [Fintype B] [∀ b, Fintype (K b)] where
  slice : AffineSubspace ℝ E
  block : ∀ b, E →ᵃ[ℝ] Matrix (K b) (K b) ℝ
  project : E →ᵃ[ℝ] (Sym2 (Fin n) → ℝ)

namespace PSDPresentation
variable {n : ℕ} {E B : Type*} {K : B → Type*}
  [AddCommGroup E] [Module ℝ E] [Fintype B] [∀ b, Fintype (K b)]

def image (L : PSDPresentation n E B K) : Set (Sym2 (Fin n) → ℝ) :=
  SignedLift.psdImage L.slice L.block L.project

end PSDPresentation

end
end Lemmata.SpanningTreeSymmetricEF
