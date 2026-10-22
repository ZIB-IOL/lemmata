module

public import Lemmata.SpanningTreeSymmetricEF.Models
public import Lemmata.SpanningTreeSymmetricEF.SDPResults

@[expose] public section

namespace Lemmata.SpanningTreeSymmetricEF

open scoped Classical
noncomputable section

/-- One PSD cone of order `k`, with an affine slice and linear projection whose
image is exactly the actual tree polytope. There are no additional scalar cones. -/
def HasExactPSD (n k : ℕ) : Prop :=
  ∃ (J : Type) (_ : Fintype J), Fintype.card J = k ∧
    Nonempty (QuadraticEndpoints.ExactPSDFormulation J (treePolytope n))

/-- Exactness, order, and coordinate-permutation symmetry all refer to the SAME
formulation. The action is a homomorphism and preserves its slice/feasible set. -/
def HasPermutationPSD (n k : ℕ) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J)
    (F : QuadraticEndpoints.ExactPSDFormulation J (treePolytope n)),
    Fintype.card J = k ∧ Nonempty (SDPResults.PermutationSymmetry F)

/-- The symmetry is explicitly orthogonal congruence, not a claim that the
compressed coordinates can be permuted. -/
def HasOrthogonalPSD (n k : ℕ) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J)
    (F : QuadraticEndpoints.ExactPSDFormulation J (treePolytope n)),
    Fintype.card J = k ∧ Nonempty (SDPResults.OrthogonalSymmetry F)

end
end Lemmata.SpanningTreeSymmetricEF
