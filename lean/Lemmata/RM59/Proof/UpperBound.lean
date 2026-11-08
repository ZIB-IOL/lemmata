module

public import Lemmata.RM59.Proof.CatalogComplete
public import Lemmata.RM59.Proof.SimplexRepresentativeCompletion
public import Lemmata.RM59.Proof.SimplexSearchChecks

@[expose] public section

namespace Lemmata.RM59

theorem representative_completion : ∀ family : Fin 348,
    CatalogCompletion.SupportCompletion (Packed.decodeWord (Certificate.seed (family.val + 1))) :=
  SimplexRepresentativeCompletion.all_representatives_complete
    SimplexSearchChecks.chunks_checked

theorem geometric_completion : GeometricCompletion :=
  CatalogCompletion.geometricCompletion_of_catalog
    CatalogUniform.catalog_cover representative_completion

theorem full_bound_thirty_two : FullBound 32 :=
  fullBound_of_geometricCompletion geometric_completion

theorem exists_rm59_approximation (f : BooleanFunction 9) :
    ∃ p ∈ reedMuller 9 5, weight (f + p) ≤ 32 := full_bound_thirty_two f

end Lemmata.RM59
