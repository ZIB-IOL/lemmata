module

public import Lemmata.ModifiedE8Bell.VisibilityCompute
public meta import Lemmata.ModifiedE8Bell.VisibilityCompute

@[expose] public section
namespace Lemmata.ModifiedE8Bell
open scoped BigOperators

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem visibility_stages_nonempty : ∀ rs ∈ visibilityStages.toList, 0 < rs.size := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- Entrywise equality of the finite local protocol with (109/165) times
 the unit-root Gram matrix. All arithmetic in this check is integral. -/
theorem visibility_entries : ∀ i j,
    1320 * tableMatrix visibilityResult.1 i j =
      109 * (visibilityResult.2 : ℤ) * (∑ k, root i k * root j k) := by
  native_decide

end Lemmata.ModifiedE8Bell
