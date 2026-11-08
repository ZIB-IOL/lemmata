module

public import Lemmata.RM59.Proof.CatalogUniform
public meta import Lemmata.RM59.Proof.CatalogUniform

@[expose] public section

namespace Lemmata.RM59.CatalogUniform

theorem catalog_checked : catalogCheck = true := by native_decide

end Lemmata.RM59.CatalogUniform
