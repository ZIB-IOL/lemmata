module

/-!
Shared helpers. Anything two contributions need goes here, through a reviewed PR,
rather than being copied between contributions.
-/

public section

namespace Lemmata.Shared

/-- Modus ponens, stated once so contributions can share it. -/
theorem mp {P Q : Prop} (hpq : P → Q) (hp : P) : Q := hpq hp

end Lemmata.Shared
