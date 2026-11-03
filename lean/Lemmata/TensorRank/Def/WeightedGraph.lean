module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Def.Graph
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

set_option autoImplicit false

namespace Lemmata.TensorRank

variable {𝕜 : Type*} [Field 𝕜]

abbrev Edge (k : ℕ) := {s : Finset (Fin k) // s.card = 2}

abbrev Incident (k : ℕ) (i : Fin k) := {e : Edge k // i ∈ e.val}

abbrev WeightedCoordinate {k : ℕ} (d : Edge k → ℕ) (i : Fin k) :=
  ∀ e : Incident k i, Fin (d e.val)

noncomputable def weightedComplete {k : ℕ} (d : Edge k → ℕ) :
    Tensor 𝕜 (Fin k) (WeightedCoordinate d) := by
  classical
  exact fun x => if ∀ (e : Edge k) (i j : Fin k) (hi : i ∈ e.val) (hj : j ∈ e.val),
    x i ⟨e, hi⟩ = x j ⟨e, hj⟩ then 1 else 0

def edgeBetween {k : ℕ} (i j : Fin k) (hji : j ≠ i) : Edge k :=
  ⟨{i, j}, by simp [Ne.symm hji]⟩

end Lemmata.TensorRank
