module

public import Lemmata.TensorRank.Def.Graph
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

set_option autoImplicit false

namespace Lemmata.TensorRank

abbrev Edge (k : ℕ) := {s : Finset (Fin k) // s.card = 2}

abbrev Incident (k : ℕ) (i : Fin k) := {e : Edge k // i ∈ e.val}

abbrev WeightedCoordinate {k : ℕ} (d : Edge k → ℕ) (i : Fin k) :=
  ∀ e : Incident k i, Fin (d e.val)

noncomputable def weightedComplete {k : ℕ} (d : Edge k → ℕ) :
    Tensor ℂ (Fin k) (WeightedCoordinate d) := by
  classical
  exact fun x => if ∀ (e : Edge k) (i j : Fin k) (hi : i ∈ e.val) (hj : j ∈ e.val),
    x i ⟨e, hi⟩ = x j ⟨e, hj⟩ then 1 else 0

def edgeBetween {k : ℕ} (i j : Fin k) (hji : j ≠ i) : Edge k :=
  ⟨{i, j}, by simp [Ne.symm hji]⟩

def edgeMap {k : ℕ} (σ : Equiv.Perm (Fin k)) : Edge k ≃ Edge k where
  toFun e := ⟨e.val.map σ.toEmbedding, by simpa using e.prop⟩
  invFun e := ⟨e.val.map σ.symm.toEmbedding, by simpa using e.prop⟩
  left_inv e := by
    apply Subtype.ext
    ext i
    simp
  right_inv e := by
    apply Subtype.ext
    ext i
    simp

end Lemmata.TensorRank
