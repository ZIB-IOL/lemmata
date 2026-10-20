module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace Lemmata.LPHardnessInP.Parity

open scoped BigOperators

/-- A Boolean bit viewed in the field with two elements. -/
def bit (b : Bool) : ZMod 2 := if b then 1 else 0

/-- An actual perfect matching in the bipartite graph with one blue and one
red edge for every pair, restricted to an odd number of red edges. -/
structure ParityMatching (n : ℕ) where
  perm : Equiv.Perm (Fin n)
  red : Fin n → Bool
  odd_red : ∑ i, bit (red i) = 1

/-- Vertex labels with total label parity equal to the size of one part. -/
structure ParityLabel (n : ℕ) where
  left : Fin n → Bool
  right : Fin n → Bool
  label_parity : (∑ i, bit (left i)) + (∑ j, bit (right j)) = (n : ZMod 2)

/-- A blue edge violates the labeling if its endpoint labels agree; a red
edge violates it if its endpoint labels disagree. -/
def Violates {n : ℕ} (L : ParityLabel n) (i j : Fin n) (red : Bool) : Prop :=
  if red then L.left i ≠ L.right j else L.left i = L.right j

instance {n : ℕ} (L : ParityLabel n) (i j : Fin n) (red : Bool) :
    Decidable (Violates L i j red) := by unfold Violates; infer_instance

/-- The number of violating selected edges, a natural number. -/
def violationCount {n : ℕ} (L : ParityLabel n) (M : ParityMatching n) : ℕ :=
  ∑ i, if Violates L i (M.perm i) (M.red i) then 1 else 0

/-- Positive edge costs on the fixed red/blue bipartite graph. -/
noncomputable def edgeCost {n : ℕ} (L : ParityLabel n) (γ : ℝ)
    (i j : Fin n) (red : Bool) : ℝ :=
  1 + if Violates L i j red then γ else 0

/-- Cost of an actual parity matching, summed over its selected edges. -/
noncomputable def matchingCost {n : ℕ} (L : ParityLabel n) (γ : ℝ)
    (M : ParityMatching n) : ℝ :=
  ∑ i, edgeCost L γ i (M.perm i) (M.red i)

end Lemmata.LPHardnessInP.Parity
