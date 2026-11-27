module

public import Lemmata.TensorRank.Main

@[expose] public section

namespace Lemmata.CompleteGraphTensorRank

open Lemmata.TensorRank

abbrev Party := Option Bool

/-- Two blocks of `r` vertices and a singleton. -/
def Block (r : ℕ) : Party → Type
  | none => Unit
  | some _ => Fin r

instance blockFintype (r : ℕ) (p : Party) : Fintype (Block r p) := by
  cases p <;> dsimp [Block] <;> infer_instance

abbrev Vertex (r : ℕ) := Sigma (Block r)

/-- Local coordinates of the triangle with edge alphabets of sizes
`d^(r*r)`, `d^r`, and `d^r`. -/
def RectangleCoordinate (r d : ℕ) : Party → Type
  | none => (Fin r → Fin d) × (Fin r → Fin d)
  | some _ => ((Fin r × Fin r) → Fin d) × (Fin r → Fin d)

instance rectangleFintype (r d : ℕ) (p : Party) :
    Fintype (RectangleCoordinate r d p) := by
  cases p <;> dsimp [RectangleCoordinate] <;> infer_instance

/-- The ordinary rectangular matrix multiplication coefficient tensor,
with coordinates at both ends of each of the three edges required to agree. -/
noncomputable def rectangle (F : Type*) [Field F] (r d : ℕ) :
    Tensor F Party (RectangleCoordinate r d) := by
  classical
  exact fun x => if (x (some false)).1 = (x (some true)).1 ∧
      (x (some false)).2 = (x none).1 ∧ (x (some true)).2 = (x none).2 then 1 else 0

/-- The exact rectangular exponent formula on already sorted positive weights. -/
noncomputable def rectangularExponent (x y z : ℝ) : ℝ :=
  x + y + (max ((x + y) * z - x * y) 0) ^ 2 / (4 * x * y * z)

/-- The sole external lower-bound input: the required specialization of
OpenAI's exact rectangular exponent theorem, in the tensor-rank model.
This proposition is a hypothesis, not an added Lean axiom. -/
def RectangularLowerBound (F : Type*) [Field F] : Prop :=
  ∀ (r d : ℕ), 1 ≤ r → 2 ≤ d →
    (d : ℝ) ^ rectangularExponent ((r : ℝ) ^ 2) r r ≤
      Tensor.asymptoticRank (rectangle F r d)

/-- The full complete-graph equality, including the formerly open odd orders. -/
def CompleteGraphEquality (F : Type*) [Field F] : Prop :=
  ∀ k d : ℕ, 2 ≤ k → 1 ≤ d →
    Tensor.asymptoticRank (completeGraph (𝕜 := F) k d) = (d : ℝ) ^ ((k : ℝ) ^ 2 / 4)

end Lemmata.CompleteGraphTensorRank
