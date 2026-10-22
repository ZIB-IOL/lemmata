module

public import Lemmata.SpanningTreeSymmetricEF.QuadraticCore

@[expose] public section


/-! Genuine affine slices and linear projections underlying the Gram models.
No coefficient vector is a variable in the slice. -/
namespace Lemmata.SpanningTreeSymmetricEF.QuadraticAffine
open scoped BigOperators Classical
open Matrix FormulationStructure QuadraticAlgebra QuadraticCore
noncomputable section
variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

def coordinatesLinear (a : Edge V → J → ℝ) : Matrix J J ℝ →ₗ[ℝ] (Edge V → ℝ) where
  toFun := coordinates a
  map_add' Y Z := by ext e; simp [coordinates,pair,map_add]
  map_smul' s Y := by ext e; simp [coordinates,pair,map_smul]

def extendLinear : (Edge V → ℝ) →ₗ[ℝ] (Sym2 V → ℝ) where
  toFun := extend
  map_add' x y := by ext e; by_cases he : e.IsDiag <;> simp [extend,he]
  map_smul' s x := by ext e; by_cases he : e.IsDiag <;> simp [extend,he]

def projection (a : Edge V → J → ℝ) : Matrix J J ℝ →ₗ[ℝ] (Sym2 V → ℝ) :=
  extendLinear.comp (coordinatesLinear a)

theorem pair_ternary (Y Z W : Matrix J J ℝ) (s : ℝ) (u v : J → ℝ) :
    pair (s • (Y-Z)+W) u v = s * (pair Y u v - pair Z u v) + pair W u v := by
  simp [pair,map_add,map_sub,map_smul]

theorem coordinates_ternary (a : Edge V → J → ℝ) (Y Z W : Matrix J J ℝ) (s : ℝ) :
    coordinates a (s • (Y-Z)+W) = s • (coordinates a Y - coordinates a Z) + coordinates a W := by
  ext e
  exact pair_ternary Y Z W s (a e) (a e)

theorem equations_ternary {active : V → Finset V} {a : Edge V → J → ℝ} {b : V → V → J → ℝ}
    {Y Z W : Matrix J J ℝ} {x y z : Edge V → ℝ}
    (hY : Equations active a b Y x) (hZ : Equations active a b Z y) (hW : Equations active a b W z)
    (s : ℝ) : Equations active a b (s • (Y-Z)+W) (s • (x-y)+z) := by
  constructor
  · intro e; simp only [pair_ternary,hY.diagonal,hZ.diagonal,hW.diagonal]; rfl
  · intro e f hef; simp [pair_ternary,hY.edge e f hef,hZ.edge e f hef,hW.edge e f hef]
  · intro r v w; simp [pair_ternary,hY.parent,hZ.parent,hW.parent]
  · intro r v e hv; simp [pair_ternary,hY.incidence r v e hv,hZ.incidence r v e hv,hW.incidence r v e hv]
  · intro r e he
    simp only [pair_ternary,Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_sub_distrib,
      hY.conservation r e he,hZ.conservation r e he,hW.conservation r e he]
    rfl
  · change (∑ e, (s*(x e-y e)+z e)) = _
    rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_sub_distrib,
      hY.cardinality,hZ.cardinality,hW.cardinality]
    ring

/-- All affine equations, with the projected variables eliminated. -/
def slice (R : RootFamily V) (a : Edge V → J → ℝ) (b : V → V → J → ℝ) :
    AffineSubspace ℝ (Matrix J J ℝ) where
  carrier := {Y | Equations R.active a b Y (coordinates a Y)}
  smul_vsub_vadd_mem' s Y Z W hY hZ hW := by
    change Equations R.active a b (s • (Y-Z)+W) (coordinates a (s • (Y-Z)+W))
    rw [coordinates_ternary]
    exact equations_ternary hY hZ hW s

/-- The earlier exactness endpoints refer to a single PSD cone intersected
with a genuine affine subspace and followed by a linear projection. -/
theorem image_as_affine_psd (R : RootFamily V) (a : Edge V → J → ℝ) (b : V → V → J → ℝ) :
    image R a b = projection a '' ((slice R a b : Set (Matrix J J ℝ)) ∩ {Y | Y.PosSemidef}) := by
  ext z
  constructor
  · rintro ⟨Y,hY,he,hz⟩
    exact ⟨Y,⟨he,hY⟩,hz⟩
  · rintro ⟨Y,⟨he,hY⟩,hz⟩
    exact ⟨Y,hY,he,hz⟩

end
end Lemmata.SpanningTreeSymmetricEF.QuadraticAffine
