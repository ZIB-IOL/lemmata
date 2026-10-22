module

public import Lemmata.SpanningTreeSymmetricEF.QuadraticValues
public import Lemmata.SpanningTreeSymmetricEF.QuadraticHull

@[expose] public section


/-! Exactness of a fixed-coefficient affine PSD formulation. Root families
below are instantiated by all nonroot vertices or vertices above the root. -/
namespace Lemmata.SpanningTreeSymmetricEF.QuadraticCore
open scoped BigOperators Classical
open Matrix FormulationStructure QuadraticAlgebra QuadraticValues ApproximationUpper
noncomputable section
variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

structure RootFamily (V : Type*) [Fintype V] [DecidableEq V] where
  active : V → Finset V
  not_root : ∀ r, r ∉ active r
  cover : ∀ S : Finset V, S.Nonempty → ∃ r ∈ S, S.erase r ⊆ active r

def extend (x : Edge V → ℝ) (e : Sym2 V) : ℝ :=
  if h : ¬ e.IsDiag then x ⟨e,h⟩ else 0

@[simp] theorem extend_edge (x : Edge V → ℝ) (e : Edge V) : extend x e.val = x e := by
  simp [extend, e.property]

@[simp] theorem extend_diag (x : Edge V → ℝ) (e : Sym2 V) (he : e.IsDiag) : extend x e = 0 := by
  simp [extend, he]

theorem extend_sum (x : Edge V → ℝ) : (∑ e, extend x e) = ∑ e, x e := by
  rw [← sum_nondiagonal _ (extend_diag x)]
  simp

theorem extend_subset_sum (x : Edge V → ℝ) (S : Finset V) :
    (∑ e ∈ S.sym2, extend x e) = ∑ e ∈ edgesIn S, x e := by
  have heq : (∑ e : Edge V, if e ∈ edgesIn S then x e else 0) =
      ∑ e : Sym2 V, if e ∈ S.sym2 then extend x e else 0 := by
    rw [← sum_nondiagonal _ (by intro e he; simp [extend_diag x e he])]
    apply Finset.sum_congr rfl
    intro e _
    simp only [extend_edge, mem_edgesIn]
    have hm : e.val ∈ S.sym2 ↔ ∀ v ∈ e.val, v ∈ S := Finset.mem_sym2_iff
    simp only [hm]
  simpa only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter] using heq.symm

theorem extend_tree (T : SimpleGraph V) : extend (treeCoordinates T) = graphIncidence T := by
  funext e
  by_cases he : e.IsDiag
  · simp [extend_diag _ e he, graphIncidence, he]
  · simp [extend, he, treeCoordinates, graphIncidence]

def coordinates (a : Edge V → J → ℝ) (Y : Matrix J J ℝ) (e : Edge V) : ℝ :=
  pair Y (a e) (a e)

def image (R : RootFamily V) (a : Edge V → J → ℝ) (b : V → V → J → ℝ) : Set (Sym2 V → ℝ) :=
  {z | ∃ Y : Matrix J J ℝ, Y.PosSemidef ∧
    Equations R.active a b Y (coordinates a Y) ∧ extend (coordinates a Y) = z}

theorem pair_mix (Y Z : Matrix J J ℝ) (s t : ℝ) (u v : J → ℝ) :
    pair (s • Y + t • Z) u v = s * pair Y u v + t * pair Z u v := by
  simp [pair, map_add, map_smul]

theorem coordinates_mix (a : Edge V → J → ℝ) (Y Z : Matrix J J ℝ) (s t : ℝ) :
    coordinates a (s • Y + t • Z) = s • coordinates a Y + t • coordinates a Z := by
  ext e
  exact pair_mix Y Z s t (a e) (a e)

theorem extend_mix (x y : Edge V → ℝ) (s t : ℝ) :
    extend (s • x + t • y) = s • extend x + t • extend y := by
  ext e
  by_cases he : e.IsDiag <;> simp [extend, he]

theorem equations_mix {active : V → Finset V} {a : Edge V → J → ℝ} {b : V → V → J → ℝ}
    {Y Z : Matrix J J ℝ} {x y : Edge V → ℝ}
    (hY : Equations active a b Y x) (hZ : Equations active a b Z y)
    (s t : ℝ) (hst : s+t=1) :
    Equations active a b (s • Y + t • Z) (s • x + t • y) := by
  constructor
  · intro e; simp only [pair_mix, hY.diagonal, hZ.diagonal]; rfl
  · intro e f hef; simp [pair_mix, hY.edge e f hef, hZ.edge e f hef]
  · intro r v w
    rw [pair_mix, hY.parent, hZ.parent, ← add_mul, hst, one_mul]
  · intro r v e hv; simp [pair_mix, hY.incidence r v e hv, hZ.incidence r v e hv]
  · intro r e he
    simp only [pair_mix, Finset.sum_add_distrib, ← Finset.mul_sum, hY.conservation r e he,
      hZ.conservation r e he]
    rfl
  · change (∑ e, (s*x e + t*y e)) = _
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hY.cardinality, hZ.cardinality, ← add_mul, hst, one_mul]

theorem image_convex (R : RootFamily V) (a : Edge V → J → ℝ) (b : V → V → J → ℝ) :
    Convex ℝ (image R a b) := by
  rintro x ⟨Y,hY,heY,rfl⟩ z ⟨Z,hZ,heZ,rfl⟩ s t hs ht hst
  refine ⟨s • Y + t • Z,(hY.smul hs).add (hZ.smul ht),?_,?_⟩
  · rw [coordinates_mix]
    exact equations_mix heY heZ s t hst
  · rw [coordinates_mix, extend_mix]

theorem image_subset_tree_polytope [Nonempty V] (R : RootFamily V)
    (a : Edge V → J → ℝ) (b : V → V → J → ℝ)
    (hb : ∀ r v, v ∉ R.active r → b r v = 0) :
    image R a b ⊆ convexHull ℝ (Set.range (treeIncidence (V := V))) := by
  rintro z ⟨Y,hY,he,rfl⟩
  apply QuadraticHull.mem_tree_polytope
  · intro e
    by_cases hd : e.IsDiag
    · simp [extend_diag _ _ hd]
    · simp only [extend, dif_pos hd]
      exact he.nonneg hY _
  · exact extend_diag _
  · intro S hS
    rw [extend_subset_sum]
    obtain ⟨r,hr,hc⟩ := R.cover S hS
    exact he.forest_le hY hb S r hr (R.not_root r) hc
  · rw [extend_sum]
    exact he.cardinality

/-- Construct a feasible tree Gram matrix from an explicit row realization. -/
theorem tree_witness_of_rows (R : RootFamily V) (a : Edge V → J → ℝ)
    (b : V → V → J → ℝ) (T : SimpleGraph V) (hT : T.IsTree)
    (H : Matrix J (Edge V) ℝ)
    (ha : ∀ e, Hᵀ *ᵥ a e = edgeValue T e)
    (hb : ∀ r v, Hᵀ *ᵥ b r v = parentValue hT R.active r v) :
    graphIncidence T ∈ image R a b := by
  let Y := H * Hᵀ
  have hY : Y.PosSemidef := by
    simpa only [Y, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose H
  have hpair (u v : J → ℝ) :
      pair Y u v = pair (1 : Matrix (Edge V) (Edge V) ℝ) (Hᵀ *ᵥ u) (Hᵀ *ᵥ v) := by
    simpa [Y] using pair_congruence (1 : Matrix (Edge V) (Edge V) ℝ) H u v
  have he := tree_equations hT R.active R.not_root
  have hx : coordinates a Y = treeCoordinates T := by
    ext e
    rw [coordinates,hpair,ha]
    exact he.diagonal e
  refine ⟨Y,hY,?_,?_⟩
  · rw [hx]
    constructor
    · intro e; rw [hpair,ha]; exact he.diagonal e
    · intro e f hf; rw [hpair,ha,ha]; exact he.edge e f hf
    · intro r v w; rw [hpair,hb,hb]; exact he.parent r v w
    · intro r v e hv; rw [hpair,ha,hb]; exact he.incidence r v e hv
    · intro r e he'
      simp only [hpair,ha,hb]
      exact he.conservation r e he'
    · exact he.cardinality
  · rw [hx,extend_tree]

/-- Generic exactness theorem. The tree-witness premise is discharged by the
explicit Gram matrices in each concrete endpoint, never left as an assumption. -/
theorem image_eq_tree_polytope [Nonempty V] (R : RootFamily V)
    (a : Edge V → J → ℝ) (b : V → V → J → ℝ)
    (hb : ∀ r v, v ∉ R.active r → b r v = 0)
    (hT : ∀ T : SpanningTree V, treeIncidence T ∈ image R a b) :
    image R a b = convexHull ℝ (Set.range (treeIncidence (V := V))) := by
  apply Set.Subset.antisymm (image_subset_tree_polytope R a b hb)
  apply convexHull_min _ (image_convex R a b)
  rintro z ⟨T,rfl⟩
  exact hT T

end
end Lemmata.SpanningTreeSymmetricEF.QuadraticCore
