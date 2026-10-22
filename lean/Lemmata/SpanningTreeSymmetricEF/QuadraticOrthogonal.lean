module

public import Lemmata.SpanningTreeSymmetricEF.QuadraticOrders
public import Lemmata.SpanningTreeSymmetricEF.QuadraticSymmetry
public import Lemmata.SpanningTreeSymmetricEF.QuadraticAffine
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section


/-! Invariant-subspace compression of the all-root Gram model. Unlike deletion
coordinates, orthonormal coordinates carry orthogonal congruences. -/
namespace Lemmata.SpanningTreeSymmetricEF.QuadraticOrthogonal
open scoped BigOperators Classical
open Matrix FormulationStructure QuadraticTrees QuadraticValues QuadraticAlgebra QuadraticCore QuadraticRaw
open QuadraticSymmetry
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

abbrev Ambient (V : Type) [Fintype V] [DecidableEq V] := EuclideanSpace ℝ (Labels V)

def parentAt (f : Ambient V) (r v : V) : ℝ :=
  if hv : v ≠ r then f (.inr ⟨(r,v),by simpa [allRoots] using hv⟩) else 0

def relation : Ambient V →ₗ[ℝ] (V → ℝ) where
  toFun f r := (∑ v, parentAt f r v) - ∑ e : Edge V, f (.inl e)
  map_add' f h := by
    ext r
    have hp (v : V) : parentAt (f+h) r v = parentAt f r v + parentAt h r v := by
      by_cases hv : v = r <;> simp [parentAt,hv]
    simp only [hp,PiLp.add_apply,Finset.sum_add_distrib,Pi.add_apply]
    ring
  map_smul' s f := by
    ext r
    have hp (v : V) : parentAt (s • f) r v = s * parentAt f r v := by
      by_cases hv : v = r <;> simp [parentAt,hv]
    simp only [hp,PiLp.smul_apply,Pi.smul_apply,RingHom.id_apply,smul_eq_mul,← Finset.mul_sum,mul_sub]

abbrev Space (V : Type) [Fintype V] [DecidableEq V] := LinearMap.ker (relation (V := V))

theorem relation_surjective [Nontrivial V] : Function.Surjective (relation (V := V)) := by
  intro x
  let f : Ambient V := WithLp.toLp 2 (fun j => match j with
    | .inl _ => 0
    | .inr p => if p.val.2 = QuadraticOrders.other p.val.1 then x p.val.1 else 0)
  refine ⟨f,?_⟩
  ext r
  change (∑ v, parentAt f r v) - (∑ e : Edge V, f (.inl e)) = x r
  have hp (v : V) : parentAt f r v = if v = QuadraticOrders.other r then x r else 0 := by
    by_cases hv : v = r
    · subst v
      simp [parentAt,Ne.symm (QuadraticOrders.other_ne r)]
    · simp [parentAt,hv,f]
  simp_rw [hp]
  simp [f]

theorem compressed_order [Nontrivial V] :
    Module.finrank ℝ (Space V) = 3 * (Fintype.card V).choose 2 - Fintype.card V := by
  have hr : LinearMap.range (relation (V := V)) = ⊤ := LinearMap.range_eq_top.mpr relation_surjective
  have hd := LinearMap.finrank_range_add_finrank_ker (relation (V := V))
  rw [hr,finrank_top,Module.finrank_pi,finrank_euclideanSpace,symmetric_order] at hd
  change Fintype.card V + Module.finrank ℝ (Space V) = 3 * (Fintype.card V).choose 2 at hd
  omega

abbrev Index (V : Type) [Fintype V] [DecidableEq V] := Fin (Module.finrank ℝ (Space V))

def basis : OrthonormalBasis (Index V) ℝ (Space V) := stdOrthonormalBasis ℝ (Space V)

def coeff (j : Labels V) (i : Index V) : ℝ := (basis i).val j

def edgeCoeff (e : Edge V) : Index V → ℝ := coeff (.inl e)

def parentCoeff (r v : V) : Index V → ℝ :=
  if hv : v ≠ r then coeff (.inr ⟨(r,v),by simpa [allRoots] using hv⟩) else 0

theorem parentCoeff_zero (r v : V) (hv : v ∉ (allRoots (V := V)).active r) :
    parentCoeff r v = 0 := by
  have hv' : v = r := by simpa [allRoots] using hv
  subst v
  simp [parentCoeff]

/-- Columns of the tree Gram factor lie in the invariant relation subspace. -/
def treeColumn (T : SimpleGraph V) (hT : T.IsTree) (e : Edge V) : Space V :=
  ⟨WithLp.toLp 2 (fun j : Labels V => match j with
    | .inl f => edgeValue T f e
    | .inr p => parentVector hT p.val.1 p.val.2 e),by
    apply LinearMap.mem_ker.mpr
    ext r
    change (∑ v, parentAt _ r v) - ∑ f : Edge V, edgeValue T f e = 0
    have hp (v : V) : parentAt
        (WithLp.toLp 2 (fun j : Labels V => match j with
          | .inl f => edgeValue T f e
          | .inr p => parentVector hT p.val.1 p.val.2 e)) r v = parentVector hT r v e := by
      by_cases hv : v = r
      · subst v; simp [parentAt,parentVector_zero]
      · simp [parentAt,hv]
    simp_rw [hp]
    have hs := congrFun (QuadraticCompression.full_root_relation T hT r) e
    simp only [Finset.sum_apply] at hs
    exact sub_eq_zero.mpr hs⟩

def treeMatrix (T : SimpleGraph V) (hT : T.IsTree) : Matrix (Index V) (Edge V) ℝ :=
  fun i e => basis.repr (treeColumn T hT e) i

/-- Evaluating the orthonormal expansion gives every old feature coordinate. -/
theorem expansion (f : Space V) (j : Labels V) :
    (∑ i, basis.repr f i * coeff j i) = f.val j := by
  have h := congrArg (fun y : Space V => y.val j) (basis.sum_repr f)
  simpa only [Submodule.coe_sum,WithLp.ofLp_sum,Finset.sum_apply,Submodule.coe_smul,PiLp.smul_apply,
    smul_eq_mul,coeff] using h

@[simp] theorem edge_row (T : SimpleGraph V) (hT : T.IsTree) (e : Edge V) :
    (treeMatrix T hT)ᵀ *ᵥ edgeCoeff e = edgeValue T e := by
  ext f
  exact expansion (treeColumn T hT f) (.inl e)

@[simp] theorem parent_row (T : SimpleGraph V) (hT : T.IsTree) (r v : V) :
    (treeMatrix T hT)ᵀ *ᵥ parentCoeff r v = parentValue hT (allRoots (V := V)).active r v := by
  by_cases hv : v = r
  · subst v
    simp [parentCoeff,parentValue,allRoots]
  · ext e
    simp only [parentCoeff,dif_pos hv,Matrix.mulVec,Matrix.transpose_apply,dotProduct,treeMatrix]
    rw [expansion]
    simp [treeColumn,parentValue,allRoots,hv]

/-- Exact projection of a single cone in orthonormal compressed coordinates. -/
theorem exact_image [Nonempty V] :
    image (allRoots (V := V)) edgeCoeff parentCoeff =
      convexHull ℝ (Set.range (ApproximationUpper.treeIncidence (V := V))) := by
  apply image_eq_tree_polytope allRoots _ _ parentCoeff_zero
  intro T
  exact tree_witness_of_rows allRoots _ _ T.val T.property (treeMatrix T.val T.property)
    (edge_row T.val T.property) (parent_row T.val T.property)

/-- Coordinate permutations preserve the full-root relations. -/
def ambientPerm (g : Equiv.Perm V) : Ambient V ≃ₗᵢ[ℝ] Ambient V :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (labelPerm g)

@[simp] theorem ambientPerm_apply (g : Equiv.Perm V) (f : Ambient V) (j : Labels V) :
    ambientPerm g f j = f ((labelPerm g).symm j) := rfl

theorem parentAt_permute (g : Equiv.Perm V) (f : Ambient V) (r v : V) :
    parentAt (ambientPerm g f) r v = parentAt f (g.symm r) (g.symm v) := by
  by_cases hv : v = r
  · subst v; simp [parentAt]
  · have hvr : g.symm v ≠ g.symm r := g.symm.injective.ne hv
    simp only [parentAt,dif_pos hv,dif_pos hvr,ambientPerm_apply]
    rfl

theorem relation_permute (g : Equiv.Perm V) (f : Ambient V) (r : V) :
    relation (ambientPerm g f) r = relation f (g.symm r) := by
  change (∑ v, parentAt (ambientPerm g f) r v) - ∑ e : Edge V, ambientPerm g f (.inl e) = _
  simp_rw [parentAt_permute,ambientPerm_apply]
  change (∑ v, parentAt f (g.symm r) (g.symm v)) - (∑ e : Edge V, f (.inl (edgePerm g.symm e))) = _
  rw [Equiv.sum_comp g.symm,Equiv.sum_comp (edgePerm g.symm) (fun e => f (.inl e))]
  rfl

/-- A real isometric action on the invariant subspace, with no symmetry oracle. -/
def spacePerm (g : Equiv.Perm V) : Space V ≃ₗᵢ[ℝ] Space V where
  toFun f := ⟨ambientPerm g f.val,by
    apply LinearMap.mem_ker.mpr
    ext r
    rw [relation_permute]
    exact congrFun (LinearMap.mem_ker.mp f.property) (g.symm r)⟩
  invFun f := ⟨ambientPerm g.symm f.val,by
    apply LinearMap.mem_ker.mpr
    ext r
    rw [relation_permute]
    exact congrFun (LinearMap.mem_ker.mp f.property) (g r)⟩
  left_inv f := by
    apply Subtype.ext
    ext j
    simp only [ambientPerm_apply]
    have ht : labelPerm g.symm = (labelPerm g).symm := congrArg (fun h : Equiv.Perm (Labels V) => h) (labelAction.map_inv g)
    rw [ht]
    simp
  right_inv f := by
    apply Subtype.ext
    ext j
    simp only [ambientPerm_apply]
    have ht : labelPerm g.symm = (labelPerm g).symm := labelAction.map_inv g
    rw [ht]
    simp
  map_add' f h := by apply Subtype.ext; exact (ambientPerm g).map_add f.val h.val
  map_smul' s f := by apply Subtype.ext; exact (ambientPerm g).map_smul s f.val
  norm_map' f := (ambientPerm g).norm_map f.val

def orthogonalMatrix (g : Equiv.Perm V) : Matrix (Index V) (Index V) ℝ :=
  (spacePerm g).toMatrix (basis (V := V)).toBasis (basis (V := V)).toBasis

theorem matrix_orthogonal (g : Equiv.Perm V) :
    orthogonalMatrix g ∈ Matrix.orthogonalGroup (Index V) ℝ :=
  (spacePerm g).toMatrix_mem_unitaryGroup (basis (V := V)) (basis (V := V))

/-- The matrix representation is coherent under composition. -/
theorem matrix_one : orthogonalMatrix (1 : Equiv.Perm V) = 1 := by
  have hp : (spacePerm (1 : Equiv.Perm V)).toLinearEquiv.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    ext j
    change f.val ((labelPerm 1).symm j) = f.val j
    have ht : labelPerm (1 : Equiv.Perm V) = 1 := labelAction.map_one
    rw [ht]
    rfl
  simp only [orthogonalMatrix,hp,LinearMap.toMatrix_id]

theorem matrix_mul (g h : Equiv.Perm V) : orthogonalMatrix (g*h) = orthogonalMatrix g * orthogonalMatrix h := by
  have hp : (spacePerm (g*h)).toLinearEquiv.toLinearMap =
      (spacePerm g).toLinearEquiv.toLinearMap.comp (spacePerm h).toLinearEquiv.toLinearMap := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    ext j
    change f.val ((labelPerm (g*h)).symm j) = f.val ((labelPerm h).symm ((labelPerm g).symm j))
    have ht : labelPerm (g*h) = labelPerm g * labelPerm h := labelAction.map_mul g h
    rw [ht]
    rfl
  simp only [orthogonalMatrix,hp]
  exact LinearMap.toMatrix_comp (basis (V := V)).toBasis (basis (V := V)).toBasis
    (basis (V := V)).toBasis _ _

def orthogonalAction : Equiv.Perm V →* Matrix.orthogonalGroup (Index V) ℝ where
  toFun g := ⟨orthogonalMatrix g,matrix_orthogonal g⟩
  map_one' := Subtype.ext matrix_one
  map_mul' g h := Subtype.ext (matrix_mul g h)

/-- Transpose transport of each original label's compressed coefficient. -/
theorem coeff_cov (g : Equiv.Perm V) (k : Labels V) :
    (orthogonalMatrix g)ᵀ *ᵥ coeff k = coeff ((labelPerm g).symm k) := by
  ext i
  simp only [Matrix.mulVec,Matrix.transpose_apply,dotProduct,orthogonalMatrix,
    LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis,OrthonormalBasis.coe_toBasis_repr_apply]
  rw [expansion]
  rfl

theorem edge_coeff_cov (g : Equiv.Perm V) (e : Edge V) :
    (orthogonalMatrix g)ᵀ *ᵥ edgeCoeff e = edgeCoeff (edgePerm g.symm e) := coeff_cov g (.inl e)

theorem parent_coeff_cov (g : Equiv.Perm V) (r v : V) :
    (orthogonalMatrix g)ᵀ *ᵥ parentCoeff r v = parentCoeff (g.symm r) (g.symm v) := by
  by_cases hv : v = r
  · subst v; simp [parentCoeff]
  · have hvr : g.symm v ≠ g.symm r := g.symm.injective.ne hv
    simp only [parentCoeff,dif_pos hv,dif_pos hvr]
    exact coeff_cov g (.inr ⟨(r,v),by simpa [allRoots] using hv⟩)

def congruence (g : Equiv.Perm V) (Y : Matrix (Index V) (Index V) ℝ) : Matrix (Index V) (Index V) ℝ :=
  orthogonalMatrix g * Y * (orthogonalMatrix g)ᵀ

theorem pair_edges (g : Equiv.Perm V) (Y : Matrix (Index V) (Index V) ℝ) (e f : Edge V) :
    pair (congruence g Y) (edgeCoeff e) (edgeCoeff f) = pair Y
      (edgeCoeff (edgePerm g.symm e)) (edgeCoeff (edgePerm g.symm f)) := by
  rw [congruence,pair_congruence,edge_coeff_cov,edge_coeff_cov]

theorem pair_parents (g : Equiv.Perm V) (Y : Matrix (Index V) (Index V) ℝ) (r v w : V) :
    pair (congruence g Y) (parentCoeff r v) (parentCoeff r w) =
      pair Y (parentCoeff (g.symm r) (g.symm v)) (parentCoeff (g.symm r) (g.symm w)) := by
  rw [congruence,pair_congruence,parent_coeff_cov,parent_coeff_cov]

theorem pair_cross (g : Equiv.Perm V) (Y : Matrix (Index V) (Index V) ℝ) (r v : V) (e : Edge V) :
    pair (congruence g Y) (edgeCoeff e) (parentCoeff r v) =
      pair Y (edgeCoeff (edgePerm g.symm e)) (parentCoeff (g.symm r) (g.symm v)) := by
  rw [congruence,pair_congruence,edge_coeff_cov,parent_coeff_cov]

/-- The orthogonal action preserves all affine constraints, not just tree witnesses. -/
theorem equations_congruence (g : Equiv.Perm V) {Y : Matrix (Index V) (Index V) ℝ} {x : Edge V → ℝ}
    (h : Equations (allRoots (V := V)).active edgeCoeff parentCoeff Y x) :
    Equations (allRoots (V := V)).active edgeCoeff parentCoeff (congruence g Y)
      (fun e => x (edgePerm g.symm e)) := by
  constructor
  · intro e; rw [pair_edges]; exact h.diagonal _
  · intro e f hef; rw [pair_edges]; exact h.edge _ _ ((edgePerm g.symm).injective.ne hef)
  · intro r v w; rw [pair_parents,h.parent]; simp [allRoots]
  · intro r v e hv
    rw [pair_cross]
    apply h.incidence
    simpa [edgePerm,Sym2.mem_map] using hv
  · intro r e _
    simp only [pair_cross]
    change (∑ v ∈ Finset.univ.erase r, pair Y
      (edgeCoeff (edgePerm g.symm e)) (parentCoeff (g.symm r) (g.symm v))) = _
    rw [sum_erase_reindex g (fun v => pair Y
      (edgeCoeff (edgePerm g.symm e)) (parentCoeff (g.symm r) v)) r]
    exact h.conservation _ _ (by intro v _; by_cases he : v = g.symm r <;> simp [allRoots,he])
  · change (∑ e, x (edgePerm g.symm e)) = _
    rw [Equiv.sum_comp (edgePerm g.symm),h.cardinality]

theorem projection_covariant (g : Equiv.Perm V) (Y : Matrix (Index V) (Index V) ℝ) :
    extend (coordinates edgeCoeff (congruence g Y)) =
      permuteVector g (extend (coordinates edgeCoeff Y)) := by
  ext e
  by_cases he : e.IsDiag
  · have hm : (Sym2.map g.symm e).IsDiag := he.map
    simp [extend,he,permuteVector,hm]
  · have hm : ¬(Sym2.map g.symm e).IsDiag := by simpa [Sym2.isDiag_map g.symm.injective] using he
    simp only [extend,dif_pos he,permuteVector,dif_pos hm,coordinates,pair_edges]
    rfl

/-- Complete symmetry endpoint for the compressed single-cone formulation. -/
theorem feasible_congruence (g : Equiv.Perm V) {Y : Matrix (Index V) (Index V) ℝ}
    (hY : Y.PosSemidef)
    (he : Equations (allRoots (V := V)).active edgeCoeff parentCoeff Y (coordinates edgeCoeff Y)) :
    (congruence g Y).PosSemidef ∧
      Equations (allRoots (V := V)).active edgeCoeff parentCoeff (congruence g Y)
        (coordinates edgeCoeff (congruence g Y)) := by
  refine ⟨?_,?_⟩
  · simpa only [congruence, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hY.mul_mul_conjTranspose_same (orthogonalMatrix g)
  · have hx : coordinates edgeCoeff (congruence g Y) =
        fun e => coordinates edgeCoeff Y (edgePerm g.symm e) := by
      ext e; exact pair_edges g Y e e
    rw [hx]
    exact equations_congruence g he

/-- The conjugations form a genuine group action by affine cone automorphisms. -/
theorem congruence_one (Y : Matrix (Index V) (Index V) ℝ) : congruence (1 : Equiv.Perm V) Y = Y := by
  simp [congruence,matrix_one]

theorem congruence_mul (g h : Equiv.Perm V) (Y : Matrix (Index V) (Index V) ℝ) :
    congruence (g*h) Y = congruence g (congruence h Y) := by
  simp only [congruence,matrix_mul,Matrix.transpose_mul,Matrix.mul_assoc]

def congruenceEquiv (g : Equiv.Perm V) :
    Matrix (Index V) (Index V) ℝ ≃ₗ[ℝ] Matrix (Index V) (Index V) ℝ where
  toFun := congruence g
  invFun := congruence g.symm
  left_inv Y := by
    rw [← congruence_mul]
    change congruence (g⁻¹*g) Y = Y
    rw [inv_mul_cancel,congruence_one]
  right_inv Y := by
    rw [← congruence_mul]
    change congruence (g*g⁻¹) Y = Y
    rw [mul_inv_cancel,congruence_one]
  map_add' Y Z := by simp [congruence,Matrix.mul_add,Matrix.add_mul]
  map_smul' s Y := by simp [congruence,Matrix.mul_smul,Matrix.smul_mul]

def affineAction : Equiv.Perm V →*
    (Matrix (Index V) (Index V) ℝ ≃ᵃ[ℝ] Matrix (Index V) (Index V) ℝ) where
  toFun g := (congruenceEquiv g).toAffineEquiv
  map_one' := by ext Y i j; exact congrFun (congrFun (congruence_one Y) i) j
  map_mul' g h := by ext Y i j; exact congrFun (congrFun (congruence_mul g h Y) i) j

theorem slice_preserved (g : Equiv.Perm V) {Y : Matrix (Index V) (Index V) ℝ}
    (he : Y ∈ QuadraticAffine.slice (allRoots (V := V)) edgeCoeff parentCoeff) :
    congruence g Y ∈ QuadraticAffine.slice (allRoots (V := V)) edgeCoeff parentCoeff := by
  have hx : coordinates edgeCoeff (congruence g Y) =
      fun e => coordinates edgeCoeff Y (edgePerm g.symm e) := by
    ext e; exact pair_edges g Y e e
  change Equations (allRoots (V := V)).active edgeCoeff parentCoeff (congruence g Y)
    (coordinates edgeCoeff (congruence g Y))
  rw [hx]
  exact equations_congruence g he

end
end Lemmata.SpanningTreeSymmetricEF.QuadraticOrthogonal
