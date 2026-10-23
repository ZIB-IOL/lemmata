module

public import Lemmata.SpanningTreeSymmetricEF.QuadraticRaw
public import Lemmata.SpanningTreeSymmetricEF.QuadraticAffine
public import Lemmata.SpanningTreeSymmetricEF.FormulationAffine

@[expose] public section


/-! Actual simultaneous row/column permutation action of the all-root lift.
Both affine feasibility and projection covariance are checked. -/
namespace Lemmata.SpanningTreeSymmetricEF.QuadraticSymmetry
open scoped BigOperators Classical
open Matrix FormulationStructure QuadraticCore QuadraticRaw QuadraticAlgebra
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

abbrev Labels (V : Type*) [Fintype V] [DecidableEq V] := Label (allRoots (V := V))

def edgePerm (g : Equiv.Perm V) : Equiv.Perm (Edge V) where
  toFun e := ⟨Sym2.map g e.val,by simpa [Sym2.isDiag_map g.injective] using e.property⟩
  invFun e := ⟨Sym2.map g.symm e.val,by simpa [Sym2.isDiag_map g.symm.injective] using e.property⟩
  left_inv e := by
    apply Subtype.ext
    change Sym2.map g.symm (Sym2.map g e.val) = e.val
    induction e.val using Sym2.inductionOn with | _ u v => simp
  right_inv e := by
    apply Subtype.ext
    change Sym2.map g (Sym2.map g.symm e.val) = e.val
    induction e.val using Sym2.inductionOn with | _ u v => simp

def parentPerm (g : Equiv.Perm V) : Equiv.Perm (ParentIndex (allRoots (V := V))) where
  toFun p := ⟨(g p.val.1,g p.val.2),by simpa [allRoots] using p.property⟩
  invFun p := ⟨(g.symm p.val.1,g.symm p.val.2),by simpa [allRoots] using p.property⟩
  left_inv p := by apply Subtype.ext; simp
  right_inv p := by apply Subtype.ext; simp

def labelPerm (g : Equiv.Perm V) : Equiv.Perm (Labels V) :=
  Equiv.sumCongr (edgePerm g) (parentPerm g)

@[simp] theorem labelPerm_edge (g : Equiv.Perm V) (e : Edge V) :
    labelPerm g (.inl e) = .inl (edgePerm g e) := rfl

@[simp] theorem labelPerm_parent (g : Equiv.Perm V) (p : ParentIndex (allRoots (V := V))) :
    labelPerm g (.inr p) = .inr (parentPerm g p) := rfl

/-- Labels carry a genuine group action, not unrelated permutations. -/
def labelAction : Equiv.Perm V →* Equiv.Perm (Labels V) where
  toFun := labelPerm
  map_one' := by
    apply Equiv.ext
    rintro (e | p)
    · change Sum.inl (edgePerm 1 e) = Sum.inl e
      apply congrArg Sum.inl
      apply Subtype.ext
      change Sym2.map (1 : Equiv.Perm V) e.val = e.val
      induction e.val using Sym2.inductionOn with | _ u v => rfl
    · change Sum.inr (parentPerm 1 p) = Sum.inr p
      rfl
  map_mul' g h := by
    apply Equiv.ext
    rintro (e | p)
    · change Sum.inl (edgePerm (g*h) e) = Sum.inl (edgePerm g (edgePerm h e))
      apply congrArg Sum.inl
      apply Subtype.ext
      change Sym2.map (g*h) e.val = Sym2.map g (Sym2.map h e.val)
      induction e.val using Sym2.inductionOn with | _ u v => rfl
    · rfl

def matrixAction : Equiv.Perm V →* (Matrix (Labels V) (Labels V) ℝ ≃ᵃ[ℝ] Matrix (Labels V) (Labels V) ℝ) :=
  FormulationAffine.matrixAction.comp labelAction

def permuted (g : Equiv.Perm V) (Y : Matrix (Labels V) (Labels V) ℝ) : Matrix (Labels V) (Labels V) ℝ :=
  Y.submatrix (labelPerm g).symm (labelPerm g).symm

theorem pair_reindex {J : Type*} [Fintype J] [DecidableEq J] (t : Equiv.Perm J)
    (Y : Matrix J J ℝ) (u v : J → ℝ) :
    pair (Y.submatrix t.symm t.symm) (u ∘ t.symm) (v ∘ t.symm) = pair Y u v := by
  simp only [pair,Matrix.toBilin'_apply,Matrix.submatrix_apply,Function.comp_apply]
  calc
    _ = ∑ i, ∑ j, u (t.symm i) * Y (t.symm i) j * v j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Equiv.sum_comp t.symm (fun j : J => u (t.symm i) * Y (t.symm i) j * v j)
    _ = _ := Equiv.sum_comp t.symm (fun i : J => ∑ j, u i * Y i j * v j)

theorem single_cov {J : Type*} [DecidableEq J] (t : Equiv.Perm J) (i : J) :
    (Pi.single (t i) 1 : J → ℝ) = Pi.single i 1 ∘ t.symm := by
  ext j
  by_cases hj : j = t i
  · subst j; simp [Pi.single_apply,Function.comp_def]
  · have hi : t.symm j ≠ i := fun hh => hj ((t.symm_apply_eq).mp hh)
    simp [Pi.single_apply,Function.comp_def,hj,Ne.symm hj,hi,Ne.symm hi]

/-- Reindexing the Gram matrix reindexes its edge/parent pairings. -/
theorem edge_coeff_cov (g : Equiv.Perm V) (e : Edge V) :
    edgeCoeff allRoots e = edgeCoeff allRoots (edgePerm g.symm e) ∘ (labelPerm g).symm := by
  have ht : labelPerm g (Sum.inl (edgePerm g.symm e)) = Sum.inl e := by
    apply congrArg Sum.inl
    apply Subtype.ext
    change Sym2.map g (Sym2.map g.symm e.val) = e.val
    induction e.val using Sym2.inductionOn with | _ u v => simp
  simpa only [edgeCoeff,ht] using single_cov (labelPerm g) (.inl (edgePerm g.symm e))

theorem parent_coeff_cov (g : Equiv.Perm V) (r v : V) :
    parentCoeff allRoots r v = parentCoeff allRoots (g.symm r) (g.symm v) ∘ (labelPerm g).symm := by
  by_cases hv : v = r
  · subst v
    ext j
    simp [parentCoeff,allRoots]
    rfl
  · have hvr : g.symm v ≠ g.symm r := g.symm.injective.ne hv
    have ht : labelPerm g (Sum.inr (⟨(g.symm r,g.symm v),by simpa [allRoots] using hvr⟩ : ParentIndex allRoots)) =
        Sum.inr (⟨(r,v),by simpa [allRoots] using hv⟩ : ParentIndex allRoots) := by
      apply congrArg Sum.inr
      apply Subtype.ext
      simp [parentPerm]
    have hs := single_cov (labelPerm g)
      (.inr (⟨(g.symm r,g.symm v),by simpa [allRoots] using hvr⟩ : ParentIndex allRoots))
    rw [ht] at hs
    have ha : v ∈ (allRoots (V := V)).active r := by simp [allRoots, hv]
    have hb : g.symm v ∈ (allRoots (V := V)).active (g.symm r) := by
      simp [allRoots, hvr]
    simpa only [parentCoeff, dite_eq_left ha, dite_eq_left hb] using hs

theorem pair_edges (g : Equiv.Perm V) (Y : Matrix (Labels V) (Labels V) ℝ) (e f : Edge V) :
    pair (permuted g Y) (edgeCoeff allRoots e) (edgeCoeff allRoots f) =
      pair Y (edgeCoeff allRoots (edgePerm g.symm e)) (edgeCoeff allRoots (edgePerm g.symm f)) := by
  rw [edge_coeff_cov g e,edge_coeff_cov g f]
  exact pair_reindex _ Y _ _

theorem pair_parents (g : Equiv.Perm V) (Y : Matrix (Labels V) (Labels V) ℝ) (r v w : V) :
    pair (permuted g Y) (parentCoeff allRoots r v) (parentCoeff allRoots r w) =
      pair Y (parentCoeff allRoots (g.symm r) (g.symm v)) (parentCoeff allRoots (g.symm r) (g.symm w)) := by
  rw [parent_coeff_cov g r v,parent_coeff_cov g r w]
  exact pair_reindex _ Y _ _

theorem pair_cross (g : Equiv.Perm V) (Y : Matrix (Labels V) (Labels V) ℝ) (r v : V) (e : Edge V) :
    pair (permuted g Y) (edgeCoeff allRoots e) (parentCoeff allRoots r v) =
      pair Y (edgeCoeff allRoots (edgePerm g.symm e)) (parentCoeff allRoots (g.symm r) (g.symm v)) := by
  rw [edge_coeff_cov g e,parent_coeff_cov g r v]
  exact pair_reindex _ Y _ _

theorem sum_erase_reindex (g : Equiv.Perm V) (f : V → ℝ) (r : V) :
    (∑ v ∈ Finset.univ.erase r, f (g.symm v)) = ∑ v ∈ Finset.univ.erase (g.symm r), f v := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ r),Finset.sum_erase_eq_sub (Finset.mem_univ (g.symm r))]
  rw [Equiv.sum_comp g.symm]

/-- Every affine equation is preserved by the vertex action. -/
theorem equations_permute (g : Equiv.Perm V) {Y : Matrix (Labels V) (Labels V) ℝ}
    {x : Edge V → ℝ} (h : Equations (allRoots (V := V)).active (edgeCoeff allRoots) (parentCoeff allRoots) Y x) :
    Equations (allRoots (V := V)).active (edgeCoeff allRoots) (parentCoeff allRoots) (permuted g Y)
      (fun e => x (edgePerm g.symm e)) := by
  constructor
  · intro e; rw [pair_edges]; exact h.diagonal _
  · intro e f hef; rw [pair_edges]; exact h.edge _ _ ((edgePerm g.symm).injective.ne hef)
  · intro r v w
    rw [pair_parents,h.parent]
    simp [allRoots]
  · intro r v e hv
    rw [pair_cross]
    apply h.incidence
    simpa [edgePerm,Sym2.mem_map] using hv
  · intro r e _
    simp only [pair_cross]
    change (∑ v ∈ Finset.univ.erase r, pair Y
      (edgeCoeff allRoots (edgePerm g.symm e)) (parentCoeff allRoots (g.symm r) (g.symm v))) = _
    rw [sum_erase_reindex g (fun v => pair Y
      (edgeCoeff allRoots (edgePerm g.symm e)) (parentCoeff allRoots (g.symm r) v)) r]
    exact h.conservation _ _ (by intro v _; by_cases he : v = g.symm r <;> simp [allRoots,he])
  · change (∑ e, x (edgePerm g.symm e)) = _
    rw [Equiv.sum_comp (edgePerm g.symm),h.cardinality]

theorem projection_covariant (g : Equiv.Perm V) (Y : Matrix (Labels V) (Labels V) ℝ) :
    extend (coordinates (edgeCoeff allRoots) (permuted g Y)) =
      permuteVector g (extend (coordinates (edgeCoeff allRoots) Y)) := by
  ext e
  by_cases he : e.IsDiag
  · have hm : (Sym2.map g.symm e).IsDiag := he.map
    simp [extend,he,permuteVector,hm]
  · have hm : ¬(Sym2.map g.symm e).IsDiag := by simpa [Sym2.isDiag_map g.symm.injective] using he
    simp only [extend,dif_pos he,permuteVector,dif_pos hm,coordinates,pair_edges]
    rfl

/-- Full coordinate-permutation equivariance of the concrete exact lift. -/
theorem feasible_permute (g : Equiv.Perm V) {Y : Matrix (Labels V) (Labels V) ℝ}
    (hY : Y.PosSemidef)
    (he : Equations (allRoots (V := V)).active (edgeCoeff allRoots) (parentCoeff allRoots) Y
      (coordinates (edgeCoeff allRoots) Y)) :
    (permuted g Y).PosSemidef ∧
      Equations (allRoots (V := V)).active (edgeCoeff allRoots) (parentCoeff allRoots) (permuted g Y)
        (coordinates (edgeCoeff allRoots) (permuted g Y)) := by
  refine ⟨hY.submatrix _,?_⟩
  have hx : coordinates (edgeCoeff allRoots) (permuted g Y) =
      fun e => coordinates (edgeCoeff allRoots) Y (edgePerm g.symm e) := by
    ext e; exact pair_edges g Y e e
  rw [hx]
  exact equations_permute g he

@[simp] theorem matrixAction_apply (g : Equiv.Perm V) (Y : Matrix (Labels V) (Labels V) ℝ) :
    matrixAction g Y = permuted g Y := rfl

theorem slice_preserved (g : Equiv.Perm V) {Y : Matrix (Labels V) (Labels V) ℝ}
    (he : Y ∈ QuadraticAffine.slice (allRoots (V := V)) (edgeCoeff allRoots) (parentCoeff allRoots)) :
    permuted g Y ∈ QuadraticAffine.slice (allRoots (V := V)) (edgeCoeff allRoots) (parentCoeff allRoots) := by
  have hx : coordinates (edgeCoeff allRoots) (permuted g Y) =
      fun e => coordinates (edgeCoeff allRoots) Y (edgePerm g.symm e) := by
    ext e; exact pair_edges g Y e e
  change Equations (allRoots (V := V)).active (edgeCoeff allRoots) (parentCoeff allRoots) (permuted g Y)
    (coordinates (edgeCoeff allRoots) (permuted g Y))
  rw [hx]
  exact equations_permute g he

end
end Lemmata.SpanningTreeSymmetricEF.QuadraticSymmetry
