module

/- Actual parent edges used in the exact quadratic Gram lift.
No orientation or spanning-tree certificate is supplied as an assumption. -/
public import Lemmata.SpanningTreeSymmetricEF.FormulationStructure

@[expose] public section


namespace Lemmata.SpanningTreeSymmetricEF.QuadraticTrees
open scoped BigOperators Classical
open SimpleGraph TreeModels FormulationStructure
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Child (r : V) := {v : V // v ≠ r}

/-- The published parent transported to the original vertex type. -/
def parent {T : SimpleGraph V} (hT : T.IsTree) (r : V) (v : Child r) : V :=
  GraphBridge.parent hT r v.val

omit [DecidableEq V] in
/-- Equality to the source's unique-path description of the parent. -/
theorem parent_eq_penultimate {T : SimpleGraph V} (hT : T.IsTree) (r : V) (v : Child r) :
    parent hT r v = (rootWalk hT r v.val).penultimate :=
  GraphBridge.parent_eq_penultimate hT r v.val v.property

omit [DecidableEq V] in
theorem parent_adj {T : SimpleGraph V} (hT : T.IsTree) (r : V) (v : Child r) :
    T.Adj v.val (parent hT r v) :=
  GraphBridge.parent_adj hT r v.val v.property

omit [DecidableEq V] in
theorem parent_support {T : SimpleGraph V} (hT : T.IsTree) (r : V) (v : Child r) :
    parent hT r v ∈ (rootWalk hT r v.val).support :=
  GraphBridge.parent_support hT r v.val v.property

def parentEdge {T : SimpleGraph V} (hT : T.IsTree) (r : V) (v : Child r) : Edge V :=
  ⟨s(v.val,parent hT r v), by simpa using (parent_adj hT r v).ne⟩

omit [DecidableEq V] in
theorem parentEdge_mem {T : SimpleGraph V} (hT : T.IsTree) (r : V) (v : Child r) :
    (parentEdge hT r v).val ∈ T.edgeSet := by
  exact parent_adj hT r v

theorem parent_orientation {T : SimpleGraph V} (hT : T.IsTree) (r : V) (v : Child r) :
    treeOrientation hT r v.val (parent hT r v) = 1 := by
  simp [treeOrientation, parent_adj hT r v, parent_support hT r v]

omit [DecidableEq V] in
theorem parentEdge_injective {T : SimpleGraph V} (hT : T.IsTree) (r : V) :
    Function.Injective (parentEdge hT r) := by
  intro v w he
  apply (GraphBridge.parentTreeEdge_bijective hT r).injective
  apply Subtype.ext
  rw [GraphBridge.parentTreeEdge_val, GraphBridge.parentTreeEdge_val]
  exact congrArg Subtype.val he

/-- The parent-edge map is a bijection from nonroot vertices to actual tree edges. -/
def parentTreeEdge {T : SimpleGraph V} (hT : T.IsTree) (r : V) (v : Child r) : T.edgeSet :=
  ⟨(parentEdge hT r v).val, parentEdge_mem hT r v⟩

omit [DecidableEq V] in
theorem parentTreeEdge_bijective {T : SimpleGraph V} (hT : T.IsTree) (r : V) :
    Function.Bijective (parentTreeEdge hT r) := by
  have heq : parentTreeEdge hT r = GraphBridge.parentTreeEdge hT r := by
    funext v
    apply Subtype.ext
    exact (GraphBridge.parentTreeEdge_val hT r v).symm
  rw [heq]
  exact GraphBridge.parentTreeEdge_bijective hT r

/-- Reindex an actual tree-edge sum by its children. -/
theorem sum_parentEdge {T : SimpleGraph V} (hT : T.IsTree) (r : V) (f : Edge V → ℝ) :
    (∑ v : Child r, f (parentEdge hT r v)) = ∑ e : Edge V, if e.val ∈ T.edgeSet then f e else 0 := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun v _ => parentEdge hT r v)
  · intro v _
    simp [parentEdge_mem hT r v]
  · intro v _ w _ h
    exact parentEdge_injective hT r h
  · intro e he
    obtain ⟨v,hv⟩ := (parentTreeEdge_bijective hT r).surjective ⟨e.val,(Finset.mem_filter.mp he).2⟩
    refine ⟨v,Finset.mem_univ _,?_⟩
    exact Subtype.ext (congrArg (fun t : T.edgeSet => t.val) hv)
  · intro v _
    rfl

/-- Edge-basis parent vector, extended by zero at the root. -/
def parentVector {T : SimpleGraph V} (hT : T.IsTree) (r v : V) : Edge V → ℝ :=
  if h : v ≠ r then Pi.single (parentEdge hT r ⟨v,h⟩) 1 else 0

theorem parentVector_zero {T : SimpleGraph V} (hT : T.IsTree) (r : V) :
    parentVector hT r r = 0 := by simp [parentVector]

theorem parentVector_incidence {T : SimpleGraph V} (hT : T.IsTree) (r v : V) (e : Edge V)
    (hv : v ∉ e.val) : parentVector hT r v e = 0 := by
  classical
  by_cases hvr : v ≠ r
  · have he : e ≠ parentEdge hT r ⟨v,hvr⟩ := by
      intro he
      apply hv
      rw [he]
      simp [parentEdge]
    simp [parentVector, hvr, he]
  · simp [parentVector, hvr]

theorem parentVector_orthonormal {T : SimpleGraph V} (hT : T.IsTree) (r v w : V) :
    parentVector hT r v ⬝ᵥ parentVector hT r w = if v = w ∧ v ≠ r then 1 else 0 := by
  classical
  by_cases hv : v ≠ r <;> by_cases hw : w ≠ r
  · have he : parentEdge hT r ⟨v,hv⟩ = parentEdge hT r ⟨w,hw⟩ ↔ v = w := by
      constructor
      · intro h; exact congrArg Subtype.val (parentEdge_injective hT r h)
      · intro h; subst w; rfl
    simp only [parentVector, dite_eq_left hv, dite_eq_left hw, single_dotProduct, one_mul]
    by_cases hvw : v = w
    · subst w; simp [hv]
    · have hne : parentEdge hT r ⟨v,hv⟩ ≠ parentEdge hT r ⟨w,hw⟩ := fun h => hvw (he.mp h)
      simp [hne, hvw]
  · have hwr : w = r := not_ne_iff.mp hw
    subst w
    simp [parentVector, hv]
  · simp [parentVector, hv, hw]
  · simp [parentVector, hv, hw]

theorem parentVector_sum {T : SimpleGraph V} (hT : T.IsTree) (r : V) (e : Edge V) :
    (∑ v, parentVector hT r v e) = if e.val ∈ T.edgeSet then 1 else 0 := by
  classical
  have hsum := sum_parentEdge hT r (fun f => (Pi.single f 1 : Edge V → ℝ) e)
  have hleft : (∑ v : Child r, (Pi.single (parentEdge hT r v) 1 : Edge V → ℝ) e) =
      ∑ v, parentVector hT r v e := by
    symm
    rw [Fintype.sum_eq_add_sum_subtype_ne _ r, parentVector_zero]
    simp only [Pi.zero_apply, zero_add]
    apply Finset.sum_congr rfl
    intro v _
    simp only [parentVector, dite_eq_left v.property]
  rw [hleft] at hsum
  rw [hsum, Finset.sum_eq_single e]
  · simp
  · intro f _ hfe
    simp [hfe.symm]
  · simp

end
end Lemmata.SpanningTreeSymmetricEF.QuadraticTrees
