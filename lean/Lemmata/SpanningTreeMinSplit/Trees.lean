module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Finset.Sym
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

public section

namespace Lemmata.SpanningTreeMinSplit

open scoped BigOperators Classical
open SimpleGraph

variable {n : ℕ}

/-- Actual spanning trees on the labelled vertex set. -/
abbrev Tree (n : ℕ) := {T : SimpleGraph (Fin n) // T.IsTree}

/-- The incidence vector on unordered pairs, including zero on diagonal pairs. -/
noncomputable def edgeValue (T : Tree n) (e : Sym2 (Fin n)) : ℝ := by
  classical
  exact if e ∈ T.val.edgeSet then 1 else 0

/-- Subtour slack with subtraction in the reals, not truncated subtraction. -/
noncomputable def subtourSlack (T : Tree n) (S : Finset (Fin n)) : ℝ :=
  (S.card : ℝ) - 1 - ∑ e ∈ S.sym2, edgeValue T e

/- The unique-path construction and the acyclicity arguments below adapt
SymmetricEF/TreeModels.lean (rootWalk and treeOrientation_projects).
The parent-edge bijection adapts SymmetricEF/QuadraticTrees.lean.
Neither parent project nor its optimization infrastructure is imported. -/

/-- Choose the unique path from the root to a vertex. -/
noncomputable def rootWalk (T : Tree n) (r v : Fin n) : T.val.Walk r v :=
  Classical.choose (T.property.existsUnique_path r v)

theorem rootWalk_isPath (T : Tree n) (r v : Fin n) :
    (rootWalk T r v).IsPath :=
  (Classical.choose_spec (T.property.existsUnique_path r v)).1

/-- Parent in the rooted actual tree, extended to fix the root. -/
noncomputable def parent (T : Tree n) (r v : Fin n) : Fin n :=
  if v = r then r else (rootWalk T r v).penultimate

@[simp] theorem parent_root (T : Tree n) (r : Fin n) : parent T r r = r := by
  simp [parent]

theorem parent_adj (T : Tree n) (r v : Fin n) (hv : v ≠ r) :
    T.val.Adj v (parent T r v) := by
  rw [parent, ite_eq_right hv]
  exact ((rootWalk T r v).adj_penultimate (Walk.not_nil_of_ne hv.symm)).symm

theorem parent_ne_self (T : Tree n) (r v : Fin n) (hv : v ≠ r) :
    parent T r v ≠ v :=
  (parent_adj T r v hv).ne.symm

theorem parent_support (T : Tree n) (r v : Fin n) (hv : v ≠ r) :
    parent T r v ∈ (rootWalk T r v).support := by
  rw [parent, ite_eq_right hv]
  exact List.mem_of_mem_dropLast ((rootWalk T r v).penultimate_mem_dropLast_support
    (Walk.not_nil_of_ne hv.symm))

theorem parent_eq_iff (T : Tree n) (r v w : Fin n) (hv : v ≠ r) :
    parent T r v = w ↔ T.val.Adj v w ∧ w ∈ (rootWalk T r v).support := by
  constructor
  · rintro rfl
    exact ⟨parent_adj T r v hv, parent_support T r v hv⟩
  · intro h
    rw [parent, ite_eq_right hv]
    exact (T.property.isAcyclic.eq_penultimate_of_adj_end
      (rootWalk_isPath T r v) h.1 h.2).symm

/-- An edge between nonroot vertices has exactly one child-to-parent orientation. -/
theorem edge_orientation (T : Tree n) (r a b : Fin n)
    (ha : a ≠ r) (hb : b ≠ r) (_hab : a ≠ b) :
    (if T.val.Adj a b then (1 : ℝ) else 0) =
      (if parent T r a = b then 1 else 0) +
      (if parent T r b = a then 1 else 0) := by
  classical
  simp only [parent_eq_iff T r a b ha, parent_eq_iff T r b a hb]
  by_cases hab : T.val.Adj a b
  · by_cases hba : b ∈ (rootWalk T r a).support
    · have hab' := T.property.isAcyclic.ne_mem_support_of_support_of_adj_of_isPath
        (rootWalk_isPath T r a) (rootWalk_isPath T r b) hab hba
      simp [hab, hab.symm, hba, hab']
    · have hab' := T.property.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
        (rootWalk_isPath T r b) (rootWalk_isPath T r a) hab.symm hba
      simp [hab, hab.symm, hba, hab']
  · have hba : ¬ T.val.Adj b a := fun h => hab h.symm
    simp [hab, hba]

/-- Nonroot vertices, indexing actual parent edges. -/
abbrev Child (r : Fin n) := {v : Fin n // v ≠ r}

/-- The actual tree edge joining a child to its parent. -/
noncomputable def parentTreeEdge (T : Tree n) (r : Fin n) (v : Child r) :
    T.val.edgeSet :=
  ⟨s(v.val, parent T r v.val), parent_adj T r v.val v.property⟩

theorem parentTreeEdge_injective (T : Tree n) (r : Fin n) :
    Function.Injective (parentTreeEdge T r) := by
  intro v w he
  have he' : s(v.val, parent T r v.val) = s(w.val, parent T r w.val) :=
    congrArg Subtype.val he
  rcases Sym2.eq_iff.mp he' with h | h
  · exact Subtype.ext h.1
  · have hadj : T.val.Adj v.val w.val := h.2 ▸ parent_adj T r v.val v.property
    have hn := T.property.isAcyclic.ne_mem_support_of_support_of_adj_of_isPath
      (rootWalk_isPath T r v.val) (rootWalk_isPath T r w.val) hadj
      (h.2 ▸ parent_support T r v.val v.property)
    exact (hn (h.1 ▸ parent_support T r w.val w.property)).elim

/-- The parent-edge map bijects nonroot vertices with actual tree edges. -/
theorem parentTreeEdge_bijective (T : Tree n) (r : Fin n) :
    Function.Bijective (parentTreeEdge T r) := by
  classical
  have hc : Fintype.card (Child r) = Fintype.card T.val.edgeSet := by
    have ht := T.property.card_edgeFinset
    have hv : Fintype.card (Child r) = Fintype.card (Fin n) - 1 := by
      simp [Child, Fintype.card_subtype_compl]
    rw [hv]
    simpa [SimpleGraph.edgeFinset] using (Nat.eq_sub_of_add_eq ht).symm
  exact (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨parentTreeEdge_injective T r, hc⟩

/-- Reindex the internal edges of a subset by their nonroot children. -/
theorem internal_edges_eq_parents (T : Tree n) (S : Finset (Fin n)) (r : Fin n) :
    (∑ e ∈ S.sym2, edgeValue T e) =
      ∑ v ∈ S.erase r, if parent T r v ∈ S then (1 : ℝ) else 0 := by
  classical
  simp only [edgeValue]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun v _ => s(v, parent T r v))
  · intro v hv
    obtain ⟨hv, hp⟩ := Finset.mem_filter.mp hv
    have hvr := (Finset.mem_erase.mp hv).1
    exact Finset.mem_filter.mpr
      ⟨Finset.mk_mem_sym2_iff.mpr ⟨(Finset.mem_erase.mp hv).2, hp⟩,
        parent_adj T r v hvr⟩
  · intro v hv w hw he
    have hvr := (Finset.mem_erase.mp (Finset.mem_filter.mp hv).1).1
    have hwr := (Finset.mem_erase.mp (Finset.mem_filter.mp hw).1).1
    have hh : parentTreeEdge T r ⟨v, hvr⟩ = parentTreeEdge T r ⟨w, hwr⟩ :=
      Subtype.ext he
    exact congrArg Subtype.val (parentTreeEdge_injective T r hh)
  · intro e he
    obtain ⟨heS, heT⟩ := Finset.mem_filter.mp he
    obtain ⟨v, hv⟩ := (parentTreeEdge_bijective T r).surjective ⟨e, heT⟩
    have hv' : s(v.val, parent T r v.val) = e := congrArg Subtype.val hv
    rw [← hv', Finset.mk_mem_sym2_iff] at heS
    exact ⟨v.val, Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨v.property, heS.1⟩, heS.2⟩, hv'⟩
  · intro _ _
    rfl

/-- Subtour slack counts children in the subset whose parent is outside it. -/
theorem subtourSlack_eq_splits (T : Tree n) (S : Finset (Fin n))
    (r : Fin n) (hr : r ∈ S) :
    subtourSlack T S =
      ∑ v ∈ S.erase r, if parent T r v ∉ S then (1 : ℝ) else 0 := by
  classical
  have hcard : ((S.erase r).card : ℝ) = (S.card : ℝ) - 1 := by
    have h := Finset.card_erase_add_one hr
    have h' : ((S.erase r).card : ℝ) + 1 = (S.card : ℝ) := by exact_mod_cast h
    linarith
  have hsplit :
      (∑ v ∈ S.erase r, if parent T r v ∈ S then (1 : ℝ) else 0) +
      (∑ v ∈ S.erase r, if parent T r v ∉ S then (1 : ℝ) else 0) =
      ((S.erase r).card : ℝ) := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _v ∈ S.erase r, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases hp : parent T r v ∈ S <;> simp [hp]
      _ = _ := by simp
  rw [subtourSlack, internal_edges_eq_parents T S r]
  linarith

end Lemmata.SpanningTreeMinSplit
