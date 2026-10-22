module

public import Lemmata.SpanningTreeSymmetricEF.QuadraticCompression

@[expose] public section


/-! Concrete matrix orders and exactness endpoints, without symmetry hypotheses.
The compressed all-root lift's equivariance is checked separately. -/
namespace Lemmata.SpanningTreeSymmetricEF.QuadraticOrders
open scoped BigOperators Classical
open FormulationStructure QuadraticCore QuadraticRaw
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

def orderedToEdge [LinearOrder V] (p : ParentIndex (orderedRoots (V := V))) : Edge V :=
  ⟨s(p.val.1,p.val.2),by
    have h : p.val.1 < p.val.2 := by simpa [orderedRoots] using p.property
    simpa using h.ne⟩

theorem orderedToEdge_bijective [LinearOrder V] :
    Function.Bijective (orderedToEdge (V := V)) := by
  constructor
  · intro p q he
    have hp : p.val.1 < p.val.2 := by simpa [orderedRoots] using p.property
    have hq : q.val.1 < q.val.2 := by simpa [orderedRoots] using q.property
    have hh : s(p.val.1,p.val.2) = s(q.val.1,q.val.2) := congrArg Subtype.val he
    rcases Sym2.eq_iff.mp hh with h | h
    · exact Subtype.ext (Prod.ext h.1 h.2)
    · have hl : p.val.2 < p.val.1 := by simpa [← h.1,← h.2] using hq
      exact (hp.asymm hl).elim
  · rintro ⟨e,he⟩
    induction e using Sym2.inductionOn with
    | _ u v =>
      have hne : u ≠ v := by simpa using he
      rcases lt_or_gt_of_ne hne with huv | hvu
      · refine ⟨⟨(u,v),by simpa [orderedRoots] using huv⟩,?_⟩
        rfl
      · refine ⟨⟨(v,u),by simpa [orderedRoots] using hvu⟩,?_⟩
        apply Subtype.ext
        exact Sym2.eq_swap

theorem asymmetric_order [LinearOrder V] :
    Fintype.card (Label (orderedRoots (V := V))) = 2 * (Fintype.card V).choose 2 := by
  have hc : Fintype.card (ParentIndex (orderedRoots (V := V))) = Fintype.card (Edge V) :=
    Fintype.card_of_bijective orderedToEdge_bijective
  rw [Fintype.card_sum,hc,card_edges]
  omega

def other [Nontrivial V] (r : V) : V := Classical.choose (exists_ne r)

theorem other_ne [Nontrivial V] (r : V) : other r ≠ r := Classical.choose_spec (exists_ne r)

/-- Remove one parent coordinate for every root. -/
def symmetricDeletion [Nontrivial V] : QuadraticCompression.Deletion (allRoots (V := V)) where
  roots := Finset.univ
  child := other
  child_mem r _ := by simpa [allRoots] using other_ne r
  full _ _ := rfl

def symmetricCompressed [Nontrivial V] : Set (Sym2 V → ℝ) :=
  image allRoots (QuadraticCompression.edgeCoeff allRoots symmetricDeletion)
    (QuadraticCompression.parentCoeff allRoots symmetricDeletion)

theorem symmetric_compressed_exact [Nonempty V] [Nontrivial V] :
    symmetricCompressed (V := V) = convexHull ℝ (Set.range (ApproximationUpper.treeIncidence (V := V))) :=
  QuadraticCompression.exact_image _ _

theorem symmetric_compressed_order [Nontrivial V] :
    Fintype.card (QuadraticCompression.Kept (allRoots (V := V)) symmetricDeletion) =
      3 * (Fintype.card V).choose 2 - Fintype.card V := by
  rw [QuadraticCompression.compressed_order,symmetric_order]
  simp [symmetricDeletion]

/-- Remove one parent coordinate for the smallest root only. -/
def asymmetricDeletion [LinearOrder V] [OrderBot V] [Nontrivial V] :
    QuadraticCompression.Deletion (orderedRoots (V := V)) where
  roots := {⊥}
  child := fun _ => other (⊥ : V)
  child_mem r hr := by
    have hr' : r = ⊥ := by simpa using hr
    subst r
    have hl : (⊥ : V) < other ⊥ := bot_lt_iff_ne_bot.mpr (other_ne ⊥)
    simpa [orderedRoots] using hl
  full r hr := by
    have hr' : r = ⊥ := by simpa using hr
    subst r
    ext v
    simp [orderedRoots,bot_lt_iff_ne_bot]

def asymmetricCompressed [LinearOrder V] [OrderBot V] [Nontrivial V] : Set (Sym2 V → ℝ) :=
  image orderedRoots (QuadraticCompression.edgeCoeff orderedRoots asymmetricDeletion)
    (QuadraticCompression.parentCoeff orderedRoots asymmetricDeletion)

theorem asymmetric_compressed_exact [Nonempty V] [LinearOrder V] [OrderBot V] [Nontrivial V] :
    asymmetricCompressed (V := V) = convexHull ℝ (Set.range (ApproximationUpper.treeIncidence (V := V))) :=
  QuadraticCompression.exact_image _ _

theorem asymmetric_compressed_order [LinearOrder V] [OrderBot V] [Nontrivial V] :
    Fintype.card (QuadraticCompression.Kept (orderedRoots (V := V)) asymmetricDeletion) =
      2 * (Fintype.card V).choose 2 - 1 := by
  rw [QuadraticCompression.compressed_order,asymmetric_order]
  simp [asymmetricDeletion]

end
end Lemmata.SpanningTreeSymmetricEF.QuadraticOrders
