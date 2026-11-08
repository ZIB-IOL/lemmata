module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Order.Prod.Lex.Basic

@[expose] public section

namespace Lemmata.RM59.CatalogInvariant

open scoped BigOperators

variable {V W : Type*} [Fintype V] [Fintype W]

def degree (adj : V → V → Bool) (v : V) : ℕ :=
  ∑ w, if adj v w then 1 else 0

def commonNeighborCount (adj : V → V → Bool) (v w : V) : ℕ :=
  ∑ u, if adj v u && adj w u then 1 else 0

def featureA (adj : V → V → Bool) (v : V) : ℕ :=
  ∑ w, commonNeighborCount adj v w ^ 2

def featureB (adj : V → V → Bool) (v : V) : ℕ :=
  ∑ w, ∑ z, if adj w z then
    commonNeighborCount adj v w * commonNeighborCount adj v z else 0

theorem degree_equiv (adj : V → V → Bool) (adj' : W → W → Bool) (e : V ≃ W)
    (he : ∀ v w, adj' (e v) (e w) = adj v w) (v : V) :
    degree adj v = degree adj' (e v) := by
  unfold degree
  exact Fintype.sum_equiv e _ _ (fun w => by rw [he v w])

theorem commonNeighborCount_equiv (adj : V → V → Bool) (adj' : W → W → Bool)
    (e : V ≃ W) (he : ∀ v w, adj' (e v) (e w) = adj v w) (v w : V) :
    commonNeighborCount adj v w = commonNeighborCount adj' (e v) (e w) := by
  unfold commonNeighborCount
  exact Fintype.sum_equiv e _ _ (fun u => by rw [he v u, he w u])

theorem featureA_equiv (adj : V → V → Bool) (adj' : W → W → Bool) (e : V ≃ W)
    (he : ∀ v w, adj' (e v) (e w) = adj v w) (v : V) :
    featureA adj v = featureA adj' (e v) := by
  unfold featureA
  exact Fintype.sum_equiv e _ _ (fun w => by
    rw [commonNeighborCount_equiv adj adj' e he v w])

theorem featureB_equiv (adj : V → V → Bool) (adj' : W → W → Bool) (e : V ≃ W)
    (he : ∀ v w, adj' (e v) (e w) = adj v w) (v : V) :
    featureB adj v = featureB adj' (e v) := by
  unfold featureB
  apply Fintype.sum_equiv e _ _
  intro w
  apply Fintype.sum_equiv e _ _
  intro z
  rw [he w z, commonNeighborCount_equiv adj adj' e he v w,
    commonNeighborCount_equiv adj adj' e he v z]

abbrev VertexFeature := ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ

def vertexFeature (adj : V → V → Bool) (mark : V → ℕ) (v : V) : VertexFeature :=
  toLex (mark v, toLex (degree adj v, toLex (featureA adj v, featureB adj v)))

def featureMultiset (adj : V → V → Bool) (mark : V → ℕ) : Multiset VertexFeature :=
  Finset.univ.val.map (vertexFeature adj mark)

def invariant (adj : V → V → Bool) (mark : V → ℕ) : List VertexFeature :=
  (featureMultiset adj mark).sort (· ≤ ·)

theorem vertexFeature_equiv (adj : V → V → Bool) (adj' : W → W → Bool)
    (mark : V → ℕ) (mark' : W → ℕ) (e : V ≃ W)
    (he : ∀ v w, adj' (e v) (e w) = adj v w) (hm : ∀ v, mark v = mark' (e v))
    (v : V) : vertexFeature adj mark v = vertexFeature adj' mark' (e v) := by
  unfold vertexFeature
  rw [hm v, degree_equiv adj adj' e he v, featureA_equiv adj adj' e he v,
    featureB_equiv adj adj' e he v]

theorem featureMultiset_equiv (adj : V → V → Bool) (adj' : W → W → Bool)
    (mark : V → ℕ) (mark' : W → ℕ) (e : V ≃ W)
    (he : ∀ v w, adj' (e v) (e w) = adj v w) (hm : ∀ v, mark v = mark' (e v)) :
    featureMultiset adj mark = featureMultiset adj' mark' := by
  have hfun : vertexFeature adj mark = (vertexFeature adj' mark') ∘ e := by
    funext v
    exact vertexFeature_equiv adj adj' mark mark' e he hm v
  unfold featureMultiset
  rw [hfun, ← Multiset.map_map, Multiset.map_univ_val_equiv e]

theorem invariant_equiv (adj : V → V → Bool) (adj' : W → W → Bool)
    (mark : V → ℕ) (mark' : W → ℕ) (e : V ≃ W)
    (he : ∀ v w, adj' (e v) (e w) = adj v w) (hm : ∀ v, mark v = mark' (e v)) :
    invariant adj mark = invariant adj' mark' := by
  unfold invariant
  rw [featureMultiset_equiv adj adj' mark mark' e he hm]

def zeroMark [Zero V] [DecidableEq V] (v : V) : ℕ := if v = 0 then 1 else 0

theorem apply_eq_zero_iff [Zero V] [Zero W] (e : V ≃ W) (hzero : e 0 = 0)
    (v : V) : e v = 0 ↔ v = 0 := by
  constructor
  · intro h
    exact e.injective (h.trans hzero.symm)
  · rintro rfl
    exact hzero

theorem zeroMark_equiv [Zero V] [Zero W] [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (hzero : e 0 = 0) (v : V) : zeroMark v = zeroMark (e v) := by
  simp only [zeroMark, apply_eq_zero_iff e hzero]

def contractionAdjacency {F : Type*} [Zero V] [DecidableEq V] [Zero F] [DecidableEq F]
    (T : V → V → V → F) (v w : V) : Bool :=
  decide (v ≠ 0 ∧ w ≠ 0 ∧ v ≠ w ∧ ∀ u, T v w u = 0)

@[simp] theorem contractionAdjacency_zero_left {F : Type*} [Zero V] [DecidableEq V]
    [Zero F] [DecidableEq F] (T : V → V → V → F) (v : V) :
    contractionAdjacency T 0 v = false := by
  simp [contractionAdjacency]

@[simp] theorem contractionAdjacency_self {F : Type*} [Zero V] [DecidableEq V]
    [Zero F] [DecidableEq F] (T : V → V → V → F) (v : V) :
    contractionAdjacency T v v = false := by
  simp [contractionAdjacency]

theorem contractionAdjacency_symm {F : Type*} [Zero V] [DecidableEq V]
    [Zero F] [DecidableEq F] (T : V → V → V → F)
    (hsymm : ∀ v w u, T v w u = T w v u) (v w : V) :
    contractionAdjacency T v w = contractionAdjacency T w v := by
  unfold contractionAdjacency
  apply Bool.decide_congr
  constructor
  · rintro ⟨hv, hw, hvw, h⟩
    exact ⟨hw, hv, Ne.symm hvw, fun u => (hsymm w v u).trans (h u)⟩
  · rintro ⟨hw, hv, hwv, h⟩
    exact ⟨hv, hw, Ne.symm hwv, fun u => (hsymm v w u).trans (h u)⟩

theorem contractionAdjacency_equiv {F : Type*} [Zero V] [Zero W]
    [DecidableEq V] [DecidableEq W] [Zero F] [DecidableEq F]
    (T : V → V → V → F) (T' : W → W → W → F) (e : V ≃ W)
    (hzero : e 0 = 0) (hT : ∀ v w u, T' (e v) (e w) (e u) = T v w u)
    (v w : V) : contractionAdjacency T' (e v) (e w) = contractionAdjacency T v w := by
  have hcon : (∀ u, T' (e v) (e w) u = 0) ↔ ∀ u, T v w u = 0 := by
    constructor
    · intro h u
      rw [← hT v w u]
      exact h (e u)
    · intro h u
      obtain ⟨a, rfl⟩ := e.surjective u
      rw [hT v w a]
      exact h a
  unfold contractionAdjacency
  apply Bool.decide_congr
  simp only [ne_eq, apply_eq_zero_iff e hzero, e.injective.eq_iff, hcon]

def contractionInvariant {F : Type*} [Zero V] [DecidableEq V] [Zero F] [DecidableEq F]
    (T : V → V → V → F) : List VertexFeature :=
  invariant (contractionAdjacency T) zeroMark

theorem contractionInvariant_equiv {F : Type*} [Zero V] [Zero W]
    [DecidableEq V] [DecidableEq W] [Zero F] [DecidableEq F]
    (T : V → V → V → F) (T' : W → W → W → F) (e : V ≃ W)
    (hzero : e 0 = 0) (hT : ∀ v w u, T' (e v) (e w) (e u) = T v w u) :
    contractionInvariant T = contractionInvariant T' := by
  exact invariant_equiv (contractionAdjacency T) (contractionAdjacency T') zeroMark zeroMark e
    (contractionAdjacency_equiv T T' e hzero hT) (zeroMark_equiv e hzero)

end Lemmata.RM59.CatalogInvariant
