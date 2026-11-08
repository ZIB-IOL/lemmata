module

public import Lemmata.RM59.Compute.GraphCache
public meta import Lemmata.RM59.Compute.GraphCache
public import Lemmata.RM59.Proof.CatalogInvariant
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Init.Data.Vector.Lemmas
public import Init.Data.Vector.OfFn

@[expose] public section

namespace Lemmata.RM59.GraphCache

open scoped BigOperators

variable {n : ℕ}

theorem bump_get (row : Vector ℕ n) (v w : Fin n) :
    (bump row v).get w = row.get w + if v = w then 1 else 0 := by
  change (row.set v.val (row[v.val] + 1) v.isLt)[w.val] =
    row[w.val] + if v = w then 1 else 0
  rw [Vector.getElem_set]
  by_cases h : v = w
  · subst w
    simp
  · have hvw : v.val ≠ w.val := fun hval => h (Fin.ext hval)
    simp [h, hvw]

theorem addNeighbors_get (row : Vector ℕ n) (vertices : List (Fin n)) (w : Fin n) :
    (addNeighbors row vertices).get w =
      row.get w + (vertices.map fun v => if v = w then 1 else 0).sum := by
  induction vertices generalizing row with
  | nil => simp [addNeighbors]
  | cons v vertices ih =>
    simp only [addNeighbors, List.foldl_cons]
    rw [← addNeighbors, ih, bump_get]
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem addWalks_get (neighbors : Fin n → List (Fin n)) (row : Vector ℕ n)
    (vertices : List (Fin n)) (w : Fin n) :
    (addWalks neighbors row vertices).get w = row.get w +
      (vertices.map fun u => ((neighbors u).map fun z => if z = w then 1 else 0).sum).sum := by
  induction vertices generalizing row with
  | nil => simp [addWalks]
  | cons v vertices ih =>
    simp only [addWalks, List.foldl_cons]
    rw [← addWalks, ih, addNeighbors_get]
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem list_sum_eq_univ_ite (vertices : List (Fin n)) (hn : vertices.Nodup)
    (f : Fin n → ℕ) :
    (vertices.map f).sum = ∑ v, if v ∈ vertices then f v else 0 := by
  induction vertices with
  | nil => simp
  | cons v vertices ih =>
    have hnot : v ∉ vertices := (List.nodup_cons.mp hn).1
    have htail : vertices.Nodup := (List.nodup_cons.mp hn).2
    rw [List.map_cons, List.sum_cons, ih htail]
    have hsplit (w : Fin n) :
        (if w ∈ v :: vertices then f w else 0) =
          (if w = v then f w else 0) + (if w ∈ vertices then f w else 0) := by
      by_cases hw : w = v
      · subst w
        simp [hnot]
      · simp [List.mem_cons, hw]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    simp

theorem neighbors_sum_eq (adj : Fin n → Fin n → Bool)
    (neighbors : Fin n → List (Fin n)) (hn : ∀ v, (neighbors v).Nodup)
    (hm : ∀ v w, w ∈ neighbors v ↔ adj v w = true) (v : Fin n) (f : Fin n → ℕ) :
    ((neighbors v).map f).sum = ∑ w, if adj v w then f w else 0 := by
  rw [list_sum_eq_univ_ite (neighbors v) (hn v)]
  simp only [hm]

private theorem neighbors_delta_sum (adj : Fin n → Fin n → Bool)
    (neighbors : Fin n → List (Fin n)) (hn : ∀ v, (neighbors v).Nodup)
    (hm : ∀ v w, w ∈ neighbors v ↔ adj v w = true) (u w : Fin n) :
    ((neighbors u).map fun z => if z = w then 1 else 0).sum = if adj u w then 1 else 0 := by
  rw [neighbors_sum_eq adj neighbors hn hm u]
  have hsplit (z : Fin n) :
      (if adj u z then if z = w then 1 else 0 else 0) =
        (if z = w then if adj u z then 1 else 0 else 0) := by
    by_cases h : z = w <;> simp [h]
  simp_rw [hsplit]
  simp

theorem commonRow_get (adj : Fin n → Fin n → Bool)
    (neighbors : Fin n → List (Fin n)) (hn : ∀ v, (neighbors v).Nodup)
    (hm : ∀ v w, w ∈ neighbors v ↔ adj v w = true)
    (hs : ∀ v w, adj v w = adj w v) (v w : Fin n) :
    (commonRow neighbors v).get w = CatalogInvariant.commonNeighborCount adj v w := by
  unfold commonRow
  rw [addWalks_get]
  have hz : (Vector.replicate n (0 : ℕ)).get w = 0 := by
    change (Vector.replicate n (0 : ℕ))[w.val] = 0
    exact Vector.getElem_replicate w.isLt
  rw [hz]
  simp_rw [neighbors_delta_sum adj neighbors hn hm]
  rw [zero_add, neighbors_sum_eq adj neighbors hn hm v]
  unfold CatalogInvariant.commonNeighborCount
  apply Finset.sum_congr rfl
  intro u _
  rw [hs u w]
  cases hv : adj v u <;> cases hw : adj w u <;> simp [hv, hw]

theorem countTable_get (neighbors : Fin n → List (Fin n)) (v : Fin n) :
    (countTable neighbors).get v = commonRow neighbors v := by
  change (Vector.ofFn fun u => commonRow neighbors u)[v.val] = _
  exact Vector.getElem_ofFn v.isLt

theorem countTable_entry (adj : Fin n → Fin n → Bool)
    (neighbors : Fin n → List (Fin n)) (hn : ∀ v, (neighbors v).Nodup)
    (hm : ∀ v w, w ∈ neighbors v ↔ adj v w = true)
    (hs : ∀ v w, adj v w = adj w v) (v w : Fin n) :
    ((countTable neighbors).get v).get w = CatalogInvariant.commonNeighborCount adj v w := by
  rw [countTable_get]
  exact commonRow_get adj neighbors hn hm hs v w

private theorem foldl_add_eq_sum {α : Type*} (vertices : List α) (f : α → ℕ) (start : ℕ) :
    vertices.foldl (fun acc z => acc + f z) start = start + (vertices.map f).sum := by
  induction vertices generalizing start with
  | nil => simp
  | cons v vertices ih => simp [List.foldl_cons, ih, Nat.add_assoc]

theorem neighborWeightedSum_eq (row : Vector ℕ n) (vertices : List (Fin n)) (w : Fin n) :
    neighborWeightedSum row vertices w = (vertices.map fun z => row.get w * row.get z).sum := by
  unfold neighborWeightedSum
  by_cases h : row.get w = 0
  · simp [h]
  · simp [h, foldl_add_eq_sum]

def cachedVertexFeature (neighbors : Fin n → List (Fin n))
    (counts : Vector (Vector ℕ n) n) (mark : Fin n → ℕ) (v : Fin n) :
    CatalogInvariant.VertexFeature :=
  toLex (mark v, toLex ((neighbors v).length,
    toLex (∑ w, ((counts.get v).get w) ^ 2,
      ∑ w, neighborWeightedSum (counts.get v) (neighbors w) w)))

theorem cachedVertexFeature_eq (adj : Fin n → Fin n → Bool)
    (neighbors : Fin n → List (Fin n)) (hn : ∀ v, (neighbors v).Nodup)
    (hm : ∀ v w, w ∈ neighbors v ↔ adj v w = true)
    (counts : Vector (Vector ℕ n) n)
    (hc : ∀ v w, (counts.get v).get w = CatalogInvariant.commonNeighborCount adj v w)
    (mark : Fin n → ℕ) (v : Fin n) :
    cachedVertexFeature neighbors counts mark v = CatalogInvariant.vertexFeature adj mark v := by
  have hd : (neighbors v).length = CatalogInvariant.degree adj v := by
    have h := neighbors_sum_eq adj neighbors hn hm v (fun _ => 1)
    simpa [CatalogInvariant.degree] using h
  have hb : (∑ w, ((neighbors w).map fun z =>
      CatalogInvariant.commonNeighborCount adj v w *
        CatalogInvariant.commonNeighborCount adj v z).sum) = CatalogInvariant.featureB adj v := by
    unfold CatalogInvariant.featureB
    apply Finset.sum_congr rfl
    intro w _
    exact neighbors_sum_eq adj neighbors hn hm w _
  unfold cachedVertexFeature CatalogInvariant.vertexFeature
  simp only [neighborWeightedSum_eq, hc, hd, CatalogInvariant.featureA, hb]

def cachedInvariant (neighbors : Fin n → List (Fin n)) (mark : Fin n → ℕ) :
    List CatalogInvariant.VertexFeature :=
  let counts := countTable neighbors
  (Finset.univ.val.map (cachedVertexFeature neighbors counts mark)).sort (· ≤ ·)

theorem cachedInvariant_eq (adj : Fin n → Fin n → Bool)
    (neighbors : Fin n → List (Fin n)) (hn : ∀ v, (neighbors v).Nodup)
    (hm : ∀ v w, w ∈ neighbors v ↔ adj v w = true)
    (hs : ∀ v w, adj v w = adj w v) (mark : Fin n → ℕ) :
    cachedInvariant neighbors mark = CatalogInvariant.invariant adj mark := by
  have hfun : cachedVertexFeature neighbors (countTable neighbors) mark =
      CatalogInvariant.vertexFeature adj mark := by
    funext v
    exact cachedVertexFeature_eq adj neighbors hn hm (countTable neighbors)
      (countTable_entry adj neighbors hn hm hs) mark v
  change (Finset.univ.val.map
    (cachedVertexFeature neighbors (countTable neighbors) mark)).sort (· ≤ ·) =
      (Finset.univ.val.map (CatalogInvariant.vertexFeature adj mark)).sort (· ≤ ·)
  rw [hfun]

end Lemmata.RM59.GraphCache
