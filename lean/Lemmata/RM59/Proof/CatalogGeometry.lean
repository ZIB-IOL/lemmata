module

public import Lemmata.RM59.Proof.CatalogGraph
public import Lemmata.RM59.Proof.CatalogUniform

@[expose] public section

namespace Lemmata.RM59.CatalogGeometry

open Packed CatalogForms CatalogContractions CatalogGraph

def neighbors (basis : Array (Array Nat)) (v : PackedPoint) : List PackedPoint :=
  (List.finRange 512).filter (adjacency basis v)

theorem neighbors_nodup (basis : Array (Array Nat)) (v : PackedPoint) :
    (neighbors basis v).Nodup :=
  (List.nodup_finRange 512).filter _

theorem mem_neighbors (basis : Array (Array Nat)) (v w : PackedPoint) :
    w ∈ neighbors basis v ↔ adjacency basis v w = true := by
  simp [neighbors]

def featureKey (feature : CatalogInvariant.VertexFeature) : List Nat :=
  let rest := ofLex (ofLex feature).2
  let last := ofLex rest.2
  [(ofLex feature).1, rest.1, last.1, last.2]

def actualKey (T : CubicForm) (v : Point 9) : List Nat :=
  featureKey (CatalogInvariant.vertexFeature
    (CatalogInvariant.contractionAdjacency (cubicFormValue T)) CatalogInvariant.zeroMark v)

theorem cached_feature_semantic (T : CubicForm) (basis : Array (Array Nat))
    (hbasis : ∀ i j : Fin 9,
      natRow ((basis[i.val]?.getD #[])[j.val]?.getD 0) =
        contractionPoint T (basisPoint i) (basisPoint j))
    (hb : BasisBound basis) (v : PackedPoint) :
    GraphCache.cachedVertexFeature (neighbors basis)
      (GraphCache.countTable (neighbors basis)) (fun w => if w.val = 0 then 1 else 0) v =
      CatalogInvariant.vertexFeature
        (CatalogInvariant.contractionAdjacency (cubicFormValue T))
        CatalogInvariant.zeroMark (decodePoint v) := by
  rw [GraphCache.cachedVertexFeature_eq (adjacency basis) (neighbors basis)
    (neighbors_nodup basis) (mem_neighbors basis)
    (GraphCache.countTable (neighbors basis))
    (GraphCache.countTable_entry (adjacency basis) (neighbors basis)
      (neighbors_nodup basis) (mem_neighbors basis) (adjacency_symm T basis hbasis hb))]
  apply CatalogInvariant.vertexFeature_equiv
    (adjacency basis) (CatalogInvariant.contractionAdjacency (cubicFormValue T))
    (fun w => if w.val = 0 then 1 else 0) CatalogInvariant.zeroMark pointEquiv
  · intro x y
    exact (adjacency_semantic T basis hbasis hb x y).symm
  · intro x
    simp only [CatalogInvariant.zeroMark, pointEquiv, Equiv.coe_fn_mk,
      decodePoint_eq_zero_iff]

theorem geometry_values (family : Fin 348) :
    (CatalogUniform.geometry (family.val + 1)).values = pairTable (familyBasis family) := rfl

set_option maxRecDepth 2048 in
theorem geometry_neighbors (family : Fin 348) :
    (CatalogUniform.geometry (family.val + 1)).neighbors =
      Array.ofFn (fun v : PackedPoint => (neighbors (familyBasis family) v).map Fin.val) := by
  change (Vector.ofFn (neighbors (familyBasis family))).toArray.map
    (fun row => row.map Fin.val) = _
  rw [Vector.toArray_ofFn, Array.map_ofFn]
  rfl

theorem neighborVector_get (basis : Array (Array Nat)) :
    (fun w => (Vector.ofFn (neighbors basis)).get w) = neighbors basis := by
  funext w
  change (Vector.ofFn (neighbors basis))[w.val] = _
  exact Vector.getElem_ofFn w.isLt

set_option maxRecDepth 8192 in
theorem geometry_vertexKey_cached (family : Fin 348) (v : PackedPoint) :
    ((CatalogUniform.geometry (family.val + 1)).vertexKeys)[v.val]?.getD [] =
      featureKey (GraphCache.cachedVertexFeature (neighbors (familyBasis family))
        (GraphCache.countTable (neighbors (familyBasis family)))
        (fun w => if w.val = 0 then 1 else 0) v) := by
  change ((Array.ofFn fun w : PackedPoint =>
    featureKey (GraphCache.cachedVertexFeature
      (fun x => (Vector.ofFn (neighbors (familyBasis family))).get x)
      (GraphCache.countTable (fun x => (Vector.ofFn (neighbors (familyBasis family))).get x))
      (fun x => if x.val = 0 then 1 else 0) w))[v.val]?.getD []) = _
  rw [neighborVector_get]
  simp only [Array.getElem?_ofFn, dif_pos v.isLt, Option.getD_some]

theorem geometry_vertexKey_semantic (family : Fin 348) (v : PackedPoint) :
    ((CatalogUniform.geometry (family.val + 1)).vertexKeys)[v.val]?.getD [] =
      actualKey (representative family) (decodePoint v) := by
  rw [geometry_vertexKey_cached,
    cached_feature_semantic (representative family) (familyBasis family)
      (family_basis_semantic family) (family_basis_bound family)]
  rfl

theorem actualKey_action (g : CoordinateGroup 9) (T : CubicForm) (v : Point 9) :
    actualKey (g • T) (g v) = actualKey T v := by
  apply (congrArg featureKey (CatalogInvariant.vertexFeature_equiv
    (CatalogInvariant.contractionAdjacency (cubicFormValue T))
    (CatalogInvariant.contractionAdjacency (cubicFormValue (g • T)))
    CatalogInvariant.zeroMark CatalogInvariant.zeroMark g.toEquiv
    (CatalogInvariant.contractionAdjacency_equiv (cubicFormValue T)
      (cubicFormValue (g • T)) g.toEquiv g.map_zero (cubicFormValue_smul_on_images g T))
    (CatalogInvariant.zeroMark_equiv g.toEquiv g.map_zero) v)).symm

theorem actualKey_stabilizer (g : CoordinateGroup 9) (T : CubicForm)
    (hg : g ∈ MulAction.stabilizer (CoordinateGroup 9) T) (v : Point 9) :
    actualKey T (g v) = actualKey T v := by
  have h := actualKey_action g T v
  rw [MulAction.mem_stabilizer_iff.mp hg] at h
  exact h

end Lemmata.RM59.CatalogGeometry
