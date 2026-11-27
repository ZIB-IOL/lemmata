module

public import Lemmata.CompleteGraphTensorRank.Statement

@[expose] public section

namespace Lemmata.CompleteGraphTensorRank

open Lemmata.TensorRank
open scoped BigOperators
open Classical

variable {F : Type*} [Field F]

theorem vertex_card (r : ℕ) : Fintype.card (Vertex r) = 2 * r + 1 := by
  simp [Vertex, Block, Fintype.card_sigma, Fintype.sum_option]
  omega

noncomputable def vertexEquiv (r : ℕ) : Vertex r ≃ Fin (2 * r + 1) :=
  Fintype.equivFinOfCardEq (vertex_card r)

abbrev NativeCoordinate (r d : ℕ) (v : Vertex r) := {w : Vertex r // w ≠ v} → Fin d

/-- Transport a vertex's neighbor coordinates along the vertex equivalence. -/
noncomputable def coordinateMap (r d : ℕ) (v : Vertex r) (x : NativeCoordinate r d v) :
    GraphCoordinate (2 * r + 1) d (vertexEquiv r v) :=
  fun j => x ⟨(vertexEquiv r).symm j.val, by
    intro h
    exact j.property (by simpa using congrArg (vertexEquiv r) h)⟩

/-- This is the existing complete-graph tensor after relabeling and local
coordinate selection; no second definition of complete-graph tensors is used. -/
noncomputable def nativeGraph (r d : ℕ) : Tensor F (Vertex r) (NativeCoordinate r d) :=
  Tensor.reindex (coordinateMap r d)
    (Tensor.relabel (vertexEquiv r) (completeGraph (𝕜 := F) (2 * r + 1) d))

theorem nativeGraph_apply (r d : ℕ) (x : ∀ v, NativeCoordinate r d v) :
    nativeGraph (F := F) r d x =
      if ∀ (v w : Vertex r) (h : v ≠ w),
        x v ⟨w, h.symm⟩ = x w ⟨v, h⟩ then 1 else 0 := by
  let e := vertexEquiv r
  have h : (∀ (i j : Fin (2 * r + 1)) (hij : i ≠ j),
      (Equiv.piCongrLeft (GraphCoordinate (2 * r + 1) d) e
        (fun v => coordinateMap r d v (x v))) i ⟨j, hij.symm⟩ =
      (Equiv.piCongrLeft (GraphCoordinate (2 * r + 1) d) e
        (fun v => coordinateMap r d v (x v))) j ⟨i, hij⟩) ↔
      ∀ (v w : Vertex r) (hvw : v ≠ w), x v ⟨w, hvw.symm⟩ = x w ⟨v, hvw⟩ := by
    constructor
    · intro h v w hvw
      simpa [e, coordinateMap] using h (e v) (e w) (e.injective.ne hvw)
    · intro h i j hij
      obtain ⟨v, rfl⟩ := e.surjective i
      obtain ⟨w, rfl⟩ := e.surjective j
      simpa [e, coordinateMap] using h v w (fun hvw => hij (congrArg e hvw))
  change (if _ then (1 : F) else 0) = _
  exact if_congr h rfl rfl

/-- Keep all inter-block edge labels and set every internal label to zero. -/
def selectCoordinates (r d : ℕ) (hd : 0 < d) :
    ∀ p, RectangleCoordinate r d p → ∀ i : Block r p, NativeCoordinate r d ⟨p, i⟩
  | none, x, _, ⟨⟨some false, j⟩, _⟩ => x.1 j
  | none, x, _, ⟨⟨some true, j⟩, _⟩ => x.2 j
  | some false, x, i, ⟨⟨some true, j⟩, _⟩ => x.1 (i, j)
  | some true, x, j, ⟨⟨some false, i⟩, _⟩ => x.1 (i, j)
  | some false, x, i, ⟨⟨none, _⟩, _⟩ => x.2 i
  | some true, x, j, ⟨⟨none, _⟩, _⟩ => x.2 j
  | _, _, _, _ => ⟨0, hd⟩

/-- The selected three-party tensor is exactly rectangular matrix multiplication. -/
theorem rectangle_eq_restriction (r d : ℕ) (hd : 0 < d) :
    rectangle F r d = Tensor.reindex (selectCoordinates r d hd)
      (Tensor.group (nativeGraph (F := F) r d)) := by
  funext x
  let y := fun v : Vertex r => selectCoordinates r d hd v.1 (x v.1) v.2
  have h : (∀ (v w : Vertex r) (hvw : v ≠ w),
      y v ⟨w, hvw.symm⟩ = y w ⟨v, hvw⟩) ↔
      (x (some false)).1 = (x (some true)).1 ∧
      (x (some false)).2 = (x none).1 ∧ (x (some true)).2 = (x none).2 := by
    constructor
    · intro h
      refine ⟨?_, ?_, ?_⟩
      · funext ij
        simpa [y, selectCoordinates] using
          h ⟨some false, ij.1⟩ ⟨some true, ij.2⟩ (by intro he; cases congrArg Sigma.fst he)
      · funext i
        simpa [y, selectCoordinates] using
          h ⟨some false, i⟩ ⟨none, ()⟩ (by intro he; cases congrArg Sigma.fst he)
      · funext j
        simpa [y, selectCoordinates] using
          h ⟨some true, j⟩ ⟨none, ()⟩ (by intro he; cases congrArg Sigma.fst he)
    · rintro ⟨hab, hac, hbc⟩ ⟨p, i⟩ ⟨q, j⟩ hpq
      cases p with
      | none => cases q with
        | none => simp [y, selectCoordinates]
        | some b => cases b <;> simp [y, selectCoordinates, hac, hbc]
      | some a => cases q with
        | none => cases a <;> simp [y, selectCoordinates, hac, hbc]
        | some b => cases a <;> cases b <;> simp [y, selectCoordinates, hab]
  change rectangle F r d x = nativeGraph (F := F) r d y
  rw [nativeGraph_apply]
  simp only [rectangle, h]

/-- Grouping vertices and applying independent coordinate selections cannot
increase asymptotic rank. This is the combinatorial reduction used below. -/
theorem rectangle_le_completeGraph (r d : ℕ) (hd : 0 < d) :
    Tensor.asymptoticRank (rectangle F r d) ≤
      Tensor.asymptoticRank (completeGraph (𝕜 := F) (2 * r + 1) d) := by
  rw [rectangle_eq_restriction r d hd]
  apply (Tensor.reindex_restricts _ _).asymptoticRank_le.trans
  apply (Tensor.asymptoticRank_group_le _).trans
  apply (Tensor.reindex_restricts _ _).asymptoticRank_le.trans
  exact (Tensor.asymptoticRank_relabel _ _).le

end Lemmata.CompleteGraphTensorRank
