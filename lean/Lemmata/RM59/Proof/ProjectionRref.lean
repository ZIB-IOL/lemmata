module

public import Lemmata.RM59.Proof.ProjectionTupleSound
public import Lemmata.RM59.Proof.FieldRank
public meta import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Lemmata.RM59.ProjectionRref

open scoped Matrix
open Lemmata.RM59.ProjectionGeometry Lemmata.RM59.ProjectionTupleChecks

abbrev F8Row := ProjectionChecks.Row

theorem snapshot_four {α : Type*} (r : Fin 4 → α) :
    Vector.ofFn r = #v[r 0, r 1, r 2, r 3] := by
  apply Vector.ext
  intro i hi
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> simp

theorem mem_01 (x : Lift × Lift) :
    projectionFromRows 0 1 #v[1, 0, x.1.1, x.1.2] #v[0, 1, x.2.1, x.2.2] ∈
      allReducedProjections := by
  have h : projectionFromRows 0 1 #v[1, 0, x.1.1, x.1.2] #v[0, 1, x.2.1, x.2.2] ∈
      scalarQuadruples.map (fun y =>
        projectionFromRows 0 1 #v[1, 0, y.1.1, y.1.2] #v[0, 1, y.2.1, y.2.2]) :=
    List.mem_map.mpr ⟨x, scalarQuadruples_complete x, rfl⟩
  simp only [allReducedProjections, List.mem_append, h, true_or, or_true]

theorem mem_02 (x : F8Scalar × F8Scalar × F8Scalar) :
    projectionFromRows 0 2 #v[1, x.1, 0, x.2.1] #v[0, 0, 1, x.2.2] ∈
      allReducedProjections := by
  have h : projectionFromRows 0 2 #v[1, x.1, 0, x.2.1] #v[0, 0, 1, x.2.2] ∈
      scalarTriples.map (fun y =>
        projectionFromRows 0 2 #v[1, y.1, 0, y.2.1] #v[0, 0, 1, y.2.2]) :=
    List.mem_map.mpr ⟨x, scalarTriples_complete x, rfl⟩
  simp only [allReducedProjections, List.mem_append, h, true_or, or_true]

theorem mem_03 (x : Lift) :
    projectionFromRows 0 3 #v[1, x.1, x.2, 0] #v[0, 0, 0, 1] ∈ allReducedProjections := by
  have h : projectionFromRows 0 3 #v[1, x.1, x.2, 0] #v[0, 0, 0, 1] ∈
      scalarPairs.map (fun y => projectionFromRows 0 3 #v[1, y.1, y.2, 0] #v[0, 0, 0, 1]) :=
    List.mem_map.mpr ⟨x, scalarPairs_complete x, rfl⟩
  simp only [allReducedProjections, List.mem_append, h, true_or, or_true]

theorem mem_12 (x : Lift) :
    projectionFromRows 1 2 #v[0, 1, 0, x.1] #v[0, 0, 1, x.2] ∈ allReducedProjections := by
  have h : projectionFromRows 1 2 #v[0, 1, 0, x.1] #v[0, 0, 1, x.2] ∈
      scalarPairs.map (fun y => projectionFromRows 1 2 #v[0, 1, 0, y.1] #v[0, 0, 1, y.2]) :=
    List.mem_map.mpr ⟨x, scalarPairs_complete x, rfl⟩
  simp only [allReducedProjections, List.mem_append, h, true_or, or_true]

theorem mem_13 (x : F8Scalar) :
    projectionFromRows 1 3 #v[0, 1, x, 0] #v[0, 0, 0, 1] ∈ allReducedProjections := by
  have h : projectionFromRows 1 3 #v[0, 1, x, 0] #v[0, 0, 0, 1] ∈
      elements.map (fun y => projectionFromRows 1 3 #v[0, 1, y, 0] #v[0, 0, 0, 1]) :=
    List.mem_map.mpr ⟨x, elements_complete x, rfl⟩
  simp only [allReducedProjections, List.mem_append, h, true_or, or_true]

theorem mem_23 :
    projectionFromRows 2 3 #v[0, 0, 1, 0] #v[0, 0, 0, 1] ∈ allReducedProjections := by
  simp only [allReducedProjections, List.mem_append, List.mem_singleton,
    eq_self_iff_true, or_true]

theorem rref_mem (p q : Fin 4) (r0 r1 : F8Row) (hpq : p < q)
    (h0p : r0 p = 1) (h0q : r0 q = 0) (h1p : r1 p = 0) (h1q : r1 q = 1)
    (h0before : ∀ j, j < p → r0 j = 0) (h1before : ∀ j, j < q → r1 j = 0) :
    projectionFromRows p q (Vector.ofFn r0) (Vector.ofFn r1) ∈ allReducedProjections := by
  fin_cases p <;> fin_cases q <;> simp at hpq
  all_goals dsimp only at h0p h0q h1p h1q h0before h1before ⊢
  · change r0 0 = 1 at h0p
    change r0 1 = 0 at h0q
    change r1 0 = 0 at h1p
    change r1 1 = 1 at h1q
    rw [snapshot_four r0, snapshot_four r1, h0p, h0q, h1p, h1q]
    exact mem_01 ((r0 2, r0 3), (r1 2, r1 3))
  · change r0 0 = 1 at h0p
    change r0 2 = 0 at h0q
    change r1 0 = 0 at h1p
    change r1 2 = 1 at h1q
    rw [snapshot_four r0, snapshot_four r1, h0p, h0q, h1p, h1q,
      h1before 1 (by decide)]
    exact mem_02 (r0 1, r0 3, r1 3)
  · change r0 0 = 1 at h0p
    change r0 3 = 0 at h0q
    change r1 0 = 0 at h1p
    change r1 3 = 1 at h1q
    rw [snapshot_four r0, snapshot_four r1, h0p, h0q, h1p, h1q,
      h1before 1 (by decide), h1before 2 (by decide)]
    exact mem_03 (r0 1, r0 2)
  · change r0 1 = 1 at h0p
    change r0 2 = 0 at h0q
    change r1 1 = 0 at h1p
    change r1 2 = 1 at h1q
    rw [snapshot_four r0, snapshot_four r1, h0p, h0q, h1p, h1q,
      h0before 0 (by decide), h1before 0 (by decide)]
    exact mem_12 (r0 3, r1 3)
  · change r0 1 = 1 at h0p
    change r0 3 = 0 at h0q
    change r1 1 = 0 at h1p
    change r1 3 = 1 at h1q
    rw [snapshot_four r0, snapshot_four r1, h0p, h0q, h1p, h1q,
      h0before 0 (by decide), h1before 0 (by decide), h1before 2 (by decide)]
    exact mem_13 (r0 2)
  · change r0 2 = 1 at h0p
    change r0 3 = 0 at h0q
    change r1 2 = 0 at h1p
    change r1 3 = 1 at h1q
    rw [snapshot_four r0, snapshot_four r1, h0p, h0q, h1p, h1q,
      h0before 0 (by decide), h0before 1 (by decide),
      h1before 0 (by decide), h1before 1 (by decide)]
    exact mem_23

theorem find_fin4_spec : ∀ f : Fin 4 → Bool, ∀ i : Fin 4,
    (List.finRange 4).find? f = some i ↔ f i = true ∧ ∀ j, j < i → f j = false := by decide

theorem find_fin4_complete : ∀ f : Fin 4 → Bool,
    (∃ i, f i = true) → ∃ i, (List.finRange 4).find? f = some i := by decide

theorem top_one_minor (a b : F8Row) (p q j : Fin 4) :
    topRows a b p q 1 j = (pivotMinor a b p q)⁻¹ * pivotMinor a b p j := by
  rw [top_one_formula]
  unfold pivotMinor
  ring

theorem normalization_projection_mem (a b c : F8Row) (normal : NormalForm)
    (h : normalizeRows a b c = some normal) : normal.projection ∈ allReducedProjections := by
  obtain ⟨p, q, hp, hq, hd, rfl⟩ := ProjectionTupleSound.normalizeRows_sound a b c normal h
  have hpSpec := (find_fin4_spec _ p).1 hp
  have hqSpec := (find_fin4_spec _ q).1 hq
  have hpq : p < q := by
    have hv : p < q ∧ pivotMinor a b p q ≠ 0 := by simpa using hqSpec.1
    exact hv.1
  have hbefore (j : Fin 4) (hj : j < p) : a j = 0 ∧ b j = 0 := by
    simpa using hpSpec.2 j hj
  have hminor (j : Fin 4) (hj : j < q) : pivotMinor a b p j = 0 := by
    by_cases hpj : p < j
    · simpa [hpj] using hqSpec.2 j hj
    · by_cases heq : j = p
      · subst j
        simp [pivotMinor]
      · have hjp : j < p := by omega
        obtain ⟨ha, hb⟩ := hbefore j hjp
        simp [pivotMinor, ha, hb]
  obtain ⟨h0p, h0q, h1p, h1q⟩ := top_pivots a b p q hd
  apply rref_mem p q (topRows a b p q 0) (topRows a b p q 1) hpq h0p h0q h1p h1q
  · intro j hj
    obtain ⟨ha, hb⟩ := hbefore j hj
    simp only [topRows, ha, hb, mul_zero, add_zero]
  · intro j hj
    rw [top_one_minor, hminor j hj, mul_zero]

end Lemmata.RM59.ProjectionRref
