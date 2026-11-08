module

public import Lemmata.RM59.Proof.FrameGeometry
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace Lemmata.RM59.VerticalFrames

open scoped Matrix

abbrev FieldPoint := TraceGeometry.FieldPoint
abbrev FieldMatrix := TraceGeometry.FieldMatrix

def horizontal (x : FieldPoint) : FieldPoint := ![x 0, x 1, 0]

theorem horizontal_eq_zero (x : FieldPoint) :
    horizontal x = 0 ↔ x 0 = 0 ∧ x 1 = 0 := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i <;> simp [horizontal, h0, h1]

theorem horizontal_eq_zero_iff_vertical (x : FieldPoint) :
    horizontal x = 0 ↔ x = TraceGeometry.vertical (x 2) := by
  rw [horizontal_eq_zero]
  constructor
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i <;> simp [TraceGeometry.vertical, h0, h1]
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩

theorem vertical_smul (r v : F8Scalar) :
    r • TraceGeometry.vertical v = TraceGeometry.vertical (r * v) := by
  ext i
  fin_cases i <;> simp [TraceGeometry.vertical]

theorem image_vertical_of_one (A : FieldMatrix) (v w : F8Scalar)
    (hv : v ≠ 0) (hw : w ≠ 0)
    (h : A *ᵥ TraceGeometry.vertical v = TraceGeometry.vertical w) :
    (fun x => A *ᵥ x) '' TraceGeometry.verticalSpace = TraceGeometry.verticalSpace := by
  have hformula (c : F8Scalar) :
      A *ᵥ TraceGeometry.vertical c = TraceGeometry.vertical (c / v * w) := by
    have he : TraceGeometry.vertical c = (c / v) • TraceGeometry.vertical v := by
      rw [vertical_smul, div_mul_cancel₀ c hv]
    rw [he, Matrix.mulVec_smul, h, vertical_smul]
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c / v * w, (hformula c).symm⟩
  · rintro _ ⟨c, rfl⟩
    refine ⟨TraceGeometry.vertical (c / w * v), ⟨c / w * v, rfl⟩, ?_⟩
    change A *ᵥ TraceGeometry.vertical (c / w * v) = TraceGeometry.vertical c
    rw [hformula]
    congr 1
    field_simp [hv, hw]

theorem independent_vertical (v : F8Scalar) (hv : v ≠ 0) (u : FieldPoint)
    (hu : horizontal u ≠ 0) : LinearIndependent F8Scalar ![TraceGeometry.vertical v, u] := by
  apply crossProduct_ne_zero_iff_linearIndependent.mp
  intro hz
  have h0 : -(v * u 1) = 0 := by
    simpa [cross_apply, TraceGeometry.vertical] using congrFun hz 0
  have h1 : v * u 0 = 0 := by
    simpa [cross_apply, TraceGeometry.vertical] using congrFun hz 1
  apply hu
  apply (horizontal_eq_zero u).2
  refine ⟨(mul_eq_zero.mp h1).resolve_left hv, ?_⟩
  exact (mul_eq_zero.mp (neg_eq_zero.mp h0)).resolve_left hv

theorem affine_vertical_triple (source target : Fin 3 → FieldPoint) (v w : F8Scalar)
    (hv : v ≠ 0) (hw : w ≠ 0)
    (hs : source 1 - source 0 = TraceGeometry.vertical v)
    (ht : target 1 - target 0 = TraceGeometry.vertical w)
    (hs2 : horizontal (source 2 - source 0) ≠ 0)
    (ht2 : horizontal (target 2 - target 0) ≠ 0) :
    ∃ A : FieldMatrix, ∃ b : FieldPoint, A.det = 1 ∧
      (fun x => A *ᵥ x) '' TraceGeometry.verticalSpace = TraceGeometry.verticalSpace ∧
      ∀ i, A *ᵥ source i + b = target i := by
  have hsind : LinearIndependent F8Scalar ![source 1 - source 0, source 2 - source 0] := by
    rw [hs]
    exact independent_vertical v hv _ hs2
  have htind : LinearIndependent F8Scalar ![target 1 - target 0, target 2 - target 0] := by
    rw [ht]
    exact independent_vertical w hw _ ht2
  obtain ⟨s3, hs3⟩ := FrameGeometry.extend_independent_triple _ _ _ hsind 1
  obtain ⟨t3, ht3⟩ := FrameGeometry.extend_independent_triple _ _ _ htind 1
  obtain ⟨A, b, hA, hmap⟩ := FrameGeometry.exists_affine_det_one_frame_map
    ![source 0, source 1, source 2, s3] ![target 0, target 1, target 2, t3]
    (by rw [hs3]; exact one_ne_zero) (ht3.trans hs3.symm)
  have h0 : A *ᵥ source 0 + b = target 0 := hmap 0
  have h1 : A *ᵥ source 1 + b = target 1 := hmap 1
  have hvertical : A *ᵥ TraceGeometry.vertical v = TraceGeometry.vertical w := by
    have hh := congrArg₂ (fun x y : FieldPoint => x - y) h1 h0
    rw [add_sub_add_right_eq_sub, ← Matrix.mulVec_sub, hs, ht] at hh
    exact hh
  refine ⟨A, b, hA, image_vertical_of_one A v w hv hw hvertical, ?_⟩
  intro i
  fin_cases i
  · exact hmap 0
  · exact hmap 1
  · exact hmap 2

end Lemmata.RM59.VerticalFrames
