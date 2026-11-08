module

public import Lemmata.RM59.Proof.ProjectionGeometry
public import Lemmata.RM59.Proof.FrameGeometry
public import Mathlib.Algebra.Module.NatInt

@[expose] public section

namespace Lemmata.RM59.ProjectionEquivalence

open scoped BigOperators Matrix
open Lemmata.RM59.ProjectionGeometry

abbrev F8Row := ProjectionChecks.Row
abbrev FieldPoint := TraceGeometry.FieldPoint
abbrev FieldMatrix := TraceGeometry.FieldMatrix

def normalizedColumns (a b c : F8Row) (p q : Fin 4) : Fin 4 → FieldPoint :=
  column (topRows a b p q 0) (topRows a b p q 1) (residual a b c p q)

theorem equal_normalized_columns (a b c a' b' c' : F8Row) (p q p' q' : Fin 4)
    (hd : pivotMinor a b p q ≠ 0) (hd' : pivotMinor a' b' p' q' ≠ 0)
    (heq : normalizedColumns a b c p q = normalizedColumns a' b' c' p' q') :
    ∃ A : FieldMatrix, A.det = 1 ∧
      (fun x => A *ᵥ x) '' TraceGeometry.verticalSpace = TraceGeometry.verticalSpace ∧
      ∀ j, A *ᵥ column a b c j = column a' b' c' j := by
  let N := normalizingMatrix a b c p q
  let N' := normalizingMatrix a' b' c' p' q'
  have hN : N.det = 1 := normalizingMatrix_det a b c p q hd
  have hN' : N'.det = 1 := normalizingMatrix_det a' b' c' p' q' hd'
  have hN'ne : N'.det ≠ 0 := by rw [hN']; exact one_ne_zero
  let B := FrameGeometry.fullFrameMap N' 1
  have hBN : B * N' = 1 := FrameGeometry.fullFrameMap_mul N' 1 hN'ne
  have hB : B.det = 1 := FrameGeometry.fullFrameMap_det_one N' 1 hN'ne (by
    rw [Matrix.det_one, hN'])
  have hNK : (fun x => N *ᵥ x) '' TraceGeometry.verticalSpace =
      TraceGeometry.verticalSpace := normalizingMatrix_image_vertical a b c p q hd
  have hN'K : (fun x => N' *ᵥ x) '' TraceGeometry.verticalSpace =
      TraceGeometry.verticalSpace := normalizingMatrix_image_vertical a' b' c' p' q' hd'
  have hBK : (fun x => B *ᵥ x) '' TraceGeometry.verticalSpace =
      TraceGeometry.verticalSpace := by
    calc
      _ = (fun x => B *ᵥ x) '' ((fun x => N' *ᵥ x) '' TraceGeometry.verticalSpace) :=
        congrArg (fun S : Set FieldPoint => (fun x => B *ᵥ x) '' S) hN'K.symm
      _ = (fun x => B *ᵥ (N' *ᵥ x)) '' TraceGeometry.verticalSpace := by
        rw [Set.image_image] <;> rfl
      _ = _ := by
        simp only [Matrix.mulVec_mulVec, hBN, Matrix.one_mulVec]
        change (id : FieldPoint → FieldPoint) '' TraceGeometry.verticalSpace =
          TraceGeometry.verticalSpace
        exact Set.image_id _
  refine ⟨B * N, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, hB, hN, one_mul]
  · calc
      _ = (fun x => B *ᵥ (N *ᵥ x)) '' TraceGeometry.verticalSpace := by
        simp only [Matrix.mulVec_mulVec]
      _ = (fun x => B *ᵥ x) '' ((fun x => N *ᵥ x) '' TraceGeometry.verticalSpace) := by
        rw [Set.image_image] <;> rfl
      _ = _ := by rw [hNK, hBK]
  · intro j
    have hcols : N *ᵥ column a b c j = N' *ᵥ column a' b' c' j := by
      calc
        _ = normalizedColumns a b c p q j := normalizingMatrix_apply a b c p q j
        _ = normalizedColumns a' b' c' p' q' j := congrFun heq j
        _ = _ := (normalizingMatrix_apply a' b' c' p' q' j).symm
    rw [← Matrix.mulVec_mulVec, hcols, Matrix.mulVec_mulVec, hBN, Matrix.one_mulVec]

def center (points : Fin 5 → FieldPoint) : FieldPoint := ∑ i, points i

def centered (points : Fin 5 → FieldPoint) (i : Fin 5) : FieldPoint := points i + center points

theorem point_add_self (x : FieldPoint) : x + x = 0 := by
  funext i
  exact F8Scalar.add_self_eq_zero (x i)

theorem sum_centered (points : Fin 5 → FieldPoint) : (∑ i, centered points i) = 0 := by
  calc
    _ = center points + 5 • center points := by
      simp only [centered, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, center]
    _ = center points + (5 : Field) • center points := by
      exact congrArg (fun x : FieldPoint => center points + x)
        (Nat.cast_smul_eq_nsmul Field 5 (center points)).symm
    _ = 0 := by
      rw [show (5 : Field) = 1 by decide, one_smul]
      exact point_add_self _

theorem centered_last (points : Fin 5 → FieldPoint) :
    centered points (Fin.last 4) = ∑ j : Fin 4, centered points j.castSucc := by
  have h := sum_centered points
  rw [Fin.sum_univ_castSucc] at h
  exact add_left_cancel (h.trans
    (point_add_self (∑ j : Fin 4, centered points j.castSucc)).symm)

def rows (points : Fin 5 → FieldPoint) : Fin 3 → F8Row :=
  fun i j => centered points j.castSucc i

theorem column_rows (points : Fin 5 → FieldPoint) (j : Fin 4) :
    column (rows points 0) (rows points 1) (rows points 2) j = centered points j.castSucc := by
  ext i
  fin_cases i <;> rfl

theorem equal_five_normal_forms (source target : Fin 5 → FieldPoint)
    (p q p' q' : Fin 4)
    (hd : pivotMinor (rows source 0) (rows source 1) p q ≠ 0)
    (hd' : pivotMinor (rows target 0) (rows target 1) p' q' ≠ 0)
    (heq : normalizedColumns (rows source 0) (rows source 1) (rows source 2) p q =
      normalizedColumns (rows target 0) (rows target 1) (rows target 2) p' q') :
    ∃ A : FieldMatrix, ∃ b : FieldPoint, A.det = 1 ∧
      (fun x => A *ᵥ x) '' TraceGeometry.verticalSpace = TraceGeometry.verticalSpace ∧
      ∀ i, A *ᵥ source i + b = target i := by
  obtain ⟨A, hA, hAK, hcols⟩ := equal_normalized_columns _ _ _ _ _ _ p q p' q' hd hd' heq
  simp only [column_rows] at hcols
  have hcentered : ∀ i, A *ᵥ centered source i = centered target i := by
    intro i
    refine Fin.lastCases ?_ (fun j => hcols j) i
    rw [centered_last source, centered_last target]
    change TraceActions.matrixLinear A (∑ j : Fin 4, centered source j.castSucc) = _
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => hcols j)
  refine ⟨A, A *ᵥ center source - center target, hA, hAK, ?_⟩
  intro i
  have h := hcentered i
  change A *ᵥ (source i + center source) = target i + center target at h
  rw [Matrix.mulVec_add] at h
  calc
    _ = (A *ᵥ source i + A *ᵥ center source) - center target := by abel
    _ = target i := by rw [h, add_sub_cancel_right]

end Lemmata.RM59.ProjectionEquivalence
