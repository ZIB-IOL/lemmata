module

public import Lemmata.Centroid.Proof.General.LocalTensor
public import Lemmata.Centroid.Proof.General.LocalCases
public import Lemmata.Centroid.Proof.General.Merge

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Lemmata.Centroid.Tensor

variable {F : Type*} [Field F] {V : Fin 3 → Type*} [∀ i, Fintype (V i)]

theorem centroid_dimension_cost_bound {T : Tensor F (Fin 3) V} (hT : Concise T) :
    General.dimensionCost (Module.finrank F (centroid T)) ≤
      ((Fintype.card (V 0) : ℝ) + Fintype.card (V 1) + Fintype.card (V 2)) / 3 := by
  classical
  have hc (a : CRT.Spectrum T hT) :
      General.dimensionCost (Module.finrank F (CRT.Factor T hT a)) ≤
        ((CRT.size T hT a 0 : ℝ) + CRT.size T hT a 1 + CRT.size T hT a 2) / 3 := by
    simpa only [Fintype.card_fin] using
      BalancedAlgebra.local_algebra_cost_bound (CRT.tensor T hT a) (CRT.concise T hT a)
        (CRT.action T hT a) (CRT.action_injective T hT a)
        (fun i => by simpa only [Fintype.card_fin] using CRT.size_pos T hT a i)
  have h := (General.dimensionCost_sum Finset.univ
    (fun a => Module.finrank F (CRT.Factor T hT a))).trans (Finset.sum_le_sum (fun a _ => hc a))
  simpa only [← CRT.dimension_sum, ← Finset.sum_div, Finset.sum_add_distrib,
    ← Nat.cast_sum, CRT.sum_size] using h

theorem centroid_average_bound {T : Tensor F (Fin 3) V} (hT : Concise T) :
    (Module.finrank F (centroid T) : ℝ) ≤
      1 + General.envelope (((Fintype.card (V 0) : ℝ) + Fintype.card (V 1) + Fintype.card (V 2)) / 3) :=
  General.dimension_le_envelope (by positivity) (centroid_dimension_cost_bound hT)

theorem centroid_component_bounds {T : Tensor F (Fin 3) V} (hT : Concise T) (N : ℕ)
    (hformat : ∀ i, Fintype.card (V i) ≤ N) :
    Module.finrank F (centroid T) ≤ supportBound N + 1 ∧
      (2 ≤ Fintype.card (CRT.Spectrum T hT) → Module.finrank F (centroid T) ≤ generalBound N) := by
  classical
  have hc (a : CRT.Spectrum T hT) (i : Fin 3) :
      Module.finrank F (CRT.Factor T hT a) ≤ General.g (CRT.size T hT a i) := by
    rw [CRT.factor_dimension_eq]
    simpa only [General.g, Fintype.card_fin] using centroid_quadratic_bound (CRT.concise T hT a) i
  have hl (a : CRT.Spectrum T hT) (N : ℕ) (hN : ∀ i, CRT.size T hT a i ≤ N) :
      Module.finrank F (CRT.Factor T hT a) ≤ supportBound N + 1 := by
    apply BalancedAlgebra.local_algebra_support_bound (CRT.tensor T hT a) (CRT.concise T hT a)
      (CRT.action T hT a) (CRT.action_injective T hT a) N
    · simpa only [Fintype.card_fin] using CRT.size_pos T hT a
    · simpa only [Fintype.card_fin] using hN
  have hcost (a : CRT.Spectrum T hT) :
      General.dimensionCost (Module.finrank F (CRT.Factor T hT a)) ≤
        ((CRT.size T hT a 0 : ℝ) + CRT.size T hT a 1 + CRT.size T hT a 2) / 3 := by
    simpa only [Fintype.card_fin] using
      BalancedAlgebra.local_algebra_cost_bound (CRT.tensor T hT a) (CRT.concise T hT a)
        (CRT.action T hT a) (CRT.action_injective T hT a)
        (fun i => by simpa only [Fintype.card_fin] using CRT.size_pos T hT a i)
  have h := General.merge_components (fun a => Module.finrank F (CRT.Factor T hT a))
    (CRT.size T hT) (CRT.size_pos T hT) hc hl hcost Finset.univ N
    (fun i => (CRT.sum_size T hT i).trans_le (hformat i))
  simpa only [← CRT.dimension_sum, Finset.card_univ] using h

theorem centroid_upper_bound {T : Tensor F (Fin 3) V} (hT : Concise T) (N : ℕ)
    (hformat : ∀ i, Fintype.card (V i) = N) :
    Module.finrank F (centroid T) ≤ generalBound N := by
  classical
  by_cases hN : N = 0
  · have h := centroid_quadratic_bound hT 0
    simpa [hformat, hN, generalBound] using h
  have hNpos : 0 < N := by omega
  by_cases hcard : 2 ≤ Fintype.card (CRT.Spectrum T hT)
  · exact (centroid_component_bounds hT N (fun i => (hformat i).le)).2 hcard
  have hsum := CRT.dimension_sum T hT
  by_cases hzero : (Finset.univ : Finset (CRT.Spectrum T hT)).card = 0
  · have hempty := Finset.card_eq_zero.mp hzero
    rw [hempty, Finset.sum_empty] at hsum
    rw [hsum]
    exact Nat.zero_le _
  have hone : (Finset.univ : Finset (CRT.Spectrum T hT)).card = 1 := by
    simp only [Finset.card_univ] at hzero ⊢
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hone
  have hsize (i : Fin 3) : Fintype.card (Fin (CRT.size T hT a i)) = N := by
    have h := CRT.sum_size T hT i
    rw [ha, Finset.sum_singleton, hformat i] at h
    simpa only [Fintype.card_fin] using h
  have hlocal := BalancedAlgebra.local_algebra_dimension_bound
    (CRT.tensor T hT a) (CRT.concise T hT a) (CRT.action T hT a)
    (CRT.action_injective T hT a) N hNpos hsize
  rw [ha, Finset.sum_singleton] at hsum
  rwa [hsum]

theorem centroid_upper_bound_at {T : Tensor F (Fin 3) V} (hT : Concise T)
    {N n s : ℕ} (hN : 2 ≤ N) (hs : s ≤ 2 * n + 1)
    (hdecomp : N = n * (n + 1) + s) (hformat : ∀ i, Fintype.card (V i) = N) :
    Module.finrank F (centroid T) ≤ generalBoundAt n s := by
  have h := centroid_upper_bound hT N hformat
  rwa [generalBound_eq hN hs hdecomp] at h

end Lemmata.Centroid.Tensor
