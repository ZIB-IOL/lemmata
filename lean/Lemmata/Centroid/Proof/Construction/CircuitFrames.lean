module

public import Lemmata.Centroid.Proof.Construction.CircuitTarget
public import Lemmata.Centroid.Proof.Construction.WeightedGrid
public import Lemmata.Centroid.Proof.Construction.SecondOrder
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Construction.Circuit

noncomputable section

variable {F : Type*} [Field F]

abbrev M (q ν : ℕ) := (algebraMap (Polynomial F) (RatFunc F)).mapMatrix (matrixM q ν)
abbrev H (q ν : ℕ) := (algebraMap (Polynomial F) (RatFunc F)).mapMatrix (matrixH q ν)

theorem M_isUnit (q ν : ℕ) : IsUnit (M (F := F) q ν) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (matrixM_ratFunc_det_ne_zero (F := F) q ν))

theorem H_isUnit (q ν : ℕ) : IsUnit (H (F := F) q ν) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (matrixH_ratFunc_det_ne_zero (F := F) q ν))

theorem M_ne_zero (q ν : ℕ) (i j : A q ν) : M (F := F) q ν i j ≠ 0 :=
  RatFunc.algebraMap_ne_zero (matrixM_ne_zero (F := F) q ν i j)

theorem H_ne_zero (q ν : ℕ) (hq : 0 < q) (i j : A q ν) : H (F := F) q ν i j ≠ 0 :=
  RatFunc.algebraMap_ne_zero (matrixH_ne_zero (F := F) q ν hq i j)

def factors {R : Type*} (q ν : ℕ) (a : A q ν → R) (b : (A q ν ⊕ Unit) → R)
    (c : (A q ν ⊕ Option (Fin q)) → R) : ∀ i, Core q ν i → R :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun j => Fin.elim0 j)))

@[simp] theorem factors_zero {R : Type*} (q ν : ℕ) (a : A q ν → R)
    (b : (A q ν ⊕ Unit) → R) (c : (A q ν ⊕ Option (Fin q)) → R) : factors q ν a b c 0 = a := rfl

@[simp] theorem factors_one {R : Type*} (q ν : ℕ) (a : A q ν → R)
    (b : (A q ν ⊕ Unit) → R) (c : (A q ν ⊕ Option (Fin q)) → R) : factors q ν a b c 1 = b := rfl

@[simp] theorem factors_two {R : Type*} (q ν : ℕ) (a : A q ν → R)
    (b : (A q ν ⊕ Unit) → R) (c : (A q ν ⊕ Option (Fin q)) → R) : factors q ν a b c 2 = c := rfl

def normalizedPoint (q ν : ℕ) (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (j k : A q ν) : A q ν → RatFunc F :=
  e (fun a => M (F := F) q ν a j * H (F := F) q ν a k)

def diagonalCoefficient (q ν : ℕ) (j k : A q ν) : RatFunc F :=
  if j = k ∧ j.isLeft then 1 else 0

def oldPoint (q ν : ℕ) (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (p : A q ν × A q ν) : ∀ i, Core q ν i → RatFunc F :=
  factors q ν (normalizedPoint q ν e p.1 p.2) (Realization.basisVector (Sum.inl p.1))
    (Realization.basisVector (Sum.inl p.2) - diagonalCoefficient (F := F) q ν p.1 p.2 •
      Realization.basisVector (Sum.inr none))

def extraPoint (q ν : ℕ) (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (j : Fin (q + 1)) : ∀ i, Core q ν i → RatFunc F :=
  factors q ν (normalizedPoint q ν e (Sum.inl j) (Sum.inl j))
    (Realization.basisVector (Sum.inl (Sum.inl j))) (Realization.basisVector (Sum.inr none))

abbrev PointIndex (q ν : ℕ) := (A q ν × A q ν) ⊕ Fin (q + 1)

def basePoint (q ν : ℕ) (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F)) :
    PointIndex q ν → ∀ i, Core q ν i → RatFunc F := Sum.elim (oldPoint q ν e) (extraPoint q ν e)

def gridPoint (q ν : ℕ) (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (p : A q ν × A q ν) : ∀ i, Core q ν i → RatFunc F :=
  factors q ν (normalizedPoint q ν e p.1 p.2) (Realization.basisVector (Sum.inl p.1))
    (Realization.basisVector (Sum.inl p.2))

def diagonalPoint (q ν : ℕ) (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (p : A q ν × A q ν) : ∀ i, Core q ν i → RatFunc F :=
  factors q ν (normalizedPoint q ν e p.1 p.2) (Realization.basisVector (Sum.inl p.1))
    (Realization.basisVector (Sum.inr none))

theorem oldPoint_simple (q ν : ℕ)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F)) (p : A q ν × A q ν) :
    Tensor.simple (oldPoint q ν e p) = Tensor.simple (gridPoint q ν e p) -
      diagonalCoefficient (F := F) q ν p.1 p.2 • Tensor.simple (diagonalPoint q ν e p) := by
  ext x
  let a := normalizedPoint q ν e p.1 p.2 (x 0)
  let b := Realization.basisVector (F := RatFunc F) (Sum.inl p.1) (x 1)
  let c := Realization.basisVector (F := RatFunc F) (Sum.inl p.2) (x 2)
  let d := diagonalCoefficient (F := F) q ν p.1 p.2
  let f := Realization.basisVector (F := RatFunc F) (Sum.inr none) (x 2)
  simp only [Tensor.simple, Fin.prod_univ_three, oldPoint, gridPoint, diagonalPoint,
    factors_zero, factors_one, factors_two, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Lemmata.TensorRank.Tensor.pure]
  change a * b * (c - d * f) = a * b * c - d * (a * b * f)
  ring

theorem sum_active_diagonal {R : Type*} [AddCommMonoid R] (q ν : ℕ) (f : A q ν → A q ν → R) :
    (∑ j, ∑ k, if j = k ∧ j.isLeft then f j k else 0) = ∑ j : Fin (q + 1), f (Sum.inl j) (Sum.inl j) := by
  simp [A, Fintype.sum_sum_type]

theorem basePoint_sum (q ν : ℕ)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F)) :
    (∑ p, Tensor.simple (basePoint q ν e p)) = ∑ p, Tensor.simple (gridPoint q ν e p) := by
  have hd : (∑ p : A q ν × A q ν, diagonalCoefficient (F := F) q ν p.1 p.2 •
      Tensor.simple (diagonalPoint q ν e p)) = ∑ j, Tensor.simple (extraPoint q ν e j) := by
    simp only [Fintype.sum_prod_type, diagonalCoefficient, ite_smul, one_smul, zero_smul]
    rw [sum_active_diagonal]
    rfl
  simp only [Fintype.sum_sum_type, basePoint, Sum.elim_inl, Sum.elim_inr]
  simp_rw [oldPoint_simple]
  rw [Finset.sum_sub_distrib, hd, sub_add_cancel]

def lowRankPoint (q ν : ℕ) (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (a : A q ν) : ∀ i, Core q ν i → RatFunc F :=
  factors q ν (e (Realization.basisVector a)) (fun b => Sum.elim (M q ν a) (fun _ => 0) b)
    (fun c => Sum.elim (H q ν a) (fun _ => 0) c)

theorem normalized_basis_expansion {K α : Type*} [Field K] [Fintype α]
    (e : (α → K) ≃ₗ[K] (α → K)) (u : α → K) (a : α) :
    e u a = ∑ b, u b * e (Realization.basisVector b) a := by
  have hex : u = ∑ b, u b • Realization.basisVector (F := K) b := by
    ext a
    simp [Realization.basisVector, smul_eq_mul, mul_ite]
  calc
    e u a = e (∑ b, u b • Realization.basisVector (F := K) b) a :=
      congrArg (fun v => e v a) hex
    _ = _ := by rw [map_sum]; simp [map_smul, smul_eq_mul]

theorem gridPoint_sum (q ν : ℕ)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F)) :
    (∑ p, Tensor.simple (gridPoint q ν e p)) = ∑ a, Tensor.simple (lowRankPoint q ν e a) := by
  ext x
  cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp only [Finset.sum_apply, Tensor.simple, Fin.prod_univ_three, gridPoint, lowRankPoint,
      factors_zero, factors_one, factors_two, h1, h2, Sum.elim_inl, Sum.elim_inr,
      Realization.basisVector, Sum.inl.injEq, Sum.inr_ne_inl, ite_false,
      Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, zero_mul,
      Fintype.sum_ite_eq, Finset.sum_const_zero,
      Lemmata.TensorRank.Tensor.pure]
  erw [normalizedPoint, normalized_basis_expansion]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem basePoint_rankAtMost (q ν : ℕ)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F)) :
    Tensor.RankAtMost (∑ p, Tensor.simple (basePoint q ν e p)) (q + 1 + ν) := by
  have hc : Fintype.card (A q ν) = q + 1 + ν := by simp [A]
  let b : Fin (q + 1 + ν) ≃ A q ν := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨fun j => lowRankPoint q ν e (b j), ?_⟩
  rw [basePoint_sum, gridPoint_sum]
  exact (b.sum_comp (fun a => Tensor.simple (lowRankPoint q ν e a))).symm

end

end Lemmata.Centroid.Construction.Circuit
