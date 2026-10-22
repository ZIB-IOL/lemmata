module

public import Lemmata.Centroid.Proof.Construction.RectangularSupport
public import Lemmata.Centroid.Proof.Construction.ThreeParty
public import Lemmata.Centroid.Proof.Construction.CircuitSpans

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Construction.Rectangular

noncomputable section

variable {F : Type*} [Field F]

def factors {R : Type*} (n t : ℕ) (a : Fin n → R) (b c : (Option (Fin n) ⊕ Fin t) → R) :
    ∀ i, Core n t i → R := Tensor.point a b c

@[simp] theorem factors_zero {R : Type*} (n t : ℕ) (a : Fin n → R)
    (b c : (Option (Fin n) ⊕ Fin t) → R) : factors n t a b c 0 = a := rfl
@[simp] theorem factors_one {R : Type*} (n t : ℕ) (a : Fin n → R)
    (b c : (Option (Fin n) ⊕ Fin t) → R) : factors n t a b c 1 = b := rfl
@[simp] theorem factors_two {R : Type*} (n t : ℕ) (a : Fin n → R)
    (b c : (Option (Fin n) ⊕ Fin t) → R) : factors n t a b c 2 = c := rfl

def splitScalar (n t : ℕ) (ht : t ≤ n) (j : Fin n) (r : Option (Fin n)) : RatFunc F :=
  ∑ k : Option (Fin t), if selected ht k = r then lambda (F := F) n t j r else 0

theorem splitScalar_selected (n t : ℕ) (ht : t ≤ n) (j : Fin n) (k : Option (Fin t)) :
    splitScalar (F := F) n t ht j (selected ht k) = lambda (F := F) n t j (selected ht k) := by
  simp [splitScalar, (selected_injective ht).eq_iff]

theorem sum_splitScalar {W : Type*} [AddCommGroup W] [Module (RatFunc F) W]
    (n t : ℕ) (ht : t ≤ n) (j : Fin n) (μ : Option (Fin n) → RatFunc F)
    (v : Option (Fin n) → W) :
    (∑ r, (μ r * splitScalar (F := F) n t ht j r) • v r) =
      ∑ k : Option (Fin t), (μ (selected ht k) * lambda (F := F) n t j (selected ht k)) • v (selected ht k) := by
  simp only [splitScalar, Finset.mul_sum, Finset.sum_smul, mul_ite, mul_zero, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  exact Fintype.sum_ite_eq _ _

theorem row_zero (n t : ℕ) (j : Fin n) :
    (∑ r : Option (Fin n), relation (F := F) n t r • gridPoint (F := F) n t j r) = 0 := by
  ext a
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, gridPoint]
  calc
    _ = M (F := F) n a j * ∑ r, relation (F := F) n t r * H (F := F) n t a r := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = 0 := by rw [relation_H, mul_zero]

theorem row_split (n t : ℕ) (ht : t ≤ n) (j : Fin n) :
    (∑ r : Option (Fin n), (relation (F := F) n t r * splitScalar (F := F) n t ht j r) • gridPoint (F := F) n t j r) =
      hPrime (F := F) n t ht j := sum_splitScalar (F := F) n t ht j (relation (F := F) n t) (gridPoint (F := F) n t j)

def oldPoint (n t : ℕ) (ht : t ≤ n) (p : Fin n × Option (Fin n)) : ∀ i, Core n t i → RatFunc F :=
  factors n t (gridPoint (F := F) n t p.1 p.2)
    (Realization.basisVector (Sum.inl (some p.1)) - splitScalar (F := F) n t ht p.1 p.2 •
      Realization.basisVector (Sum.inl none))
    (Realization.basisVector (Sum.inl p.2))

def extraPoint (n t : ℕ) (ht : t ≤ n) (k : Option (Fin t)) : ∀ i, Core n t i → RatFunc F :=
  factors n t (fun _ => 1) (Realization.basisVector (Sum.inl none))
    (Realization.basisVector (Sum.inl (selected ht k)))

abbrev PointIndex (n t : ℕ) := (Fin n × Option (Fin n)) ⊕ Option (Fin t)

def basePoint (n t : ℕ) (ht : t ≤ n) : PointIndex n t → ∀ i, Core n t i → RatFunc F :=
  Sum.elim (oldPoint (F := F) n t ht) (extraPoint (F := F) n t ht)

def gridTensorPoint (n t : ℕ) (p : Fin n × Option (Fin n)) : ∀ i, Core n t i → RatFunc F :=
  factors n t (gridPoint (F := F) n t p.1 p.2)
    (Realization.basisVector (Sum.inl (some p.1))) (Realization.basisVector (Sum.inl p.2))

def diagonalPoint (n t : ℕ) (p : Fin n × Option (Fin n)) : ∀ i, Core n t i → RatFunc F :=
  factors n t (gridPoint (F := F) n t p.1 p.2)
    (Realization.basisVector (Sum.inl none)) (Realization.basisVector (Sum.inl p.2))

theorem oldPoint_simple (n t : ℕ) (ht : t ≤ n) (p : Fin n × Option (Fin n)) :
    Tensor.simple (oldPoint (F := F) n t ht p) = Tensor.simple (gridTensorPoint (F := F) n t p) -
      splitScalar (F := F) n t ht p.1 p.2 • Tensor.simple (diagonalPoint (F := F) n t p) := by
  ext x
  simp only [Tensor.simple, Fin.prod_univ_three, oldPoint, gridTensorPoint, diagonalPoint,
    factors_zero, factors_one, factors_two, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Lemmata.TensorRank.Tensor.pure]
  let a := gridPoint (F := F) n t p.1 p.2 (x 0)
  let b := Realization.basisVector (F := RatFunc F) (Sum.inl (some p.1)) (x 1)
  let c := Realization.basisVector (F := RatFunc F) (Sum.inl p.2) (x 2)
  let d := splitScalar (F := F) n t ht p.1 p.2
  let f := Realization.basisVector (F := RatFunc F) (Sum.inl none) (x 1)
  change a * (b - d * f) * c = a * b * c - d * (a * f * c)
  ring

def lowRankPoint (n t : ℕ) (a : Fin n) : ∀ i, Core n t i → RatFunc F :=
  factors n t (Realization.basisVector a)
    (Sum.elim (fun b => Option.elim b 0 (M (F := F) n a)) (fun _ => 0))
    (Sum.elim (H (F := F) n t a) (fun _ => 0))

end

end Lemmata.Centroid.Construction.Rectangular
