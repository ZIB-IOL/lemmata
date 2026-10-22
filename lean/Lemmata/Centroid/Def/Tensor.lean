module

public import Lemmata.TensorRank.Main

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace Lemmata.Centroid

universe u v w z

/-- A tensor as a coefficient array on a family of coordinate types. -/
abbrev Tensor (R : Type u) (ι : Type v) (V : ι → Type w) := Lemmata.TensorRank.Tensor R ι V

namespace Tensor

variable {R : Type u} {ι : Type v} {V : ι → Type w} {W : ι → Type z}

/-- The simple tensor formed from one coordinate vector at each party. -/
abbrev simple [CommMonoid R] [Fintype ι] (u : ∀ i, V i → R) : Tensor R ι V :=
  Lemmata.TensorRank.Tensor.pure u

@[simp] theorem simple_apply [CommMonoid R] [Fintype ι]
    (u : ∀ i, V i → R) (x : ∀ i, V i) : simple u x = ∏ i, u i (x i) := rfl

/-- The Kronecker product pairs coordinates within each original party. -/
abbrev kronecker [Mul R] (T : Tensor R ι V) (S : Tensor R ι W) :
    Tensor R ι (fun i => V i × W i) :=
  Lemmata.TensorRank.Tensor.product T S

@[simp] theorem kronecker_apply [Mul R] (T : Tensor R ι V) (S : Tensor R ι W)
    (x : ∀ i, V i × W i) :
    kronecker T S x = T (fun i => (x i).1) * S (fun i => (x i).2) := rfl

theorem kronecker_simple [CommMonoid R] [Fintype ι]
    (u : ∀ i, V i → R) (v : ∀ i, W i → R) :
    kronecker (simple u) (simple v) =
      simple (fun i p => u i p.1 * v i p.2) := by
  funext x
  exact (Finset.prod_mul_distrib : _).symm

/-- Regrouped tensor power: each original party keeps all of its copy coordinates. -/
abbrev power [CommMonoid R] (T : Tensor R ι V) (n : ℕ) :
    Tensor R ι (fun i => Fin n → V i) :=
  Lemmata.TensorRank.Tensor.power T n

@[simp] theorem power_apply [CommMonoid R] (T : Tensor R ι V) (n : ℕ)
    (x : ∀ i, Fin n → V i) : power T n x = ∏ j, T (fun i => x i j) := rfl

theorem power_simple [CommMonoid R] [Fintype ι]
    (u : ∀ i, V i → R) (n : ℕ) :
    power (simple u) n = simple (fun i x => ∏ j, u i (x j)) := by
  funext x
  simp only [power, simple, Lemmata.TensorRank.Tensor.pure, Lemmata.TensorRank.Tensor.power]
  exact Finset.prod_comm

@[simp] theorem kronecker_zero_left [MulZeroClass R] (S : Tensor R ι W) :
    kronecker (0 : Tensor R ι V) S = 0 := by
  funext x
  exact zero_mul _

@[simp] theorem kronecker_zero_right [MulZeroClass R] (T : Tensor R ι V) :
    kronecker T (0 : Tensor R ι W) = 0 := by
  funext x
  exact mul_zero _

theorem kronecker_add_left [Distrib R] (T₁ T₂ : Tensor R ι V)
    (S : Tensor R ι W) :
    kronecker (T₁ + T₂) S = kronecker T₁ S + kronecker T₂ S := by
  funext x
  exact add_mul _ _ _

theorem kronecker_add_right [Distrib R] (T : Tensor R ι V)
    (S₁ S₂ : Tensor R ι W) :
    kronecker T (S₁ + S₂) = kronecker T S₁ + kronecker T S₂ := by
  funext x
  exact mul_add _ _ _

/-- Apply one matrix to each party, summing over the input coordinates. -/
noncomputable abbrev localMap [CommSemiring R] [Fintype ι] [∀ i, Fintype (V i)]
    (A : ∀ i, W i → V i → R) (T : Tensor R ι V) : Tensor R ι W :=
  Lemmata.TensorRank.Tensor.localMap A T

@[simp] theorem localMap_apply [CommSemiring R] [Fintype ι] [∀ i, Fintype (V i)]
    (A : ∀ i, W i → V i → R) (T : Tensor R ι V) (y : ∀ i, W i) :
    localMap A T y = ∑ x : ∀ i, V i, (∏ i, A i (y i) (x i)) * T x := rfl

theorem localMap_simple [CommSemiring R] [Fintype ι] [∀ i, Fintype (V i)]
    (A : ∀ i, W i → V i → R) (u : ∀ i, V i → R) :
    localMap A (simple u) = simple (fun i y => ∑ x, A i y x * u i x) := by
  funext y
  simp only [localMap, simple, Lemmata.TensorRank.Tensor.pure, Lemmata.TensorRank.Tensor.localMap]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun x _ => (Finset.prod_mul_distrib : _).symm

@[simp] theorem localMap_zero [CommSemiring R] [Fintype ι] [∀ i, Fintype (V i)]
    (A : ∀ i, W i → V i → R) : localMap A (0 : Tensor R ι V) = 0 := by
  funext y
  simp [localMap, Lemmata.TensorRank.Tensor.localMap]

theorem localMap_add [CommSemiring R] [Fintype ι] [∀ i, Fintype (V i)]
    (A : ∀ i, W i → V i → R) (T S : Tensor R ι V) :
    localMap A (T + S) = localMap A T + localMap A S := by
  funext y
  simp [localMap, mul_add, Finset.sum_add_distrib, Lemmata.TensorRank.Tensor.localMap]

theorem localMap_sum [CommSemiring R] [Fintype ι] [∀ i, Fintype (V i)]
    {J : Type*} (s : Finset J) (A : ∀ i, W i → V i → R)
    (T : J → Tensor R ι V) :
    localMap A (∑ j ∈ s, T j) = ∑ j ∈ s, localMap A (T j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih => simp [Finset.sum_insert hj, localMap_add, ih]

theorem localMap_smul [CommSemiring R] [Fintype ι] [∀ i, Fintype (V i)]
    (A : ∀ i, W i → V i → R) (c : R) (T : Tensor R ι V) :
    localMap A (c • T) = c • localMap A T := by
  funext y
  simp only [localMap, Pi.smul_apply, smul_eq_mul, Lemmata.TensorRank.Tensor.localMap]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => mul_left_comm _ _ _

/-- Composition of independent local maps is again an independent local map. -/
theorem localMap_comp [CommSemiring R] [Fintype ι]
    [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] {U : ι → Type*}
    (B : ∀ i, U i → W i → R) (A : ∀ i, W i → V i → R) (T : Tensor R ι V) :
    localMap B (localMap A T) =
      localMap (fun i z x => ∑ y, B i z y * A i y x) T := by
  funext z
  simp only [localMap, Lemmata.TensorRank.Tensor.localMap]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, Fintype.prod_sum]
  congr 1
  exact Finset.sum_congr rfl fun y _ => (Finset.prod_mul_distrib : _).symm

/-- A coordinate restriction selects an input coordinate separately at each party. -/
abbrev restrict (f : ∀ i, W i → V i) (T : Tensor R ι V) : Tensor R ι W :=
  Lemmata.TensorRank.Tensor.reindex f T

@[simp] theorem restrict_apply (f : ∀ i, W i → V i) (T : Tensor R ι V)
    (y : ∀ i, W i) : restrict f T y = T (fun i => f i (y i)) := rfl

theorem localMap_restrict [CommSemiring R] [Fintype ι] [∀ i, Fintype (V i)]
    (f : ∀ i, W i → V i) (T : Tensor R ι V) :
    localMap (fun i w v => if v = f i w then 1 else 0) T = restrict f T := by
  funext y
  simp [localMap, restrict, Fintype.prod_ite_zero, ← funext_iff, Lemmata.TensorRank.Tensor.reindex, Lemmata.TensorRank.Tensor.localMap]

@[simp] theorem restrict_simple [CommMonoid R] [Fintype ι]
    (f : ∀ i, W i → V i) (u : ∀ i, V i → R) :
    restrict f (simple u) = simple (fun i y => u i (f i y)) := rfl

@[simp] theorem restrict_zero [Zero R] (f : ∀ i, W i → V i) :
    restrict f (0 : Tensor R ι V) = 0 := rfl

theorem restrict_add [Add R] (f : ∀ i, W i → V i) (T S : Tensor R ι V) :
    restrict f (T + S) = restrict f T + restrict f S := rfl

theorem restrict_comp {U : ι → Type*} (g : ∀ i, U i → W i)
    (f : ∀ i, W i → V i) (T : Tensor R ι V) :
    restrict g (restrict f T) = restrict (fun i z => f i (g i z)) T := rfl

theorem restrict_sum [AddCommMonoid R] {J : Type*} (s : Finset J)
    (f : ∀ i, W i → V i) (T : J → Tensor R ι V) :
    restrict f (∑ j ∈ s, T j) = ∑ j ∈ s, restrict f (T j) := by
  funext y
  simp only [restrict, Finset.sum_apply, Lemmata.TensorRank.Tensor.reindex]

/-- Apply a ring homomorphism to every coefficient (for example polynomial evaluation). -/
def mapCoefficients {S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (T : Tensor R ι V) : Tensor S ι V := fun x => f (T x)

@[simp] theorem mapCoefficients_apply {S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (T : Tensor R ι V) (x : ∀ i, V i) :
    mapCoefficients f T x = f (T x) := rfl

@[simp] theorem mapCoefficients_simple {S : Type*} [CommSemiring R] [CommSemiring S]
    [Fintype ι] (f : R →+* S) (u : ∀ i, V i → R) :
    mapCoefficients f (simple u) = simple (fun i x => f (u i x)) := by
  funext x
  exact map_prod f _ _

@[simp] theorem mapCoefficients_zero {S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) : mapCoefficients f (0 : Tensor R ι V) = 0 := by
  funext x
  exact map_zero f

theorem mapCoefficients_add {S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (T U : Tensor R ι V) :
    mapCoefficients f (T + U) = mapCoefficients f T + mapCoefficients f U := by
  funext x
  exact map_add f _ _

theorem mapCoefficients_sum {S : Type*} [Semiring R] [Semiring S] {J : Type*}
    (s : Finset J) (f : R →+* S) (T : J → Tensor R ι V) :
    mapCoefficients f (∑ j ∈ s, T j) = ∑ j ∈ s, mapCoefficients f (T j) := by
  funext x
  simp only [mapCoefficients, Finset.sum_apply, map_sum]

@[simp] theorem mapCoefficients_kronecker {S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (T : Tensor R ι V) (U : Tensor R ι W) :
    mapCoefficients f (kronecker T U) =
      kronecker (mapCoefficients f T) (mapCoefficients f U) := by
  funext x
  exact map_mul f _ _

@[simp] theorem mapCoefficients_power {S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (T : Tensor R ι V) (n : ℕ) :
    mapCoefficients f (power T n) = power (mapCoefficients f T) n := by
  funext x
  exact map_prod f _ _

end Tensor
end Lemmata.Centroid
