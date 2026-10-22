module

public import Lemmata.Centroid.Proof.General.LocalAverage

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Lemmata.Centroid.Tensor

variable {F : Type*} [Field F] {V : Fin 3 → Type*} [∀ i, Fintype (V i)]

def operatorCodim (J : Submodule F (∀ i, Matrix (V i) (V i) F)) (i : Fin 3) : ℕ :=
  Fintype.card (V i) - Module.finrank F (commonKernel J i)

theorem operatorCodim_pos (J : Submodule F (∀ i, Matrix (V i) (V i) F)) {R : ℕ}
    (hR : 0 < R) (hbound : ∀ i, R ≤ Module.finrank F (commonKernel J i) * operatorCodim J i)
    (i : Fin 3) : 0 < operatorCodim J i := by
  have h := hbound i
  by_contra h'
  have hz : operatorCodim J i = 0 := by omega
  rw [hz, Nat.mul_zero] at h
  omega

theorem operatorProfile_average (J : Submodule F (∀ i, Matrix (V i) (V i) F)) {R : ℕ}
    (hR : 0 < R) (hbound : ∀ i, R ≤ Module.finrank F (commonKernel J i) * operatorCodim J i) :
    let u := ((operatorCodim J 0 : ℝ) * operatorCodim J 1 * operatorCodim J 2) ^ (1 / 3 : ℝ)
    u + R / u ≤ ((Fintype.card (V 0) : ℝ) + Fintype.card (V 1) + Fintype.card (V 2)) / 3 := by
  have hq (i : Fin 3) : (0 : ℝ) < operatorCodim J i := by
    exact_mod_cast operatorCodim_pos J hR hbound i
  have hm (i : Fin 3) : (operatorCodim J i : ℝ) + R / (operatorCodim J i : ℝ) ≤
      Fintype.card (V i) := by
    have hk : Module.finrank F (commonKernel J i) ≤ Fintype.card (V i) := by
      simpa only [Module.finrank_pi] using Submodule.finrank_le (commonKernel J i)
    have heq : Module.finrank F (commonKernel J i) + operatorCodim J i = Fintype.card (V i) :=
      Nat.add_sub_of_le hk
    have heqR : (Module.finrank F (commonKernel J i) : ℝ) + operatorCodim J i = Fintype.card (V i) := by
      exact_mod_cast heq
    have hboundR : (R : ℝ) ≤ Module.finrank F (commonKernel J i) * (operatorCodim J i : ℝ) := by
      exact_mod_cast hbound i
    have hd : (R : ℝ) / operatorCodim J i ≤ Module.finrank F (commonKernel J i) :=
      (div_le_iff₀ (hq i)).2 hboundR
    linarith
  exact General.geometric_mean3_module_bound (by positivity) (hq 0) (hq 1) (hq 2) (hm 0) (hm 1) (hm 2)

namespace BalancedAlgebra

variable {A : Type*} [CommRing A] [Algebra F A] [FiniteDimensional F A]
variable (T : Tensor F (Fin 3) V) (hT : Concise T) (f : A →ₐ[F] centroidAlgebra T hT)

theorem nilpotent_ideal_cost_bound (hf : Function.Injective f) (I : Ideal A) (hI : IsNilpotent I)
    (hr : 0 < Module.finrank F I) :
    General.supportCost (Module.finrank F I) ≤
      ((Fintype.card (V 0) : ℝ) + Fintype.card (V 1) + Fintype.card (V 2)) / 3 := by
  let J := idealSpace T hT f I
  have hbound (i : Fin 3) : Module.finrank F I ≤ Module.finrank F (commonKernel J i) * operatorCodim J i :=
    nilpotent_ideal_kernel_bound T hT f hf I hI i
  have hmean := operatorProfile_average J hr hbound
  have hprod := ideal_product_bound T hT f hf I
  change Module.finrank F I ^ 2 ≤ ∏ i : Fin 3, operatorCodim J i at hprod
  rw [Fin.prod_univ_three] at hprod
  have hprodR : (Module.finrank F I : ℝ) ^ 2 ≤
      (operatorCodim J 0 : ℝ) * operatorCodim J 1 * operatorCodim J 2 := by exact_mod_cast hprod
  have hroot := Real.rpow_le_rpow (sq_nonneg (Module.finrank F I : ℝ)) hprodR
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ Module.finrank F I)] at hroot
  norm_num at hroot
  have hrR : (1 : ℝ) ≤ Module.finrank F I := by exact_mod_cast hr
  exact (General.supportCost_le_u_add_div hrR hroot).trans hmean

theorem split_algebra_cost_bound (hf : Function.Injective f) (I : Ideal A) (hI : IsNilpotent I)
    (hresidue : Module.finrank F (A ⧸ I) = 1) (hformat : ∀ i, 0 < Fintype.card (V i)) :
    General.dimensionCost (Module.finrank F A) ≤
      ((Fintype.card (V 0) : ℝ) + Fintype.card (V 1) + Fintype.card (V 2)) / 3 := by
  have hdim := General.ideal_dimension_split (F := F) I
  rw [hresidue] at hdim
  by_cases hr : Module.finrank F I = 0
  · have hd : Module.finrank F A = 1 := by omega
    rw [hd, General.dimensionCost_one]
    have h₀ : (1 : ℝ) ≤ Fintype.card (V 0) := by exact_mod_cast hformat 0
    have h₁ : (1 : ℝ) ≤ Fintype.card (V 1) := by exact_mod_cast hformat 1
    have h₂ : (1 : ℝ) ≤ Fintype.card (V 2) := by exact_mod_cast hformat 2
    linarith
  · have hrpos : 0 < Module.finrank F I := by omega
    have hd : Module.finrank F A = Module.finrank F I + 1 := by omega
    rw [hd]
    simp only [General.dimensionCost, show ¬ Module.finrank F I + 1 ≤ 1 by omega,
      ite_false, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    exact nilpotent_ideal_cost_bound T hT f hf I hI hrpos

end BalancedAlgebra
end Lemmata.Centroid.Tensor
