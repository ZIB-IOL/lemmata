module

public import Lemmata.Centroid.Proof.General.ResidueNumeric
public import Lemmata.Centroid.Proof.General.SplitAverage

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Lemmata.Centroid.Tensor.BalancedAlgebra

variable {F : Type*} [Field F] {V : Fin 3 → Type*} [∀ i, Fintype (V i)]
  {A : Type*} [CommRing A] [Algebra F A] [FiniteDimensional F A]
  (T : Tensor F (Fin 3) V) (hT : Concise T) (f : A →ₐ[F] centroidAlgebra T hT)

theorem nonsplit_algebra_dichotomy (hf : Function.Injective f) (I : Ideal A) [I.IsMaximal]
    (hI : IsNilpotent I) (he : 2 ≤ Module.finrank F (A ⧸ I))
    (hformat : ∀ i, 0 < Fintype.card (V i)) :
    (∀ i, Module.finrank F A ≤ Fintype.card (V i)) ∨
      (10 ≤ Module.finrank F A ∧ General.residueCost ((Module.finrank F A : ℝ) - 2) ≤
        ((Fintype.card (V 0) : ℝ) + Fintype.card (V 1) + Fintype.card (V 2)) / 3) := by
  let J := idealSpace T hT f I
  let k (i : Fin 3) := Module.finrank F (commonKernel J i)
  let q := operatorCodim J
  have hsplit := General.ideal_dimension_split (F := F) I
  have hm (i : Fin 3) : Fintype.card (V i) = k i + q i := by
    have hk : k i ≤ Fintype.card (V i) := by
      simpa only [Module.finrank_pi] using Submodule.finrank_le (commonKernel J i)
    exact (Nat.add_sub_of_le hk).symm
  have hbound (i : Fin 3) : Module.finrank F I * Module.finrank F (A ⧸ I) ≤ k i * q i :=
    nilpotent_ideal_residue_bound T hT f hf I hI i
  have hprod := ideal_product_bound T hT f hf I
  change Module.finrank F I ^ 2 ≤ ∏ i : Fin 3, q i at hprod
  rw [Fin.prod_univ_three] at hprod
  exact General.residue_profile_dichotomy (Module.finrank F A) (Module.finrank F (A ⧸ I))
    (Module.finrank F I) k q (fun i => Fintype.card (V i)) he hsplit.symm
    (General.residue_degree_dvd_finrank (F := F) (M := A) I hI)
    (residue_degree_dvd_kernel T hT f I hI) (residue_degree_dvd_codim T hT f I hI)
    hm hformat hbound hprod

theorem nonsplit_algebra_dimension_bound (hf : Function.Injective f) (I : Ideal A) [I.IsMaximal]
    (hI : IsNilpotent I) (he : 2 ≤ Module.finrank F (A ⧸ I)) (N : ℕ)
    (hformat : ∀ i, 0 < Fintype.card (V i)) (hN : ∀ i, Fintype.card (V i) ≤ N) :
    Module.finrank F A ≤ generalBound N := by
  rcases nonsplit_algebra_dichotomy T hT f hf I hI he hformat with h | ⟨hD, hcost⟩
  · exact ((h 0).trans (hN 0)).trans (General.le_generalBound N)
  · apply General.residue_cost_dimension_bound _ _ hD
    have h₀ : (Fintype.card (V 0) : ℝ) ≤ N := by exact_mod_cast hN 0
    have h₁ : (Fintype.card (V 1) : ℝ) ≤ N := by exact_mod_cast hN 1
    have h₂ : (Fintype.card (V 2) : ℝ) ≤ N := by exact_mod_cast hN 2
    linarith

theorem nonsplit_algebra_cost_bound (hf : Function.Injective f) (I : Ideal A) [I.IsMaximal]
    (hI : IsNilpotent I) (he : 2 ≤ Module.finrank F (A ⧸ I))
    (hformat : ∀ i, 0 < Fintype.card (V i)) :
    General.dimensionCost (Module.finrank F A) ≤
      ((Fintype.card (V 0) : ℝ) + Fintype.card (V 1) + Fintype.card (V 2)) / 3 := by
  rcases nonsplit_algebra_dichotomy T hT f hf I hI he hformat with h | ⟨hD, hcost⟩
  · have h₀ : (Module.finrank F A : ℝ) ≤ Fintype.card (V 0) := by exact_mod_cast h 0
    have h₁ : (Module.finrank F A : ℝ) ≤ Fintype.card (V 1) := by exact_mod_cast h 1
    have h₂ : (Module.finrank F A : ℝ) ≤ Fintype.card (V 2) := by exact_mod_cast h 2
    have hle := General.dimensionCost_le_self (Module.finrank F A)
    linarith
  · exact General.dimensionCost_le_of_residueCost hD hcost

end Lemmata.Centroid.Tensor.BalancedAlgebra
