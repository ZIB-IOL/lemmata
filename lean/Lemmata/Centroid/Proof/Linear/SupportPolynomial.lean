module

public import Lemmata.Centroid.Proof.Linear.ArraySubspaces
public import Lemmata.Centroid.Proof.Linear.PolynomialExtension

@[expose] public section

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.Centroid.Linear

variable {F α β γ : Type*} [Field F] [Fintype α] [Fintype β] [Fintype γ]

theorem exists_polynomial_support_annihilator (S : Submodule F (α × (β × γ) → F))
    (hdim : Module.finrank F (annihilatorQuotientImage S) <
      Module.finrank F (coordinateOrthogonal (arraySupport S))) :
    ∃ w : γ → MvPolynomial α F, w ≠ 0 ∧ ∀ m : α →₀ ℕ,
      (fun p : α × γ => (MvPolynomial.X p.1 * w p.2).coeff m) ∈
        coordinateOrthogonal (arraySupport (S.map swapFirstTwo.toLinearMap)) := by
  let A := coordinateOrthogonal (arraySupport S)
  let Z := annihilatorQuotientImage S
  let bA := Module.finBasis F A
  let bZ := Module.finBasis F Z
  let L : α → ((Fin (Module.finrank F A) → F) →ₗ[F] (Fin (Module.finrank F Z) → F)) :=
    fun a => bZ.equivFun.toLinearMap.comp
      ((annihilatorRowMap S a).comp bA.equivFun.symm.toLinearMap)
  obtain ⟨p, hp, hL⟩ := exists_polynomial_pencil_kernel L (by simpa only [Fintype.card_fin] using hdim)
  let g : (Fin (Module.finrank F A) → F) →ₗ[F] (β × γ → F) :=
    A.subtype.comp bA.equivFun.symm.toLinearMap
  have hg : Function.Injective g := Subtype.val_injective.comp bA.equivFun.symm.injective
  let a := polynomialMap g p
  have ha : a ≠ 0 := by
    intro hz
    apply hp
    apply polynomialMap_injective g hg
    simpa only [map_zero] using hz
  obtain ⟨⟨v, c⟩, hvc⟩ := Function.ne_iff.mp ha
  refine ⟨fun c => a (v, c), fun hz => hvc (congrFun hz c), ?_⟩
  intro m
  let q : α → A := fun u => bA.equivFun.symm (fun j => (MvPolynomial.X u * p j).coeff m)
  have hcoord : (∑ u, L u (fun j => (MvPolynomial.X u * p j).coeff m)) = 0 := by
    funext z
    have he := congrArg (fun r : Fin (Module.finrank F Z) → MvPolynomial α F => (r z).coeff m) hL
    simpa only [Finset.sum_apply, MvPolynomial.coeff_sum, polynomialMap_coeff,
      Pi.zero_apply, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using he
  have hz : (∑ u, annihilatorRowMap S u (q u)) = 0 := by
    apply bZ.equivFun.injective
    rw [map_sum, map_zero]
    exact hcoord
  have hquot : (secondRowAnnihilator S).mkQ (∑ u, arrayInsert u (q u).val) = 0 := by
    rw [map_sum]
    have he := congrArg Subtype.val hz
    simp only [Submodule.coe_sum, Submodule.coe_zero] at he
    change (∑ u, (secondRowAnnihilator S).mkQ (arrayInsert u (q u).val)) = 0 at he
    exact he
  have hmem : (∑ u, arrayInsert u (q u).val) ∈ secondRowAnnihilator S :=
    (Submodule.Quotient.mk_eq_zero _).mp hquot
  have hcoeff (u : α) : (fun t : β × γ => (MvPolynomial.X u * a t).coeff m) = (q u).val := by
    have hmap : polynomialMap g (fun j => MvPolynomial.X u * p j) =
        fun t => MvPolynomial.X u * a t :=
      (polynomialMap g).map_smul (MvPolynomial.X u) p
    funext t
    calc
      _ = (polynomialMap g (fun j => MvPolynomial.X u * p j) t).coeff m := by rw [hmap]
      _ = _ := polynomialMap_coeff g _ m t
  have heq : (∑ u, arrayInsert u (q u).val) =
      fun t : α × (β × γ) => (MvPolynomial.X t.1 * a t.2).coeff m := by
    rw [sum_arrayInsert]
    funext t
    exact (congrFun (hcoeff t.1) t.2).symm
  rw [heq] at hmem
  exact (mem_secondRowAnnihilator S _).mp hmem v

end Lemmata.Centroid.Linear
