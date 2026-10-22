module

public import Lemmata.Centroid.Proof.Tensor.Support
public import Mathlib.LinearAlgebra.Dimension.DivisionRing

@[expose] public section

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.Centroid.Linear

variable {F α β γ : Type*} [Field F] [Fintype α] [Fintype β] [Fintype γ]

def arraySlice (a : α) : (α × β → F) →ₗ[F] (β → F) where
  toFun v b := v (a, b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def arraySupport (S : Submodule F (α × β → F)) : Submodule F (β → F) :=
  ⨆ a, S.map (arraySlice a)

def arrayInsert (a : α) : (β → F) →ₗ[F] (α × β → F) where
  toFun v p := if p.1 = a then v p.2 else 0
  map_add' v w := by funext p; by_cases h : p.1 = a <;> simp [h]
  map_smul' r v := by funext p; by_cases h : p.1 = a <;> simp [h]

def rowSubspace (P : Submodule F (β → F)) : Submodule F (α × β → F) where
  carrier := {v | ∀ a, arraySlice a v ∈ P}
  zero_mem' := fun _ => P.zero_mem
  add_mem' := fun hv hw a => P.add_mem (hv a) (hw a)
  smul_mem' := fun r _ hv a => P.smul_mem r (hv a)

def rowSubspaceEquiv (P : Submodule F (β → F)) : rowSubspace (α := α) P ≃ₗ[F] (α → P) where
  toFun v a := ⟨arraySlice a v.val, v.property a⟩
  invFun v := ⟨fun p => (v p.1).val p.2, fun a => (v a).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype α] [Fintype β] in
theorem arrayInsert_mem_rowSubspace (P : Submodule F (β → F)) (a : α) {v : β → F}
    (hv : v ∈ P) : arrayInsert a v ∈ rowSubspace P := by
  intro a'
  by_cases h : a' = a
  · simpa only [arraySlice, LinearMap.coe_mk, AddHom.coe_mk, arrayInsert, h, ite_true] using hv
  · have he : arraySlice a' (arrayInsert a v) = 0 := by
      funext b
      simp [arraySlice, arrayInsert, h]
    rw [he]
    exact P.zero_mem

omit [Fintype β] in
theorem sum_arrayInsert (v : α → β → F) : (∑ a, arrayInsert a (v a)) = fun p => v p.1 p.2 := by
  funext p
  simp [arrayInsert, Finset.sum_apply]

theorem rowSubspace_finrank (P : Submodule F (β → F)) :
    Module.finrank F (rowSubspace (α := α) P) = Fintype.card α * Module.finrank F P := by
  rw [(rowSubspaceEquiv P).finrank_eq, Module.finrank_pi_fintype]
  simp

omit [Fintype α] [Fintype β] in
theorem le_rowSubspace_support (S : Submodule F (α × β → F)) : S ≤ rowSubspace (arraySupport S) := by
  intro v hv a
  exact Submodule.mem_iSup_of_mem a ⟨v, hv, rfl⟩

theorem finrank_le_card_mul_arraySupport (S : Submodule F (α × β → F)) :
    Module.finrank F S ≤ Fintype.card α * Module.finrank F (arraySupport S) := by
  exact (Submodule.finrank_mono (le_rowSubspace_support S)).trans_eq (rowSubspace_finrank _)

theorem rowSubspace_orthogonal_support (S : Submodule F (α × β → F)) :
    rowSubspace (α := α) (coordinateOrthogonal (arraySupport S)) ≤ coordinateOrthogonal S := by
  intro v hv
  rw [mem_coordinateOrthogonal]
  intro w hw
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro a _
  exact (mem_coordinateOrthogonal _ _).mp (hv a) (arraySlice a w)
    (Submodule.mem_iSup_of_mem a ⟨w, hw, rfl⟩)

def swapFirstTwo : (α × (β × γ) → F) ≃ₗ[F] (β × (α × γ) → F) :=
  LinearEquiv.funCongrLeft F F
    { toFun := fun p => (p.2.1, p.1, p.2.2)
      invFun := fun p => (p.2.1, p.1, p.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

omit [Fintype α] [Fintype β] [Fintype γ] in
@[simp] theorem swapFirstTwo_apply (v : α × (β × γ) → F) (b : β) (a : α) (c : γ) :
    swapFirstTwo v (b, a, c) = v (a, b, c) := rfl

theorem coordinateOrthogonal_swap (S : Submodule F (α × (β × γ) → F)) :
    coordinateOrthogonal (S.map swapFirstTwo.toLinearMap) =
      (coordinateOrthogonal S).map swapFirstTwo.toLinearMap := by
  ext v
  constructor
  · intro hv
    refine ⟨swapFirstTwo.symm v, ?_, by simp⟩
    apply (mem_coordinateOrthogonal S _).mpr
    intro w hw
    have he := (mem_coordinateOrthogonal _ _).mp hv (swapFirstTwo w) ⟨w, hw, rfl⟩
    change (∑ p : β × (α × γ), v p * w (p.2.1, p.1, p.2.2)) = 0 at he
    change (∑ p : α × (β × γ), v (p.2.1, p.1, p.2.2) * w p) = 0
    simp only [Fintype.sum_prod_type] at he ⊢
    rw [Finset.sum_comm] at he
    exact he
  · rintro ⟨u, hu, rfl⟩
    rw [mem_coordinateOrthogonal]
    rintro _ ⟨w, hw, rfl⟩
    have he := (mem_coordinateOrthogonal _ _).mp hu w hw
    change (∑ p : β × (α × γ), u (p.2.1, p.1, p.2.2) * w (p.2.1, p.1, p.2.2)) = 0
    simp only [Fintype.sum_prod_type] at he ⊢
    rw [Finset.sum_comm]
    exact he

theorem finrank_quotient_image_add {M : Type*} [AddCommGroup M] [Module F M]
    [FiniteDimensional F M] (P Q : Submodule F M) :
    Module.finrank F (P.map Q.mkQ) + Module.finrank F Q = Module.finrank F (P ⊔ Q : Submodule F M) := by
  let g := Q.mkQ.domRestrict P
  have hk : g.ker = (P ⊓ Q).comap P.subtype := by
    ext x
    change (Submodule.Quotient.mk x.1 : M ⧸ Q) = 0 ↔ x.1 ∈ P ⊓ Q
    rw [Submodule.Quotient.mk_eq_zero Q]
    exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
  have hkd : Module.finrank F g.ker = Module.finrank F (P ⊓ Q : Submodule F M) := by
    rw [hk]
    exact (Submodule.comap_equiv_self_of_inj_of_le (f := P.subtype)
      (p := P ⊓ Q) P.subtype_injective (fun x hx => ⟨⟨x, hx.1⟩, rfl⟩)).finrank_eq
  have hd := g.finrank_range_add_finrank_ker
  change Module.finrank F (Q.mkQ.domRestrict P).range + Module.finrank F g.ker = _ at hd
  rw [LinearMap.range_domRestrict, hkd] at hd
  have hs := Submodule.finrank_sup_add_finrank_inf_eq P Q
  omega

theorem finrank_inf_ker_add_finrank_map {M N : Type*} [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] (P : Submodule F M) [FiniteDimensional F P] (g : M →ₗ[F] N) :
    Module.finrank F (P ⊓ g.ker : Submodule F M) + Module.finrank F (P.map g) =
      Module.finrank F P := by
  have hk : (g.domRestrict P).ker = (P ⊓ g.ker).comap P.subtype := by
    ext x
    change g x.1 = 0 ↔ x.1 ∈ P ⊓ g.ker
    exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
  have hkd : Module.finrank F (g.domRestrict P).ker =
      Module.finrank F (P ⊓ g.ker : Submodule F M) := by
    rw [hk]
    exact (Submodule.comap_equiv_self_of_inj_of_le (f := P.subtype)
      (p := P ⊓ g.ker) P.subtype_injective (fun x hx => ⟨⟨x, hx.1⟩, rfl⟩)).finrank_eq
  have hd := (g.domRestrict P).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, hkd] at hd
  omega

def secondRowAnnihilator (S : Submodule F (α × (β × γ) → F)) :
    Submodule F (α × (β × γ) → F) :=
  (rowSubspace (α := β) (coordinateOrthogonal (arraySupport (S.map swapFirstTwo.toLinearMap)))).map
    swapFirstTwo.symm.toLinearMap

omit [Fintype β] in
theorem mem_secondRowAnnihilator (S : Submodule F (α × (β × γ) → F)) (v : α × (β × γ) → F) :
    v ∈ secondRowAnnihilator S ↔ ∀ b : β,
      (fun p : α × γ => v (p.1, b, p.2)) ∈ coordinateOrthogonal (arraySupport (S.map swapFirstTwo.toLinearMap)) := by
  constructor
  · rintro ⟨w, hw, rfl⟩ b
    exact hw b
  · intro hv
    exact ⟨swapFirstTwo v, hv, LinearEquiv.symm_apply_apply swapFirstTwo v⟩

theorem secondRowAnnihilator_le (S : Submodule F (α × (β × γ) → F)) :
    secondRowAnnihilator S ≤ coordinateOrthogonal S := by
  rintro _ ⟨v, hv, rfl⟩
  have hc := rowSubspace_orthogonal_support (S.map swapFirstTwo.toLinearMap) hv
  rw [coordinateOrthogonal_swap] at hc
  obtain ⟨w, hw, he⟩ := hc
  have he' : (swapFirstTwo (F := F) (α := α) (β := β) (γ := γ)).symm v = w := by
    apply (swapFirstTwo (F := F) (α := α) (β := β) (γ := γ)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact he.symm
  change (swapFirstTwo (F := F) (α := α) (β := β) (γ := γ)).symm v ∈ coordinateOrthogonal S
  rw [he']
  exact hw

theorem secondRowAnnihilator_finrank (S : Submodule F (α × (β × γ) → F)) :
    Module.finrank F (secondRowAnnihilator S) =
      Fintype.card β * Module.finrank F (coordinateOrthogonal (arraySupport (S.map swapFirstTwo.toLinearMap))) := by
  rw [secondRowAnnihilator, swapFirstTwo.symm.finrank_map_eq, rowSubspace_finrank]

def annihilatorQuotientImage (S : Submodule F (α × (β × γ) → F)) :
    Submodule F ((α × (β × γ) → F) ⧸ secondRowAnnihilator S) :=
  (rowSubspace (α := α) (coordinateOrthogonal (arraySupport S))).map
    (secondRowAnnihilator S).mkQ

def annihilatorRowMap (S : Submodule F (α × (β × γ) → F)) (a : α) :
    coordinateOrthogonal (arraySupport S) →ₗ[F] annihilatorQuotientImage S :=
  (((secondRowAnnihilator S).mkQ.comp (arrayInsert a)).comp
    (coordinateOrthogonal (arraySupport S)).subtype).codRestrict _ (by
      intro v
      exact ⟨arrayInsert a v.val, arrayInsert_mem_rowSubspace _ a v.property, rfl⟩)

theorem annihilatorQuotientImage_rank_bound (S : Submodule F (α × (β × γ) → F)) :
    Module.finrank F (annihilatorQuotientImage S) + Module.finrank F S ≤
      Fintype.card β * Module.finrank F (arraySupport (S.map swapFirstTwo.toLinearMap)) := by
  have hd := finrank_quotient_image_add
    (rowSubspace (α := α) (coordinateOrthogonal (arraySupport S))) (secondRowAnnihilator S)
  have hle := Submodule.finrank_mono
    (sup_le (rowSubspace_orthogonal_support S) (secondRowAnnihilator_le S))
  have hS := finrank_coordinateOrthogonal S
  have hQ := finrank_coordinateOrthogonal (arraySupport (S.map swapFirstTwo.toLinearMap))
  rw [Fintype.card_prod, Fintype.card_prod] at hS
  rw [Fintype.card_prod] at hQ
  rw [secondRowAnnihilator_finrank] at hd
  change Module.finrank F (annihilatorQuotientImage S) + _ = _ at hd
  nlinarith

end Lemmata.Centroid.Linear
