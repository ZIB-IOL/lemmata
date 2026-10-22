module

public import Lemmata.Centroid.Proof.Tensor.Support
public import Lemmata.Centroid.Proof.Tensor.ProductLinear

@[expose] public section

open scoped TensorProduct
open Classical

noncomputable section

namespace Lemmata.Centroid.Linear

variable {F α β : Type*} [Field F] [Fintype α] [Fintype β]

omit [Fintype α] in
theorem functionProduct_rightCoefficient (t : (α → F) ⊗[F] (β → F)) (b : β) (a : α) :
    rightCoefficients (Pi.basisFun F β) t b a =
      Lemmata.Centroid.Tensor.functionProductEquiv t (a, b) := by
  induction t using TensorProduct.inductionOn with
  | tmul u v =>
    simp [rightCoefficients_tmul, Lemmata.Centroid.Tensor.functionProductEquiv_tmul, mul_comm]
  | add t s ht hs => simp [ht, hs]

theorem functionProduct_comm (t : (α → F) ⊗[F] (β → F)) (p : β × α) :
    Lemmata.Centroid.Tensor.functionProductEquiv (TensorProduct.comm F _ _ t) p =
      Lemmata.Centroid.Tensor.functionProductEquiv t (p.2, p.1) := by
  induction t using TensorProduct.inductionOn with
  | tmul u v => simp [Lemmata.Centroid.Tensor.functionProductEquiv_tmul, mul_comm]
  | add t s ht hs => simp [ht, hs]

omit [Fintype α] in
theorem mem_functionProduct_left (P : Submodule F (α → F))
    (t : (α → F) ⊗[F] (β → F))
    (h : ∀ b, (fun a => Lemmata.Centroid.Tensor.functionProductEquiv t (a, b)) ∈ P) :
    t ∈ tensorSubspace P ⊤ := by
  apply (mem_tensorSubspace_top_right (Pi.basisFun F β) P t).2
  intro b
  have heq : (rightCoefficients (Pi.basisFun F β) t) b =
      fun a => Lemmata.Centroid.Tensor.functionProductEquiv t (a, b) := by
    funext a
    exact functionProduct_rightCoefficient t b a
  rw [heq]
  exact h b

theorem mem_functionProduct (P : Submodule F (α → F)) (Q : Submodule F (β → F))
    (t : (α → F) ⊗[F] (β → F))
    (hP : ∀ b, (fun a => Lemmata.Centroid.Tensor.functionProductEquiv t (a, b)) ∈ P)
    (hQ : ∀ a, (fun b => Lemmata.Centroid.Tensor.functionProductEquiv t (a, b)) ∈ Q) :
    t ∈ tensorSubspace P Q := by
  rw [tensorSubspace_eq_inf_top]
  refine ⟨mem_functionProduct_left P t hP, ?_⟩
  have hc : TensorProduct.comm F _ _ t ∈ tensorSubspace Q ⊤ := by
    apply mem_functionProduct_left
    intro a
    simpa only [functionProduct_comm] using hQ a
  have hm := Submodule.mem_map_of_mem (f := (TensorProduct.comm F _ _).toLinearMap) hc
  rw [tensorSubspace_comm] at hm
  simpa using hm

theorem array_support_bound (S : Submodule F (α × β → F))
    (P : Submodule F (α → F)) (Q : Submodule F (β → F))
    (hP : ∀ f ∈ S, ∀ b, (fun a => f (a, b)) ∈ P)
    (hQ : ∀ f ∈ S, ∀ a, (fun b => f (a, b)) ∈ Q) :
    Module.finrank F S ≤ Module.finrank F P * Module.finrank F Q := by
  let e := Lemmata.Centroid.Tensor.functionProductEquiv (F := F) (α := α) (β := β)
  let f : S →ₗ[F] tensorSubspace P Q :=
    ((e.symm.toLinearMap).comp S.subtype).codRestrict _ (by
      intro s
      change e.symm s.val ∈ tensorSubspace P Q
      apply mem_functionProduct P Q
      · intro b
        change (fun a => e (e.symm s.val) (a, b)) ∈ P
        rw [e.apply_symm_apply]
        exact hP s.val s.property b
      · intro a
        change (fun b => e (e.symm s.val) (a, b)) ∈ Q
        rw [e.apply_symm_apply]
        exact hQ s.val s.property a)
  have hf : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    apply e.symm.injective
    exact congrArg Subtype.val h
  have h := LinearMap.finrank_le_finrank_of_injective hf
  rwa [finrank_tensorSubspace] at h

end Lemmata.Centroid.Linear

namespace Lemmata.Centroid.Tensor

variable {F ι : Type*} [Field F] [Fintype ι]
variable {V : ι → Type*} [∀ i, Fintype (V i)]

def supportLift (i : ι) : Tensor F ι V →ₗ[F] (V i × (∀ j, V j) → F) where
  toFun T p := T (Function.update p.2 i p.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype ι] [∀ i, Fintype (V i)] in
@[simp] theorem supportLift_apply (i : ι) (T : Tensor F ι V) (p : V i × (∀ j, V j)) :
    supportLift i T p = T (Function.update p.2 i p.1) := rfl

omit [Fintype ι] [∀ i, Fintype (V i)] in
theorem supportLift_injective (i : ι) : Function.Injective (supportLift (F := F) (V := V) i) := by
  intro T U h
  funext x
  have hx := congrFun h (x i, x)
  simpa only [supportLift_apply, Function.update_eq_self] using hx

theorem finrank_le_oneSupportAt_mul_oppositeSupportAt
    (S : Submodule F (Tensor F ι V)) (i : ι) :
    Module.finrank F S ≤ Module.finrank F (oneSupportAt S i) *
      Module.finrank F (oppositeSupportAt S i) := by
  have h := Linear.array_support_bound (S.map (supportLift i)) (oneSupportAt S i)
    (oppositeSupportAt S i) (by
      rintro _ ⟨T, hT, rfl⟩ x
      exact Submodule.mem_iSup_of_mem x ⟨T, hT, rfl⟩) (by
      rintro _ ⟨T, hT, rfl⟩ a
      exact Submodule.mem_iSup_of_mem a ⟨T, hT, rfl⟩)
  rw [← (Submodule.equivMapOfInjective (supportLift i) (supportLift_injective i) S).finrank_eq] at h
  exact h

end Lemmata.Centroid.Tensor
