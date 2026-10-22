module

public import Lemmata.Centroid.Proof.General.CentroidBounds
public import Lemmata.Centroid.Proof.Tensor.SupportTensor

@[expose] public section

open scoped BigOperators Matrix
open Classical

noncomputable section

namespace Lemmata.Centroid.Tensor

variable {F : Type*} [Field F] {V : Fin 3 → Type*} [∀ i, Fintype (V i)]

theorem fin3_three_cover (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (l : Fin 3) : l = i ∨ l = j ∨ l = k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp_all

local instance : DecidableEq (Fin 3) := Classical.decEq _

def pairSlice (j k : Fin 3) (x : ∀ i, V i) :
    Tensor F (Fin 3) V →ₗ[F] (V j × V k → F) where
  toFun T p := T (Function.update (Function.update x j p.1) k p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [∀ i, Fintype (V i)] in
theorem pairSlice_injective_on_constant (S : Submodule F (Tensor F (Fin 3) V))
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (x : ∀ i, V i)
    (hconst : ∀ T ∈ S, ∀ y a, T (Function.update y i a) = T y) :
    Function.Injective ((pairSlice j k x).domRestrict S) := by
  intro T U h
  apply Subtype.ext
  funext y
  let z := Function.update (Function.update x j (y j)) k (y k)
  have hzy : Function.update z i (y i) = y := by
    funext l
    rcases fin3_three_cover i j k hij hik hjk l with rfl | rfl | rfl
    · simp [z]
    · simp [z, Ne.symm hij, hjk]
    · simp [z, Ne.symm hik]
  have he := congrFun h (y j, y k)
  change T.val z = U.val z at he
  calc
    T.val y = T.val z := by rw [← hzy]; exact hconst T.val T.property z (y i)
    _ = U.val z := he
    _ = U.val y := by rw [← hzy]; exact (hconst U.val U.property z (y i)).symm

theorem constant_leg_support_bound (S : Submodule F (Tensor F (Fin 3) V))
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (P : Submodule F (V j → F)) (Q : Submodule F (V k → F))
    (hconst : ∀ T ∈ S, ∀ y a, T (Function.update y i a) = T y)
    (hP : ∀ T ∈ S, ∀ x, oneSlice j x T ∈ P)
    (hQ : ∀ T ∈ S, ∀ x, oneSlice k x T ∈ Q) :
    Module.finrank F S ≤ Module.finrank F P * Module.finrank F Q := by
  cases isEmpty_or_nonempty (∀ i, V i) with
  | inl h =>
    let : IsEmpty (∀ i, V i) := h
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le _
  | inr h =>
    obtain ⟨x⟩ := h
    have hbound := Linear.array_support_bound (S.map (pairSlice j k x)) P Q (by
      rintro _ ⟨T, hT, rfl⟩ b
      have hp := hP T hT (Function.update x k b)
      convert hp using 1
      funext a
      exact congrArg T (Function.update_comm hjk a b x)) (by
      rintro _ ⟨T, hT, rfl⟩ a
      exact hQ T hT (Function.update x j a))
    have hdim := LinearMap.finrank_range_of_inj
      (pairSlice_injective_on_constant S i j k hij hik hjk x hconst)
    have hr : ((pairSlice j k x).domRestrict S).range = S.map (pairSlice j k x) := by
      ext f
      constructor
      · rintro ⟨T, rfl⟩; exact ⟨T.val, T.property, rfl⟩
      · rintro ⟨T, hT, rfl⟩; exact ⟨⟨T, hT⟩, rfl⟩
    rw [hr] at hdim
    rwa [hdim] at hbound

theorem contraction_legAction_other (T : Tensor F (Fin 3) V) {i j : Fin 3}
    (hij : i ≠ j) (A : Matrix (V j) (V j) F) (f : V i → F) :
    contraction (legAction T j A) i f = legAction (contraction T i f) j A := by
  funext x
  simp only [contraction_apply, legAction_apply, Function.update_of_ne (Ne.symm hij),
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [Function.update_comm hij]
  ring

theorem contraction_constant_leg (T : Tensor F (Fin 3) V) (i : Fin 3) (f : V i → F)
    (x : ∀ i, V i) (a : V i) :
    contraction T i f (Function.update x i a) = contraction T i f x := by
  simp only [contraction_apply, Function.update_idem]

theorem oneSlice_legAction (T : Tensor F (Fin 3) V) (i : Fin 3)
    (A : Matrix (V i) (V i) F) (x : ∀ i, V i) :
    A *ᵥ oneSlice i x T = oneSlice i x (legAction T i A) := by
  funext a
  simp only [Matrix.mulVec, dotProduct, oneSlice_apply, legAction_apply,
    Function.update_self, Function.update_idem]

theorem annihilator_contraction_commonKernel {T : Tensor F (Fin 3) V}
    {J : Submodule F (∀ i, Matrix (V i) (V i) F)} (hJ : J ≤ centroid T)
    {i j : Fin 3} (hij : i ≠ j) {f : V i → F}
    (hf : f ∈ annihilatorAt (imageAt T J i) i) (x : ∀ i, V i) :
    oneSlice j x (contraction T i f) ∈ commonKernel J j := by
  rw [mem_commonKernel]
  intro A hA
  rw [oneSlice_legAction, ← contraction_legAction_other T hij]
  have hmem : legAction T j (A j) ∈ imageAt T J i := by
    rw [imageAt_eq hJ i j]
    exact ⟨A, hA, rfl⟩
  rw [(mem_annihilatorAt _ _ _).mp hf _ hmem, map_zero]

theorem centroid_image_oneSupport_codim_bound {T : Tensor F (Fin 3) V} (hT : Concise T)
    {J : Submodule F (∀ i, Matrix (V i) (V i) F)} (hJ : J ≤ centroid T)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Fintype.card (V i) - Module.finrank F (oneSupportAt (imageAt T J i) i) ≤
      Module.finrank F (commonKernel J j) * Module.finrank F (commonKernel J k) := by
  let P := annihilatorAt (imageAt T J i) i
  let S := P.map (contraction T i)
  have hbound := constant_leg_support_bound S i j k hij hik hjk
    (commonKernel J j) (commonKernel J k) (by
      rintro _ ⟨f, _, rfl⟩ x a
      exact contraction_constant_leg T i f x a) (by
      rintro _ ⟨f, hf, rfl⟩ x
      exact annihilator_contraction_commonKernel hJ hij hf x) (by
      rintro _ ⟨f, hf, rfl⟩ x
      exact annihilator_contraction_commonKernel hJ hik hf x)
  have hdim : Module.finrank F S = Module.finrank F P :=
    (Submodule.equivMapOfInjective (contraction T i) (hT i) P).finrank_eq.symm
  have hsum := finrank_oneSupportAt_add_annihilatorAt (imageAt T J i) i
  change Module.finrank F (oneSupportAt (imageAt T J i) i) + Module.finrank F P =
    Fintype.card (V i) at hsum
  omega

end Lemmata.Centroid.Tensor
