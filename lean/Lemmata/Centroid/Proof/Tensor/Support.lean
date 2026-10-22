module

public import Lemmata.Centroid.Proof.Centroid
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

@[expose] public section

open scoped BigOperators Matrix
open Classical

noncomputable section

namespace Lemmata.Centroid.Linear

variable {F α : Type*} [Field F] [Fintype α]

def coordinatePairing (u : α → F) : (α → F) →ₗ[F] F where
  toFun v := ∑ a, u a * v a
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' t v := by simp [Finset.mul_sum, mul_left_comm]

def coordinateDual : (α → F) →ₗ[F] Module.Dual F (α → F) where
  toFun := coordinatePairing
  map_add' u v := by ext w; simp [coordinatePairing, add_mul, Finset.sum_add_distrib]
  map_smul' t u := by ext w; simp [coordinatePairing, Finset.mul_sum, mul_assoc]

theorem coordinateDual_injective : Function.Injective (coordinateDual (F := F) (α := α)) := by
  intro u v h
  funext a
  have ha := congrArg (fun f : Module.Dual F (α → F) =>
    f (fun b => if b = a then 1 else 0)) h
  change (∑ b, u b * if b = a then 1 else 0) =
    ∑ b, v b * if b = a then 1 else 0 at ha
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using ha

def coordinateDualEquiv : (α → F) ≃ₗ[F] Module.Dual F (α → F) :=
  LinearEquiv.ofBijective coordinateDual ⟨coordinateDual_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Subspace.dual_finrank_eq])).mp coordinateDual_injective⟩

def coordinateOrthogonal (P : Submodule F (α → F)) : Submodule F (α → F) :=
  P.dualAnnihilator.comap coordinateDual

@[simp] theorem mem_coordinateOrthogonal (P : Submodule F (α → F)) (u : α → F) :
    u ∈ coordinateOrthogonal P ↔ ∀ v ∈ P, ∑ a, u a * v a = 0 :=
  Submodule.mem_dualAnnihilator _

theorem finrank_coordinateOrthogonal (P : Submodule F (α → F)) :
    Module.finrank F (coordinateOrthogonal P) + Module.finrank F P = Fintype.card α := by
  have hmap : (coordinateOrthogonal P).map coordinateDual = P.dualAnnihilator :=
    Submodule.map_comap_eq_of_surjective coordinateDualEquiv.surjective _
  have hdim := coordinateDualEquiv.finrank_map_eq (coordinateOrthogonal P)
  change Module.finrank F ((coordinateOrthogonal P).map coordinateDual) = _ at hdim
  rw [hmap] at hdim
  have hsum := Subspace.finrank_add_finrank_dualAnnihilator_eq P
  rw [Module.finrank_fintype_fun_eq_card] at hsum
  omega

end Lemmata.Centroid.Linear

namespace Lemmata.Centroid.Tensor

variable {F ι : Type*} [Field F] {V : ι → Type*} [∀ i, Fintype (V i)]

def oneSlice (i : ι) (x : ∀ j, V j) : Tensor F ι V →ₗ[F] (V i → F) where
  toFun T a := T (Function.update x i a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def oppositeSlice (i : ι) (a : V i) : Tensor F ι V →ₗ[F] Tensor F ι V where
  toFun T x := T (Function.update x i a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def oneSupportAt (S : Submodule F (Tensor F ι V)) (i : ι) : Submodule F (V i → F) :=
  ⨆ x : ∀ j, V j, S.map (oneSlice i x)

def oppositeSupportAt (S : Submodule F (Tensor F ι V)) (i : ι) :
    Submodule F (Tensor F ι V) :=
  ⨆ a : V i, S.map (oppositeSlice i a)

def annihilatorAt (S : Submodule F (Tensor F ι V)) (i : ι) : Submodule F (V i → F) :=
  ⨅ T : S, (contraction T.val i).ker

omit [∀ i, Fintype (V i)] in
@[simp] theorem oneSlice_apply (i : ι) (x : ∀ j, V j) (T : Tensor F ι V) (a : V i) :
    oneSlice i x T a = T (Function.update x i a) := rfl

@[simp] theorem mem_annihilatorAt (S : Submodule F (Tensor F ι V)) (i : ι) (u : V i → F) :
    u ∈ annihilatorAt S i ↔ ∀ T ∈ S, contraction T i u = 0 := by
  simp only [annihilatorAt, Submodule.mem_iInf, LinearMap.mem_ker, Subtype.forall]

theorem annihilatorAt_eq_orthogonal (S : Submodule F (Tensor F ι V)) (i : ι) :
    annihilatorAt S i = Linear.coordinateOrthogonal (oneSupportAt S i) := by
  ext u
  rw [mem_annihilatorAt, Linear.mem_coordinateOrthogonal]
  constructor
  · intro hu
    have hle : oneSupportAt S i ≤ (Linear.coordinatePairing u).ker := by
      apply iSup_le
      intro x
      rintro _ ⟨T, hT, rfl⟩
      exact congrFun (hu T hT) x
    exact fun v hv => hle hv
  · intro hu T hT
    funext x
    exact hu (oneSlice i x T) (Submodule.mem_iSup_of_mem x ⟨T, hT, rfl⟩)

theorem finrank_oneSupportAt_add_annihilatorAt (S : Submodule F (Tensor F ι V)) (i : ι) :
    Module.finrank F (oneSupportAt S i) + Module.finrank F (annihilatorAt S i) =
      Fintype.card (V i) := by
  rw [annihilatorAt_eq_orthogonal, Nat.add_comm]
  exact Linear.finrank_coordinateOrthogonal _

def rowSpace (J : Submodule F (∀ i, Matrix (V i) (V i) F)) (i : ι) :
    Submodule F (V i → F) :=
  Submodule.span F {r | ∃ A ∈ J, ∃ a : V i, r = (A i).row a}

def commonKernel (J : Submodule F (∀ i, Matrix (V i) (V i) F)) (i : ι) :
    Submodule F (V i → F) :=
  ⨅ A : J, (A.val i).mulVecLin.ker

@[simp] theorem mem_commonKernel
    (J : Submodule F (∀ i, Matrix (V i) (V i) F)) (i : ι) (u : V i → F) :
    u ∈ commonKernel J i ↔ ∀ A ∈ J, (A i) *ᵥ u = 0 := by
  simp only [commonKernel, Submodule.mem_iInf, LinearMap.mem_ker,
    Matrix.mulVecLin_apply, Subtype.forall]

theorem commonKernel_eq_orthogonal (J : Submodule F (∀ i, Matrix (V i) (V i) F)) (i : ι) :
    commonKernel J i = Linear.coordinateOrthogonal (rowSpace J i) := by
  ext u
  simp only [commonKernel, Submodule.mem_iInf, LinearMap.mem_ker, Matrix.mulVecLin_apply,
    Subtype.forall, Linear.mem_coordinateOrthogonal]
  constructor
  · intro hu
    have hle : rowSpace J i ≤ (Linear.coordinatePairing u).ker := by
      apply Submodule.span_le.2
      rintro r ⟨A, hA, a, rfl⟩
      have h := congrFun (hu A hA) a
      change ∑ b, u b * A i a b = 0
      simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply, mul_comm] using h
    exact fun v hv => hle hv
  · intro hu A hA
    funext a
    have h := hu ((A i).row a) (Submodule.subset_span ⟨A, hA, a, rfl⟩)
    simpa only [Matrix.mulVec, dotProduct, Matrix.row_apply, Pi.zero_apply, mul_comm] using h

theorem finrank_rowSpace_add_commonKernel
    (J : Submodule F (∀ i, Matrix (V i) (V i) F)) (i : ι) :
    Module.finrank F (rowSpace J i) + Module.finrank F (commonKernel J i) =
      Fintype.card (V i) := by
  rw [commonKernel_eq_orthogonal, Nat.add_comm]
  exact Linear.finrank_coordinateOrthogonal _

def imageAt (T : Tensor F ι V) (J : Submodule F (∀ i, Matrix (V i) (V i) F)) (i : ι) :
    Submodule F (Tensor F ι V) :=
  J.map ((legAction T i).comp (LinearMap.proj i))

theorem imageAt_eq {T : Tensor F ι V}
    {J : Submodule F (∀ i, Matrix (V i) (V i) F)} (hJ : J ≤ centroid T) (i j : ι) :
    imageAt T J i = imageAt T J j := by
  apply le_antisymm
  · rintro _ ⟨A, hA, rfl⟩
    exact ⟨A, hA, (hJ hA j i)⟩
  · rintro _ ⟨A, hA, rfl⟩
    exact ⟨A, hA, (hJ hA i j)⟩

theorem finrank_imageAt [Fintype ι] {T : Tensor F ι V} (hT : Concise T)
    {J : Submodule F (∀ i, Matrix (V i) (V i) F)} (hJ : J ≤ centroid T) (i : ι) :
    Module.finrank F (imageAt T J i) = Module.finrank F J := by
  let f := ((legAction T i).comp (LinearMap.proj i)).domRestrict J
  have hf : Function.Injective f := by
    intro A B h
    apply Subtype.ext
    funext j
    apply legAction_injective hT j
    exact (hJ A.property j i).trans (h.trans (hJ B.property i j))
  change Module.finrank F (J.map ((legAction T i).comp (LinearMap.proj i))) = _
  rw [← LinearMap.range_domRestrict]
  exact LinearMap.finrank_range_of_inj hf

omit [∀ i, Fintype (V i)] in
@[simp] theorem oppositeSlice_apply (i : ι) (a : V i) (T : Tensor F ι V) (x : ∀ j, V j) :
    oppositeSlice i a T x = T (Function.update x i a) := rfl

theorem oppositeSlice_legAction (T : Tensor F ι V) (i : ι)
    (A : Matrix (V i) (V i) F) (a : V i) :
    oppositeSlice i a (legAction T i A) = contraction T i (A.row a) := by
  funext x
  simp only [oppositeSlice_apply, legAction_apply, contraction_apply, Function.update_self,
    Function.update_idem, Matrix.row_apply]

theorem oppositeSupportAt_imageAt (T : Tensor F ι V)
    (J : Submodule F (∀ i, Matrix (V i) (V i) F)) (i : ι) :
    oppositeSupportAt (imageAt T J i) i = (rowSpace J i).map (contraction T i) := by
  apply le_antisymm
  · apply iSup_le
    intro a
    rintro _ ⟨U, ⟨A, hA, rfl⟩, rfl⟩
    refine ⟨(A i).row a, Submodule.subset_span ⟨A, hA, a, rfl⟩, ?_⟩
    exact (oppositeSlice_legAction T i (A i) a).symm
  · apply Submodule.map_le_iff_le_comap.2
    apply Submodule.span_le.2
    rintro r ⟨A, hA, a, rfl⟩
    change contraction T i ((A i).row a) ∈ oppositeSupportAt (imageAt T J i) i
    rw [← oppositeSlice_legAction]
    exact Submodule.mem_iSup_of_mem a ⟨legAction T i (A i), ⟨A, hA, rfl⟩, rfl⟩

theorem finrank_oppositeSupportAt_imageAt [Fintype ι] {T : Tensor F ι V}
    (hT : Concise T) (J : Submodule F (∀ i, Matrix (V i) (V i) F)) (i : ι) :
    Module.finrank F (oppositeSupportAt (imageAt T J i) i) =
      Fintype.card (V i) - Module.finrank F (commonKernel J i) := by
  rw [oppositeSupportAt_imageAt,
    ← (Submodule.equivMapOfInjective (contraction T i) (hT i) _).finrank_eq]
  have h := finrank_rowSpace_add_commonKernel J i
  omega

theorem mulVec_oneSlice (T : Tensor F ι V) (i : ι)
    (A : Matrix (V i) (V i) F) (x : ∀ j, V j) :
    A *ᵥ oneSlice i x T = oneSlice i x (legAction T i A) := by
  funext a
  simp only [Matrix.mulVec, dotProduct, oneSlice_apply, legAction_apply,
    Function.update_self, Function.update_idem]

theorem oneSupportAt_le_commonKernel (S : Submodule F (Tensor F ι V))
    (J : Submodule F (∀ i, Matrix (V i) (V i) F)) (i : ι)
    (hkill : ∀ A ∈ J, ∀ T ∈ S, legAction T i (A i) = 0) :
    oneSupportAt S i ≤ commonKernel J i := by
  apply iSup_le
  intro x
  rintro _ ⟨T, hT, rfl⟩
  rw [mem_commonKernel]
  intro A hA
  rw [mulVec_oneSlice, hkill A hA T hT, map_zero]

end Lemmata.Centroid.Tensor
