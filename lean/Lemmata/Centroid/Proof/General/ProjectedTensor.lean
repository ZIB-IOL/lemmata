module

public import Lemmata.Centroid.Proof.General.BalancedProjection
public import Lemmata.Centroid.Proof.Tensor.Maps

@[expose] public section

open scoped BigOperators Matrix
open Classical

noncomputable section

namespace Lemmata.Centroid.Tensor.BalancedAlgebra

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A]
variable {V : Fin 3 → Type*} [∀ i, Fintype (V i)]
variable (T : Tensor F (Fin 3) V) (hT : Concise T)
variable (f : A →ₐ[F] centroidAlgebra T hT)

def projectedImage (I : Ideal A) (P : ∀ i, Matrix (V i) (V i) F) (i : Fin 3) :=
  imageAt T (leftFamily T hT f I P) i

def leftMatrixAction (I : Ideal A) (P : ∀ i, Matrix (V i) (V i) F) (i : Fin 3) :
    I →ₗ[F] Matrix (V i) (V i) F :=
  (mulLeftLinearMap (V i) F (P i)).comp
    (((centroidProjectionAlgHom T hT i).comp f).toLinearMap.comp (I.subtype.restrictScalars F))

theorem toLin_leftMatrixAction (I : Ideal A) (P : ∀ i, Matrix (V i) (V i) F) (i : Fin 3) :
    let := legModule T hT f i
    let := legScalarTower T hT f i
    Matrix.toLinAlgEquiv'.toLinearMap.comp (leftMatrixAction T hT f I P i) =
      General.leftProjectedAction I (P i).mulVecLin := by
  let := legModule T hT f i
  let := legScalarTower T hT f i
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro u
  change (P i * (f c.1).val i) *ᵥ u = P i *ᵥ ((f c.1).val i *ᵥ u)
  exact (Matrix.mulVec_mulVec _ _ _).symm

theorem leftMatrixAction_ker (hf : Function.Injective f) (I : Ideal A)
    (P : ∀ i, Matrix (V i) (V i) F) (i : Fin 3)
    (hP : (P i).mulVecLin.ker = commonKernel (idealSpace T hT f I) i) :
    (leftMatrixAction T hT f I P i).ker = General.annihilatorSubspace (F := F) I := by
  let := legModule T hT f i
  let := legScalarTower T hT f i
  let := legFaithful T hT f hf i
  have hk : (P i).mulVecLin.ker = (General.idealKernel (M := V i → F) I).restrictScalars F := by
    rw [leg_idealKernel]
    exact hP
  calc
    _ = (Matrix.toLinAlgEquiv'.toLinearMap.comp (leftMatrixAction T hT f I P i)).ker :=
      (LinearMap.ker_comp_of_ker_eq_bot _
        (LinearMap.ker_eq_bot.mpr Matrix.toLinAlgEquiv'.injective)).symm
    _ = (General.leftProjectedAction I (P i).mulVecLin).ker := by rw [toLin_leftMatrixAction]
    _ = _ := General.leftProjectedAction_ker I (P i).mulVecLin hk

theorem projectedImage_finrank (hf : Function.Injective f) (I : Ideal A)
    (P : ∀ i, Matrix (V i) (V i) F) (i : Fin 3)
    (hP : (P i).mulVecLin.ker = commonKernel (idealSpace T hT f I) i) :
    Module.finrank F (projectedImage T hT f I P i) =
      Module.finrank F (General.AnnihilatorQuotient F A I) := by
  let g := (legAction T i).comp (leftMatrixAction T hT f I P i)
  have hg : g.range = projectedImage T hT f I P i := by
    ext U
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨leftFamilyMap P (f c.1).val, ⟨(f c.1).val, ⟨c.1, c.2, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨_, ⟨c, hc, rfl⟩, rfl⟩, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
  have hk : g.ker = General.annihilatorSubspace (F := F) I := by
    rw [LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr (legAction_injective hT i))]
    exact leftMatrixAction_ker T hT f hf I P i hP
  have he := g.quotKerEquivRange
  rw [hk, hg] at he
  exact he.finrank_eq.symm

theorem projected_action_other (P : ∀ i, Matrix (V i) (V i) F) {i j : Fin 3}
    (hij : i ≠ j) (c : A) :
    legAction T i (P i * (f c).val i) =
      legAction (legAction T i (P i)) j ((f c).val j) := by
  rw [legAction_mul, (f c).property i j]
  exact legAction_comm T hij _ _

theorem projectedImage_eq_other (I : Ideal A) (P : ∀ i, Matrix (V i) (V i) F)
    {i j : Fin 3} (hij : i ≠ j) :
    projectedImage T hT f I P i = imageAt (legAction T i (P i)) (idealSpace T hT f I) j := by
  ext U
  constructor
  · rintro ⟨_, ⟨_, ⟨c, hc, rfl⟩, rfl⟩, rfl⟩
    exact ⟨(f c).val, ⟨c, hc, rfl⟩, (projected_action_other T hT f P hij c).symm⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨leftFamilyMap P (f c).val, ⟨(f c).val, ⟨c, hc, rfl⟩, rfl⟩,
      projected_action_other T hT f P hij c⟩

theorem projected_annihilator_action_zero (hf : Function.Injective f) (I : Ideal A)
    (P : ∀ i, Matrix (V i) (V i) F) {i j : Fin 3} (hij : i ≠ j)
    (hP : (P i).mulVecLin.ker = commonKernel (idealSpace T hT f I) i)
    (c : A) (hc : c ∈ General.annihilatorInIdeal I) :
    legAction (legAction T i (P i)) j ((f c).val j) = 0 := by
  rw [← projected_action_other T hT f P hij c]
  have hz : leftMatrixAction T hT f I P i ⟨c, hc.1⟩ = 0 := by
    change (⟨c, hc.1⟩ : I) ∈ (leftMatrixAction T hT f I P i).ker
    rw [leftMatrixAction_ker T hT f hf I P i hP]
    exact hc
  change legAction T i (leftMatrixAction T hT f I P i ⟨c, hc.1⟩) = 0
  rw [hz, map_zero]

theorem projected_tensor_oneSupport (hf : Function.Injective f) (I : Ideal A)
    (P : ∀ i, Matrix (V i) (V i) F) {i j : Fin 3} (hij : i ≠ j)
    (hP : (P i).mulVecLin.ker = commonKernel (idealSpace T hT f I) i) :
    oneSupportAt (Submodule.span F {legAction T i (P i)}) j ≤
      commonKernel (idealSpace T hT f (General.annihilatorInIdeal I)) j := by
  apply oneSupportAt_le_commonKernel
  rintro _ ⟨c, hc, rfl⟩ U hU
  have hspan : Submodule.span F {legAction T i (P i)} ≤
      (applyLeg j ((f c).val j)).ker := by
    apply Submodule.span_le.mpr
    rintro W (rfl : W = legAction T i (P i))
    exact projected_annihilator_action_zero T hT f hf I P hij hP c hc
  exact hspan hU

theorem projectedImage_eq_rightFamily (hf : Function.Injective f) (I : Ideal A)
    (P Q : ∀ i, Matrix (V i) (V i) F) {i j : Fin 3} (hij : i ≠ j)
    (hP : (P i).mulVecLin.ker = commonKernel (idealSpace T hT f I) i)
    (hQ : Q j * Q j = Q j)
    (hrange : (Q j).mulVecLin.range =
      commonKernel (idealSpace T hT f (General.annihilatorInIdeal I)) j) :
    projectedImage T hT f I P i = imageAt (legAction T i (P i)) (rightFamily T hT f I Q) j := by
  have hfix : legAction (legAction T i (P i)) j (Q j) = legAction T i (P i) := by
    apply legAction_eq_self_of_oneSupport hQ
      (S := Submodule.span F {legAction T i (P i)})
    · rw [hrange]
      exact projected_tensor_oneSupport T hT f hf I P hij hP
    · exact Submodule.subset_span (Set.mem_singleton _)
  rw [projectedImage_eq_other T hT f I P hij]
  ext U
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨rightFamilyMap Q (f c).val, ⟨(f c).val, ⟨c, hc, rfl⟩, rfl⟩, ?_⟩
    change legAction (legAction T i (P i)) j ((f c).val j * Q j) = _
    rw [legAction_mul, hfix]
    rfl
  · rintro ⟨_, ⟨_, ⟨c, hc, rfl⟩, rfl⟩, rfl⟩
    refine ⟨(f c).val, ⟨c, hc, rfl⟩, ?_⟩
    change legAction (legAction T i (P i)) j ((f c).val j) =
      legAction (legAction T i (P i)) j ((f c).val j * Q j)
    rw [legAction_mul, hfix]

omit T hT f in
private theorem fin3_prod_eq (d : Fin 3 → ℕ) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∏ l : Fin 3, d l) = d i * d j * d k := by
  rw [Fin.prod_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first | exact (hij rfl).elim | exact (hik rfl).elim | exact (hjk rfl).elim | ac_rfl

theorem projected_image_product_bound (hf : Function.Injective f) (I : Ideal A)
    (P Q : ∀ i, Matrix (V i) (V i) F) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hP : (P i).mulVecLin.ker = commonKernel (idealSpace T hT f I) i)
    (hQj : Q j * Q j = Q j) (hQk : Q k * Q k = Q k)
    (hrj : (Q j).mulVecLin.range =
      commonKernel (idealSpace T hT f (General.annihilatorInIdeal I)) j)
    (hrk : (Q k).mulVecLin.range =
      commonKernel (idealSpace T hT f (General.annihilatorInIdeal I)) k) :
    Module.finrank F (General.AnnihilatorQuotient F A I) ^ 2 ≤
      Module.finrank F (rowSpace (leftFamily T hT f I P) i) *
        (Module.finrank F (commonKernel (idealSpace T hT f (General.annihilatorInIdeal I)) j) -
          Module.finrank F (commonKernel (idealSpace T hT f I) j)) *
        (Module.finrank F (commonKernel (idealSpace T hT f (General.annihilatorInIdeal I)) k) -
          Module.finrank F (commonKernel (idealSpace T hT f I) k)) := by
  let S := projectedImage T hT f I P i
  have hi : Module.finrank F (oppositeSupportAt S i) =
      Module.finrank F (rowSpace (leftFamily T hT f I P) i) := by
    rw [show S = imageAt T (leftFamily T hT f I P) i from rfl, oppositeSupportAt_imageAt]
    exact (Submodule.equivMapOfInjective (contraction T i) (hT i) _).finrank_eq.symm
  have hj : Module.finrank F (oppositeSupportAt S j) ≤
      Module.finrank F (commonKernel (idealSpace T hT f (General.annihilatorInIdeal I)) j) -
        Module.finrank F (commonKernel (idealSpace T hT f I) j) := by
    change Module.finrank F (oppositeSupportAt (projectedImage T hT f I P i) j) ≤ _
    rw [projectedImage_eq_rightFamily T hT f hf I P Q hij hP hQj hrj,
      oppositeSupportAt_imageAt]
    exact (Submodule.finrank_map_le _ _).trans (rightFamily_row_finrank_le T hT f I Q j hQj hrj)
  have hk : Module.finrank F (oppositeSupportAt S k) ≤
      Module.finrank F (commonKernel (idealSpace T hT f (General.annihilatorInIdeal I)) k) -
        Module.finrank F (commonKernel (idealSpace T hT f I) k) := by
    change Module.finrank F (oppositeSupportAt (projectedImage T hT f I P i) k) ≤ _
    rw [projectedImage_eq_rightFamily T hT f hf I P Q hik hP hQk hrk,
      oppositeSupportAt_imageAt]
    exact (Submodule.finrank_map_le _ _).trans (rightFamily_row_finrank_le T hT f I Q k hQk hrk)
  have hprod : (∏ l : Fin 3, Module.finrank F (oppositeSupportAt S l)) =
      Module.finrank F (oppositeSupportAt S i) * Module.finrank F (oppositeSupportAt S j) *
        Module.finrank F (oppositeSupportAt S k) := by
    exact fin3_prod_eq _ i j k hij hik hjk
  calc
    _ = Module.finrank F S ^ 2 := by rw [projectedImage_finrank T hT f hf I P i hP]
    _ ≤ ∏ l : Fin 3, Module.finrank F (oppositeSupportAt S l) := support_product_bound S
    _ = _ := hprod
    _ ≤ _ := by rw [hi]; exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hj) hk

omit T hT f in
theorem exists_matrix_projection_kernel {α : Type*} [Fintype α] (K : Submodule F (α → F)) :
    ∃ P : Matrix α α F, P.mulVecLin.ker = K := by
  obtain ⟨W, hW⟩ := K.exists_isCompl
  let p := W.projection K hW.symm
  refine ⟨LinearMap.toMatrixAlgEquiv' p, ?_⟩
  change (Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv' p)).ker = K
  rw [Matrix.toLinAlgEquiv'_toMatrixAlgEquiv', Submodule.ker_projection]

omit T hT f in
theorem exists_matrix_projection_range {α : Type*} [Fintype α] (H : Submodule F (α → F)) :
    ∃ Q : Matrix α α F, Q * Q = Q ∧ Q.mulVecLin.range = H := by
  obtain ⟨W, hW⟩ := H.exists_isCompl
  let p := H.projection W hW
  refine ⟨LinearMap.toMatrixAlgEquiv' p, ?_, ?_⟩
  · rw [← map_mul]
    exact congrArg LinearMap.toMatrixAlgEquiv' (Submodule.isIdempotentElem_projection hW)
  · change (Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv' p)).range = H
    rw [Matrix.toLinAlgEquiv'_toMatrixAlgEquiv', Submodule.range_projection]

theorem projected_support_product_bound (hf : Function.Injective f) (I : Ideal A)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    let := legModule T hT f i
    let := legScalarTower T hT f i
    let := legFaithful T hT f hf i
    Module.finrank F (General.AnnihilatorQuotient F A I) ^ 2 ≤
      (Module.finrank F (General.ProjectedModule A (V i → F) I) -
          Module.finrank F (General.projectedKernel (M := V i → F) I)) *
        (Module.finrank F (commonKernel (idealSpace T hT f (General.annihilatorInIdeal I)) j) -
          Module.finrank F (commonKernel (idealSpace T hT f I) j)) *
        (Module.finrank F (commonKernel (idealSpace T hT f (General.annihilatorInIdeal I)) k) -
          Module.finrank F (commonKernel (idealSpace T hT f I) k)) := by
  let := legModule T hT f i
  let := legScalarTower T hT f i
  let := legFaithful T hT f hf i
  choose P hP using fun l => exists_matrix_projection_kernel (commonKernel (idealSpace T hT f I) l)
  choose Q hQ hr using fun l => exists_matrix_projection_range
    (commonKernel (idealSpace T hT f (General.annihilatorInIdeal I)) l)
  have h := projected_image_product_bound T hT f hf I P Q i j k hij hik hjk
    (hP i) (hQ j) (hQ k) (hr j) (hr k)
  rwa [leftFamily_row_finrank T hT f hf I P i (hP i)] at h

theorem projected_support_Q_bound [FiniteDimensional F A] (hf : Function.Injective f)
    (I : Ideal A) (hI : IsNilpotent I) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (Q : ℕ)
    (hQ : Fintype.card (V i) - Module.finrank F (commonKernel (idealSpace T hT f I) i) ≤ Q)
    (hx : Q - 1 < Module.finrank F I - Module.finrank F (General.annihilatorInIdeal I)) :
    (Module.finrank F I - Module.finrank F (General.annihilatorInIdeal I)) ^ 2 ≤
      (Q - 2) *
        (Module.finrank F (commonKernel (idealSpace T hT f (General.annihilatorInIdeal I)) j) -
          Module.finrank F (commonKernel (idealSpace T hT f I) j)) *
        (Module.finrank F (commonKernel (idealSpace T hT f (General.annihilatorInIdeal I)) k) -
          Module.finrank F (commonKernel (idealSpace T hT f I) k)) := by
  let := legModule T hT f i
  let := legScalarTower T hT f i
  let := legFaithful T hT f hf i
  have hQ' : Module.finrank F (General.ProjectedModule A (V i → F) I) ≤ Q := by
    rwa [General.projectedModule_finrank, Module.finrank_pi, leg_kernel_finrank]
  have hx' : Q - 1 < Module.finrank F (General.AnnihilatorQuotient F A I) := by
    rwa [General.annihilatorQuotient_finrank]
  have hh := General.projectedKernel_finrank_two_le (F := F) (M := V i → F) I hI Q hQ' hx'
  have hsub : Module.finrank F (General.ProjectedModule A (V i → F) I) -
      Module.finrank F (General.projectedKernel (M := V i → F) I) ≤ Q - 2 := by omega
  have h := projected_support_product_bound T hT f hf I i j k hij hik hjk
  rw [General.annihilatorQuotient_finrank] at h
  exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hsub))

end Lemmata.Centroid.Tensor.BalancedAlgebra
