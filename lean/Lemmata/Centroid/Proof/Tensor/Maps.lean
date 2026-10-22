module

public import Lemmata.Centroid.Proof.Centroid
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

open scoped BigOperators Matrix
open Classical

noncomputable section

namespace Lemmata.Centroid.Tensor

variable {F ι : Type*} [Field F] [Fintype ι]
variable {V W : ι → Type*} [∀ i, Fintype (V i)] [∀ i, Fintype (W i)]

def localMapLinear (A : ∀ i, Matrix (W i) (V i) F) :
    Tensor F ι V →ₗ[F] Tensor F ι W where
  toFun := localMap A
  map_add' := localMap_add A
  map_smul' := localMap_smul A

omit [∀ i, Fintype (W i)] in
@[simp] theorem localMapLinear_apply (A : ∀ i, Matrix (W i) (V i) F) (T : Tensor F ι V) :
    localMapLinear A T = localMap A T := rfl

theorem localMap_identity (T : Tensor F ι V) :
    localMap (fun i => (1 : Matrix (V i) (V i) F)) T = T := by
  have h := localMap_restrict (fun _ x => x) T
  have hA : (fun i (x y : V i) => if y = x then (1 : F) else 0) =
      (fun i => (1 : Matrix (V i) (V i) F)) := by
    funext i x y
    simp [Matrix.one_apply, eq_comm]
  rw [hA] at h
  exact h

def localEquiv (e : ∀ i, (V i → F) ≃ₗ[F] (W i → F)) :
    Tensor F ι V ≃ₗ[F] Tensor F ι W where
  toFun := localMap (fun i y x => LinearMap.toMatrix' (e i).toLinearMap y x)
  invFun := localMap (fun i x y => LinearMap.toMatrix' (e i).symm.toLinearMap x y)
  left_inv T := by
    rw [localMap_comp]
    have h (i : ι) : LinearMap.toMatrix' (e i).symm.toLinearMap *
        LinearMap.toMatrix' (e i).toLinearMap = 1 := by
      rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]
    change localMap (fun i y x =>
      (LinearMap.toMatrix' (e i).symm.toLinearMap * LinearMap.toMatrix' (e i).toLinearMap) y x) T = T
    simp only [h, localMap_identity]
  right_inv T := by
    rw [localMap_comp]
    have h (i : ι) : LinearMap.toMatrix' (e i).toLinearMap *
        LinearMap.toMatrix' (e i).symm.toLinearMap = 1 := by
      rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id]
    change localMap (fun i y x =>
      (LinearMap.toMatrix' (e i).toLinearMap * LinearMap.toMatrix' (e i).symm.toLinearMap) y x) T = T
    simp only [h, localMap_identity]
  map_add' := localMap_add _
  map_smul' := localMap_smul _

omit [∀ i, Fintype (V i)] in
theorem simple_update_coordinate (u : ∀ i, V i → F) (x : ∀ i, V i) (i : ι) (a : V i) :
    simple u (Function.update x i a) =
      u i a * ∏ j ∈ Finset.univ.erase i, u j (x j) := by
  rw [simple_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

omit [∀ i, Fintype (V i)] in
theorem simple_update_factor (u : ∀ i, V i → F) (i : ι) (w : V i → F) (x : ∀ i, V i) :
    simple (Function.update u i w) x =
      w (x i) * ∏ j ∈ Finset.univ.erase i, u j (x j) := by
  rw [simple_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem legAction_simple (u : ∀ i, V i → F) (i : ι) (A : Matrix (V i) (V i) F) :
    legAction (simple u) i A = simple (Function.update u i (A *ᵥ u i)) := by
  funext x
  simp only [legAction_apply, simple_update_coordinate, simple_update_factor,
    Matrix.mulVec, dotProduct]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

omit [∀ i, Fintype (V i)] in
theorem simple_basis (x : ∀ i, V i) :
    simple (fun i a => if a = x i then (1 : F) else 0) = Pi.single x 1 := by
  funext y
  simp [simple, Pi.single_apply, Fintype.prod_ite_zero, ← funext_iff, eq_comm]

theorem linearMap_ext_simple {M : Type*} [AddCommGroup M] [Module F M]
    {f g : Tensor F ι V →ₗ[F] M}
    (h : ∀ u : ∀ i, V i → F, f (simple u) = g (simple u)) : f = g := by
  apply (Pi.basisFun F (∀ i, V i)).ext
  intro x
  rw [Pi.basisFun_apply, ← simple_basis]
  exact h _

def applyLeg (i : ι) (A : Matrix (V i) (V i) F) : Tensor F ι V →ₗ[F] Tensor F ι V where
  toFun T := legAction T i A
  map_add' T S := by
    funext x
    simp only [legAction_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c T := by
    funext x
    simp only [legAction_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      RingHom.id_apply, mul_left_comm]

omit [Fintype ι] in
@[simp] theorem applyLeg_apply (i : ι) (A : Matrix (V i) (V i) F) (T : Tensor F ι V) :
    applyLeg i A T = legAction T i A := rfl

omit [Fintype ι] [∀ i, Fintype (W i)] in
theorem map_factor_update (M : ∀ i, Matrix (W i) (V i) F) (u : ∀ i, V i → F)
    (i : ι) (w : V i → F) :
    (fun j => M j *ᵥ Function.update u i w j) =
      Function.update (fun j => M j *ᵥ u j) i (M i *ᵥ w) := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp only [Function.update_of_ne h]

theorem legAction_localMap (M : ∀ i, Matrix (W i) (V i) F)
    (T : Tensor F ι V) (i : ι) (A : Matrix (V i) (V i) F) (B : Matrix (W i) (W i) F)
    (hcomm : B * M i = M i * A) :
    legAction (localMap (fun j y x => M j y x) T) i B =
      localMap (fun j y x => M j y x) (legAction T i A) := by
  let f := (applyLeg i B).comp (localMapLinear M)
  let g := (localMapLinear M).comp (applyLeg i A)
  have heq : f = g := by
    apply linearMap_ext_simple
    intro u
    change legAction (localMap (fun j y x => M j y x) (simple u)) i B =
      localMap (fun j y x => M j y x) (legAction (simple u) i A)
    rw [localMap_simple, legAction_simple, legAction_simple, localMap_simple]
    change simple (Function.update (fun j => M j *ᵥ u j) i (B *ᵥ (M i *ᵥ u i))) =
      simple (fun j => M j *ᵥ Function.update u i (A *ᵥ u i) j)
    rw [map_factor_update, Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec]
  exact congrArg (fun l : Tensor F ι V →ₗ[F] Tensor F ι W => l T) heq

def matrixOfEquiv {α β : Type*} [Fintype α] [Fintype β]
    (e : (α → F) ≃ₗ[F] (β → F)) : Matrix β α F :=
  LinearMap.toMatrix' e.toLinearMap

theorem matrixOfEquiv_symm_mul {α β : Type*} [Fintype α] [Fintype β]
    (e : (α → F) ≃ₗ[F] (β → F)) : matrixOfEquiv e.symm * matrixOfEquiv e = 1 := by
  rw [matrixOfEquiv, matrixOfEquiv, ← LinearMap.toMatrix'_comp,
    LinearEquiv.symm_comp, LinearMap.toMatrix'_id]

theorem matrixOfEquiv_mul_symm {α β : Type*} [Fintype α] [Fintype β]
    (e : (α → F) ≃ₗ[F] (β → F)) : matrixOfEquiv e * matrixOfEquiv e.symm = 1 :=
  matrixOfEquiv_symm_mul e.symm

def matrixConjugation {α β : Type*} [Fintype α] [Fintype β]
    (e : (α → F) ≃ₗ[F] (β → F)) : Matrix α α F ≃ₗ[F] Matrix β β F where
  toFun A := matrixOfEquiv e * A * matrixOfEquiv e.symm
  invFun B := matrixOfEquiv e.symm * B * matrixOfEquiv e
  left_inv A := by
    calc
      _ = (matrixOfEquiv e.symm * matrixOfEquiv e) * A *
          (matrixOfEquiv e.symm * matrixOfEquiv e) := by simp only [Matrix.mul_assoc]
      _ = A := by simp only [matrixOfEquiv_symm_mul, one_mul, mul_one]
  right_inv B := by
    calc
      _ = (matrixOfEquiv e * matrixOfEquiv e.symm) * B *
          (matrixOfEquiv e * matrixOfEquiv e.symm) := by simp only [Matrix.mul_assoc]
      _ = B := by simp only [matrixOfEquiv_mul_symm, one_mul, mul_one]
  map_add' A B := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

@[simp] theorem matrixConjugation_apply {α β : Type*} [Fintype α] [Fintype β]
    (e : (α → F) ≃ₗ[F] (β → F)) (A : Matrix α α F) :
    matrixConjugation e A = matrixOfEquiv e * A * matrixOfEquiv e.symm := rfl

theorem matrixConjugation_intertwines {α β : Type*} [Fintype α] [Fintype β]
    (e : (α → F) ≃ₗ[F] (β → F)) (A : Matrix α α F) :
    matrixConjugation e A * matrixOfEquiv e = matrixOfEquiv e * A := by
  rw [matrixConjugation_apply, Matrix.mul_assoc, Matrix.mul_assoc,
    matrixOfEquiv_symm_mul, mul_one]

theorem localEquiv_legAction (e : ∀ i, (V i → F) ≃ₗ[F] (W i → F))
    (T : Tensor F ι V) (i : ι) (A : Matrix (V i) (V i) F) :
    legAction (localEquiv e T) i (matrixConjugation (e i) A) =
      localEquiv e (legAction T i A) :=
  legAction_localMap (fun j => matrixOfEquiv (e j)) T i A _
    (matrixConjugation_intertwines (e i) A)

omit [Fintype ι] in
theorem concise_iff_legAction_injective (T : Tensor F ι V) :
    Concise T ↔ ∀ i, Function.Injective (legAction T i) := by
  refine ⟨fun h i => legAction_injective h i, ?_⟩
  intro h i u v huv
  have hz : contraction T i (u - v) = 0 := by rw [map_sub, huv, sub_self]
  funext a
  let A : Matrix (V i) (V i) F := fun r b => if r = a then (u - v) b else 0
  have hA : legAction T i A = 0 := by
    funext x
    simp only [legAction_apply]
    dsimp only [A]
    by_cases hx : x i = a
    · simp only [hx, ite_true]
      exact congrFun hz x
    · simp only [hx, ite_false, zero_mul, Finset.sum_const_zero, Pi.zero_apply]
  have hzero : A = 0 := h i (hA.trans (map_zero _).symm)
  have ha := congrFun (congrFun hzero a) a
  exact sub_eq_zero.mp (by simpa [A] using ha)

theorem Concise.localEquiv {T : Tensor F ι V} (hT : Concise T)
    (e : ∀ i, (V i → F) ≃ₗ[F] (W i → F)) : Concise (localEquiv e T) := by
  apply (concise_iff_legAction_injective _).2
  intro i A B h
  obtain ⟨A, rfl⟩ := (matrixConjugation (e i)).surjective A
  obtain ⟨B, rfl⟩ := (matrixConjugation (e i)).surjective B
  rw [localEquiv_legAction, localEquiv_legAction] at h
  exact congrArg (matrixConjugation (e i))
    (legAction_injective hT i ((Lemmata.Centroid.Tensor.localEquiv e).injective h))

def conjugateFamily (e : ∀ i, (V i → F) ≃ₗ[F] (W i → F)) :
    (∀ i, Matrix (V i) (V i) F) ≃ₗ[F] (∀ i, Matrix (W i) (W i) F) :=
  LinearEquiv.piCongrRight fun i => matrixConjugation (e i)

omit [Fintype ι] in
theorem conjugateFamily_symm (e : ∀ i, (V i → F) ≃ₗ[F] (W i → F)) :
    conjugateFamily (fun i => (e i).symm) = (conjugateFamily e).symm := by
  apply LinearEquiv.ext
  intro A
  funext i
  rfl

theorem localEquiv_symm_apply (e : ∀ i, (V i → F) ≃ₗ[F] (W i → F)) (T : Tensor F ι V) :
    localEquiv (fun i => (e i).symm) (localEquiv e T) = T := by
  change (localEquiv e).symm (localEquiv e T) = T
  exact (localEquiv e).symm_apply_apply T

theorem conjugateFamily_mem_centroid (e : ∀ i, (V i → F) ≃ₗ[F] (W i → F))
    {T : Tensor F ι V} {A : ∀ i, Matrix (V i) (V i) F} (hA : A ∈ centroid T) :
    conjugateFamily e A ∈ centroid (localEquiv e T) := by
  intro i j
  change legAction (localEquiv e T) i (matrixConjugation (e i) (A i)) =
    legAction (localEquiv e T) j (matrixConjugation (e j) (A j))
  rw [localEquiv_legAction, localEquiv_legAction, hA i j]

def centroidLocalEquiv (e : ∀ i, (V i → F) ≃ₗ[F] (W i → F)) (T : Tensor F ι V) :
    centroid T ≃ₗ[F] centroid (localEquiv e T) where
  toFun A := ⟨conjugateFamily e A.val, conjugateFamily_mem_centroid e A.property⟩
  invFun B := ⟨(conjugateFamily e).symm B.val, by
    have h := conjugateFamily_mem_centroid (fun i => (e i).symm) B.property
    rw [conjugateFamily_symm, localEquiv_symm_apply] at h
    exact h⟩
  left_inv A := Subtype.ext ((conjugateFamily e).symm_apply_apply A.val)
  right_inv B := Subtype.ext ((conjugateFamily e).apply_symm_apply B.val)
  map_add' A B := Subtype.ext ((conjugateFamily e).map_add A.val B.val)
  map_smul' c A := Subtype.ext ((conjugateFamily e).map_smul c A.val)

theorem finrank_centroid_localEquiv (e : ∀ i, (V i → F) ≃ₗ[F] (W i → F))
    (T : Tensor F ι V) :
    Module.finrank F (centroid (localEquiv e T)) = Module.finrank F (centroid T) :=
  (centroidLocalEquiv e T).finrank_eq.symm

end Lemmata.Centroid.Tensor
