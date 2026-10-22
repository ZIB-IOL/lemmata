module

public import Lemmata.Centroid.Def.Rank
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Single-leg actions, conciseness, and tensor centroids. -/

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.Centroid.Tensor

variable {F : Type*} [Field F] {ι : Type*}
variable {V : ι → Type*} [∀ i, Fintype (V i)]

def contraction (T : Tensor F ι V) (i : ι) :
    (V i → F) →ₗ[F] Tensor F ι V where
  toFun f x := ∑ a, f a * T (Function.update x i a)
  map_add' f g := by
    ext x
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c f := by
    ext x
    simp [smul_eq_mul, Finset.mul_sum, mul_assoc]

@[simp] theorem contraction_apply (T : Tensor F ι V) (i : ι)
    (f : V i → F) (x : ∀ i, V i) :
    contraction T i f x = ∑ a, f a * T (Function.update x i a) := rfl

def Concise (T : Tensor F ι V) : Prop :=
  ∀ i, Function.Injective (contraction T i)

@[simp] theorem contraction_zero (i : ι) :
    contraction (0 : Tensor F ι V) i = 0 := by
  ext f x
  simp

theorem Concise.ne_zero [Nonempty ι] [∀ i, Nonempty (V i)]
    {T : Tensor F ι V} (hT : Concise T) : T ≠ 0 := by
  intro h
  subst T
  let i : ι := Classical.choice inferInstance
  let a : V i := Classical.choice inferInstance
  have hf : Pi.single a (1 : F) = (0 : V i → F) := by
    apply hT i
    simp
  have := congrFun hf a
  simp at this

def legAction (T : Tensor F ι V) (i : ι) :
    Matrix (V i) (V i) F →ₗ[F] Tensor F ι V where
  toFun A x := ∑ a, A (x i) a * T (Function.update x i a)
  map_add' A B := by
    ext x
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c A := by
    ext x
    simp [smul_eq_mul, Finset.mul_sum, mul_assoc]

@[simp] theorem legAction_apply (T : Tensor F ι V) (i : ι)
    (A : Matrix (V i) (V i) F) (x : ∀ i, V i) :
    legAction T i A x = ∑ a, A (x i) a * T (Function.update x i a) := rfl

theorem legAction_injective {T : Tensor F ι V} (hT : Concise T) (i : ι) :
    Function.Injective (legAction T i) := by
  intro A B h
  funext a
  apply hT i
  ext x
  have hx := congrFun h (Function.update x i a)
  simpa only [legAction_apply, Function.update_self, Function.update_idem,
    contraction_apply] using hx

@[simp] theorem legAction_one (T : Tensor F ι V) (i : ι) :
    legAction T i (1 : Matrix (V i) (V i) F) = T := by
  ext x
  simp [legAction, Matrix.one_apply]

theorem legAction_mul (T : Tensor F ι V) (i : ι)
    (A B : Matrix (V i) (V i) F) :
    legAction T i (A * B) = legAction (legAction T i B) i A := by
  ext x
  simp only [legAction_apply, Matrix.mul_apply, Finset.sum_mul,
    Finset.mul_sum, Function.update_self, Function.update_idem, mul_assoc]
  rw [Finset.sum_comm]

theorem legAction_comm (T : Tensor F ι V) {i j : ι} (h : i ≠ j)
    (A : Matrix (V i) (V i) F) (B : Matrix (V j) (V j) F) :
    legAction (legAction T j B) i A = legAction (legAction T i A) j B := by
  ext x
  simp only [legAction_apply, Function.update_of_ne h, Function.update_of_ne h.symm,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [Function.update_comm h]
  ring

def actionSpace (T : Tensor F ι V) (i : ι) : Submodule F (Tensor F ι V) :=
  (legAction T i).range

def centroid (T : Tensor F ι V) : Submodule F (∀ i, Matrix (V i) (V i) F) where
  carrier := {A | ∀ i j, legAction T i (A i) = legAction T j (A j)}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB i j
    simpa only [Pi.add_apply, map_add] using congrArg₂ (· + ·) (hA i j) (hB i j)
  smul_mem' := by
    intro c A hA i j
    simpa only [Pi.smul_apply, map_smul] using congrArg (c • ·) (hA i j)

@[simp] theorem mem_centroid_iff (T : Tensor F ι V)
    (A : ∀ i, Matrix (V i) (V i) F) :
    A ∈ centroid T ↔ ∀ i j, legAction T i (A i) = legAction T j (A j) := Iff.rfl

def centroidProjection (T : Tensor F ι V) (i : ι) :
    centroid T →ₗ[F] Matrix (V i) (V i) F where
  toFun A := A.val i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem centroidProjection_injective {T : Tensor F ι V} (hT : Concise T) (i : ι) :
    Function.Injective (centroidProjection T i) := by
  intro A B h
  apply Subtype.ext
  funext j
  apply legAction_injective hT j
  exact (A.property j i).trans ((congrArg (legAction T i) h).trans (B.property i j))

def centroidEvaluation (T : Tensor F ι V) (i : ι) :
    centroid T →ₗ[F] Tensor F ι V where
  toFun A := legAction T i (A.val i)
  map_add' A B := by simp
  map_smul' c A := by simp

theorem centroidEvaluation_injective {T : Tensor F ι V} (hT : Concise T) (i : ι) :
    Function.Injective (centroidEvaluation T i) := by
  intro A B h
  apply Subtype.ext
  funext j
  apply legAction_injective hT j
  exact (A.property j i).trans (h.trans (B.property i j))

theorem range_centroidEvaluation (T : Tensor F ι V) (i : ι) :
    (centroidEvaluation T i).range = ⨅ j, actionSpace T j := by
  ext t
  constructor
  · rintro ⟨A, rfl⟩
    rw [Submodule.mem_iInf]
    intro j
    exact ⟨A.val j, A.property j i⟩
  · intro ht
    rw [Submodule.mem_iInf] at ht
    have hj : ∀ j, ∃ A, legAction T j A = t := by
      intro j
      exact ht j
    choose A hA using hj
    refine ⟨⟨A, ?_⟩, hA i⟩
    intro j k
    exact (hA j).trans (hA k).symm

theorem finrank_centroid_eq_intersection [Fintype ι]
    {T : Tensor F ι V} (hT : Concise T) (i : ι) :
    Module.finrank F (centroid T) =
      Module.finrank F (⨅ j, actionSpace T j : Submodule F (Tensor F ι V)) := by
  rw [← range_centroidEvaluation T i,
    LinearMap.finrank_range_of_inj (centroidEvaluation_injective hT i)]

end Lemmata.Centroid.Tensor

namespace Lemmata.Centroid.Tensor

variable {F : Type*} [Field F] {V : Fin 3 → Type*} [∀ i, Fintype (V i)]

private theorem centroid_actions_commute_at {T : Tensor F (Fin 3) V}
    {A B : ∀ i, Matrix (V i) (V i) F} (hA : A ∈ centroid T) (hB : B ∈ centroid T)
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) :
    legAction (legAction T i (B i)) i (A i) =
      legAction (legAction T i (A i)) i (B i) := by
  calc
    _ = legAction (legAction T j (B j)) i (A i) := congrArg (fun U => legAction U i (A i)) (hB i j)
    _ = legAction (legAction T i (A i)) j (B j) := legAction_comm T hij _ _
    _ = legAction (legAction T k (A k)) j (B j) := congrArg (fun U => legAction U j (B j)) (hA i k)
    _ = legAction (legAction T j (B j)) k (A k) := legAction_comm T hjk _ _
    _ = legAction (legAction T i (B i)) k (A k) := congrArg (fun U => legAction U k (A k)) (hB j i)
    _ = legAction (legAction T k (A k)) i (B i) := legAction_comm T hki _ _
    _ = _ := congrArg (fun U => legAction U i (B i)) (hA k i)

theorem centroid_actions_commute {T : Tensor F (Fin 3) V}
    {A B : ∀ i, Matrix (V i) (V i) F} (hA : A ∈ centroid T) (hB : B ∈ centroid T)
    (i : Fin 3) :
    legAction (legAction T i (B i)) i (A i) =
      legAction (legAction T i (A i)) i (B i) := by
  fin_cases i
  · exact centroid_actions_commute_at hA hB 0 1 2 (by decide) (by decide) (by decide)
  · exact centroid_actions_commute_at hA hB 1 2 0 (by decide) (by decide) (by decide)
  · exact centroid_actions_commute_at hA hB 2 0 1 (by decide) (by decide) (by decide)

theorem centroid_mul_comm {T : Tensor F (Fin 3) V} (hT : Concise T)
    {A B : ∀ i, Matrix (V i) (V i) F} (hA : A ∈ centroid T) (hB : B ∈ centroid T) :
    A * B = B * A := by
  funext i
  apply legAction_injective hT i
  simp only [Pi.mul_apply, legAction_mul]
  exact centroid_actions_commute hA hB i

theorem centroid_mul_mem {T : Tensor F (Fin 3) V} (hT : Concise T)
    {A B : ∀ i, Matrix (V i) (V i) F} (hA : A ∈ centroid T) (hB : B ∈ centroid T) :
    A * B ∈ centroid T := by
  intro i j
  by_cases hij : i = j
  · subst j
    rfl
  have hcomm := congrFun (centroid_mul_comm hT hA hB) j
  calc
    _ = legAction (legAction T i (B i)) i (A i) := legAction_mul T i _ _
    _ = legAction (legAction T j (B j)) i (A i) := congrArg (fun U => legAction U i (A i)) (hB i j)
    _ = legAction (legAction T i (A i)) j (B j) := legAction_comm T hij _ _
    _ = legAction (legAction T j (A j)) j (B j) := congrArg (fun U => legAction U j (B j)) (hA i j)
    _ = legAction T j (B j * A j) := (legAction_mul T j _ _).symm
    _ = _ := congrArg (legAction T j) hcomm.symm

def centroidAlgebra (T : Tensor F (Fin 3) V) (hT : Concise T) :
    Subalgebra F (∀ i, Matrix (V i) (V i) F) where
  carrier := centroid T
  zero_mem' := (centroid T).zero_mem
  add_mem' := (centroid T).add_mem
  mul_mem' := centroid_mul_mem hT
  algebraMap_mem' c := by
    intro i j
    simp [Algebra.algebraMap_eq_smul_one]

@[simp] theorem centroidAlgebra_toSubmodule (T : Tensor F (Fin 3) V) (hT : Concise T) :
    (centroidAlgebra T hT).toSubmodule = centroid T := rfl

instance centroidAlgebraCommRing (T : Tensor F (Fin 3) V) (hT : Concise T) :
    CommRing (centroidAlgebra T hT) :=
  { (inferInstance : Ring (centroidAlgebra T hT)) with
    mul_comm := fun A B => Subtype.ext (centroid_mul_comm hT A.property B.property) }

def centroidProjectionAlgHom (T : Tensor F (Fin 3) V) (hT : Concise T) (i : Fin 3) :
    centroidAlgebra T hT →ₐ[F] Matrix (V i) (V i) F :=
  (Pi.evalAlgHom F (fun i => Matrix (V i) (V i) F) i).comp (centroidAlgebra T hT).val

theorem centroidProjectionAlgHom_injective {T : Tensor F (Fin 3) V}
    (hT : Concise T) (i : Fin 3) :
    Function.Injective (centroidProjectionAlgHom T hT i) :=
  centroidProjection_injective hT i

def centroidRepresentation (T : Tensor F (Fin 3) V) (hT : Concise T) (i : Fin 3) :
    centroidAlgebra T hT →ₐ[F] Module.End F (V i → F) :=
  Matrix.toLinAlgEquiv'.toAlgHom.comp (centroidProjectionAlgHom T hT i)

theorem centroidRepresentation_injective {T : Tensor F (Fin 3) V}
    (hT : Concise T) (i : Fin 3) :
    Function.Injective (centroidRepresentation T hT i) :=
  Matrix.toLinAlgEquiv'.injective.comp (centroidProjectionAlgHom_injective hT i)

def centroidDualProjectionAlgHom (T : Tensor F (Fin 3) V) (hT : Concise T) (i : Fin 3) :
    centroidAlgebra T hT →ₐ[F] Matrix (V i) (V i) F where
  toFun A := (A.val i).transpose
  map_zero' := rfl
  map_one' := Matrix.transpose_one
  map_add' A B := Matrix.transpose_add _ _
  map_mul' A B := by
    change (A.val i * B.val i).transpose = (A.val i).transpose * (B.val i).transpose
    have h : A.val i * B.val i = B.val i * A.val i :=
      congrFun (centroid_mul_comm hT A.property B.property) i
    rw [h, Matrix.transpose_mul]
  commutes' c := by simp [Algebra.algebraMap_eq_smul_one]

def centroidDualRepresentation (T : Tensor F (Fin 3) V) (hT : Concise T) (i : Fin 3) :
    centroidAlgebra T hT →ₐ[F] Module.End F (V i → F) :=
  Matrix.toLinAlgEquiv'.toAlgHom.comp (centroidDualProjectionAlgHom T hT i)

theorem centroidDualRepresentation_injective {T : Tensor F (Fin 3) V}
    (hT : Concise T) (i : Fin 3) :
    Function.Injective (centroidDualRepresentation T hT i) := by
  intro A B h
  apply centroidProjectionAlgHom_injective hT i
  apply Matrix.transpose_injective
  exact Matrix.toLinAlgEquiv'.injective h

end Lemmata.Centroid.Tensor
