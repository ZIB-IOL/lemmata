module

public import Lemmata.Centroid.Proof.Centroid
public import Mathlib.Logic.Equiv.Basic

@[expose] public section

namespace Lemmata.Centroid

abbrev Cubic (F I : Type*) := Tensor F (Fin 3) (fun _ => I)

namespace Cubic

variable {F I : Type*} [Field F]

def IsSymmetric (T : Cubic F I) : Prop :=
  ∀ (σ : Equiv.Perm (Fin 3)) (x : Fin 3 → I), T (fun i => x (σ i)) = T x

def symmetricSubmodule : Submodule F (Cubic F I) where
  carrier := {T | IsSymmetric T}
  zero_mem' := by intro σ x; rfl
  add_mem' := by
    intro T S hT hS σ x
    exact congrArg₂ (· + ·) (hT σ x) (hS σ x)
  smul_mem' := by
    intro c T hT σ x
    exact congrArg (c * ·) (hT σ x)

def permute (σ : Equiv.Perm (Fin 3)) : Cubic F I →ₗ[F] Cubic F I where
  toFun T x := T (fun i => x (σ i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem permute_apply (σ : Equiv.Perm (Fin 3)) (T : Cubic F I) (x : Fin 3 → I) :
    permute σ T x = T (fun i => x (σ i)) := rfl

theorem permute_eq {T : Cubic F I} (hT : IsSymmetric T) (σ : Equiv.Perm (Fin 3)) :
    permute σ T = T := funext (hT σ)

variable [Fintype I]

theorem legAction_permute (σ : Equiv.Perm (Fin 3)) (T : Cubic F I)
    (i : Fin 3) (A : Matrix I I F) :
    permute σ (Tensor.legAction T i A) = Tensor.legAction (permute σ T) (σ i) A := by
  classical
  ext x
  simp only [permute_apply, Tensor.legAction_apply]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  congr 1
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [Function.update, h, σ.injective.ne h]

private theorem centroid_pair {T : Cubic F I} (hT : Tensor.Concise T)
    (hS : IsSymmetric T) {A : Fin 3 → Matrix I I F} (hA : A ∈ Tensor.centroid T)
    (i j k : Fin 3) (_hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) : A i = A j := by
  classical
  apply Tensor.legAction_injective hT j
  have h := congrArg (permute (Equiv.swap i j)) (hA i k)
  rw [legAction_permute, legAction_permute, permute_eq hS] at h
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hki hkj] at h
  exact h.trans (hA k j)

theorem centroid_diagonal {T : Cubic F I} (hT : Tensor.Concise T)
    (hS : IsSymmetric T) {A : Fin 3 → Matrix I I F} (hA : A ∈ Tensor.centroid T) :
    ∀ i j, A i = A j := by
  have h01 : A 0 = A 1 := centroid_pair hT hS hA 0 1 2 (by decide) (by decide) (by decide)
  have h02 : A 0 = A 2 := centroid_pair hT hS hA 0 2 1 (by decide) (by decide) (by decide)
  have h0 : ∀ i, A i = A 0 := by
    intro i
    fin_cases i
    · rfl
    · exact h01.symm
    · exact h02.symm
  intro i j
  exact (h0 i).trans (h0 j).symm

theorem centroid_action_isSymmetric {T : Cubic F I} (hT : Tensor.Concise T)
    (hS : IsSymmetric T) {A : Fin 3 → Matrix I I F} (hA : A ∈ Tensor.centroid T) :
    IsSymmetric (Tensor.legAction T 0 (A 0)) := by
  intro σ x
  have heq : permute σ (Tensor.legAction T 0 (A 0)) = Tensor.legAction T 0 (A 0) := by
    calc
      _ = Tensor.legAction (permute σ T) (σ 0) (A 0) := legAction_permute σ T 0 (A 0)
      _ = Tensor.legAction T (σ 0) (A 0) := by rw [permute_eq hS]
      _ = Tensor.legAction T (σ 0) (A (σ 0)) :=
        congrArg (Tensor.legAction T (σ 0)) (centroid_diagonal hT hS hA 0 (σ 0))
      _ = Tensor.legAction T 0 (A 0) := hA (σ 0) 0
  exact congrFun heq x

end Cubic

end Lemmata.Centroid
