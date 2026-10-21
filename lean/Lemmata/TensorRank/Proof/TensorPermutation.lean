module

public import Lemmata.TensorRank.Proof.TensorSpectrum
public import Lemmata.TensorRank.Proof.WeightedGraph

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.Tensor

universe u v w z

variable {R : Type u} [CommSemiring R] {I J : Type v}
variable [Fintype I] [Fintype J] {V W : I → Type w}
variable [∀ i, Fintype (V i)]

theorem localMap_relabel (e : J ≃ I) (A : ∀ i, W i → V i → R) (T : Tensor R I V) :
    localMap (fun j => A (e j)) (relabel e T) = relabel e (localMap A T) := by
  funext y
  unfold localMap relabel
  apply Fintype.sum_equiv (Equiv.piCongrLeft V e)
  intro x
  congr 1
  apply Fintype.prod_equiv e
  intro j
  simp

theorem Restricts.relabel (e : J ≃ I) {S : Tensor R I W} {T : Tensor R I V}
    (h : Restricts S T) : Restricts (relabel e S) (relabel e T) := by
  obtain ⟨A, rfl⟩ := h
  exact ⟨fun j => A (e j), (localMap_relabel e A T).symm⟩

omit [Fintype I] [Fintype J] [∀ i, Fintype (V i)] in
theorem relabel_add (e : J ≃ I) (S T : Tensor R I V) :
    relabel e (S + T) = relabel e S + relabel e T := rfl

variable [∀ i, Fintype (W i)]

theorem relabel_embed {U : I → Type w} (e : J ≃ I) (f : ∀ i, V i ↪ U i) (T : Tensor R I V) :
    relabel e (embed f T) = embed (fun j => f (e j)) (relabel e T) :=
  (localMap_relabel e (fun i y x => if f i x = y then 1 else 0) T).symm

theorem relabel_directSum (e : J ≃ I) (S : Tensor R I V) (T : Tensor R I W) :
    relabel e (directSum S T) = directSum (relabel e S) (relabel e T) := by
  rw [directSum, relabel_add, relabel_embed, relabel_embed]
  rfl

omit [CommSemiring R] [Fintype I] [Fintype J] [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] in
theorem relabel_comp {K : Type z} (e : J ≃ I) (f : K ≃ J) (T : Tensor R I V) :
    relabel f (relabel e T) = relabel (f.trans e) T := by
  funext x
  unfold relabel
  congr 1
  funext i
  obtain ⟨j, rfl⟩ := e.surjective i
  obtain ⟨a, rfl⟩ := f.surjective j
  simp only [Equiv.piCongrLeft_apply_apply]
  exact (Equiv.piCongrLeft_apply_apply V (f.trans e) x a).symm

omit [CommSemiring R] [Fintype I] [Fintype J] [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] in
theorem relabel_refl (T : Tensor R I V) : relabel (Equiv.refl I) T = T := by
  funext x
  simp [relabel]
  rfl

omit [Fintype I] [Fintype J] [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] in
theorem relabel_product_exact (e : J ≃ I) (S : Tensor R I V) (T : Tensor R I W) :
    relabel e (product S T) = product (relabel e S) (relabel e T) := by
  funext x
  change S (fun i => (Equiv.piCongrLeft (fun i => V i × W i) e x i).1) *
    T (fun i => (Equiv.piCongrLeft (fun i => V i × W i) e x i).2) = _
  congr 1 <;> congr 1 <;> funext i <;> obtain ⟨j, rfl⟩ := e.surjective i <;> simp

end Lemmata.TensorRank.Tensor

namespace Lemmata.TensorRank.TensorSemiring

variable {k : ℕ}

theorem Object.rel_relabel (σ : Equiv.Perm (Fin k)) {A B : Object k} (h : Object.Rel A B) :
    Object.Rel (Object.relabel σ A) (Object.relabel σ B) := h.relabel σ

theorem Object.equivalent_relabel (σ : Equiv.Perm (Fin k)) {A B : Object k}
    (h : Object.Equivalent A B) : Object.Equivalent (Object.relabel σ A) (Object.relabel σ B) :=
  ⟨Object.rel_relabel σ h.1, Object.rel_relabel σ h.2⟩

def relabel (σ : Equiv.Perm (Fin k)) : Value k → Value k :=
  Quot.map (Object.relabel σ) (fun _ _ h => Object.equivalent_relabel σ h)

@[simp] theorem relabel_ofObject (σ : Equiv.Perm (Fin k)) (A : Object k) :
    relabel σ (ofObject A) = ofObject (Object.relabel σ A) := rfl

@[simp] theorem ofTensor_relabel (σ : Equiv.Perm (Fin k))
    {V : Fin k → Type} [∀ i, Fintype (V i)] (T : Tensor ℂ (Fin k) V) :
    ofTensor (Tensor.relabel σ T) = relabel σ (ofTensor T) := rfl

def relabelHom (σ : Equiv.Perm (Fin k)) : Value k →+* Value k where
  toFun := relabel σ
  map_zero' := Quot.sound (Object.equivalent_of_zero _ rfl)
  map_one' := by
    apply Quot.sound
    apply Object.equivalent_of_reindex (Object.relabel σ (Object.one k)) (Object.one k)
      (fun _ => Equiv.refl _)
    rfl
  map_add' a b := by
    refine Quot.inductionOn a (fun A => Quot.inductionOn b (fun B => ?_))
    apply Quot.sound
    apply Object.equivalent_of_reindex (Object.relabel σ (Object.add A B))
      (Object.add (Object.relabel σ A) (Object.relabel σ B)) (fun _ => Equiv.refl _)
    exact Tensor.relabel_directSum σ A.tensor B.tensor
  map_mul' a b := by
    refine Quot.inductionOn a (fun A => Quot.inductionOn b (fun B => ?_))
    apply Quot.sound
    apply Object.equivalent_of_reindex (Object.relabel σ (Object.mul A B))
      (Object.mul (Object.relabel σ A) (Object.relabel σ B)) (fun _ => Equiv.refl _)
    exact Tensor.relabel_product_exact σ A.tensor B.tensor

@[simp] theorem relabelHom_apply (σ : Equiv.Perm (Fin k)) (a : Value k) :
    relabelHom σ a = relabel σ a := rfl

theorem rel_relabel (σ : Equiv.Perm (Fin k)) {a b : Value k} (h : Rel a b) :
    Rel (relabel σ a) (relabel σ b) := by
  revert h
  refine Quot.inductionOn a (fun A => Quot.inductionOn b (fun B => ?_))
  exact fun h => Object.rel_relabel σ h

@[simp] theorem relabel_one (a : Value k) : relabel 1 a = a := by
  refine Quot.inductionOn a (fun A => ?_)
  apply Quot.sound
  apply Object.equivalent_of_reindex (Object.relabel 1 A) A (fun _ => Equiv.refl _)
  exact Tensor.relabel_refl A.tensor

theorem relabel_mul (σ τ : Equiv.Perm (Fin k)) (a : Value k) :
    relabel (σ * τ) a = relabel τ (relabel σ a) := by
  refine Quot.inductionOn a (fun A => ?_)
  apply Quot.sound
  apply Object.equivalent_symm
  apply Object.equivalent_of_reindex (Object.relabel τ (Object.relabel σ A))
    (Object.relabel (σ * τ) A) (fun _ => Equiv.refl _)
  exact Tensor.relabel_comp σ τ A.tensor

def relabelEquiv (σ : Equiv.Perm (Fin k)) : Value k ≃+* Value k where
  toFun := relabel σ
  invFun := relabel σ.symm
  left_inv a := by
    rw [← relabel_mul]
    change relabel (σ * σ⁻¹) a = a
    rw [mul_inv_cancel, relabel_one]
  right_inv a := by
    rw [← relabel_mul]
    change relabel (σ⁻¹ * σ) a = a
    rw [inv_mul_cancel, relabel_one]
  map_add' := (relabelHom σ).map_add
  map_mul' := (relabelHom σ).map_mul

theorem rank_relabel (σ : Equiv.Perm (Fin k)) (a : Value k) : rank (relabel σ a) = rank a :=
  Quot.inductionOn a fun A => Object.rank_relabel σ A

theorem relabel_weightedComplete (d : Edge k → ℕ) (σ : Equiv.Perm (Fin k)) :
    relabel σ (ofTensor (weightedComplete d)) =
      ofTensor (weightedComplete (fun e => d (edgeMap σ e))) := by
  have h := ofTensor_reindex (weightedRelabelCoordinate d σ)
    (weightedComplete (fun e => d (edgeMap σ e)))
  rw [weighted_relabel_reindex] at h
  exact h

end Lemmata.TensorRank.TensorSemiring
