module

public import Lemmata.TensorRank.Def.TensorSemiring
public import Lemmata.TensorRank.Proof.DirectSum
public import Lemmata.TensorRank.Proof.Context
public import Lemmata.TensorRank.Proof.Parties
public import Mathlib.Data.Quot

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.Tensor

variable {R I : Type*} [CommSemiring R] [Fintype I]
variable {V W U : I → Type*}
variable [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] [∀ i, Fintype (U i)]

omit [∀ i, Fintype (U i)] in
theorem localMap_embed (e : ∀ i, V i ↪ W i) (A : ∀ i, U i → W i → R)
    (T : Tensor R I V) :
    localMap A (embed e T) = localMap (fun i y x => A i y (e i x)) T := by
  unfold embed
  rw [localMap_comp]
  congr 1
  funext i y x
  simp

omit [∀ i, Fintype (U i)] in
theorem embed_comp (e : ∀ i, V i ↪ W i) (f : ∀ i, W i ↪ U i) (T : Tensor R I V) :
    embed f (embed e T) = embed (fun i => (e i).trans (f i)) T := by
  change localMap (fun i y x => if f i x = y then 1 else 0) (embed e T) = _
  rw [localMap_embed]
  rfl

omit [∀ i, Fintype (W i)] in
theorem embed_add (e : ∀ i, V i ↪ W i) (S T : Tensor R I V) :
    embed e (S + T) = embed e S + embed e T := localMap_add _ _ _

omit [∀ i, Fintype (W i)] in
theorem embed_zero (e : ∀ i, V i ↪ W i) : embed e (0 : Tensor R I V) = 0 :=
  localMap_zero _

omit [∀ i, Fintype (W i)] [∀ i, Fintype (U i)] in
theorem embed_refl (T : Tensor R I V) : embed (fun i => Function.Embedding.refl (V i)) T = T := by
  change localMap (fun _ y x => if x = y then 1 else 0) T = T
  exact localMap_select (fun _ => id) T

omit [Fintype I] [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] [∀ i, Fintype (U i)] in
theorem reindex_add (e : ∀ i, W i → V i) (S T : Tensor R I V) :
    reindex e (S + T) = reindex e S + reindex e T := rfl

omit [Fintype I] [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] [∀ i, Fintype (U i)] in
theorem reindex_zero (e : ∀ i, W i → V i) : reindex e (0 : Tensor R I V) = 0 := rfl

omit [∀ i, Fintype (W i)] in
theorem reindex_embed {Z : I → Type*} (e : ∀ i, V i ↪ W i) (f : ∀ i, V i ↪ Z i)
    (q : ∀ i, Z i ≃ W i) (h : ∀ i x, q i (f i x) = e i x) (T : Tensor R I V) :
    reindex (fun i => q i) (embed e T) = embed f T := by
  funext y
  unfold reindex embed localMap
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have he : e i (x i) = q i (y i) ↔ f i (x i) = y i := by
    rw [← h]
    exact (q i).injective.eq_iff
  simp only [he]

omit [∀ i, Fintype (W i)] in
theorem reindex_embed_eq {Z : I → Type*} (e : ∀ i, V i ↪ W i)
    (q : ∀ i, Z i ≃ W i) (T : Tensor R I V) :
    reindex (fun i => q i) (embed e T) =
      embed (fun i => (e i).trans (q i).symm.toEmbedding) T :=
  reindex_embed e _ q (fun i _ => (q i).apply_symm_apply _) T

theorem embed_directSum {Z : I → Type*} [∀ i, Fintype (Z i)]
    (e : ∀ i, (V i ⊕ W i) ↪ Z i) (S : Tensor R I V) (T : Tensor R I W) :
    embed e (directSum S T) =
      embed (fun i => Function.Embedding.inl.trans (e i)) S +
        embed (fun i => Function.Embedding.inr.trans (e i)) T := by
  rw [directSum, embed_add, embed_comp, embed_comp]

omit [∀ i, Fintype (W i)] in
theorem embed_product {Z : I → Type*} [∀ i, Fintype (Z i)]
    (e : ∀ i, V i ↪ W i) (f : ∀ i, U i ↪ Z i)
    (S : Tensor R I V) (T : Tensor R I U) :
    product (embed e S) (embed f T) =
      embed (fun i => (e i).prodMap (f i)) (product S T) := by
  unfold embed
  rw [← localMap_product]
  congr 1
  funext i y x
  by_cases he : e i x.1 = y.1 <;> by_cases hf : f i x.2 = y.2 <;>
    simp [productKernel, Function.Embedding.prodMap, Prod.ext_iff, he, hf]

def sumKernel (A : ∀ i, W i → V i → R) {Z : I → Type*}
    (B : ∀ i, Z i → U i → R) :
    ∀ i, (W i ⊕ Z i) → (V i ⊕ U i) → R :=
  fun i y x => match y, x with
    | .inl y, .inl x => A i y x
    | .inr y, .inr x => B i y x
    | _, _ => 0

theorem localMap_directSum {Z : I → Type*} [∀ i, Fintype (Z i)]
    (A : ∀ i, W i → V i → R) (B : ∀ i, Z i → U i → R)
    (S : Tensor R I V) (T : Tensor R I U) :
    localMap (sumKernel A B) (directSum S T) =
      directSum (localMap A S) (localMap B T) := by
  rw [directSum, localMap_add, localMap_embed, localMap_embed, directSum]
  congr 1
  · unfold embed
    rw [localMap_comp]
    congr 1
    funext i y x
    cases y <;> simp [sumKernel]
  · unfold embed
    rw [localMap_comp]
    congr 1
    funext i y x
    cases y <;> simp [sumKernel]

theorem Restricts.directSum {Z : I → Type*} [∀ i, Fintype (Z i)]
    {S : Tensor R I V} {T : Tensor R I W} {A : Tensor R I U} {B : Tensor R I Z}
    (h : Restricts S T) (g : Restricts A B) :
    Restricts (directSum S A) (directSum T B) := by
  obtain ⟨K, rfl⟩ := h
  obtain ⟨L, rfl⟩ := g
  exact ⟨sumKernel K L, (localMap_directSum K L T B).symm⟩

theorem directSum_comm_reindex (S : Tensor R I V) (T : Tensor R I W) :
    reindex (fun i => Equiv.sumComm (V i) (W i)) (directSum T S) = directSum S T := by
  simp only [directSum, reindex_add, reindex_embed_eq]
  rw [add_comm]
  rfl

theorem directSum_assoc_reindex (S : Tensor R I V) (T : Tensor R I W) (H : Tensor R I U) :
    reindex (fun i => Equiv.sumAssoc (V i) (W i) (U i)) (directSum S (directSum T H)) =
      directSum (directSum S T) H := by
  simp only [directSum, embed_add, embed_comp, reindex_add, reindex_embed_eq]
  rw [add_assoc]
  rfl

theorem directSum_zero_reindex (T : Tensor R I V) :
    reindex (fun i => (Equiv.emptySum Empty (V i)).symm)
      (directSum (0 : Tensor R I (fun _ => Empty)) T) = T := by
  simp only [directSum, embed_zero, zero_add, reindex_embed_eq]
  convert embed_refl T using 1
  rfl

theorem directSum_product_reindex (S : Tensor R I V) (T : Tensor R I W) (H : Tensor R I U) :
    reindex (fun i => Equiv.sumProdDistrib (V i) (W i) (U i))
      (directSum (product S H) (product T H)) = product (directSum S T) H := by
  have h1 := embed_product (fun i => (Function.Embedding.inl : V i ↪ V i ⊕ W i))
    (fun i => Function.Embedding.refl (U i)) S H
  have h2 := embed_product (fun i => (Function.Embedding.inr : W i ↪ V i ⊕ W i))
    (fun i => Function.Embedding.refl (U i)) T H
  rw [embed_refl] at h1 h2
  have hmul : product (directSum S T) H =
      product (embed (fun _ => Function.Embedding.inl) S) H +
        product (embed (fun _ => Function.Embedding.inr) T) H := by
    funext x
    exact add_mul _ _ _
  rw [hmul, h1, h2]
  simp only [directSum, reindex_add, reindex_embed_eq]
  rfl

omit [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] [∀ i, Fintype (U i)] in
theorem embed_diagonal [Nonempty I] (m : ℕ) (e : ∀ i, Fin m ↪ V i) :
    embed e (diagonal (R := R) (I := I) m) =
      ∑ a : Fin m, pure (fun i y => if e i a = y then 1 else 0) := by
  exact localMap_diagonal _ _

omit [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] [∀ i, Fintype (U i)] in
theorem directSum_diagonal_reindex [Nonempty I] (m n : ℕ) :
    reindex (fun _ : I => (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)))
      (diagonal (R := R) (I := I) (m + n)) =
        directSum (diagonal m) (diagonal n) := by
  rw [directSum, embed_diagonal, embed_diagonal, diagonal_eq_sum]
  funext x
  simp only [reindex, Pi.add_apply, Finset.sum_apply, pure]
  have he := Fintype.sum_equiv (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))
    (fun a => ∏ i, if a = x i then (1 : R) else 0)
    (fun a => ∏ i, if finSumFinEquiv (x i) = a then (1 : R) else 0) (fun a => by
      apply Finset.prod_congr rfl
      intro i _
      simp only [EmbeddingLike.apply_eq_iff_eq, eq_comm])
  rw [← he, Fintype.sum_sum_type]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro a ha <;>
    apply Finset.prod_congr rfl <;> intro i hi <;> congr 1

end Lemmata.TensorRank.Tensor

namespace Lemmata.TensorRank.TensorSemiring.Object

variable {k : ℕ}

theorem rel_refl (A : Object k) : Rel A A := Tensor.Restricts.refl A.tensor

theorem rel_trans {A B C : Object k} (h : Rel A B) (g : Rel B C) : Rel A C :=
  h.trans g

theorem equivalent_refl (A : Object k) : Equivalent A A := ⟨rel_refl A, rel_refl A⟩

theorem equivalent_symm {A B : Object k} (h : Equivalent A B) : Equivalent B A := ⟨h.2, h.1⟩

theorem equivalent_trans {A B C : Object k} (h : Equivalent A B) (g : Equivalent B C) :
    Equivalent A C := ⟨h.1.trans g.1, g.2.trans h.2⟩

theorem equivalent_of_reindex (A B : Object k)
    (e : ∀ i, B.format.Coordinate i ≃ A.format.Coordinate i)
    (h : Tensor.reindex (fun i => e i) A.tensor = B.tensor) : Equivalent A B := by
  have h1 := Tensor.reindex_restricts (fun i => e i) A.tensor
  rw [h] at h1
  have h2 := Tensor.reindex_restricts (fun i => (e i).symm) B.tensor
  have he : Tensor.reindex (fun i => (e i).symm) B.tensor = A.tensor := by
    rw [← h]
    funext x
    simp [Tensor.reindex]
  rw [he] at h2
  exact ⟨h2, h1⟩

theorem rel_add {A B C D : Object k} (h : Rel A B) (g : Rel C D) :
    Rel (add A C) (add B D) := h.directSum g

theorem rel_mul {A B C D : Object k} (h : Rel A B) (g : Rel C D) :
    Rel (mul A C) (mul B D) := h.product g

theorem equivalent_add {A B C D : Object k} (h : Equivalent A B) (g : Equivalent C D) :
    Equivalent (add A C) (add B D) := ⟨rel_add h.1 g.1, rel_add h.2 g.2⟩

theorem equivalent_mul {A B C D : Object k} (h : Equivalent A B) (g : Equivalent C D) :
    Equivalent (mul A C) (mul B D) := ⟨rel_mul h.1 g.1, rel_mul h.2 g.2⟩

theorem equivalent_of_zero (A : Object k) (h : A.tensor = 0) : Equivalent A (zero k) := by
  constructor
  · refine ⟨fun _ _ _ => 0, ?_⟩
    change A.tensor = Tensor.localMap _ 0
    rw [h, Tensor.localMap_zero]
  · refine ⟨fun _ _ _ => 0, ?_⟩
    change 0 = Tensor.localMap _ A.tensor
    rw [h]
    exact (Tensor.localMap_zero _).symm

theorem equivalent_add_comm (A B : Object k) : Equivalent (add A B) (add B A) :=
  equivalent_of_reindex _ _ (fun _ => Equiv.sumComm _ _) (Tensor.directSum_comm_reindex B.tensor A.tensor)

theorem equivalent_add_assoc (A B C : Object k) :
    Equivalent (add (add A B) C) (add A (add B C)) := by
  apply equivalent_symm
  exact equivalent_of_reindex (add A (add B C)) (add (add A B) C) (fun _ => Equiv.sumAssoc _ _ _)
    (Tensor.directSum_assoc_reindex A.tensor B.tensor C.tensor)

theorem equivalent_zero_add (A : Object k) : Equivalent (add (zero k) A) A :=
  equivalent_of_reindex _ _ (fun i => (Equiv.emptySum Empty (A.format.Coordinate i)).symm)
    (Tensor.directSum_zero_reindex A.tensor)

theorem equivalent_mul_comm (A B : Object k) : Equivalent (mul A B) (mul B A) := by
  apply equivalent_of_reindex _ _ (fun i => Equiv.prodComm _ _)
  funext x
  exact mul_comm _ _

theorem equivalent_mul_assoc (A B C : Object k) :
    Equivalent (mul (mul A B) C) (mul A (mul B C)) := by
  apply equivalent_symm
  apply equivalent_of_reindex _ _ (fun i => Equiv.prodAssoc _ _ _)
  funext x
  exact (mul_assoc _ _ _).symm

theorem equivalent_one_mul (A : Object k) : Equivalent (mul (one k) A) A := by
  apply equivalent_of_reindex _ _ (fun i => (Equiv.punitProd (A.format.Coordinate i)).symm)
  funext x
  exact one_mul _

theorem equivalent_zero_mul (A : Object k) : Equivalent (mul (zero k) A) (zero k) := by
  apply equivalent_of_zero
  funext x
  exact zero_mul _

theorem equivalent_add_mul (A B C : Object k) :
    Equivalent (mul (add A B) C) (add (mul A C) (mul B C)) := by
  apply equivalent_symm
  exact equivalent_of_reindex (add (mul A C) (mul B C)) (mul (add A B) C)
    (fun _ => Equiv.sumProdDistrib _ _ _) (Tensor.directSum_product_reindex A.tensor B.tensor C.tensor)

theorem equivalent_nat_zero : Equivalent (nat k 0) (zero k) := by
  apply equivalent_of_zero
  funext x
  simp [nat, Tensor.diagonal]

theorem equivalent_nat_one : Equivalent (nat k 1) (one k) := by
  apply equivalent_of_reindex (nat k 1) (one k) (fun _ => Equiv.ofUnique PUnit (Fin 1))
  funext x
  exact Tensor.diagonal_one _

theorem equivalent_nat_add [Nonempty (Fin k)] (m n : ℕ) :
    Equivalent (nat k (m + n)) (add (nat k m) (nat k n)) :=
  equivalent_of_reindex _ _ (fun _ => finSumFinEquiv) (Tensor.directSum_diagonal_reindex m n)

theorem rank_relabel (σ : Equiv.Perm (Fin k)) (A : Object k) :
    Tensor.rank (relabel σ A).tensor = Tensor.rank A.tensor :=
  Tensor.rank_relabel σ A.tensor

end Lemmata.TensorRank.TensorSemiring.Object

namespace Lemmata.TensorRank.TensorSemiring

variable {k : ℕ}

instance : Zero (Value k) := ⟨ofObject (Object.zero k)⟩
instance : One (Value k) := ⟨ofObject (Object.one k)⟩

instance : Add (Value k) := ⟨Quot.map₂ Object.add
  (fun A _ _ h => Object.equivalent_add (Object.equivalent_refl A) h)
  (fun _ _ C h => Object.equivalent_add h (Object.equivalent_refl C))⟩

instance : Mul (Value k) := ⟨Quot.map₂ Object.mul
  (fun A _ _ h => Object.equivalent_mul (Object.equivalent_refl A) h)
  (fun _ _ C h => Object.equivalent_mul h (Object.equivalent_refl C))⟩

@[simp] theorem ofObject_zero : ofObject (Object.zero k) = (0 : Value k) := rfl
@[simp] theorem ofObject_one : ofObject (Object.one k) = (1 : Value k) := rfl
@[simp] theorem ofObject_add (A B : Object k) : ofObject (Object.add A B) = ofObject A + ofObject B := rfl
@[simp] theorem ofObject_mul (A B : Object k) : ofObject (Object.mul A B) = ofObject A * ofObject B := rfl

theorem value_add_zero (a : Value k) : a + 0 = a := by
  refine Quot.inductionOn a (fun A => ?_)
  exact Quot.sound (Object.equivalent_trans (Object.equivalent_add_comm A (Object.zero k))
    (Object.equivalent_zero_add A))

theorem value_mul_one (a : Value k) : a * 1 = a := by
  refine Quot.inductionOn a (fun A => ?_)
  exact Quot.sound (Object.equivalent_trans (Object.equivalent_mul_comm A (Object.one k))
    (Object.equivalent_one_mul A))

theorem value_mul_zero (a : Value k) : a * 0 = 0 := by
  refine Quot.inductionOn a (fun A => ?_)
  exact Quot.sound (Object.equivalent_trans (Object.equivalent_mul_comm A (Object.zero k))
    (Object.equivalent_zero_mul A))

instance : CommSemiring (Value k) where
  add := (· + ·)
  zero := 0
  mul := (· * ·)
  one := 1
  nsmul := nsmulRec
  natCast n := nsmulRec n 1
  natCast_zero := rfl
  natCast_succ _ := rfl
  add_assoc a b c := Quot.inductionOn a fun A => Quot.inductionOn b fun B =>
    Quot.inductionOn c fun C => Quot.sound (Object.equivalent_add_assoc A B C)
  add_comm a b := Quot.inductionOn a fun A => Quot.inductionOn b fun B =>
    Quot.sound (Object.equivalent_add_comm A B)
  zero_add a := Quot.inductionOn a fun A => Quot.sound (Object.equivalent_zero_add A)
  add_zero := value_add_zero
  mul_assoc a b c := Quot.inductionOn a fun A => Quot.inductionOn b fun B =>
    Quot.inductionOn c fun C => Quot.sound (Object.equivalent_mul_assoc A B C)
  mul_comm a b := Quot.inductionOn a fun A => Quot.inductionOn b fun B =>
    Quot.sound (Object.equivalent_mul_comm A B)
  one_mul a := Quot.inductionOn a fun A => Quot.sound (Object.equivalent_one_mul A)
  mul_one := value_mul_one
  zero_mul a := Quot.inductionOn a fun A => Quot.sound (Object.equivalent_zero_mul A)
  mul_zero := value_mul_zero
  right_distrib a b c := Quot.inductionOn a fun A => Quot.inductionOn b fun B =>
    Quot.inductionOn c fun C => Quot.sound (Object.equivalent_add_mul A B C)
  left_distrib a b c := by
    refine Quot.inductionOn a (fun A => Quot.inductionOn b (fun B => Quot.inductionOn c (fun C => ?_)))
    exact Quot.sound (Object.equivalent_trans (Object.equivalent_mul_comm A (Object.add B C))
      (Object.equivalent_trans (Object.equivalent_add_mul B C A)
        (Object.equivalent_add (Object.equivalent_mul_comm B A) (Object.equivalent_mul_comm C A))))

@[simp] theorem ofObject_nat [Nonempty (Fin k)] (n : ℕ) :
    ofObject (Object.nat k n) = (n : Value k) := by
  induction n with
  | zero => exact Quot.sound Object.equivalent_nat_zero
  | succ n ih =>
      rw [Nat.cast_succ, ← ih, ← ofObject_one, ← ofObject_add]
      exact Quot.sound (Object.equivalent_trans (Object.equivalent_nat_add n 1)
        (Object.equivalent_add (Object.equivalent_refl _) Object.equivalent_nat_one))

def Rel (a b : Value k) : Prop :=
  Quot.liftOn₂ a b Object.Rel
    (fun _ _ _ h => propext ⟨fun g => g.trans h.1, fun g => g.trans h.2⟩)
    (fun _ _ _ h => propext ⟨fun g => h.2.trans g, fun g => h.1.trans g⟩)

@[simp] theorem rel_ofObject (A B : Object k) : Rel (ofObject A) (ofObject B) ↔ Object.Rel A B := Iff.rfl

def rank (a : Value k) : ℕ :=
  Quot.liftOn a (fun A => Tensor.rank A.tensor)
    (fun _ _ h => Nat.le_antisymm h.1.rank_le h.2.rank_le)

@[simp] theorem rank_ofObject (A : Object k) : rank (ofObject A) = Tensor.rank A.tensor := rfl

@[simp] theorem rank_zero : rank (0 : Value k) = 0 := Tensor.rank_zero

theorem ofObject_eq_zero (A : Object k) : ofObject A = 0 ↔ A.tensor = 0 := by
  constructor
  · intro h
    have hr := congrArg rank h
    rw [rank_ofObject, rank_zero, Tensor.rank_eq_zero_iff] at hr
    exact hr
  · intro h
    exact Quot.sound (Object.equivalent_of_zero A h)

theorem rel_refl (a : Value k) : Rel a a :=
  Quot.inductionOn a fun A => Object.rel_refl A

theorem rel_trans {a b c : Value k} (h : Rel a b) (g : Rel b c) : Rel a c := by
  revert h g
  refine Quot.inductionOn a (fun A => Quot.inductionOn b (fun B => Quot.inductionOn c (fun C => ?_)))
  exact fun h g => Object.rel_trans h g

theorem rel_add {a b c d : Value k} (h : Rel a b) (g : Rel c d) : Rel (a + c) (b + d) := by
  revert h g
  refine Quot.inductionOn a (fun A => Quot.inductionOn b (fun B =>
    Quot.inductionOn c (fun C => Quot.inductionOn d (fun D => ?_))))
  exact fun h g => Object.rel_add h g

theorem rel_mul {a b c d : Value k} (h : Rel a b) (g : Rel c d) : Rel (a * c) (b * d) := by
  revert h g
  refine Quot.inductionOn a (fun A => Quot.inductionOn b (fun B =>
    Quot.inductionOn c (fun C => Quot.inductionOn d (fun D => ?_))))
  exact fun h g => Object.rel_mul h g

theorem zero_rel [Nonempty (Fin k)] (a : Value k) : Rel 0 a := by
  refine Quot.inductionOn a (fun A => ?_)
  refine ⟨fun _ _ _ => 0, ?_⟩
  funext x
  exact Empty.elim (x (Classical.arbitrary (Fin k)))

@[simp] theorem ofTensor_zero {V : Fin k → Type} [∀ i, Fintype (V i)] :
    ofTensor (0 : Tensor ℂ (Fin k) V) = 0 :=
  (ofObject_eq_zero _).mpr rfl

@[simp] theorem ofTensor_product {V W : Fin k → Type} [∀ i, Fintype (V i)] [∀ i, Fintype (W i)]
    (S : Tensor ℂ (Fin k) V) (T : Tensor ℂ (Fin k) W) :
    ofTensor (Tensor.product S T) = ofTensor S * ofTensor T := rfl

@[simp] theorem ofTensor_reindex {V W : Fin k → Type} [∀ i, Fintype (V i)] [∀ i, Fintype (W i)]
    (e : ∀ i, W i ≃ V i) (T : Tensor ℂ (Fin k) V) :
    ofTensor (Tensor.reindex (fun i => e i) T) = ofTensor T := by
  exact (Quot.sound (Object.equivalent_of_reindex
    ⟨⟨V, fun _ => inferInstance⟩, T⟩
    ⟨⟨W, fun _ => inferInstance⟩, Tensor.reindex (fun i => e i) T⟩ e rfl)).symm

@[simp] theorem rel_ofTensor {V W : Fin k → Type} [∀ i, Fintype (V i)] [∀ i, Fintype (W i)]
    (S : Tensor ℂ (Fin k) V) (T : Tensor ℂ (Fin k) W) :
    Rel (ofTensor S) (ofTensor T) ↔ Tensor.Restricts S T := Iff.rfl

end Lemmata.TensorRank.TensorSemiring
