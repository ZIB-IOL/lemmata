module

public import Lemmata.TensorRank.Proof.TensorSemiring
public import Lemmata.TensorRank.Proof.SpectrumAsymptotic

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.TensorSemiring

variable {k : ℕ}

def preorder (hk : 2 ≤ k) : Spectrum.StrassenPreorder (Value k) := by
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨1, by omega⟩
  letI : Nonempty (Fin k) := ⟨i⟩
  have hji : j ≠ i := by intro h; have := congrArg Fin.val h; dsimp [i, j] at this; omega
  refine
    { Rel := Rel
      refl := rel_refl
      trans := rel_trans
      zero_le := zero_rel
      nat_iff := ?_
      add := rel_add
      mul := rel_mul
      cofinal := ?_ }
  · intro m n
    rw [← ofObject_nat m, ← ofObject_nat n]
    change Tensor.Restricts (Tensor.diagonal (R := ℂ) (I := Fin k) m) (Tensor.diagonal n) ↔ m ≤ n
    constructor
    · intro h
      have hr := h.rank_le
      rwa [Tensor.rank_diagonal m i j hji, Tensor.rank_diagonal n i j hji] at hr
    · intro h
      exact (Tensor.rankLE_iff_restricts_diagonal _ _).mp ((Tensor.rankLE_diagonal m).mono h)
  · intro a b
    refine Quot.inductionOn a (fun A => Quot.inductionOn b (fun B => ?_))
    intro hb
    have hB : B.tensor ≠ 0 := fun h => hb ((ofObject_eq_zero B).mpr h)
    refine ⟨Tensor.rank A.tensor, ?_⟩
    rw [← ofObject_nat, ← ofObject_mul]
    change Tensor.Restricts A.tensor (Tensor.copies (Tensor.rank A.tensor) B.tensor)
    exact (Tensor.restricts_diagonal_rank A.tensor).trans (Tensor.diagonal_restricts_copies _ hB)

theorem preorder_oneLeNonzero (hk : 2 ≤ k) : (preorder hk).OneLeNonzero := by
  let : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  intro a
  refine Quot.inductionOn a (fun A => ?_)
  intro ha
  have hA : A.tensor ≠ 0 := fun h => ha ((ofObject_eq_zero A).mpr h)
  have h1 : ofObject (Object.nat k 1) = (1 : Value k) := by simpa only [Nat.cast_one] using ofObject_nat (k := k) 1
  change Rel 1 (ofObject A)
  rw [← h1]
  exact Tensor.diagonal_one_restricts hA

theorem preorder_rank_ofObject (hk : 2 ≤ k) (A : Object k) :
    (preorder hk).rank (ofObject A) = Tensor.rank A.tensor := by
  let : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  apply Nat.le_antisymm
  · apply ((preorder hk).rank_le_iff _ _).mpr
    rw [← ofObject_nat]
    exact Tensor.restricts_diagonal_rank A.tensor
  · apply (Tensor.rank_le_iff _ _).mpr
    apply (Tensor.rankLE_iff_restricts_diagonal _ _).mpr
    have h := (preorder hk).rel_rank (ofObject A)
    rwa [← ofObject_nat] at h

theorem power_cons_reindex {V : Fin k → Type} [∀ i, Fintype (V i)]
    (T : Tensor ℂ (Fin k) V) (n : ℕ) :
    Tensor.reindex (fun i => Fin.consEquiv (fun _ : Fin (n + 1) => V i))
      (Tensor.power T (n + 1)) = Tensor.product T (Tensor.power T n) := by
  funext x
  simp [Tensor.reindex, Tensor.power, Tensor.product, Fin.consEquiv, Fin.prod_univ_succ]

theorem Object.equivalent_power_zero (A : Object k) : Object.Equivalent (A.power 0) (Object.one k) := by
  apply Object.equivalent_of_reindex _ _ (fun i => Equiv.ofUnique PUnit (Fin 0 → A.format.Coordinate i))
  funext x
  simp [Tensor.reindex, Object.power, Tensor.power, Object.one]

theorem Object.equivalent_power_succ (A : Object k) (n : ℕ) :
    Object.Equivalent (A.power (n + 1)) (Object.mul A (A.power n)) :=
  Object.equivalent_of_reindex _ _
    (fun i => Fin.consEquiv (fun _ : Fin (n + 1) => A.format.Coordinate i))
    (power_cons_reindex A.tensor n)

@[simp] theorem ofObject_power (A : Object k) (n : ℕ) : ofObject (A.power n) = ofObject A ^ n := by
  induction n with
  | zero => exact Quot.sound (Object.equivalent_power_zero A)
  | succ n ih =>
      rw [pow_succ', ← ih, ← ofObject_mul]
      exact Quot.sound (Object.equivalent_power_succ A n)

@[simp] theorem ofTensor_power {V : Fin k → Type} [∀ i, Fintype (V i)]
    (T : Tensor ℂ (Fin k) V) (n : ℕ) : ofTensor (Tensor.power T n) = ofTensor T ^ n :=
  ofObject_power ⟨⟨V, fun _ => inferInstance⟩, T⟩ n

theorem preorder_asymptoticRank_ofObject (hk : 2 ≤ k) (A : Object k) :
    (preorder hk).asymptoticRank (ofObject A) = Tensor.asymptoticRank A.tensor := by
  unfold Spectrum.StrassenPreorder.asymptoticRank Tensor.asymptoticRank Tensor.rankRoot
  congr 1
  funext n
  rw [← ofObject_power, preorder_rank_ofObject]
  rfl

theorem preorder_asymptoticRank_ofTensor (hk : 2 ≤ k)
    {V : Fin k → Type} [∀ i, Fintype (V i)] (T : Tensor ℂ (Fin k) V) :
    (preorder hk).asymptoticRank (ofTensor T) = Tensor.asymptoticRank T :=
  preorder_asymptoticRank_ofObject hk _

@[simp] theorem ofTensor_diagonal [Nonempty (Fin k)] (n : ℕ) :
    ofTensor (Tensor.diagonal (R := ℂ) (I := Fin k) n) = (n : Value k) := ofObject_nat n

@[simp] theorem ofTensor_copies [Nonempty (Fin k)]
    {V : Fin k → Type} [∀ i, Fintype (V i)] (n : ℕ) (T : Tensor ℂ (Fin k) V) :
    ofTensor (Tensor.copies n T) = n * ofTensor T := by
  rw [Tensor.copies, ofTensor_product, ofTensor_diagonal]

end Lemmata.TensorRank.TensorSemiring
