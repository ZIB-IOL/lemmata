module

public import Lemmata.TensorRank.Proof.PolynomialProduct

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.PolynomialProduct

variable {J : Type*} [Fintype J]

def assemble {V : Bool ⊕ J → Type*} (u : V (.inl false)) (v : V (.inl true))
    (x : ∀ j, V (.inr j)) : ∀ p, V p
  | .inl false => u
  | .inl true => v
  | .inr j => x j

def assignmentEquiv (V : Bool ⊕ J → Type*) :
    (∀ p, V p) ≃ V (.inl false) × V (.inl true) × (∀ j, V (.inr j)) where
  toFun x := (x (.inl false), x (.inl true), fun j => x (.inr j))
  invFun x := assemble x.1 x.2.1 x.2.2
  left_inv x := by funext p; rcases p with ⟨⟨⟩⟩ | j <;> rfl
  right_inv _ := rfl

omit [Fintype J] in
theorem assignmentEquiv_apply (V : Bool ⊕ J → Type*) (x : ∀ p, V p) :
    assignmentEquiv V x = (x (.inl false), x (.inl true), fun j => x (.inr j)) := rfl

def twoReaderKernel {R : Type*} [Zero R] [One R] {V W : Bool ⊕ J → Type*}
    (A : W (.inl false) → V (.inl false) → R)
    (B : W (.inl true) → V (.inl true) → R) (e : ∀ j, W (.inr j) → V (.inr j)) :
    ∀ p, W p → V p → R
  | .inl false => A
  | .inl true => B
  | .inr j => fun y v => if v = e j y then 1 else 0

theorem localMap_twoReaders {R : Type*} [CommSemiring R] {V W : Bool ⊕ J → Type*}
    [∀ p, Fintype (V p)] (A : W (.inl false) → V (.inl false) → R)
    (B : W (.inl true) → V (.inl true) → R) (e : ∀ j, W (.inr j) → V (.inr j))
    (T : Tensor R (Bool ⊕ J) V) (x : ∀ p, W p) :
    Tensor.localMap (twoReaderKernel A B e) T x =
      ∑ u, ∑ v, A (x (.inl false)) u * B (x (.inl true)) v *
        T (assemble u v (fun j => e j (x (.inr j)))) := by
  let : DecidableEq (Bool ⊕ J) := Classical.decEq _
  have h := Fintype.sum_equiv (assignmentEquiv V)
    (fun z => (∏ p, twoReaderKernel A B e p (x p) (z p)) * T z)
    (fun z => A (x (.inl false)) z.1 * B (x (.inl true)) z.2.1 *
      ((∏ j, if z.2.2 j = e j (x (.inr j)) then 1 else 0) *
        T (assemble z.1 z.2.1 z.2.2)))
    (fun z => by
      have hz : assemble (z (.inl false)) (z (.inl true)) (fun j => z (.inr j)) = z := by
        funext p
        rcases p with ⟨⟨⟩⟩ | j <;> rfl
      simp only [Fintype.prod_sum_type, Fintype.prod_bool, twoReaderKernel, assignmentEquiv_apply]
      rw [hz]
      simp only [mul_assoc, mul_comm, mul_left_comm]
      congr 3)
  refine h.trans ?_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  dsimp only
  rw [← Finset.mul_sum]
  congr 1
  simp only [Fintype.prod_boole, ← funext_iff]
  simp

def quotientVector (b : ℕ) (hb : 2 ≤ b) (i : Fin (b + 1)) : Fin b × Fin 2 :=
  if h : i.val = 0 then (⟨0, by omega⟩, 1)
  else (⟨i.val - 1, by have := i.isLt; omega⟩, 0)

def kernelPositive (b : ℕ) (i : Fin (b - 1)) : Fin b × Fin 2 :=
  (⟨i.val + 1, by have := i.isLt; omega⟩, 1)

def kernelNegative (b : ℕ) (i : Fin (b - 1)) : Fin b × Fin 2 :=
  (⟨i.val, by have := i.isLt; omega⟩, 0)

def concaveInput (b : ℕ) (hb : 2 ≤ b) :
    (Fin (b + 1) ⊕ Fin (b - 1)) → (Fin b × Fin 2) → Polynomial ℂ
  | .inl i, u => Polynomial.X * if u = quotientVector b hb i then 1 else 0
  | .inr i, u => (if u = kernelPositive b i then 1 else 0) -
      (if u = kernelNegative b i then 1 else 0)

def concaveOutput (a : J → ℕ) (b : ℕ) :
    (Fin (b + degree a + 1) ⊕ Fin ((b - 1) + degree a)) →
      (Fin (b + degree a) × Fin 2) → Polynomial ℂ
  | .inl z, v => if v.2 = 0 then (if v.1.val + 1 = z.val then 1 else 0)
      else (if v.1.val = z.val then 1 else 0)
  | .inr z, v => Polynomial.X * if v.2 = 1 ∧ v.1.val = z.val + 1 then 1 else 0

def concaveKernel (a : J → ℕ) (b : ℕ) (hb : 2 ≤ b) :
    ∀ p, ConcaveCoordinate a b p → SelectedCoordinate a b p × BitCoordinate p → Polynomial ℂ :=
  twoReaderKernel (concaveInput b hb) (concaveOutput a b) (fun _ y => (y, PUnit.unit))

def outputIndex (a : J → ℕ) (b : ℕ) (u : Fin b) (x : ∀ j, Fin (a j)) : Fin (b + degree a) :=
  ⟨u.val + ∑ j, (x j).val, by have := input_sum_le a x; have := u.isLt; omega⟩

theorem amplified_value (a : J → ℕ) (b : ℕ) (u : Fin b × Fin 2)
    (v : Fin (b + degree a) × Fin 2) (x : ∀ j, Fin (a j)) :
    amplified a b (assemble u v (fun j => (x j, PUnit.unit))) =
      if v = (outputIndex a b u.1 x, u.2) then 1 else 0 := by
  have he : u.1.val + (∑ j, (x j).val) = v.1.val ↔ v.1 = outputIndex a b u.1 x := by
    exact ⟨fun h => Fin.ext h.symm, fun h => by rw [h]; rfl⟩
  simp only [amplified, Tensor.product, selected, pairing, assemble, he]
  by_cases h₁ : v.1 = outputIndex a b u.1 x
  · by_cases h₂ : v.2 = u.2
    · simp [h₁, h₂, Prod.ext_iff]
    · have h₂' := Ne.symm h₂
      simp [h₁, h₂, h₂', Prod.ext_iff]
  · simp [h₁, Prod.ext_iff]

theorem concave_polynomialMap (a : J → ℕ) (b : ℕ) (hb : 2 ≤ b)
    (x : ∀ p, ConcaveCoordinate a b p) :
    Tensor.polynomialMap (concaveKernel a b hb) (amplified a b) x =
      ∑ u : Fin b × Fin 2, concaveInput b hb (x (.inl false)) u *
        concaveOutput a b (x (.inl true))
          (outputIndex a b u.1 (fun j => x (.inr j)), u.2) := by
  rw [Tensor.polynomialMap, concaveKernel, localMap_twoReaders]
  apply Finset.sum_congr rfl
  intro u _
  simp_rw [amplified_value]
  simp

theorem concave_polynomialMap_split (a : J → ℕ) (b : ℕ) (hb : 2 ≤ b)
    (x : ∀ p, ConcaveCoordinate a b p) :
    Tensor.polynomialMap (concaveKernel a b hb) (amplified a b) x =
      match x (.inl false) with
      | .inl y => Polynomial.X * concaveOutput a b (x (.inl true))
          (outputIndex a b (quotientVector b hb y).1 (fun j => x (.inr j)),
            (quotientVector b hb y).2)
      | .inr y => concaveOutput a b (x (.inl true))
          (outputIndex a b (kernelPositive b y).1 (fun j => x (.inr j)), (kernelPositive b y).2) -
          concaveOutput a b (x (.inl true))
          (outputIndex a b (kernelNegative b y).1 (fun j => x (.inr j)), (kernelNegative b y).2) := by
  rw [concave_polynomialMap]
  cases hy : x (.inl false) with
  | inl y =>
    simp only [concaveInput, mul_assoc]
    rw [← Finset.mul_sum]
    simp
  | inr y =>
    simp only [concaveInput, sub_mul, Finset.sum_sub_distrib]
    simp

private theorem quotient_output (a : J → ℕ) (b : ℕ) (hb : 2 ≤ b)
    (y : Fin (b + 1)) (z : Fin (b + degree a + 1)) (x : ∀ j, Fin (a j)) :
    concaveOutput a b (.inl z) (outputIndex a b (quotientVector b hb y).1 x,
      (quotientVector b hb y).2) = if y.val + (∑ j, (x j).val) = z.val then 1 else 0 := by
  by_cases hy : y.val = 0
  · simp [quotientVector, hy, concaveOutput, outputIndex]
  · simp only [quotientVector, hy, dite_false, concaveOutput, ite_true,
      outputIndex]
    apply if_congr _ rfl rfl
    have := y.isLt
    omega

private theorem kernel_output_quotient (a : J → ℕ) (b : ℕ)
    (y : Fin (b - 1)) (z : Fin (b + degree a + 1)) (x : ∀ j, Fin (a j)) :
    concaveOutput a b (.inl z) (outputIndex a b (kernelPositive b y).1 x, (kernelPositive b y).2) -
      concaveOutput a b (.inl z) (outputIndex a b (kernelNegative b y).1 x, (kernelNegative b y).2) = 0 := by
  simp [concaveOutput, kernelPositive, kernelNegative, outputIndex,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem kernel_output_kernel (a : J → ℕ) (b : ℕ)
    (y : Fin (b - 1)) (z : Fin ((b - 1) + degree a)) (x : ∀ j, Fin (a j)) :
    concaveOutput a b (.inr z) (outputIndex a b (kernelPositive b y).1 x, (kernelPositive b y).2) -
      concaveOutput a b (.inr z) (outputIndex a b (kernelNegative b y).1 x, (kernelNegative b y).2) =
        Polynomial.X * if y.val + (∑ j, (x j).val) = z.val then 1 else 0 := by
  simp only [concaveOutput, kernelPositive, kernelNegative, outputIndex, Fin.reduceEq,
    true_and, false_and, ite_false, mul_zero, sub_zero]
  congr 1
  apply if_congr _ rfl rfl
  omega

theorem concave_leading (a : J → ℕ) (b : ℕ) (hb : 2 ≤ b) :
    Tensor.Leading (Tensor.polynomialMap (concaveKernel a b hb) (amplified a b)) 1
      (concave a b) := by
  have he (n : ℕ) (hn : n ≤ 1) (x : ∀ p, ConcaveCoordinate a b p) :
      (Tensor.polynomialMap (concaveKernel a b hb) (amplified a b) x).coeff n =
        if n = 1 then concave a b x else 0 := by
    have hn2 : n ≠ 2 := by omega
    rw [concave_polynomialMap_split]
    cases hy : x (.inl false) with
    | inl y =>
      cases hz : x (.inl true) with
      | inl z =>
        dsimp only
        rw [quotient_output]
        simp only [concave, Finset.sum_apply, Fintype.sum_bool, concaveSector, hy, hz]
        split_ifs <;> subst_vars <;> simp_all [Polynomial.coeff_X, eq_comm]
      | inr z =>
        dsimp only
        simp only [concave, Finset.sum_apply, Fintype.sum_bool, concaveSector, hy, hz, concaveOutput]
        split_ifs <;> subst_vars <;> norm_num [← pow_two, Polynomial.coeff_X_pow, hn2]
    | inr y =>
      cases hz : x (.inl true) with
      | inl z =>
        dsimp only
        rw [kernel_output_quotient]
        simp [concave, concaveSector, hy, hz]
      | inr z =>
        dsimp only
        rw [kernel_output_kernel]
        simp only [concave, Finset.sum_apply, Fintype.sum_bool, concaveSector, hy, hz]
        split_ifs <;> subst_vars <;> simp_all [Polynomial.coeff_X, eq_comm]
  constructor
  · funext x
    exact (he 1 le_rfl x).trans (ite_eq_left rfl)
  · intro n hn
    funext x
    exact (he n (by omega) x).trans (ite_eq_right (by omega))

theorem concave_degenerates (a : J → ℕ) (b : ℕ) (hb : 2 ≤ b) :
    Tensor.Degenerates (concave a b) (amplified a b) :=
  ⟨concaveKernel a b hb, 1, concave_leading a b hb⟩

def sumLabel {A B : Type*} : A ⊕ B → Bool
  | .inl _ => false
  | .inr _ => true

theorem concaveSector_reads_input (a : J → ℕ) (b : ℕ) :
    Tensor.Reads (concaveSector a b) (.inl false) sumLabel := by
  intro q x hx
  cases q <;> cases hi : x (.inl false) <;> cases ho : x (.inl true) <;>
    simp_all [concaveSector, sumLabel]

theorem concaveSector_reads_output (a : J → ℕ) (b : ℕ) :
    Tensor.Reads (concaveSector a b) (.inl true) sumLabel := by
  intro q x hx
  cases q <;> cases hi : x (.inl false) <;> cases ho : x (.inl true) <;>
    simp_all [concaveSector, sumLabel]

def plusEmbedding (a : J → ℕ) (b : ℕ) (p : Bool ⊕ J) :
    SelectedCoordinate a (b + 1) p → ConcaveCoordinate a b p :=
  match p with
  | .inl false => Sum.inl
  | .inl true => fun z => .inl (Fin.cast (by omega : (b + 1) + degree a = b + degree a + 1) z)
  | .inr _ => id

def minusEmbedding (a : J → ℕ) (b : ℕ) (p : Bool ⊕ J) :
    SelectedCoordinate a (b - 1) p → ConcaveCoordinate a b p :=
  match p with
  | .inl false => Sum.inr
  | .inl true => Sum.inr
  | .inr _ => id

theorem plusSector_restricts (a : J → ℕ) (b : ℕ) :
    Tensor.Restricts (selected a (b + 1)) (concaveSector a b false) := by
  refine ⟨fun p y v => if v = plusEmbedding a b p y then 1 else 0, ?_⟩
  rw [Tensor.localMap_select]
  funext x
  rfl

theorem minusSector_restricts (a : J → ℕ) (b : ℕ) :
    Tensor.Restricts (selected a (b - 1)) (concaveSector a b true) := by
  refine ⟨fun p y v => if v = minusEmbedding a b p y then 1 else 0, ?_⟩
  rw [Tensor.localMap_select]
  funext x
  rfl

end Lemmata.TensorRank.PolynomialProduct
