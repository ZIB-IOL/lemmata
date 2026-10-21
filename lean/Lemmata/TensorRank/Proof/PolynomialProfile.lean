module

public import Lemmata.TensorRank.Proof.PolynomialConcavity
public import Lemmata.TensorRank.Proof.PolynomialTripling
public import Lemmata.TensorRank.Proof.PolynomialTransport

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace Lemmata.TensorRank.PolynomialProduct

abbrev Functional (P : Type*) :=
  ∀ {V : P → Type} [∀ p, Fintype (V p)], Tensor ℂ P V → ℝ

variable {J : Type} [Fintype J]

structure Functional.Laws (F : Functional (Bool ⊕ J)) : Prop where
  restricts {V W : Bool ⊕ J → Type} [∀ p, Fintype (V p)] [∀ p, Fintype (W p)]
    {S : Tensor ℂ (Bool ⊕ J) W} {T : Tensor ℂ (Bool ⊕ J) V} :
    Tensor.Restricts S T → F S ≤ F T
  degenerates {V W : Bool ⊕ J → Type} [∀ p, Fintype (V p)] [∀ p, Fintype (W p)]
    {S : Tensor ℂ (Bool ⊕ J) W} {T : Tensor ℂ (Bool ⊕ J) V} :
    Tensor.Degenerates S T → F S ≤ F T
  product {V W : Bool ⊕ J → Type} [∀ p, Fintype (V p)] [∀ p, Fintype (W p)]
    (S : Tensor ℂ (Bool ⊕ J) V) (T : Tensor ℂ (Bool ⊕ J) W) :
    F (Tensor.product S T) = F S * F T
  relabel {V : Bool ⊕ J → Type} [∀ p, Fintype (V p)]
    (e : Equiv.Perm (Bool ⊕ J)) (T : Tensor ℂ (Bool ⊕ J) V) :
    F (Tensor.relabel e T) = F T
  readerSum {C : Type} [Fintype C] {V : Bool ⊕ J → Type} [∀ p, Fintype (V p)]
    (Z : C → Tensor ℂ (Bool ⊕ J) V)
    (left : V (.inl false) → C) (right : V (.inl true) → C) :
    Tensor.Reads Z (.inl false) left → Tensor.Reads Z (.inl true) right →
      (∑ c, F (Z c)) ≤ F (∑ c, Z c)
  pairing : F (PolynomialProduct.pairing (J := J)) = 2

theorem selected_concavity {F : Functional (Bool ⊕ J)} (hF : Functional.Laws F)
    (a : J → ℕ) (b : ℕ) (hb : 2 ≤ b) :
    F (selected a (b - 1)) + F (selected a (b + 1)) ≤ 2 * F (selected a b) := by
  have hs := hF.readerSum (concaveSector a b) sumLabel sumLabel
    (concaveSector_reads_input a b) (concaveSector_reads_output a b)
  have hp := hF.restricts (plusSector_restricts a b)
  have hm := hF.restricts (minusSector_restricts a b)
  have hd := hF.degenerates (concave_degenerates a b hb)
  have ha : F (amplified a b) = 2 * F (selected a b) := by
    rw [amplified, hF.product, hF.pairing]
    ring
  change _ ≤ F (concave a b) at hs
  simp only [Fintype.sum_bool] at hs
  rw [ha] at hd
  linarith

theorem selected_tripling {F : Functional (Bool ⊕ J)} (hF : Functional.Laws F)
    (a : J → ℕ) (b : ℕ) :
    3 * F (selected a b) ≤ F (selected a (3 * b + degree a)) := by
  have hs := hF.readerSum (tripleSector a b) (inputLabel a b) (outputLabel a b)
    (tripleSector_reads_input a b) (tripleSector_reads_output a b)
  have hl := hF.restricts (leftSector_restricts a b)
  have hm := hF.restricts (middleSector_restricts a b)
  have hr := hF.restricts (rightSector_restricts a b)
  have hd := hF.degenerates (triple_degenerates a b)
  rw [hF.relabel] at hm
  simp only [Fin.sum_univ_three] at hs hd
  linarith

omit [Fintype J] in
theorem selected_value_relabel_tensor {K : Type} [Fintype K]
    {j : K} {F : Functional (Bool ⊕ Other j)} (hF : Functional.Laws F)
    (a : K → ℕ) (hj : 0 < a j) :
    F (selected (remaining a j) (a j)) = F (Tensor.relabel (inputPartyEquiv j) (tensor a)) := by
  exact le_antisymm (hF.restricts (selected_restricts_relabel_tensor a j hj))
    (hF.restricts (relabel_tensor_restricts_selected a j hj))

end Lemmata.TensorRank.PolynomialProduct
