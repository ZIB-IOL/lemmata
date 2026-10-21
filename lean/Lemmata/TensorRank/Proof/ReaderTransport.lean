module

public import Lemmata.TensorRank.Proof.EqualSectors
public import Lemmata.TensorRank.Proof.Parties

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.Tensor

universe u v w z

variable {R : Type u} {I : Type v} {J : Type w} {V : I → Type z}

theorem Reads.relabel [Zero R] {C : Type*} (e : J ≃ I) (reader : J)
    {Z : C → Tensor R I V} {label : V (e reader) → C} (h : Reads Z (e reader) label) :
    Reads (fun q => relabel e (Z q)) reader label := by
  intro q x hx
  simpa using h q (Equiv.piCongrLeft V e x) hx

theorem relabel_sum [AddCommMonoid R] {C : Type*} [Fintype C]
    (e : J ≃ I) (Z : C → Tensor R I V) :
    relabel e (∑ c, Z c) = ∑ c, relabel e (Z c) := by
  funext x
  simp only [relabel, Finset.sum_apply]

theorem relabel_product [Mul R] {W : I → Type*} (e : J ≃ I)
    (T : Tensor R I V) (S : Tensor R I W) :
    relabel e (product T S) = product (relabel e T) (relabel e S) := by
  funext x
  have h₁ : (fun i => (Equiv.piCongrLeft (fun i => V i × W i) e x i).1) =
      Equiv.piCongrLeft V e (fun j => (x j).1) := by
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    simp
  have h₂ : (fun i => (Equiv.piCongrLeft (fun i => V i × W i) e x i).2) =
      Equiv.piCongrLeft W e (fun j => (x j).2) := by
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    simp
  change T _ * S _ = T _ * S _
  rw [h₁, h₂]

theorem relabel_wordTensor [CommSemiring R] {C : Type*} {N : ℕ}
    (e : J ≃ I) (Z : C → Tensor R I V) (w : Fin N → C) :
    relabel e (wordTensor Z w) = wordTensor (fun c => relabel e (Z c)) w := by
  funext x
  simp only [relabel, wordTensor, indexedProduct]
  apply Finset.prod_congr rfl
  intro j _
  congr 1
  funext i
  obtain ⟨p, rfl⟩ := e.surjective i
  simp

def relabelContextCoordinate {W : J → Type*} (e : J ≃ I) (j : J) :
    (W j × V (e j)) ≃ (W (e.symm (e j)) × V (e j)) :=
  Equiv.prodCongr (Equiv.cast (congrArg W (e.symm_apply_apply j).symm)) (Equiv.refl _)

theorem relabel_context_reindex [Mul R] {W : J → Type*}
    (e : J ≃ I) (S : Tensor R J W) (T : Tensor R I V) :
    reindex (fun j => relabelContextCoordinate e j)
      (relabel e (product (relabel e.symm S) T)) = product S (relabel e T) := by
  funext x
  let y := Equiv.piCongrLeft (fun i => W (e.symm i) × V i) e
    (fun j => relabelContextCoordinate e j (x j))
  have hy (j : J) : y (e j) = relabelContextCoordinate e j (x j) := by simp [y]
  have h₁ : Equiv.piCongrLeft W e.symm (fun i => (y i).1) = fun j => (x j).1 := by
    funext j
    rw [Equiv.piCongrLeft_apply_eq_cast]
    simp [hy, relabelContextCoordinate]
  have h₂ : (fun i => (y i).2) = Equiv.piCongrLeft V e (fun j => (x j).2) := by
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    simp [hy, relabelContextCoordinate]
  change S (Equiv.piCongrLeft W e.symm (fun i => (y i).1)) * T (fun i => (y i).2) =
    S (fun j => (x j).1) * T (Equiv.piCongrLeft V e (fun j => (x j).2))
  rw [h₁, h₂]

theorem asymptoticRank_relabel_context [CommSemiring R] [Fintype I] [Fintype J]
    {W : J → Type*} [∀ i, Fintype (V i)] [∀ j, Fintype (W j)]
    (e : J ≃ I) (S : Tensor R J W) (T : Tensor R I V) :
    asymptoticRank (product (relabel e.symm S) T) =
      asymptoticRank (product S (relabel e T)) := by
  symm
  rw [← relabel_context_reindex e S T, asymptoticRank_reindex]
  exact asymptoticRank_relabel e (product (relabel e.symm S) T)

end Lemmata.TensorRank.Tensor

namespace Lemmata.TensorRank.Separation

def markedReaders {k : ℕ} (a b : Fin k) (hab : a ≠ b) :
    Bool ≃ {i : Fin k // i = a ∨ i = b} where
  toFun
    | false => ⟨a, Or.inl rfl⟩
    | true => ⟨b, Or.inr rfl⟩
  invFun x := if x.val = a then false else true
  left_inv x := by cases x <;> simp [hab.symm]
  right_inv x := by
    rcases x with ⟨x, hx⟩
    rcases hx with rfl | rfl <;> simp [hab.symm]

def readerEquiv {k : ℕ} (a b : Fin k) (hab : a ≠ b) : Party (k - 2) ≃ Fin k := by
  have hc : Fintype.card {i : Fin k // i = a ∨ i = b} = 2 := by
    simpa using (Fintype.card_congr (markedReaders a b hab)).symm
  have hn : Fintype.card {i : Fin k // ¬ (i = a ∨ i = b)} = k - 2 := by
    rw [Fintype.card_subtype_compl, hc, Fintype.card_fin]
  exact (Equiv.sumCongr (markedReaders a b hab) (Fintype.equivFinOfCardEq hn).symm).trans
    (Equiv.sumCompl (fun i : Fin k => i = a ∨ i = b))

theorem readerEquiv_left {k : ℕ} (a b : Fin k) (hab : a ≠ b) :
    readerEquiv a b hab (.inl false) = a := rfl

theorem readerEquiv_right {k : ℕ} (a b : Fin k) (hab : a ≠ b) :
    readerEquiv a b hab (.inl true) = b := rfl

theorem fixed_type_bound_readers {k : ℕ} (hk : 2 ≤ k) (a b : Fin k) (hab : a ≠ b)
    {C : Type*} [Fintype C] {N : ℕ} {V U : Fin k → Type*}
    [∀ i, Fintype (V i)] [∀ i, Fintype (U i)]
    (Z : C → Tensor ℂ (Fin k) V) (H : Tensor ℂ (Fin k) U)
    {left : V a → C} {right : V b → C}
    (hleft : Tensor.Reads Z a left) (hright : Tensor.Reads Z b right)
    {h : C → Fin (N + 1)} (base : Types.Words h) :
    Tensor.asymptoticRank (Tensor.product
      (Tensor.relabel (readerEquiv a b hab).symm (readerPairing (Fintype.card (Types.Words h))))
      (Tensor.product (Tensor.wordTensor Z base.val) H)) ≤
      ((k - 1 : ℕ) : ℝ) * Tensor.asymptoticRank (Tensor.product (Tensor.power (∑ c, Z c) N) H) := by
  let e := readerEquiv a b hab
  have hl : Tensor.Reads (fun c => Tensor.relabel e (Z c)) (.inl false) left :=
    Tensor.Reads.relabel e (.inl false) hleft
  have hr : Tensor.Reads (fun c => Tensor.relabel e (Z c)) (.inl true) right :=
    Tensor.Reads.relabel e (.inl true) hright
  have hb := fixed_type_bound_context (fun c => Tensor.relabel e (Z c)) (Tensor.relabel e H) hl hr base
  have hs : Tensor.product (Tensor.power (∑ c, Tensor.relabel e (Z c)) N) (Tensor.relabel e H) =
      Tensor.relabel e (Tensor.product (Tensor.power (∑ c, Z c) N) H) := by
    rw [Tensor.relabel_product, Tensor.relabel_power, Tensor.relabel_sum]
  rw [hs] at hb
  rw [Tensor.asymptoticRank_relabel e (Tensor.product (Tensor.power (∑ c, Z c) N) H)] at hb
  have hdim : k - 2 + 1 = k - 1 := by omega
  rw [Tensor.asymptoticRank_relabel_context e (readerPairing (Fintype.card (Types.Words h)))
    (Tensor.product (Tensor.wordTensor Z base.val) H),
    Tensor.relabel_product e (Tensor.wordTensor Z base.val) H,
    Tensor.relabel_wordTensor e Z base.val]
  simpa only [hdim] using hb

end Lemmata.TensorRank.Separation
