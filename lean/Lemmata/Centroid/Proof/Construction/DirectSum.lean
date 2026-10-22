module

public import Lemmata.Centroid.Proof.Construction.Relabel
public import Lemmata.Centroid.Proof.Construction.LowerBound
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Tensor

noncomputable section

variable {F α β : Type*} [Field F] [Fintype α] [Fintype β]

def leftBlock (T : Tensor F (Fin 3) (fun _ => α)) : Tensor F (Fin 3) (fun _ => α ⊕ β) :=
  fun x => match x 0, x 1, x 2 with
    | Sum.inl a, Sum.inl b, Sum.inl c => T ![a, b, c]
    | _, _, _ => 0

def directSum (T : Tensor F (Fin 3) (fun _ => α))
    (S : Tensor F (Fin 3) (fun _ => β)) : Tensor F (Fin 3) (fun _ => α ⊕ β) :=
  leftBlock T + restrict (fun _ => Sum.swap) (leftBlock S)

omit [Fintype α] in
theorem vec_three (x : Fin 3 → α) : ![x 0, x 1, x 2] = x := by
  funext i
  fin_cases i <;> rfl

omit [Fintype α] [Fintype β] in
theorem leftBlock_simple (u : Fin 3 → α → F) :
    leftBlock (β := β) (simple u) = simple (fun i => Sum.elim (u i) (fun _ => 0)) := by
  ext x
  simp only [leftBlock, simple, Fin.prod_univ_three, Lemmata.TensorRank.Tensor.pure]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> simp

omit [Fintype α] [Fintype β] in
theorem leftBlock_sum {J : Type*} [Fintype J]
    (T : J → Tensor F (Fin 3) (fun _ => α)) :
    leftBlock (β := β) (∑ j, T j) = ∑ j, leftBlock (T j) := by
  ext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp [leftBlock, h0, h1, h2]

omit [Fintype α] in
@[simp] theorem update_three_zero [DecidableEq (Fin 3)] (a b c d : α) :
    Function.update ![a, b, c] (0 : Fin 3) d = ![d, b, c] := by
  ext i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
  · exact Function.update_self _ _ _
  · exact Function.update_of_ne (fun h => (by decide : (1 : ℕ) ≠ 0) (congrArg Fin.val h)) _ _
  · exact Function.update_of_ne (fun h => (by decide : (2 : ℕ) ≠ 0) (congrArg Fin.val h)) _ _

omit [Fintype α] in
@[simp] theorem update_three_one [DecidableEq (Fin 3)] (a b c d : α) :
    Function.update ![a, b, c] (1 : Fin 3) d = ![a, d, c] := by
  ext i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
  · exact Function.update_of_ne (fun h => (by decide : (0 : ℕ) ≠ 1) (congrArg Fin.val h)) _ _
  · exact Function.update_self _ _ _
  · exact Function.update_of_ne (fun h => (by decide : (2 : ℕ) ≠ 1) (congrArg Fin.val h)) _ _

omit [Fintype α] in
@[simp] theorem update_three_two [DecidableEq (Fin 3)] (a b c d : α) :
    Function.update ![a, b, c] (2 : Fin 3) d = ![a, b, d] := by
  ext i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
  · exact Function.update_of_ne (fun h => (by decide : (0 : ℕ) ≠ 2) (congrArg Fin.val h)) _ _
  · exact Function.update_of_ne (fun h => (by decide : (1 : ℕ) ≠ 2) (congrArg Fin.val h)) _ _
  · exact Function.update_self _ _ _

omit [Fintype α] [Fintype β] in
theorem RankAtMost.leftBlock {T : Tensor F (Fin 3) (fun _ => α)} {r : ℕ}
    (hT : RankAtMost T r) : RankAtMost (Tensor.leftBlock (β := β) T) r := by
  obtain ⟨u, rfl⟩ := hT
  refine ⟨fun q i => Sum.elim (u q i) (fun _ => 0), ?_⟩
  simp only [leftBlock_sum, leftBlock_simple]

omit [Fintype α] [Fintype β] in
theorem RationalBorderRankAtMost.leftBlock {T : Tensor F (Fin 3) (fun _ => α)} {r : ℕ}
    (hT : RationalBorderRankAtMost T r) :
    RationalBorderRankAtMost (Tensor.leftBlock (β := β) T) r := by
  obtain ⟨A⟩ := hT
  refine ⟨⟨Tensor.leftBlock A.family, A.rank_bound.leftBlock, ?_, ?_⟩⟩
  · intro x
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
      simp only [Tensor.leftBlock, h0, h1, h2] <;>
      first | exact A.regular _ | exact RationalFunction.regular_zero
  · intro x
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
      simp only [Tensor.leftBlock, h0, h1, h2] <;>
      first | exact A.value _ | simp

omit [Fintype α] [Fintype β] in
theorem RationalBorderRankAtMost.directSum
    {T : Tensor F (Fin 3) (fun _ => α)} {S : Tensor F (Fin 3) (fun _ => β)} {r s : ℕ}
    (hT : RationalBorderRankAtMost T r) (hS : RationalBorderRankAtMost S s) :
    RationalBorderRankAtMost (Tensor.directSum T S) (r + s) :=
  hT.leftBlock.add (hS.leftBlock.restrict (fun _ => Sum.swap))

theorem contraction_directSum_left
    (T : Tensor F (Fin 3) (fun _ => α)) (S : Tensor F (Fin 3) (fun _ => β))
    (i : Fin 3) (f : α ⊕ β → F) (x : Fin 3 → α) :
    contraction (directSum T S) i f (fun j => Sum.inl (x j)) =
      contraction T i (fun a => f (Sum.inl a)) x := by
  conv_rhs => rw [← vec_three x]
  fin_cases i <;>
    simp [contraction_apply, Fintype.sum_sum_type, directSum, leftBlock, restrict]

theorem contraction_directSum_right
    (T : Tensor F (Fin 3) (fun _ => α)) (S : Tensor F (Fin 3) (fun _ => β))
    (i : Fin 3) (f : α ⊕ β → F) (x : Fin 3 → β) :
    contraction (directSum T S) i f (fun j => Sum.inr (x j)) =
      contraction S i (fun a => f (Sum.inr a)) x := by
  conv_rhs => rw [← vec_three x]
  fin_cases i <;>
    simp [contraction_apply, Fintype.sum_sum_type, directSum, leftBlock, restrict]

theorem Concise.directSum
    {T : Tensor F (Fin 3) (fun _ => α)} {S : Tensor F (Fin 3) (fun _ => β)}
    (hT : Concise T) (hS : Concise S) : Concise (Tensor.directSum T S) := by
  intro i f g h
  have hl : (fun a => f (Sum.inl a)) = (fun a => g (Sum.inl a)) := hT i (by
    ext x
    simpa only [contraction_directSum_left] using congrFun h (fun j => Sum.inl (x j)))
  have hr : (fun a => f (Sum.inr a)) = (fun a => g (Sum.inr a)) := hS i (by
    ext x
    simpa only [contraction_directSum_right] using congrFun h (fun j => Sum.inr (x j)))
  ext a
  cases a with
  | inl a => exact congrFun hl a
  | inr a => exact congrFun hr a

def blockDiagonal (A : Matrix α α F) (B : Matrix β β F) : Matrix (α ⊕ β) (α ⊕ β) F :=
  fun r c => match r, c with
    | Sum.inl a, Sum.inl b => A a b
    | Sum.inr a, Sum.inr b => B a b
    | _, _ => 0

theorem legAction_directSum
    (T : Tensor F (Fin 3) (fun _ => α)) (S : Tensor F (Fin 3) (fun _ => β))
    (A : Matrix α α F) (B : Matrix β β F) (i : Fin 3) :
    legAction (directSum T S) i (blockDiagonal A B) =
      directSum (legAction T i A) (legAction S i B) := by
  ext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> fin_cases i <;>
    simp [legAction_apply, Fintype.sum_sum_type, directSum, leftBlock, restrict,
      blockDiagonal, h0, h1, h2]

def centroidDirectSum (T : Tensor F (Fin 3) (fun _ => α))
    (S : Tensor F (Fin 3) (fun _ => β)) :
    (centroid T × centroid S) →ₗ[F] centroid (directSum T S) where
  toFun A := ⟨fun i => blockDiagonal (A.1.val i) (A.2.val i), fun i j => by
    rw [legAction_directSum, legAction_directSum, A.1.property i j, A.2.property i j]⟩
  map_add' A B := by
    apply Subtype.ext
    funext i r c
    cases r <;> cases c <;> simp [blockDiagonal]
  map_smul' c A := by
    apply Subtype.ext
    funext i r s
    cases r <;> cases s <;> simp [blockDiagonal]

theorem centroidDirectSum_injective (T : Tensor F (Fin 3) (fun _ => α))
    (S : Tensor F (Fin 3) (fun _ => β)) : Function.Injective (centroidDirectSum T S) := by
  intro A B h
  apply Prod.ext
  · apply Subtype.ext
    funext i r c
    exact congrArg (fun C : centroid (directSum T S) => C.val i (Sum.inl r) (Sum.inl c)) h
  · apply Subtype.ext
    funext i r c
    exact congrArg (fun C : centroid (directSum T S) => C.val i (Sum.inr r) (Sum.inr c)) h

theorem finrank_centroid_directSum (T : Tensor F (Fin 3) (fun _ => α))
    (S : Tensor F (Fin 3) (fun _ => β)) :
    Module.finrank F (centroid T) + Module.finrank F (centroid S) ≤
      Module.finrank F (centroid (directSum T S)) := by
  simpa only [Module.finrank_prod] using
    LinearMap.finrank_le_finrank_of_injective (centroidDirectSum_injective T S)

end

end Lemmata.Centroid.Tensor
