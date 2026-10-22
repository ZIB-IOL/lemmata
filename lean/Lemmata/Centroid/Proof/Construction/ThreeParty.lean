module

public import Lemmata.Centroid.Proof.Construction.Monomial
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Realization

noncomputable section

variable {F : Type*} [Field F]
variable {U L : Fin 3 → Type*} [∀ i, Fintype (U i)]

def basisPairs (p : ∀ i, L i → ∀ j, U j) : PairFamily F U L :=
  fun i l => basisVector (fun j : {j // j ≠ i} => p i l j.val)

theorem sector_basisPairs_zero (p : ∀ i, L i → ∀ j, U j)
    (x : ∀ i, Coordinates U L i) :
    sector (basisPairs (F := F) p) 0 x = match x 0 with
      | Sum.inl _ => 0
      | Sum.inr l => coreEntry 1 (x 1) (p 0 l 1) * coreEntry 2 (x 2) (p 0 l 2) := by
  unfold sector
  cases x 0 with
  | inl _ => rfl
  | inr l =>
    change pairEmbedding 0 (basisVector (fun j : {j : Fin 3 // j ≠ 0} => p 0 l j.val)) x = _
    rw [pairEmbedding_basisVector]
    convert prod_other_zero (F := F) (fun j => coreEntry j (x j) (p 0 l j)) using 1
    congr 1
    ext j
    simp

theorem sector_basisPairs_one (p : ∀ i, L i → ∀ j, U j)
    (x : ∀ i, Coordinates U L i) :
    sector (basisPairs (F := F) p) 1 x = match x 1 with
      | Sum.inl _ => 0
      | Sum.inr l => coreEntry 0 (x 0) (p 1 l 0) * coreEntry 2 (x 2) (p 1 l 2) := by
  unfold sector
  cases x 1 with
  | inl _ => rfl
  | inr l =>
    change pairEmbedding 1 (basisVector (fun j : {j : Fin 3 // j ≠ 1} => p 1 l j.val)) x = _
    rw [pairEmbedding_basisVector]
    convert prod_other_one (F := F) (fun j => coreEntry j (x j) (p 1 l j)) using 1
    congr 1
    ext j
    simp

theorem sector_basisPairs_two (p : ∀ i, L i → ∀ j, U j)
    (x : ∀ i, Coordinates U L i) :
    sector (basisPairs (F := F) p) 2 x = match x 2 with
      | Sum.inl _ => 0
      | Sum.inr l => coreEntry 0 (x 0) (p 2 l 0) * coreEntry 1 (x 1) (p 2 l 1) := by
  unfold sector
  cases x 2 with
  | inl _ => rfl
  | inr l =>
    change pairEmbedding 2 (basisVector (fun j : {j : Fin 3 // j ≠ 2} => p 2 l j.val)) x = _
    rw [pairEmbedding_basisVector]
    convert prod_other_two (F := F) (fun j => coreEntry j (x j) (p 2 l j)) using 1
    congr 1
    ext j
    simp

theorem tensor_basisPairs_apply (p : ∀ i, L i → ∀ j, U j) (τ : Tensor F (Fin 3) U)
    (x : ∀ i, Coordinates U L i) :
    tensor (basisPairs p) τ x =
      (match x 0 with
      | Sum.inl _ => 0
      | Sum.inr l => coreEntry 1 (x 1) (p 0 l 1) * coreEntry 2 (x 2) (p 0 l 2)) +
      (match x 1 with
      | Sum.inl _ => 0
      | Sum.inr l => coreEntry 0 (x 0) (p 1 l 0) * coreEntry 2 (x 2) (p 1 l 2)) +
      (match x 2 with
      | Sum.inl _ => 0
      | Sum.inr l => coreEntry 0 (x 0) (p 2 l 0) * coreEntry 1 (x 1) (p 2 l 1)) +
        coreEmbedding τ x := by
  simp only [tensor, Pi.add_apply, Fin.sum_univ_three, sector_basisPairs_zero,
    sector_basisPairs_one, sector_basisPairs_two]

end

end Lemmata.Centroid.Realization

namespace Lemmata.Centroid.Tensor

variable {V : Fin 3 → Type*}

def point (a : V 0) (b : V 1) (c : V 2) : ∀ i, V i :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun j => Fin.elim0 j)))

@[simp] theorem point_zero (a : V 0) (b : V 1) (c : V 2) : point a b c 0 = a := rfl
@[simp] theorem point_one (a : V 0) (b : V 1) (c : V 2) : point a b c 1 = b := rfl
@[simp] theorem point_two (a : V 0) (b : V 1) (c : V 2) : point a b c 2 = c := rfl

@[simp] theorem point_eta (x : ∀ i, V i) : point (x 0) (x 1) (x 2) = x := by
  funext i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
  all_goals rfl

@[simp] theorem update_point_zero [DecidableEq (Fin 3)] (a r : V 0) (b : V 1) (c : V 2) :
    Function.update (point a b c) 0 r = point r b c := by
  funext i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
  · exact Function.update_self _ _ _
  · exact Function.update_of_ne (fun h => (by decide : (1 : ℕ) ≠ 0) (congrArg Fin.val h)) _ _
  · exact Function.update_of_ne (fun h => (by decide : (2 : ℕ) ≠ 0) (congrArg Fin.val h)) _ _

@[simp] theorem update_point_one [DecidableEq (Fin 3)] (a : V 0) (b r : V 1) (c : V 2) :
    Function.update (point a b c) 1 r = point a r c := by
  funext i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
  · exact Function.update_of_ne (fun h => (by decide : (0 : ℕ) ≠ 1) (congrArg Fin.val h)) _ _
  · exact Function.update_self _ _ _
  · exact Function.update_of_ne (fun h => (by decide : (2 : ℕ) ≠ 1) (congrArg Fin.val h)) _ _

@[simp] theorem update_point_two [DecidableEq (Fin 3)] (a : V 0) (b : V 1) (c r : V 2) :
    Function.update (point a b c) 2 r = point a b r := by
  funext i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
  · exact Function.update_of_ne (fun h => (by decide : (0 : ℕ) ≠ 2) (congrArg Fin.val h)) _ _
  · exact Function.update_of_ne (fun h => (by decide : (1 : ℕ) ≠ 2) (congrArg Fin.val h)) _ _
  · exact Function.update_self _ _ _

end Lemmata.Centroid.Tensor
