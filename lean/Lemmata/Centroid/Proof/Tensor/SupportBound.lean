module

public import Lemmata.Centroid.Proof.Tensor.LeadingSupport
public import Lemmata.Centroid.Proof.Combinatorics.Tripartite
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.Centroid.Tensor

def threeCoordinates (V : Fin 3 → Type*) : (∀ i, V i) ≃ V 0 × V 1 × V 2 :=
  (Fin.consEquiv V).symm.trans
    (Equiv.prodCongr (Equiv.refl _) (piFinTwoEquiv fun j : Fin 2 => V j.succ))

@[simp] theorem threeCoordinates_apply (V : Fin 3 → Type*) (x : ∀ i, V i) :
    threeCoordinates V x = (x 0, x 1, x 2) := rfl

variable {F : Type*} [Field F] {V : Fin 3 → Type*} [∀ i, Fintype (V i)]

theorem support_product_bound_ordered [∀ i, LinearOrder (V i)] [∀ i, Nonempty (V i)]
    (S : Submodule F (Tensor F (Fin 3) V)) :
    Module.finrank F S ^ 2 ≤ ∏ i : Fin 3, Module.finrank F (oppositeSupportAt S i) := by
  let _ : ∀ i, DecidableEq (V i) := fun _ => Classical.decEq _
  let a₀ (i : Fin 3) : V i := Finset.univ.min' Finset.univ_nonempty
  have ha₀ (i : Fin 3) (a : V i) : a₀ i ≤ a := Finset.min'_le _ _ (Finset.mem_univ _)
  let L := (lexLeading S).image (fun x => threeCoordinates V (ofLex x))
  have hcard : L.card = Module.finrank F S := by
    dsimp only [L]
    calc
      _ = (lexLeading S).card := Finset.card_image_of_injective _
        (fun x y h => ofLex.injective ((threeCoordinates V).injective h))
      _ = _ := card_lexLeading S
  have hAB : (L.image (fun p => (p.1, p.2.1))).card ≤
      Module.finrank F (oppositeSupportAt S 2) := by
    dsimp only [L]
    rw [Finset.image_image]
    apply card_projection_le_oppositeSupportAt S 2 (a₀ 2) (ha₀ 2)
    intro x
    exact congrArg₂ Prod.mk
      (project_update_of_ne x 2 0 (a₀ 2) (by decide))
      (project_update_of_ne x 2 1 (a₀ 2) (by decide))
  have hAC : (L.image (fun p => (p.1, p.2.2))).card ≤
      Module.finrank F (oppositeSupportAt S 1) := by
    dsimp only [L]
    rw [Finset.image_image]
    apply card_projection_le_oppositeSupportAt S 1 (a₀ 1) (ha₀ 1)
    intro x
    exact congrArg₂ Prod.mk
      (project_update_of_ne x 1 0 (a₀ 1) (by decide))
      (project_update_of_ne x 1 2 (a₀ 1) (by decide))
  have hBC : (L.image (fun p => (p.2.1, p.2.2))).card ≤
      Module.finrank F (oppositeSupportAt S 0) := by
    dsimp only [L]
    rw [Finset.image_image]
    apply card_projection_le_oppositeSupportAt S 0 (a₀ 0) (ha₀ 0)
    intro x
    exact congrArg₂ Prod.mk
      (project_update_of_ne x 0 1 (a₀ 0) (by decide))
      (project_update_of_ne x 0 2 (a₀ 0) (by decide))
  calc
    _ = L.card ^ 2 := by rw [hcard]
    _ ≤ _ := Combinatorics.loomis_whitney L
    _ ≤ Module.finrank F (oppositeSupportAt S 2) * Module.finrank F (oppositeSupportAt S 1) *
        Module.finrank F (oppositeSupportAt S 0) := Nat.mul_le_mul (Nat.mul_le_mul hAB hAC) hBC
    _ = _ := by rw [Fin.prod_univ_three]; ring

theorem support_product_bound (S : Submodule F (Tensor F (Fin 3) V)) :
    Module.finrank F S ^ 2 ≤ ∏ i : Fin 3, Module.finrank F (oppositeSupportAt S i) := by
  cases isEmpty_or_nonempty (∀ i, V i) with
  | inl h =>
    let _ : IsEmpty (∀ i, V i) := h
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le _
  | inr h =>
    let _ : ∀ i, Nonempty (V i) := fun i => ⟨(Classical.choice h) i⟩
    let _ : ∀ i, LinearOrder (V i) := fun i =>
      LinearOrder.lift' (Fintype.equivFin (V i)) (Fintype.equivFin (V i)).injective
    exact support_product_bound_ordered S

theorem centroid_subspace_product_bound {T : Tensor F (Fin 3) V} (hT : Concise T)
    {J : Submodule F (∀ i, Matrix (V i) (V i) F)} (hJ : J ≤ centroid T) :
    Module.finrank F J ^ 2 ≤ ∏ i : Fin 3,
      (Fintype.card (V i) - Module.finrank F (commonKernel J i)) := by
  have h := support_product_bound (imageAt T J 0)
  rw [finrank_imageAt hT hJ] at h
  have heq (i : Fin 3) : Module.finrank F (oppositeSupportAt (imageAt T J 0) i) =
      Fintype.card (V i) - Module.finrank F (commonKernel J i) := by
    rw [imageAt_eq hJ 0 i]
    exact finrank_oppositeSupportAt_imageAt hT J i
  simpa only [heq] using h

theorem square_zero_image_oneSupportAt {T : Tensor F (Fin 3) V}
    {J : Submodule F (∀ i, Matrix (V i) (V i) F)} (hJ : J ≤ centroid T)
    (hzero : ∀ A ∈ J, ∀ B ∈ J, A * B = 0) (i : Fin 3) :
    oneSupportAt (imageAt T J 0) i ≤ commonKernel J i := by
  apply oneSupportAt_le_commonKernel
  intro A hA U hU
  rw [imageAt_eq hJ 0 i] at hU
  obtain ⟨B, hB, rfl⟩ := hU
  change legAction (legAction T i (B i)) i (A i) = 0
  rw [← legAction_mul]
  have hAB : A i * B i = 0 := congrFun (hzero A hA B hB) i
  rw [hAB, map_zero]

theorem square_zero_image_support_budget {T : Tensor F (Fin 3) V} (hT : Concise T)
    {J : Submodule F (∀ i, Matrix (V i) (V i) F)} (hJ : J ≤ centroid T)
    (hzero : ∀ A ∈ J, ∀ B ∈ J, A * B = 0) (i : Fin 3) :
    Module.finrank F (oneSupportAt (imageAt T J 0) i) +
      Module.finrank F (oppositeSupportAt (imageAt T J 0) i) ≤ Fintype.card (V i) := by
  have hone := Submodule.finrank_mono (square_zero_image_oneSupportAt hJ hzero i)
  have hpair : Module.finrank F (oppositeSupportAt (imageAt T J 0) i) =
      Fintype.card (V i) - Module.finrank F (commonKernel J i) := by
    rw [imageAt_eq hJ 0 i]
    exact finrank_oppositeSupportAt_imageAt hT J i
  have hdim := finrank_rowSpace_add_commonKernel J i
  omega

end Lemmata.Centroid.Tensor
