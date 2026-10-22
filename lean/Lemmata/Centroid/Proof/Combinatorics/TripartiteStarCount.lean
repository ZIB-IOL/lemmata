module

public import Lemmata.Centroid.Proof.Combinatorics.TripartiteBudgets

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Combinatorics

noncomputable section

structure StarChain (α : Type*) (h d : ℕ) where
  full : Finset α
  tail : Finset α
  center : Finset α
  center_tail : center ⊆ tail
  tail_full : tail ⊆ full
  card_full : full.card = h
  card_tail : tail.card = d
  card_center : center.card = 1

namespace StarChain

variable {α β γ : Type*} {h d : ℕ}

theorem center_full (A : StarChain α h d) : A.center ⊆ A.full :=
  A.center_tail.trans A.tail_full

def holesAB (A : StarChain α h d) (B : StarChain β h d) (C : StarChain γ h d)
    (o : Bool) : Finset (α × β × γ) :=
  if o then A.tail ×ˢ (B.center ×ˢ C.full) else A.center ×ˢ (B.tail ×ˢ C.full)

def holesAC (A : StarChain α h d) (B : StarChain β h d) (C : StarChain γ h d)
    (o : Bool) : Finset (α × β × γ) :=
  if o then A.tail ×ˢ (B.full ×ˢ C.center) else A.center ×ˢ (B.full ×ˢ C.tail)

def holesBC (A : StarChain α h d) (B : StarChain β h d) (C : StarChain γ h d)
    (o : Bool) : Finset (α × β × γ) :=
  if o then A.full ×ˢ (B.tail ×ˢ C.center) else A.full ×ˢ (B.center ×ˢ C.tail)

private theorem product_three_subset {A₀ A : Finset α} {B₀ B : Finset β} {C₀ C : Finset γ}
    (ha : A₀ ⊆ A) (hb : B₀ ⊆ B) (hc : C₀ ⊆ C) :
    A₀ ×ˢ (B₀ ×ˢ C₀) ⊆ A ×ˢ (B ×ˢ C) :=
  Finset.product_subset_product ha (Finset.product_subset_product hb hc)

theorem holesAB_subset (A : StarChain α h d) (B : StarChain β h d) (C : StarChain γ h d)
    (o : Bool) : holesAB A B C o ⊆ A.full ×ˢ (B.full ×ˢ C.full) := by
  cases o
  · exact product_three_subset A.center_full B.tail_full (Finset.Subset.refl _)
  · exact product_three_subset A.tail_full B.center_full (Finset.Subset.refl _)

theorem holesAC_subset (A : StarChain α h d) (B : StarChain β h d) (C : StarChain γ h d)
    (o : Bool) : holesAC A B C o ⊆ A.full ×ˢ (B.full ×ˢ C.full) := by
  cases o
  · exact product_three_subset A.center_full (Finset.Subset.refl _) C.tail_full
  · exact product_three_subset A.tail_full (Finset.Subset.refl _) C.center_full

theorem holesBC_subset (A : StarChain α h d) (B : StarChain β h d) (C : StarChain γ h d)
    (o : Bool) : holesBC A B C o ⊆ A.full ×ˢ (B.full ×ˢ C.full) := by
  cases o
  · exact product_three_subset (Finset.Subset.refl _) B.center_full C.tail_full
  · exact product_three_subset (Finset.Subset.refl _) B.tail_full C.center_full

def remaining (A : StarChain α h d) (B : StarChain β h d) (C : StarChain γ h d)
    (o₁ o₂ o₃ : Bool) : Finset (α × β × γ) :=
  A.full ×ˢ (B.full ×ˢ C.full) \ (holesAB A B C o₁ ∪ holesAC A B C o₂ ∪ holesBC A B C o₃)

private theorem complement_three {ι : Type*} [DecidableEq ι] (U A B C : Finset ι)
    (hA : A ⊆ U) (hB : B ⊆ U) (hC : C ⊆ U) :
    (U \ (A ∪ B ∪ C)).card + A.card + B.card + C.card + (A ∩ B ∩ C).card =
      U.card + (A ∩ B).card + (A ∩ C).card + (B ∩ C).card := by
  have hsub : A ∪ B ∪ C ⊆ U := Finset.union_subset (Finset.union_subset hA hB) hC
  have h := Finset.card_sdiff_add_card_eq_card hsub
  have hab := Finset.card_union_add_card_inter A B
  have habc := Finset.card_union_add_card_inter (A ∪ B) C
  have hacbc := Finset.card_union_add_card_inter (A ∩ C) (B ∩ C)
  have heq : (A ∩ C) ∩ (B ∩ C) = A ∩ B ∩ C := by
    ext x
    simp only [Finset.mem_inter]
    exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, h.2⟩⟩⟩
  rw [heq, ← Finset.union_inter_distrib_right] at hacbc
  omega

theorem remaining_bound (A : StarChain α h d) (B : StarChain β h d) (C : StarChain γ h d)
    (o₁ o₂ o₃ : Bool) :
    (remaining A B C o₁ o₂ o₃).card + 3 * h * d ≤ h ^ 3 + d ^ 2 + d := by
  have hi := complement_three (A.full ×ˢ (B.full ×ˢ C.full))
    (holesAB A B C o₁) (holesAC A B C o₂) (holesBC A B C o₃)
    (holesAB_subset A B C o₁) (holesAC_subset A B C o₂) (holesBC_subset A B C o₃)
  have hrem : A.full ×ˢ (B.full ×ˢ C.full) \
      (holesAB A B C o₁ ∪ holesAC A B C o₂ ∪ holesBC A B C o₃) = remaining A B C o₁ o₂ o₃ := by
    ext p
    simp only [remaining, Finset.mem_sdiff]
  rw [hrem] at hi
  have hAcf := Finset.inter_eq_left.mpr A.center_full
  have hAtf := Finset.inter_eq_left.mpr A.tail_full
  have hAct := Finset.inter_eq_left.mpr A.center_tail
  have hAtc := Finset.inter_eq_right.mpr A.center_tail
  have hBcf := Finset.inter_eq_left.mpr B.center_full
  have hBfc := Finset.inter_eq_right.mpr B.center_full
  have hBtf := Finset.inter_eq_left.mpr B.tail_full
  have hBft := Finset.inter_eq_right.mpr B.tail_full
  have hBct := Finset.inter_eq_left.mpr B.center_tail
  have hBtc := Finset.inter_eq_right.mpr B.center_tail
  have hCfc := Finset.inter_eq_right.mpr C.center_full
  have hCft := Finset.inter_eq_right.mpr C.tail_full
  have hCct := Finset.inter_eq_left.mpr C.center_tail
  have hCtc := Finset.inter_eq_right.mpr C.center_tail
  cases o₁ <;> cases o₂ <;> cases o₃ <;>
    simp only [holesAB, holesAC, holesBC, Bool.false_eq_true, ite_false, ite_true,
      Finset.product_inter_product, hAcf, hAtf, hAct, hAtc,
      hBcf, hBfc, hBtf, hBft, hBct, hBtc, hCfc, hCft, hCct, hCtc,
      Finset.inter_self, Finset.card_product, A.card_full, A.card_tail, A.card_center,
      B.card_full, B.card_tail, B.card_center, C.card_full, C.card_tail, C.card_center,
      one_mul, mul_one] at hi <;> nlinarith [sq_nonneg (d - 1 : ℤ)]

end StarChain

end

end Lemmata.Centroid.Combinatorics
