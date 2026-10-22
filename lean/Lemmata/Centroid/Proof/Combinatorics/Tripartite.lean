module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Combinatorics

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem trilinear_sum_sq_le (A : α → β → ℕ) (B : α → γ → ℕ) (C : β → γ → ℕ) :
    (∑ p : β × γ, C p.1 p.2 * ∑ a, A a p.1 * B a p.2) ^ 2 ≤
      (∑ a, ∑ b, A a b ^ 2) * (∑ a, ∑ c, B a c ^ 2) *
        ∑ p : β × γ, C p.1 p.2 ^ 2 := by
  let Z : β × γ → ℕ := fun p => ∑ a, A a p.1 * B a p.2
  have hz : (∑ p, Z p ^ 2) ≤
      (∑ a, ∑ b, A a b ^ 2) * (∑ a, ∑ c, B a c ^ 2) := by
    calc
      _ ≤ ∑ p : β × γ, (∑ a, A a p.1 ^ 2) * (∑ a, B a p.2 ^ 2) := by
        apply Finset.sum_le_sum
        intro p _
        exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => A a p.1) (fun a => B a p.2)
      _ = (∑ b, ∑ a, A a b ^ 2) * (∑ c, ∑ a, B a c ^ 2) := by
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul]
      _ = _ := by
        congr 1
        · exact Finset.sum_comm
        · exact Finset.sum_comm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun p : β × γ => C p.1 p.2) Z
  calc
    _ ≤ (∑ p : β × γ, C p.1 p.2 ^ 2) * ∑ p, Z p ^ 2 := hcs
    _ ≤ (∑ p : β × γ, C p.1 p.2 ^ 2) *
        ((∑ a, ∑ b, A a b ^ 2) * (∑ a, ∑ c, B a c ^ 2)) :=
      Nat.mul_le_mul_left _ hz
    _ = _ := by ring

noncomputable def triangles (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) : Finset (α × β × γ) := by
  classical
  exact Finset.univ.filter fun p => (p.1, p.2.1) ∈ AB ∧
    (p.1, p.2.2) ∈ AC ∧ (p.2.1, p.2.2) ∈ BC

theorem card_triangles_eq_sum (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) :
    (triangles AB AC BC).card = ∑ p : β × γ,
      (if p ∈ BC then 1 else 0) * ∑ a,
        (if (a, p.1) ∈ AB then 1 else 0) * (if (a, p.2) ∈ AC then 1 else 0) := by
  classical
  calc
    _ = ∑ a : α, ∑ b : β, ∑ c : γ,
        if (a, b) ∈ AB ∧ (a, c) ∈ AC ∧ (b, c) ∈ BC then 1 else 0 := by
      simp only [triangles, Finset.card_filter, Fintype.sum_prod_type]
    _ = ∑ b : β, ∑ c : γ, ∑ a : α,
        if (a, b) ∈ AB ∧ (a, c) ∈ AC ∧ (b, c) ∈ BC then 1 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp_all

theorem card_triangles_sq_le (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) :
    (triangles AB AC BC).card ^ 2 ≤ AB.card * AC.card * BC.card := by
  classical
  rw [card_triangles_eq_sum]
  have h := trilinear_sum_sq_le (fun a b => if (a, b) ∈ AB then 1 else 0)
    (fun a c => if (a, c) ∈ AC then 1 else 0)
    (fun b c => if (b, c) ∈ BC then 1 else 0)
  have hAB : (∑ a : α, ∑ b : β, (if (a, b) ∈ AB then 1 else 0 : ℕ) ^ 2) = AB.card := by
    rw [← Fintype.sum_prod_type']
    simp
  have hAC : (∑ a : α, ∑ c : γ, (if (a, c) ∈ AC then 1 else 0 : ℕ) ^ 2) = AC.card := by
    rw [← Fintype.sum_prod_type']
    simp
  have hBC : (∑ p : β × γ, (if p ∈ BC then 1 else 0 : ℕ) ^ 2) = BC.card := by simp
  rw [hAB, hAC, hBC] at h
  simpa only [Prod.mk.eta] using h

theorem loomis_whitney (S : Finset (α × β × γ)) :
    S.card ^ 2 ≤ (S.image (fun p => (p.1, p.2.1))).card *
      (S.image (fun p => (p.1, p.2.2))).card *
        (S.image (fun p => (p.2.1, p.2.2))).card := by
  classical
  have hsub : S ⊆ triangles (S.image (fun p => (p.1, p.2.1)))
      (S.image (fun p => (p.1, p.2.2))) (S.image (fun p => (p.2.1, p.2.2))) := by
    intro p hp
    apply Finset.mem_filter.2
    exact ⟨Finset.mem_univ _, Finset.mem_image_of_mem _ hp,
      Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  exact (Nat.pow_le_pow_left (Finset.card_le_card hsub) 2).trans (card_triangles_sq_le _ _ _)

end Lemmata.Centroid.Combinatorics
