module

public import Lemmata.Centroid.Proof.Linear.SupportReduction
public import Lemmata.Centroid.Proof.Linear.ArrayTriangle

@[expose] public section

open Classical

noncomputable section

namespace Lemmata.Centroid.Linear

private theorem support_large_case {n s r r₀ r₁ p₀ c R : ℕ}
    (hsplit : r₀ + r₁ = r) (h₀ : r₀ ≤ n * p₀) (hp : p₀ + c ≤ n ^ 2 + s)
    (h₁ : r₁ + R ≤ n * c) (hexp : n * s ≤ R + s.choose 2) :
    r ≤ n ^ 3 + s * (s - 1) := by
  have hbudget := Nat.mul_le_mul_left n hp
  have hchoose : s.choose 2 ≤ s * (s - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.div_le_self _ _
  nlinarith

private theorem support_small_case {n s r r₀ r₁ c R : ℕ}
    (hc : c < s) (hsplit : r₀ + r₁ = r)
    (h₀ : r₀ ≤ n ^ 3 + (s - 1) * (s - c))
    (h₁ : r₁ + R ≤ n * c) (hexp : n * c ≤ R + c.choose 2) :
    r ≤ n ^ 3 + s * (s - 1) := by
  have hchoose : c.choose 2 ≤ c * (s - 1) := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left c (Nat.sub_le_sub_right hc.le 1))
  have hsc : s - c + c = s := Nat.sub_add_cancel hc.le
  nlinarith

variable {F α β γ : Type*} [Field F] [Fintype α] [Fintype β] [Fintype γ]

theorem annihilatorQuotientImage_lt_of_large_rank {n s : ℕ}
    (S : Submodule F (α × (β × γ) → F))
    (_hα : Fintype.card α = n) (hβ : Fintype.card β = n) (hs : 2 ≤ s)
    (hW : n + s ≤ Fintype.card γ)
    (hP : Module.finrank F (arraySupport S) ≤ n ^ 2 + s)
    (hQ : Module.finrank F (arraySupport (S.map swapFirstTwo.toLinearMap)) ≤ n ^ 2 + s)
    (hr : n ^ 3 + s * (s - 1) < Module.finrank F S) :
    Module.finrank F (annihilatorQuotientImage S) <
      Module.finrank F (coordinateOrthogonal (arraySupport S)) := by
  have hz := annihilatorQuotientImage_rank_bound S
  have hA := finrank_coordinateOrthogonal (arraySupport S)
  rw [hβ] at hz
  rw [Fintype.card_prod, hβ] at hA
  have hW' := Nat.mul_le_mul_left n hW
  have hQ' := Nat.mul_le_mul_left n hQ
  have hs₁ : s - 1 + 1 = s := by omega
  have hs₂ : s - 2 + 2 = s := by omega
  nlinarith [Nat.zero_le (s * (s - 2))]

theorem support_lemma_array_full_card_eq {n s : ℕ}
    (S : Submodule F (α × (β × γ) → F))
    (hα : Fintype.card α = n) (hβ : Fintype.card β = n) (hs : 2 ≤ s) (hsn : s ≤ n)
    (hfull : arraySupport (arraySupport S) = ⊤) (hW : n + s ≤ Fintype.card γ)
    (hP : Module.finrank F (arraySupport S) ≤ n ^ 2 + s)
    (hQ : Module.finrank F (arraySupport (S.map swapFirstTwo.toLinearMap)) ≤ n ^ 2 + s) :
    Module.finrank F S ≤ n ^ 3 + s * (s - 1) := by
  by_contra h
  have hr : n ^ 3 + s * (s - 1) < Module.finrank F S := by omega
  obtain ⟨w, hw, hann⟩ := exists_polynomial_support_annihilator S
    (annihilatorQuotientImage_lt_of_large_rank S hα hβ hs hW hP hQ hr)
  let L := (arraySupport S).map (pairPolynomialMap w)
  let c := Module.finrank F L
  have hc : 1 ≤ c := Submodule.one_le_finrank_iff.mpr
    (pairPolynomialMap_image_ne_bot (arraySupport S) hfull w hw)
  have hfullQ : arraySupport (arraySupport (S.map swapFirstTwo.toLinearMap)) = ⊤ := by
    rw [arraySupport_twice_swap, hfull]
  have hqpos : 1 ≤ Module.finrank F
      ((arraySupport (S.map swapFirstTwo.toLinearMap)).map (pairPolynomialMap w)) :=
    Submodule.one_le_finrank_iff.mpr
      (pairPolynomialMap_image_ne_bot _ hfullQ w hw)
  have hfirst := supportKernel_first_rank_bound S w
  have hsecond := supportKernel_second_rank_bound S w
  have hsplit := supportKernel_split_rank S w
  have himage := supportImage_rank_bound S w hann
  rw [hα] at himage
  have hP₀ : Module.finrank F (arraySupport (supportKernel S w)) + c ≤ n ^ 2 + s := by
    exact hfirst.trans hP
  have hQ₀ : Module.finrank F (arraySupport ((supportKernel S w).map swapFirstTwo.toLinearMap)) + 1 ≤
      n ^ 2 + s := by omega
  by_cases hcs : s ≤ c
  · have hexp := polynomial_variable_expansion_bound L s hcs
    rw [hα] at hexp
    have hzero := finrank_le_card_mul_arraySupport (supportKernel S w)
    rw [hα] at hzero
    exact h (support_large_case hsplit hzero hP₀ himage hexp)
  · have hclt : c < s := by omega
    have hp₀ : Module.finrank F (arraySupport (supportKernel S w)) ≤ n ^ 2 + (s - c) := by omega
    have hq₀ : Module.finrank F (arraySupport ((supportKernel S w).map swapFirstTwo.toLinearMap)) ≤
        n ^ 2 + (s - 1) := by omega
    have hzero := array_triangle_bound (supportKernel S w) hα.le hβ.le
      (show s - c ≤ s - 1 by omega) (show s - 1 ≤ n by omega) hp₀ hq₀
    have hexp := polynomial_variable_expansion_bound L c le_rfl
    rw [hα] at hexp
    exact h (support_small_case hclt hsplit hzero himage hexp)

theorem support_lemma_array_full {n s : ℕ}
    (S : Submodule F (Fin n × (Fin n × γ) → F)) (hs : 2 ≤ s) (hsn : s ≤ n)
    (hfull : arraySupport (arraySupport S) = ⊤) (hW : n + s ≤ Fintype.card γ)
    (hP : Module.finrank F (arraySupport S) ≤ n ^ 2 + s)
    (hQ : Module.finrank F (arraySupport (S.map swapFirstTwo.toLinearMap)) ≤ n ^ 2 + s) :
    Module.finrank F S ≤ n ^ 3 + s * (s - 1) := by
  exact support_lemma_array_full_card_eq S (by simp) (by simp) hs hsn hfull hW hP hQ

end Lemmata.Centroid.Linear
