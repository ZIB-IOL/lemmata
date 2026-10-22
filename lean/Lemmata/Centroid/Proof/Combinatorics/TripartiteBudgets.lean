module

public import Lemmata.Centroid.Proof.Combinatorics.RectangularTripartite
public import Mathlib.Tactic.Zify

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Combinatorics

noncomputable section

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [LinearOrder α] [LinearOrder β] [LinearOrder γ]

private theorem product_rectangle {a b h t : ℕ} (ha : a ≤ h) (ht : t ≤ b) :
    a * b + h * t ≤ h * b + a * t := by
  have ha' : (a : ℤ) ≤ h := by exact_mod_cast ha
  have ht' : (t : ℤ) ≤ b := by exact_mod_cast ht
  have hh := mul_nonneg (sub_nonneg.mpr ha') (sub_nonneg.mpr ht')
  have hz : (a : ℤ) * b + h * t ≤ h * b + a * t := by nlinarith
  exact_mod_cast hz

private theorem product_budget {h u v B t : ℕ} (hu : u ≤ h) (hB : B ≤ h ^ 2)
    (ht : B + t ≤ h ^ 2 + v) : h * B + u * t ≤ h ^ 3 + u * v := by
  have hu' : (u : ℤ) ≤ h := by exact_mod_cast hu
  have hB' : (B : ℤ) ≤ (h : ℤ) ^ 2 := by exact_mod_cast hB
  have ht' : (B : ℤ) + t ≤ (h : ℤ) ^ 2 + v := by exact_mod_cast ht
  have hp := mul_nonneg (sub_nonneg.mpr hu') (sub_nonneg.mpr hB')
  have hq := mul_le_mul_of_nonneg_left ht' (Int.natCast_nonneg u)
  have hz : (h : ℤ) * B + u * t ≤ (h : ℤ) ^ 3 + u * v := by nlinarith
  exact_mod_cast hz

theorem bounded_degree_product (a b : α → ℕ) {h u v : ℕ}
    (ha : ∀ j, a j ≤ h) (hb : ∀ j, b j ≤ h) (hmono : Antitone b) (hu : u ≤ h)
    (hsuma : ∑ j, a j ≤ h ^ 2 + u) (hsumb : ∑ j, b j ≤ h ^ 2 + v) :
    ∑ j, a j * b j ≤ h ^ 3 + u * v := by
  by_cases hn : Fintype.card α ≤ h
  · calc
      _ ≤ ∑ _j : α, h * h := Finset.sum_le_sum fun j _ => Nat.mul_le_mul (ha j) (hb j)
      _ = Fintype.card α * (h * h) := by simp
      _ ≤ h * (h * h) := Nat.mul_le_mul_right _ hn
      _ ≤ h ^ 3 + u * v := by nlinarith
  · have hhn : h < Fintype.card α := by omega
    let H := initialSegment α h
    let j₀ := monoEquivOfFin α rfl ⟨h, hhn⟩
    let t := b j₀
    let B := ∑ j ∈ H, b j
    have hH : H.card = h := by simp [H, min_eq_right hhn.le]
    have hjrank : orderRank j₀ = h := by simp [j₀, orderRank]
    have hjnot : j₀ ∉ H := by simp [H, hjrank]
    have hbefore (j : α) (hj : j ∈ H) : t ≤ b j := by
      apply hmono
      apply orderRank_strictMono.le_iff_le.1
      have hr := (mem_initialSegment j h).1 hj
      omega
    have hafter (j : α) (hj : j ∉ H) : b j ≤ t := by
      apply hmono
      apply orderRank_strictMono.le_iff_le.1
      have hr : ¬orderRank j < h := fun h => hj ((mem_initialSegment j _).2 h)
      omega
    have hlocal (j : α) : a j * b j + (if j ∈ H then h * t else 0) ≤
        (if j ∈ H then h * b j else 0) + a j * t := by
      by_cases hj : j ∈ H
      · simpa only [ite_eq_left hj] using product_rectangle (ha j) (hbefore j hj)
      · simpa only [ite_eq_right hj, add_zero, zero_add] using
          Nat.mul_le_mul_left (a j) (hafter j hj)
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hlocal j)
    have hsum' : (∑ j, a j * b j) + h * h * t ≤ h * B + (∑ j, a j) * t := by
      simpa [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hH, B, mul_assoc] using hsum
    have hconcentrate : (∑ j, a j * b j) ≤ h * B + u * t := by
      have hmul := Nat.mul_le_mul_right t hsuma
      nlinarith
    have hB : B ≤ h ^ 2 := by
      calc
        _ ≤ ∑ _j ∈ H, h := Finset.sum_le_sum (fun j _ => hb j)
        _ = h ^ 2 := by simp [hH, pow_two]
    have hBt : B + t ≤ h ^ 2 + v := by
      have hsub : (∑ j ∈ insert j₀ H, b j) ≤ ∑ j, b j :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      rw [Finset.sum_insert hjnot] at hsub
      exact (by omega : B + t ≤ ∑ j, b j).trans hsumb
    exact hconcentrate.trans (product_budget hu hB hBt)

omit [Fintype α] [Fintype β] in
theorem rectangular_pair_small {E : Finset (α × β)} (hrect : Rectangular E) {h : ℕ}
    (hbudget : E.card ≤ h ^ 2 + h) :
    (E.image Prod.fst).card ≤ h ∨ (E.image Prod.snd).card ≤ h := by
  by_contra hn
  have hleft : h + 1 ≤ (E.image Prod.fst).card := by omega
  have hright : h + 1 ≤ (E.image Prod.snd).card := by omega
  have hne : E.Nonempty := by
    by_contra he
    have hz : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp [hz] at hleft
  have hcard := hrect.card_bound hne
  by_cases hle : (E.image Prod.fst).card ≤ (E.image Prod.snd).card
  · rw [max_eq_right hle] at hcard
    have hp := Nat.mul_le_mul_right (E.image Prod.snd).card hleft
    have hq := Nat.mul_le_mul_left h hright
    nlinarith
  · rw [max_eq_left (le_of_not_ge hle)] at hcard
    have hp := Nat.mul_le_mul_left (E.image Prod.fst).card hright
    have hq := Nat.mul_le_mul_left h hleft
    nlinarith

private theorem card_neighbors_sum (E : Finset (α × β)) :
    (∑ a, (neighbors E a).card) = E.card := by
  calc
    _ = ∑ p : α × β, if p ∈ E then 1 else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      simp only [neighbors, Finset.card_filter]
    _ = _ := by simp

omit [Fintype α] in
private theorem card_neighbors_as_sum (E : Finset (α × β)) (a : α) :
    (neighbors E a).card = ∑ b, if (a, b) ∈ E then 1 else 0 := by
  simp only [neighbors, Finset.card_filter]

theorem card_triangles_degree_product (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) : (triangles AB AC BC).card ≤
      ∑ c, (neighbors (transposeEdges AC) c).card * (neighbors (transposeEdges BC) c).card := by
  have hsub : triangles AB AC BC ⊆ triangles Finset.univ AC BC := by
    intro p hp
    have h := (mem_triangles_iff AB AC BC p).1 hp
    exact (mem_triangles_iff Finset.univ AC BC p).2 ⟨Finset.mem_univ _, h.2⟩
  apply (Finset.card_le_card hsub).trans_eq
  rw [card_triangles_eq_sum]
  simp only [Finset.mem_univ, ite_true, one_mul]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [card_neighbors_as_sum, card_neighbors_as_sum]
  simp only [mem_transposeEdges']
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hbc : (b, c) ∈ BC
  · simp only [ite_eq_left hbc, one_mul, mul_one]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hac : (a, c) ∈ AC <;> simp [hac]
  · simp [hbc]

omit [Fintype α] in
private theorem neighbors_subset_snd (E : Finset (α × β)) (a : α) :
    neighbors E a ⊆ E.image Prod.snd := by
  intro b hb
  exact Finset.mem_image.mpr ⟨(a, b), (mem_neighbors E a b).1 hb, rfl⟩

theorem positive_budget_small_two (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) {h u v : ℕ} (hu : u ≤ h) (hBC : DownClosed BC)
    (hα : (AC.image Prod.fst).card ≤ h) (hβ : (BC.image Prod.fst).card ≤ h)
    (hACbudget : AC.card ≤ h ^ 2 + u) (hBCbudget : BC.card ≤ h ^ 2 + v) :
    (triangles AB AC BC).card ≤ h ^ 3 + u * v := by
  apply (card_triangles_degree_product AB AC BC).trans
  apply bounded_degree_product _ _ (h := h) (u := u) (v := v)
  · intro c
    exact (Finset.card_le_card (neighbors_subset_snd (transposeEdges AC) c)).trans
      (by simpa only [transposeEdges_image_snd] using hα)
  · intro c
    exact (Finset.card_le_card (neighbors_subset_snd (transposeEdges BC) c)).trans
      (by simpa only [transposeEdges_image_snd] using hβ)
  · exact neighbors_card_antitone hBC.transpose
  · exact hu
  · simpa only [card_neighbors_sum, card_transposeEdges] using hACbudget
  · simpa only [card_neighbors_sum, card_transposeEdges] using hBCbudget

theorem positive_budget (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) {h e₁ e₂ e₃ : ℕ}
    (he₃ : e₃ ≤ e₂) (he₂ : e₂ ≤ e₁) (he₁ : e₁ ≤ h)
    (hAB : AB.card ≤ h ^ 2 + e₁) (hAC : AC.card ≤ h ^ 2 + e₂)
    (hBC : BC.card ≤ h ^ 2 + e₃) : (triangles AB AC BC).card ≤ h ^ 3 + e₁ * e₂ := by
  obtain ⟨A, B, C, hA, hB, hC, htri, hrA, hrB, hrC, hdA, hdB, hdC, hfirst, hsecond, hthird⟩ :=
    exists_active_rectangular AB AC BC
  have hAb := hA.trans hAB
  have hBb := hB.trans hAC
  have hCb := hC.trans hBC
  have hAs := rectangular_pair_small hrA (h := h) (hAb.trans (by omega))
  have hBs := rectangular_pair_small hrB (h := h) (hBb.trans (by omega))
  have hCs := rectangular_pair_small hrC (h := h) (hCb.trans (by omega))
  rw [← hfirst] at hBs
  rw [← hsecond, ← hthird] at hCs
  apply htri.trans
  by_cases hα : (A.image Prod.fst).card ≤ h
  · by_cases hβ : (A.image Prod.snd).card ≤ h
    · have hbound := positive_budget_small_two A B C (he₂.trans he₁) hdC
        (hfirst ▸ hα) (hsecond ▸ hβ) hBb hCb
      have hprod := Nat.mul_le_mul_left e₂ (he₃.trans he₂)
      nlinarith
    · have hγ : (B.image Prod.snd).card ≤ h := by omega
      have hbound := positive_budget_small_two B A (transposeEdges C) he₁ hdC.transpose hα
        (by simpa only [transposeEdges_image_fst, ← hthird] using hγ) hAb
        (by simpa only [card_transposeEdges] using hCb)
      rw [card_triangles_swap_last] at hbound
      exact hbound.trans (Nat.add_le_add_left (Nat.mul_le_mul_left e₁ he₃) _)
  · have hβ : (A.image Prod.snd).card ≤ h := by omega
    have hγ : (B.image Prod.snd).card ≤ h := by omega
    have hbound := positive_budget_small_two C (transposeEdges A) (transposeEdges B) he₁
      hdB.transpose (by simpa only [transposeEdges_image_fst] using hβ)
      (by simpa only [transposeEdges_image_fst] using hγ)
      (by simpa only [card_transposeEdges] using hAb)
      (by simpa only [card_transposeEdges] using hBb)
    simpa only [card_triangles_cycle] using hbound

end

end Lemmata.Centroid.Combinatorics
