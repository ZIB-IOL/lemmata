module

public import Lemmata.Centroid.Proof.General.MergeNumeric
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

open scoped BigOperators

namespace Lemmata.Centroid.General

theorem merge_components {ι : Type*} (d : ι → ℕ) (m : ι → Fin 3 → ℕ)
    (hpositive : ∀ a i, 0 < m a i)
    (hcoarse : ∀ a i, d a ≤ g (m a i))
    (hlocal : ∀ a N, (∀ i, m a i ≤ N) → d a ≤ supportBound N + 1)
    (hcost : ∀ a, dimensionCost (d a) ≤ ((m a 0 : ℝ) + m a 1 + m a 2) / 3)
    (s : Finset ι) (N : ℕ) (hformat : ∀ i, ∑ a ∈ s, m a i ≤ N) :
    (∑ a ∈ s, d a) ≤ supportBound N + 1 ∧
      (2 ≤ s.card → (∑ a ∈ s, d a) ≤ generalBound N) := by
  classical
  induction N using Nat.strong_induction_on generalizing s with
  | h N ih =>
    by_cases hs : s = ∅
    · subst s
      simp
    have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
    by_cases hcard : s.card = 1
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
      simp only [Finset.sum_singleton] at hformat ⊢
      exact ⟨hlocal a N hformat, by simp⟩
    have hcard₂ : 2 ≤ s.card := by have := hsne.card_pos; omega
    have hprod : (s ×ˢ (Finset.univ : Finset (Fin 3))).Nonempty := by
      obtain ⟨a, ha⟩ := hsne
      exact ⟨(a, 0), Finset.mem_product.mpr ⟨ha, Finset.mem_univ _⟩⟩
    obtain ⟨⟨a, j⟩, haj, hmin⟩ :=
      (s ×ˢ (Finset.univ : Finset (Fin 3))).exists_min_image (fun p => m p.1 p.2) hprod
    have ha : a ∈ s := (Finset.mem_product.mp haj).1
    have hmin' : ∀ b ∈ s, ∀ i, m a j ≤ m b i := by
      intro b hb i
      exact hmin (b, i) (Finset.mem_product.mpr ⟨hb, Finset.mem_univ _⟩)
    let t := s.erase a
    have htcard : 0 < t.card := by
      dsimp [t]
      rw [Finset.card_erase_of_mem ha]
      omega
    obtain ⟨b, hb⟩ := Finset.card_pos.mp htcard
    have hbs : b ∈ s := Finset.mem_of_mem_erase hb
    have hsplit (i : Fin 3) : m a i + ∑ b ∈ t, m b i = ∑ b ∈ s, m b i := by
      simpa only [add_comm] using s.sum_erase_add (fun b => m b i) ha
    have hdsplit : d a + ∑ b ∈ t, d b = ∑ b ∈ s, d b := by
      simpa only [add_comm] using s.sum_erase_add d ha
    have hrest (i : Fin 3) : m a j ≤ ∑ b ∈ t, m b i :=
      (hmin' b hbs i).trans (Finset.single_le_sum (fun x _ => Nat.zero_le (m x i)) hb)
    have hN₂ : 2 ≤ N := by
      have hp := hpositive a 0
      have hq := hpositive b 0
      have hr := Finset.single_le_sum (fun x (_ : x ∈ t) => Nat.zero_le (m x 0)) hb
      have hf := hformat 0
      rw [← hsplit] at hf
      omega
    have hbound : ∀ i, ∑ b ∈ t, m b i ≤ N - m a j := by
      intro i
      have hf := hformat i
      rw [← hsplit] at hf
      have hm := hmin' a ha i
      omega
    have hsmallN : N - m a j < N := by
      have hp := hpositive a j
      have hNpos := hN₂
      omega
    have hboundRest := (ih (N - m a j) hsmallN t hbound).1
    let n := generalIndex N
    let r := N - n * (n + 1)
    have hn : 0 < n := generalIndex_pos hN₂
    have hr : r ≤ 2 * n + 1 := general_remainder_le hN₂
    have hdecomp : N = n * (n + 1) + r := general_decomposition N
    have hsharp : (∑ b ∈ s, d b) ≤ generalBound N := by
      by_cases hsmall : m a j < 2 * n
      · have hloss := small_loss_at hn hr hdecomp (hpositive a j) hsmall
        have hc := hcoarse a j
        have hM : 1 ≤ generalBound N := by
          rw [generalBound_eq hN₂ hr hdecomp]
          have := generalBoundAt_base_le n r
          omega
        omega
      · let u : ℝ := ((m a 0 : ℝ) + m a 1 + m a 2) / 3
        let v : ℝ := ((∑ b ∈ t, m b 0 : ℕ) + (∑ b ∈ t, m b 1 : ℕ) +
          (∑ b ∈ t, m b 2 : ℕ)) / 3
        have hu : 2 * (n : ℝ) ≤ u := by
          have h₀ : 2 * (n : ℝ) ≤ m a 0 := by exact_mod_cast (le_trans (by omega) (hmin' a ha 0))
          have h₁ : 2 * (n : ℝ) ≤ m a 1 := by exact_mod_cast (le_trans (by omega) (hmin' a ha 1))
          have h₂ : 2 * (n : ℝ) ≤ m a 2 := by exact_mod_cast (le_trans (by omega) (hmin' a ha 2))
          dsimp [u]
          linarith
        have hv : 2 * (n : ℝ) ≤ v := by
          have h₀ : 2 * (n : ℝ) ≤ (∑ b ∈ t, m b 0 : ℕ) := by exact_mod_cast (le_trans (by omega) (hrest 0))
          have h₁ : 2 * (n : ℝ) ≤ (∑ b ∈ t, m b 1 : ℕ) := by exact_mod_cast (le_trans (by omega) (hrest 1))
          have h₂ : 2 * (n : ℝ) ≤ (∑ b ∈ t, m b 2 : ℕ) := by exact_mod_cast (le_trans (by omega) (hrest 2))
          dsimp [v]
          linarith
        have huv : u + v ≤ N := by
          have h₀ : (m a 0 : ℝ) + (∑ b ∈ t, m b 0 : ℕ) ≤ N := by exact_mod_cast ((hsplit 0).trans_le (hformat 0))
          have h₁ : (m a 1 : ℝ) + (∑ b ∈ t, m b 1 : ℕ) ≤ N := by exact_mod_cast ((hsplit 1).trans_le (hformat 1))
          have h₂ : (m a 2 : ℝ) + (∑ b ∈ t, m b 2 : ℕ) ≤ N := by exact_mod_cast ((hsplit 2).trans_le (hformat 2))
          dsimp [u, v]
          linarith
        have hcu : (d a : ℝ) ≤ 1 + envelope u :=
          dimension_le_envelope (by dsimp [u]; positivity) (hcost a)
        have hcv : (∑ b ∈ t, d b : ℕ) ≤ 1 + envelope v := by
          apply dimension_le_envelope (by dsimp [v]; positivity)
          have hsum := (dimensionCost_sum t d).trans (Finset.sum_le_sum (fun b _ => hcost b))
          simpa only [← Finset.sum_div, Finset.sum_add_distrib, ← Nat.cast_sum, v] using hsum
        rw [← hdsplit]
        exact large_merge_bound hn hr hdecomp hu hv huv hcu hcv
    exact ⟨hsharp.trans (generalBound_le_support_succ N), fun _ => hsharp⟩

end Lemmata.Centroid.General
