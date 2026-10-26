module

public import Lemmata.CocubicCovering.Proof.Forms
public meta import Lemmata.CocubicCovering.Proof.Forms

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.Covering

open scoped BigOperators

private theorem compl_subset_of_union_eq_univ {m : ℕ} {s t : Finset (Fin m)}
    (h : t ∪ s = Finset.univ) : sᶜ ⊆ t := by
  intro i hi
  have hiu : i ∈ t ∪ s := by rw [h]; simp
  exact (Finset.mem_union.mp hiu).resolve_right (Finset.mem_compl.mp hi)

theorem lower_degree_moment {m : ℕ} (hm : 4 ≤ m) (p : ANF m)
    (hp : DegreeLE p (m - 4)) (s : Finset (Fin m)) (hs : s.card ≤ 4) :
    (∑ x : Vector m, monomial s x * eval p x) =
      if s.card = 4 then p sᶜ else 0 := by
  classical
  rw [monomial_moment]
  by_cases hs4 : s.card = 4
  · rw [if_pos hs4, Finset.sum_eq_single sᶜ]
    · have hu : sᶜ ∪ s = Finset.univ := by
        ext i
        by_cases hi : i ∈ s <;> simp [hi]
      simp [hu]
    · intro t ht hne
      by_cases hu : t ∪ s = Finset.univ
      · have hsub := compl_subset_of_union_eq_univ hu
        have hlarge : m - 4 < t.card := by
          by_contra hn
          have heq : sᶜ = t := Finset.eq_of_subset_of_card_le hsub (by
            simpa only [Finset.card_compl, Fintype.card_fin, hs4] using
              (show t.card ≤ m - 4 by omega))
          exact hne heq.symm
        simp [hp t hlarge]
      · simp [hu]
    · simp
  · rw [if_neg hs4]
    apply Finset.sum_eq_zero
    intro t ht
    by_cases hu : t ∪ s = Finset.univ
    · have hsub := compl_subset_of_union_eq_univ hu
      have hcard := Finset.card_le_card hsub
      have hc := Finset.card_compl_add_card s
      simp only [Fintype.card_fin] at hc
      have hlarge : m - 4 < t.card := by omega
      simp [hp t hlarge]
    · simp [hu]

private theorem compl_union_eq_univ_iff {m : ℕ} (c s : Finset (Fin m)) :
    cᶜ ∪ s = Finset.univ ↔ c ⊆ s := by
  constructor
  · intro h i hi
    have hiu : i ∈ cᶜ ∪ s := by rw [h]; simp
    exact (Finset.mem_union.mp hiu).resolve_left (by simpa using hi)
  · intro h
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    by_cases hi : i ∈ c
    · exact Finset.mem_union_right _ (h hi)
    · exact Finset.mem_union_left _ (Finset.mem_compl.mpr hi)

theorem cocubic_moment_subset {m : ℕ} (c : CubicCoefficients m) (s : Finset (Fin m)) :
    (∑ x : Vector m, monomial s x * eval (cubicComplement c) x) =
      ∑ t : {t : Finset (Fin m) // t.card = 3}, if t.val ⊆ s then c t else 0 := by
  classical
  let summand : Finset (Fin m) → Field := fun t =>
    cubicComplement c tᶜ * if tᶜ ∪ s = Finset.univ then 1 else 0
  have hreindex :
      (∑ x : Vector m, monomial s x * eval (cubicComplement c) x) = ∑ t, summand t := by
    rw [monomial_moment]
    apply Finset.sum_bij (fun t _ => tᶜ)
    · intro t ht
      exact Finset.mem_univ _
    · intro a ha b hb hab
      simpa using congrArg (fun t : Finset (Fin m) => tᶜ) hab
    · intro t ht
      exact ⟨tᶜ, Finset.mem_univ _, by simp⟩
    · intro t ht
      simp only [summand, compl_compl]
  rw [hreindex]
  calc
    (∑ t, summand t) =
        ∑ t ∈ Finset.univ.filter (fun t : Finset (Fin m) => t.card = 3), summand t := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro t ht hnot
      have hc : t.card ≠ 3 := by simpa using hnot
      simp [summand, cubicComplement, hc]
    _ = ∑ t : {t : Finset (Fin m) // t.card = 3}, summand t.val :=
      Finset.sum_subtype _ (by simp) summand
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      simp [summand, cubicComplement, t.property, compl_union_eq_univ_iff]

end Lemmata.CocubicCovering.Covering
