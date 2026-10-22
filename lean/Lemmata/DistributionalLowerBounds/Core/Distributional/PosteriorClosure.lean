module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.FerrersVariance

@[expose] public section

/-!
# Adaptive posterior closure

A numerical LMO answer is reduced by `ExactLMO.lean` to exact ranks on active
coordinates and integer lower bounds on inactive coordinates.  This module
proves that arbitrary adaptive sequences of such disclosures preserve exactly
the claimed constraint form; conditioning a uniform prior therefore restricts
it uniformly to the compatible subtype.
-/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

structure RankConstraint (d : ℕ) where
  exactRanks : Fin d → Finset (Fin d)
  lowerRank : Fin d → ℕ

namespace RankConstraint

/-- Compatibility with accumulated exact assignments and one-based lower
bounds. -/
def Compatible {d : ℕ} (S : RankConstraint d) (pi : Equiv.Perm (Fin d)) : Prop :=
  ∀ i,
    (∀ r ∈ S.exactRanks i, pi i = r) ∧
      S.lowerRank i ≤ (pi i).val + 1

/-- Empty initial transcript. -/
def empty (d : ℕ) : RankConstraint d where
  exactRanks _ := ∅
  lowerRank _ := 1

@[simp] lemma compatible_empty {d : ℕ} (pi : Equiv.Perm (Fin d)) :
    (empty d).Compatible pi := by
  intro i
  simp [empty]

end RankConstraint

/-- Discrete information contained in one exact LMO answer. -/
structure RankDisclosure (d : ℕ) where
  active : Finset (Fin d)
  activeRank : Fin d → Fin d
  inactiveLower : Fin d → ℕ

namespace RankDisclosure

/-- A hidden permutation gives the specified answer. -/
def Agrees {d : ℕ} (A : RankDisclosure d) (pi : Equiv.Perm (Fin d)) : Prop :=
  ∀ i, if i ∈ A.active then pi i = A.activeRank i
       else A.inactiveLower i ≤ (pi i).val + 1

/-- Append one answer to a transcript state. -/
def refine {d : ℕ} (S : RankConstraint d) (A : RankDisclosure d) :
    RankConstraint d where
  exactRanks i := if i ∈ A.active then insert (A.activeRank i) (S.exactRanks i)
    else S.exactRanks i
  lowerRank i := if i ∈ A.active then S.lowerRank i
    else max (S.lowerRank i) (A.inactiveLower i)

/-- One-step posterior closure, with no hidden real-valued information. -/
theorem compatible_refine_iff {d : ℕ}
    (S : RankConstraint d) (A : RankDisclosure d) (pi : Equiv.Perm (Fin d)) :
    (A.refine S).Compatible pi ↔ S.Compatible pi ∧ A.Agrees pi := by
  constructor
  · intro h
    constructor
    · intro i
      by_cases hai : i ∈ A.active
      · have hexact : ∀ r ∈ insert (A.activeRank i) (S.exactRanks i), pi i = r := by
          simpa [refine, hai] using (h i).1
        have hlower : S.lowerRank i ≤ (pi i).val + 1 := by
          simpa [refine, hai] using (h i).2
        exact ⟨fun r hr => hexact r (Finset.mem_insert_of_mem hr), hlower⟩
      · have hi := h i
        have hexact : ∀ r ∈ S.exactRanks i, pi i = r := by
          simpa [refine, hai] using hi.1
        have hlower : max (S.lowerRank i) (A.inactiveLower i) ≤
            (pi i).val + 1 := by simpa [refine, hai] using hi.2
        exact ⟨hexact, (le_max_left _ _).trans hlower⟩
    · intro i
      by_cases hai : i ∈ A.active
      · have hexact : ∀ r ∈ insert (A.activeRank i) (S.exactRanks i), pi i = r := by
          simpa [refine, hai] using (h i).1
        simp [hai]
        exact hexact _ (Finset.mem_insert_self _ _)
      · have hlower : max (S.lowerRank i) (A.inactiveLower i) ≤
            (pi i).val + 1 := by simpa [refine, hai] using (h i).2
        simp [hai]
        exact (le_max_right _ _).trans hlower
  · rintro ⟨hS, hA⟩ i
    by_cases hai : i ∈ A.active
    · have ha := hA i
      simp [hai] at ha
      constructor
      · intro r hr
        have hr' : r ∈ insert (A.activeRank i) (S.exactRanks i) := by
          simpa [refine, hai] using hr
        rw [Finset.mem_insert] at hr'
        rcases hr' with rfl | hr
        · exact ha
        · exact (hS i).1 r hr
      · simpa [refine, hai] using (hS i).2
    · have ha := hA i
      simp [hai] at ha
      constructor
      · simpa [refine, hai] using (hS i).1
      · simpa [refine, hai] using max_le (hS i).2 ha

/-- Exact set identity behind uniform conditioning. -/
theorem compatibleSet_refine {d : ℕ}
    (S : RankConstraint d) (A : RankDisclosure d) :
    {pi : Equiv.Perm (Fin d) | (A.refine S).Compatible pi} =
      {pi | S.Compatible pi} ∩ {pi | A.Agrees pi} := by
  ext pi
  exact compatible_refine_iff S A pi

end RankDisclosure

/-- A finite adaptive transcript represented only by its discrete disclosures. -/
def applyDisclosures {d : ℕ} :
    RankConstraint d → List (RankDisclosure d) → RankConstraint d
  | S, [] => S
  | S, A :: tail => applyDisclosures (A.refine S) tail

/-- Arbitrarily many adaptive answers introduce only accumulated exact ranks
and lower bounds. -/
theorem applyDisclosures_compatible_iff {d : ℕ}
    (S : RankConstraint d) (answers : List (RankDisclosure d))
    (pi : Equiv.Perm (Fin d)) :
    (applyDisclosures S answers).Compatible pi ↔
      S.Compatible pi ∧
        ∀ k (hk : k < answers.length),
          (answers.get ⟨k, hk⟩).Agrees pi := by
  induction answers generalizing S with
  | nil => simp [applyDisclosures]
  | cons A tail ih =>
      rw [applyDisclosures, ih, RankDisclosure.compatible_refine_iff]
      constructor
      · rintro ⟨⟨hS, hA⟩, htail⟩
        refine ⟨hS, ?_⟩
        intro k hk
        cases k with
        | zero => simpa using hA
        | succ k =>
            simpa using htail k (Nat.lt_of_succ_lt_succ hk)
      · rintro ⟨hS, hall⟩
        refine ⟨⟨hS, ?_⟩, ?_⟩
        · simpa using hall 0 (by simp)
        · intro k hk
          simpa using hall (k + 1) (by simpa using Nat.succ_lt_succ hk)

end Lemmata.DistributionalLowerBounds.Core.Distributional
