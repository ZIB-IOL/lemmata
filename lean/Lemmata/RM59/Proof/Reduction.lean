module

public import Lemmata.RM59.Proof.Moments
public import Lemmata.RM59.Proof.Descent

@[expose] public section

namespace Lemmata.RM59

open scoped symmDiff

def OddSupportBound (B : ℕ) : Prop :=
  ∀ S : Finset (Point 9), Odd S.card →
    ∃ R : Finset (Point 9), MatchSupportMoments 3 S R ∧ R.card ≤ B

def SupportBound (B : ℕ) : Prop :=
  ∀ S : Finset (Point 9),
    ∃ R : Finset (Point 9), MatchSupportMoments 3 S R ∧ R.card ≤ B

def FullBound (B : ℕ) : Prop :=
  ∀ f : BooleanFunction 9,
    ∃ p ∈ reedMuller 9 5, weight (f + p) ≤ B

def GeometricCompletion : Prop :=
  ∀ H P : Finset (Point 9),
    (∀ s, s.card ≤ 2 → supportMoment H s = 0) →
    AffineIndependent Field ((↑) : P → Point 9) →
    P.card ∈ ({1, 3, 5, 7, 9} : Finset ℕ) →
    ∃ G : Finset (Point 9),
      MatchSupportMoments 3 G H ∧ (G ∆ P).card ≤ 31

theorem oddSupportBound_of_geometricCompletion
    (h : GeometricCompletion) : OddSupportBound 31 := by
  classical
  intro S hS
  obtain ⟨P, hP, hcard, hmatch⟩ :=
    exists_odd_simplex_matchSupportMoments_two S hS
  have hzero : ∀ s, s.card ≤ 2 → supportMoment (S ∆ P) s = 0 := by
    intro s hs
    rw [supportMoment_symmDiff, hmatch s hs, field_add_self]
  obtain ⟨G, hG, hbound⟩ := h (S ∆ P) P hzero hP hcard
  refine ⟨G ∆ P, ?_, hbound⟩
  intro s hs
  calc
    supportMoment S s =
        (supportMoment S s + supportMoment P s) + supportMoment P s := by
      simp [add_assoc]
    _ = supportMoment (S ∆ P) s + supportMoment P s := by
      rw [supportMoment_symmDiff]
    _ = supportMoment G s + supportMoment P s := by rw [hG s hs]
    _ = supportMoment (G ∆ P) s := (supportMoment_symmDiff G P s).symm

theorem supportBound_of_oddSupportBound {B : ℕ}
    (h : OddSupportBound B) : SupportBound (B + 1) := by
  classical
  intro S
  by_cases hodd : Odd S.card
  · obtain ⟨R, hmatch, hbound⟩ := h S hodd
    exact ⟨R, hmatch, hbound.trans (Nat.le_succ _)⟩
  · have hzero : supportMoment S ∅ = 0 :=
      (field_eq_zero_or_one (supportMoment S ∅)).resolve_right
        (fun hS => hodd ((supportMoment_empty_eq_one_iff S).mp hS))
    have hflip : Odd (S ∆ {0}).card := by
      apply (supportMoment_empty_eq_one_iff (S ∆ {0})).mp
      rw [supportMoment_symmDiff, hzero, supportMoment_singleton, monomial_empty,
        zero_add]
    obtain ⟨R, hmatch, hbound⟩ := h (S ∆ {0}) hflip
    refine ⟨R ∆ {0}, ?_, ?_⟩
    · intro s hs
      calc
        supportMoment S s =
            (supportMoment S s + supportMoment {0} s) + supportMoment {0} s := by
          simp [add_assoc]
        _ = supportMoment (S ∆ {0}) s + supportMoment {0} s := by
          rw [supportMoment_symmDiff]
        _ = supportMoment R s + supportMoment {0} s := by rw [hmatch s hs]
        _ = supportMoment (R ∆ {0}) s := (supportMoment_symmDiff R {0} s).symm
    · calc
        (R ∆ {0}).card ≤ (R ∪ {0}).card :=
          Finset.card_le_card Finset.symmDiff_subset_union
        _ ≤ R.card + ({0} : Finset (Point 9)).card := Finset.card_union_le _ _
        _ = R.card + 1 := by simp
        _ ≤ B + 1 := Nat.add_le_add_right hbound 1

theorem fullBound_of_supportBound {B : ℕ}
    (h : SupportBound B) : FullBound B := by
  intro f
  obtain ⟨R, hmatch, hbound⟩ := h (support f)
  let p := f + indicator R
  have hp : p ∈ reedMuller 9 5 := by
    simpa only [indicator_support] using match_support_moments_mem_rm59 hmatch
  refine ⟨p, hp, ?_⟩
  have heq : f + p = indicator R := by
    funext x
    change f x + (f x + indicator R x) = indicator R x
    rw [← add_assoc, field_add_self, zero_add]
  rw [heq, weight_indicator]
  exact hbound

theorem fullBound_of_geometricCompletion (h : GeometricCompletion) : FullBound 32 :=
  fullBound_of_supportBound
    (supportBound_of_oddSupportBound (oddSupportBound_of_geometricCompletion h))

end Lemmata.RM59
