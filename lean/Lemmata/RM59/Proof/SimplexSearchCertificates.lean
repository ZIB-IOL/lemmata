module

public import Lemmata.RM59.Proof.SimplexSearchGeometry
public import Lemmata.RM59.Proof.CommonConfigurations
public import Lemmata.RM59.Proof.IndexedDerivation

@[expose] public section

namespace Lemmata.RM59.SimplexSearchCertificates

open scoped symmDiff
open Packed AvailableConfigurations PlaneCertificates PlaneFinder SimplexSearch

structure PairData where
  steps : Array (DerivationStep PackedPoint)
  roots : Array Nat
  locations : Array Nat
  table : Array Bool

structure TripleData where
  steps : Array (DerivationStep (PackedPoint × PackedPoint))
  roots : Array Nat
  locations : Array Nat
  table : Array Bool

def pairDataCheck (family dimension : Nat) (data : PairData) : Bool :=
  decide (2 ≤ dimension ∧ (Certificate.seed family).length + (dimension + 1) ≤ 35) &&
    indexedDerivationCheck (SmallPairCertificates.pairSeeds family)
      (SmallPairCertificates.familyMoves family) data.steps data.roots &&
    decide (PairPlaneCertificates.PairCoverageValid data.table data.steps data.locations) &&
    noSimplex (lookup data.table) dimension

def tripleDataCheck (family : Nat) (data : TripleData) : Bool :=
  decide ((Certificate.seed family).length ≤ 28) &&
    indexedDerivationCheck (TripleCertificates.tripleSeeds family)
      (TripleCertificates.tripleMoves family) data.steps data.roots &&
    decide (TripleCertificates.CoverageValid data.table ⟨data.steps⟩ data.locations) &&
    noSimplex (lookup data.table) 8

private theorem point_add_self (x : Point 9) : x + x = 0 := by
  funext i
  exact field_add_self _

private theorem eq_of_add_eq_zero (x y : Point 9) (h : x + y = 0) : x = y := by
  have heq := congrArg (fun z : Point 9 => z + y) h
  simpa only [add_assoc, point_add_self, add_zero, zero_add] using heq

private theorem shared_point_sum (x y z : Point 9) : (x + y) + (x + z) = y + z := by
  calc
    _ = (x + x) + (y + z) := by ac_rfl
    _ = _ := by rw [point_add_self, zero_add]

theorem exists_missing_triple (table : Array Bool) {dimension : Nat} (hd : 2 ≤ dimension)
    (hcheck : noSimplex (lookup table) dimension = true) (P : Finset (Point 9))
    (hcard : P.card = dimension + 1) (hAI : AffineIndependent Field ((↑) : P → Point 9)) :
    ∃ a b c : P, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      lookup table (encodePoint (a.val + b.val)) (encodePoint (a.val + c.val)) = false := by
  classical
  by_contra! hnone
  apply noSimplex_excludes (lookup table) hd hcheck P hcard hAI
  intro a b c hab hac hbc
  change lookup table (encodePoint (a.val + b.val)) (encodePoint (a.val + c.val)) = true
  cases hv : lookup table (encodePoint (a.val + b.val)) (encodePoint (a.val + c.val)) with
  | false => exact False.elim (hnone a b c hab hac hbc hv)
  | true => rfl

private theorem triple_directions_valid {P : Finset (Point 9)} (a b c : P)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    encodePoint (a.val + b.val) ≠ 0 ∧ encodePoint (a.val + c.val) ≠ 0 ∧
      encodePoint (a.val + b.val) ≠ encodePoint (a.val + c.val) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← encodePoint_zero]
    exact fun h => hab (Subtype.ext (eq_of_add_eq_zero _ _ (encodePoint_injective h)))
  · rw [← encodePoint_zero]
    exact fun h => hac (Subtype.ext (eq_of_add_eq_zero _ _ (encodePoint_injective h)))
  · exact fun h => hbc (Subtype.ext (add_left_cancel (encodePoint_injective h)))

theorem pair_completion (i : Fin 348) (dimension : Nat) (data : PairData)
    (hcheck : pairDataCheck (i.val + 1) dimension data = true)
    (P : Finset (Point 9)) (hcard : P.card = dimension + 1)
    (hAI : AffineIndependent Field ((↑) : P → Point 9)) :
    ∃ G : Finset (Point 9),
      MatchSupportMoments 3 G (decodeWord (Certificate.seed (i.val + 1))) ∧
        (G ∆ P).card ≤ 31 := by
  have hc := hcheck
  simp only [pairDataCheck, Bool.and_eq_true_iff, and_assoc] at hc
  have hsize := of_decide_eq_true hc.1
  have hderive := indexedDerivationCheck_sound _ _ _ _ hc.2.1
  have hcoverage := of_decide_eq_true hc.2.2.1
  obtain ⟨a, b, c, hab, hac, hbc, hfalse⟩ :=
    exists_missing_triple data.table hsize.1 hc.2.2.2 P hcard hAI
  obtain ⟨ha, hb, hne⟩ := triple_directions_valid a b c hab hac hbc
  have havailable (x : Point 9)
      (h : PairPlaneCertificates.IndexCovers data.steps data.locations (encodePoint x)) :
      PairAvailable (decodeWord (Certificate.seed (i.val + 1)))
        (Certificate.seed (i.val + 1)).length x := by
    obtain ⟨k, hk⟩ := PairPlaneCertificates.indexCovers_marked _ _ _ h
    have hh := SmallPairCertificates.trace_available i data.steps hderive k
    rw [hk, decodePoint_encodePoint] at hh
    exact hh
  have hbound : (Certificate.seed (i.val + 1)).length + P.card ≤ 35 := by omega
  rcases hcoverage _ _ ha hb hne hfalse with hmarked | hmarked | hmarked
  · exact AvailableConfigurations.pair_completion (Certificate.seed_support_properties i).2.2.1
      a.val b.val a.property b.property (fun h => hab (Subtype.ext h)) (havailable _ hmarked) hbound
  · exact AvailableConfigurations.pair_completion (Certificate.seed_support_properties i).2.2.1
      a.val c.val a.property c.property (fun h => hac (Subtype.ext h)) (havailable _ hmarked) hbound
  · rw [← encodePoint_add, shared_point_sum] at hmarked
    exact AvailableConfigurations.pair_completion (Certificate.seed_support_properties i).2.2.1
      b.val c.val b.property c.property (fun h => hbc (Subtype.ext h)) (havailable _ hmarked) hbound

theorem triple_completion (i : Fin 348) (data : TripleData)
    (hcheck : tripleDataCheck (i.val + 1) data = true)
    (P : Finset (Point 9)) (hcard : P.card = 9)
    (hAI : AffineIndependent Field ((↑) : P → Point 9)) :
    ∃ G : Finset (Point 9),
      MatchSupportMoments 3 G (decodeWord (Certificate.seed (i.val + 1))) ∧
        (G ∆ P).card ≤ 31 := by
  have hc := hcheck
  simp only [tripleDataCheck, Bool.and_eq_true_iff, and_assoc] at hc
  have hweight := of_decide_eq_true hc.1
  have hderive := indexedDerivationCheck_sound _ _ _ _ hc.2.1
  have hcoverage := of_decide_eq_true hc.2.2.1
  obtain ⟨a, b, c, hab, hac, hbc, hfalse⟩ :=
    exists_missing_triple data.table (dimension := 8) (by decide) hc.2.2.2 P hcard hAI
  obtain ⟨ha, hb, hne⟩ := triple_directions_valid a b c hab hac hbc
  have hmarked := TripleCertificates.coverage_marked data.table ⟨data.steps⟩ data.locations
    hcoverage _ _ ha hb hne hfalse
  have havailable := TripleCertificates.marked_available i ⟨data.steps⟩
    ⟨hweight, hderive⟩ _ hmarked
  simp only [decodePoint_encodePoint] at havailable
  apply AvailableConfigurations.triple_completion (Certificate.seed_support_properties i).2.2.1
    a.val b.val c.val a.property b.property c.property (fun h => hab (Subtype.ext h))
    (fun h => hac (Subtype.ext h)) (fun h => hbc (Subtype.ext h)) havailable
  omega

end Lemmata.RM59.SimplexSearchCertificates
