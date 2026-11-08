module

public import Lemmata.RM59.Proof.AvailableConfigurations
public import Lemmata.RM59.Proof.PlaneGeometry
public import Lemmata.RM59.Proof.PackedLinear
public import Lemmata.RM59.Compute.SimplexSearch
public meta import Lemmata.RM59.Compute.SimplexSearch

@[expose] public section

namespace Lemmata.RM59.PlaneCertificates

open Packed PlaneGeometry

abbrev PackedAllowed := PackedPoint → PackedPoint → Bool

def semantic (allowed : PackedAllowed) (a b : Point 9) : Prop :=
  allowed (encodePoint a) (encodePoint b) = true

theorem encodePoint_injective : Function.Injective encodePoint :=
  pointEquiv.symm.injective

@[simp] theorem encodePoint_zero : encodePoint 0 = 0 := by
  apply decodePoint_injective
  simp only [decodePoint_encodePoint, decodePoint_zero]

theorem encodePoint_add (x y : Point 9) :
    encodePoint (x + y) = xorPoint (encodePoint x) (encodePoint y) := by
  apply decodePoint_injective
  simp only [decodePoint_encodePoint, decodePoint_xorPoint]

end Lemmata.RM59.PlaneCertificates

namespace Lemmata.RM59.PlaneDeletion

open PlaneGeometry

theorem allTriplePlanes_reindex {ι κ : Type*} (allowed : Point 9 → Point 9 → Prop)
    (p : ι → Point 9) (f : κ → ι) (hf : Function.Injective f)
    (hp : AllTriplePlanes allowed p) : AllTriplePlanes allowed (p ∘ f) := by
  intro i j k hij hik hjk
  exact hp (f i) (f j) (f k) (fun heq => hij (hf heq))
    (fun heq => hik (hf heq)) (fun heq => hjk (hf heq))

end Lemmata.RM59.PlaneDeletion

namespace Lemmata.RM59.SmallPairCertificates

open Packed AvailableConfigurations SupportForms

def pairSeeds (family : Nat) : List PackedPoint :=
  (Certificate.familyWords family).flatMap fun word =>
    word.flatMap fun x =>
      (word.filter fun y => decide (x ≠ y)).map fun y => xorPoint x y

def familySymmetries (family : Nat) : List (Nat × List PackedPoint) :=
  Certificate.symmetries.toList.filter fun entry => decide (entry.1 = family)

def familyMoves (family : Nat) : Array (PackedPoint → PackedPoint) :=
  (familySymmetries family).toArray.map fun entry =>
    evalColumns (Certificate.symmetryColumns entry.2)

theorem pairSeeds_available (i : Fin 348) :
    ∀ x ∈ pairSeeds (i.val + 1),
      PairAvailable (decodeWord (Certificate.seed (i.val + 1)))
        (Certificate.seed (i.val + 1)).length (decodePoint x) := by
  intro d hd
  obtain ⟨word, hword, hd⟩ := List.mem_flatMap.mp hd
  obtain ⟨x, hx, hd⟩ := List.mem_flatMap.mp hd
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hd
  obtain ⟨hy, hne⟩ := List.mem_filter.mp hy
  exact family_pair_seed i word hword x y hx hy (of_decide_eq_true hne)

theorem familyMoves_available (i : Fin 348) :
    ∀ k : Fin (familyMoves (i.val + 1)).size, ∀ x,
      PairAvailable (decodeWord (Certificate.seed (i.val + 1)))
        (Certificate.seed (i.val + 1)).length (decodePoint x) →
      PairAvailable (decodeWord (Certificate.seed (i.val + 1)))
        (Certificate.seed (i.val + 1)).length
          (decodePoint ((familyMoves (i.val + 1))[k.val] x)) := by
  intro k x hx
  have hmem : (familyMoves (i.val + 1))[k.val] ∈ familyMoves (i.val + 1) :=
    Array.getElem_mem k.isLt
  obtain ⟨entry, hentry, heq⟩ := Array.mem_map.mp hmem
  have hfiltered := List.mem_toArray.mp hentry
  obtain ⟨hentry, hfamily⟩ := List.mem_filter.mp hfiltered
  rw [← heq]
  exact family_pair_move i entry hentry (of_decide_eq_true hfamily) x hx

abbrev Marked (steps : Array (DerivationStep PackedPoint)) (x : PackedPoint) : Prop :=
  ∃ i : Fin steps.size, steps[i.val].value = x

theorem trace_available (i : Fin 348) (steps : Array (DerivationStep PackedPoint))
    (htrace : DerivationValid (pairSeeds (i.val + 1)) (familyMoves (i.val + 1)) steps) :
    ∀ k : Fin steps.size,
      PairAvailable (decodeWord (Certificate.seed (i.val + 1)))
        (Certificate.seed (i.val + 1)).length (decodePoint steps[k.val].value) :=
  derivation_sound
    (fun x => PairAvailable (decodeWord (Certificate.seed (i.val + 1)))
      (Certificate.seed (i.val + 1)).length (decodePoint x))
    (pairSeeds (i.val + 1)) (familyMoves (i.val + 1)) steps htrace
    (pairSeeds_available i) (familyMoves_available i)

end Lemmata.RM59.SmallPairCertificates

namespace Lemmata.RM59.TripleCertificates

open Packed AvailableConfigurations PlaneGeometry PlaneCertificates PlaneFinder

abbrev PackedPair := PackedPoint × PackedPoint

def tripleSeeds (family : Nat) : List PackedPair :=
  (Certificate.familyWords family).flatMap fun word =>
    word.flatMap fun x => word.flatMap fun y =>
      (word.filter fun z => decide (x ≠ y ∧ x ≠ z ∧ y ≠ z)).map fun z =>
        (xorPoint x y, xorPoint x z)

def swapPair (p : PackedPair) : PackedPair := (p.2, p.1)

def shearPair (p : PackedPair) : PackedPair := (p.1, xorPoint p.1 p.2)

def tripleMoves (family : Nat) : Array (PackedPair → PackedPair) :=
  #[swapPair, shearPair] ++
    (SmallPairCertificates.familySymmetries family).toArray.map fun entry p =>
      (evalColumns (Certificate.symmetryColumns entry.2) p.1,
        evalColumns (Certificate.symmetryColumns entry.2) p.2)

theorem tripleSeeds_available (i : Fin 348) :
    ∀ p ∈ tripleSeeds (i.val + 1),
      TripleAvailable (decodeWord (Certificate.seed (i.val + 1)))
        (Certificate.seed (i.val + 1)).length (decodePoint p.1) (decodePoint p.2) := by
  intro p hp
  obtain ⟨word, hword, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨x, hx, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨y, hy, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hp
  obtain ⟨hz, hne⟩ := List.mem_filter.mp hz
  have hdistinct := of_decide_eq_true hne
  exact family_triple_seed i word hword x y z hx hy hz
    hdistinct.1 hdistinct.2.1 hdistinct.2.2

theorem tripleMoves_available (i : Fin 348) :
    ∀ k : Fin (tripleMoves (i.val + 1)).size, ∀ p,
      TripleAvailable (decodeWord (Certificate.seed (i.val + 1)))
        (Certificate.seed (i.val + 1)).length (decodePoint p.1) (decodePoint p.2) →
      TripleAvailable (decodeWord (Certificate.seed (i.val + 1)))
        (Certificate.seed (i.val + 1)).length
        (decodePoint (((tripleMoves (i.val + 1))[k.val] p).1))
        (decodePoint (((tripleMoves (i.val + 1))[k.val] p).2)) := by
  intro k p hp
  have hmem : (tripleMoves (i.val + 1))[k.val] ∈ tripleMoves (i.val + 1) :=
    Array.getElem_mem k.isLt
  rcases Array.mem_append.mp hmem with hmem | hmem
  · simp only [Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with heq | heq
    · rw [heq]
      exact hp.swap
    · rw [heq]
      simpa only [shearPair, decodePoint_xorPoint] using hp.shear
  · obtain ⟨entry, hentry, heq⟩ := Array.mem_map.mp hmem
    have hfiltered := List.mem_toArray.mp hentry
    obtain ⟨hentry, hfamily⟩ := List.mem_filter.mp hfiltered
    rw [← heq]
    exact family_triple_move i entry hentry (of_decide_eq_true hfamily) p.1 p.2 hp

structure TripleData where
  steps : Array (DerivationStep PackedPair)

def TripleValid (family : Nat) (data : TripleData) : Prop :=
  (Certificate.seed family).length ≤ 28 ∧
    DerivationValid (tripleSeeds family) (tripleMoves family) data.steps

instance (family : Nat) (data : TripleData) : Decidable (TripleValid family data) := by
  unfold TripleValid
  infer_instance

abbrev Marked (steps : Array (DerivationStep PackedPair)) (p : PackedPair) : Prop :=
  ∃ i : Fin steps.size, steps[i.val].value = p

theorem marked_available (i : Fin 348) (data : TripleData)
    (hvalid : TripleValid (i.val + 1) data) (p : PackedPair) (hp : Marked data.steps p) :
    TripleAvailable (decodeWord (Certificate.seed (i.val + 1)))
      (Certificate.seed (i.val + 1)).length (decodePoint p.1) (decodePoint p.2) :=
  derivation_covers
    (fun p => TripleAvailable (decodeWord (Certificate.seed (i.val + 1)))
      (Certificate.seed (i.val + 1)).length (decodePoint p.1) (decodePoint p.2))
    (tripleSeeds (i.val + 1)) (tripleMoves (i.val + 1)) data.steps hvalid.2
    (tripleSeeds_available i) (tripleMoves_available i) p hp

def coverageIndex (locations : Array Nat) (a b : PackedPoint) : Nat :=
  locations[512 * a.val + b.val]?.getD 0

def CoverageValid (table : Array Bool) (data : TripleData) (locations : Array Nat) : Prop :=
  ∀ a b : PackedPoint, a ≠ 0 → b ≠ 0 → a ≠ b → lookup table a b = false →
    if hj : coverageIndex locations a b < data.steps.size then
      data.steps[coverageIndex locations a b].value = (a, b)
    else False

instance (table : Array Bool) (data : TripleData) (locations : Array Nat) :
    Decidable (CoverageValid table data locations) := by
  unfold CoverageValid
  infer_instance

theorem coverage_marked (table : Array Bool) (data : TripleData) (locations : Array Nat)
    (h : CoverageValid table data locations) (a b : PackedPoint)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (hfalse : lookup table a b = false) :
    Marked data.steps (a, b) := by
  have hv := h a b ha hb hab hfalse
  by_cases hj : coverageIndex locations a b < data.steps.size
  · exact ⟨⟨coverageIndex locations a b, hj⟩, by simpa only [dif_pos hj] using hv⟩
  · simp only [dif_neg hj] at hv

end Lemmata.RM59.TripleCertificates

namespace Lemmata.RM59.PairPlaneCertificates

open Packed AvailableConfigurations PlaneGeometry PlaneCertificates PlaneFinder
open SmallPairCertificates

def locationIndex (locations : Array Nat) (x : PackedPoint) : Nat :=
  locations[x.val]?.getD 0

def IndexCovers (steps : Array (DerivationStep PackedPoint))
    (locations : Array Nat) (x : PackedPoint) : Prop :=
  if hj : locationIndex locations x < steps.size then
    steps[locationIndex locations x].value = x
  else False

instance (steps : Array (DerivationStep PackedPoint)) (locations : Array Nat) (x : PackedPoint) :
    Decidable (IndexCovers steps locations x) := by
  unfold IndexCovers
  infer_instance

def PairCoverageValid (table : Array Bool) (steps : Array (DerivationStep PackedPoint))
    (locations : Array Nat) : Prop :=
  ∀ a b : PackedPoint, a ≠ 0 → b ≠ 0 → a ≠ b → lookup table a b = false →
    IndexCovers steps locations a ∨ IndexCovers steps locations b ∨
      IndexCovers steps locations (xorPoint a b)

instance (table : Array Bool) (steps : Array (DerivationStep PackedPoint)) (locations : Array Nat) :
    Decidable (PairCoverageValid table steps locations) := by
  unfold PairCoverageValid
  infer_instance

theorem indexCovers_marked (steps : Array (DerivationStep PackedPoint))
    (locations : Array Nat) (x : PackedPoint) (h : IndexCovers steps locations x) :
    Marked steps x := by
  by_cases hj : locationIndex locations x < steps.size
  · exact ⟨⟨locationIndex locations x, hj⟩, by simpa only [IndexCovers, dif_pos hj] using h⟩
  · simp only [IndexCovers, dif_neg hj] at h

end Lemmata.RM59.PairPlaneCertificates
