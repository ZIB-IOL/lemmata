module

public import Lemmata.RM59.Proof.SimplexSearchCertificates
public meta import Lemmata.RM59.Proof.SimplexSearchCertificates

@[expose] public section

namespace Lemmata.RM59.SimplexSearchFinder

open scoped symmDiff
open Packed SimplexSearchCertificates

structure Closure (α : Type*) where
  steps : Array (DerivationStep α)
  roots : Array Nat
  locations : Array Nat
  seen : Array Bool

def closure {α : Type*} (seeds : List α) (moves : Array (α → α))
    (cell : α → Nat) (count : Nat) (keep : α → Bool) : Closure α := Id.run do
  let mut steps : Array (DerivationStep α) := #[]
  let mut roots : Array Nat := #[]
  let mut seen : Array Bool := Array.replicate count false
  let mut locations : Array Nat := Array.replicate count 0
  for entry in seeds.zipIdx do
    let x := entry.1
    if keep x && !(seen[cell x]?.getD false) then
      locations := locations.set! (cell x) steps.size
      seen := seen.set! (cell x) true
      steps := steps.push ⟨x, none⟩
      roots := roots.push entry.2
  for j in List.range count do
    if let some step := steps[j]? then
      for k in List.range moves.size do
        if let some move := moves[k]? then
          let x := move step.value
          if !(seen[cell x]?.getD false) then
            locations := locations.set! (cell x) steps.size
            seen := seen.set! (cell x) true
            steps := steps.push ⟨x, some (j, k)⟩
            roots := roots.push 0
  return ⟨steps, roots, locations, seen⟩

def pairCell (p : PackedPoint × PackedPoint) : Nat := 512 * p.1.val + p.2.val

def findPairData (family : Nat) : PairData :=
  let reached := closure (SmallPairCertificates.pairSeeds family)
    (SmallPairCertificates.familyMoves family) Fin.val 512 (fun _ => true)
  let table := Array.ofFn fun i : Fin (512 * 512) =>
    let a : PackedPoint := ⟨i.val / 512, by have hi := i.isLt; omega⟩
    let b : PackedPoint := ⟨i.val % 512, Nat.mod_lt _ (by decide)⟩
    a != 0 && b != 0 && a != b &&
      !(reached.seen[a.val]?.getD false) && !(reached.seen[b.val]?.getD false) &&
      !(reached.seen[(xorPoint a b).val]?.getD false)
  ⟨reached.steps, reached.roots, reached.locations, table⟩

def findTripleData (family : Nat) : TripleData :=
  let reached := closure (TripleCertificates.tripleSeeds family)
    (TripleCertificates.tripleMoves family) pairCell (512 * 512)
    (fun p => p.1 < p.2 && p.2 < xorPoint p.1 p.2)
  let table := Array.ofFn fun i : Fin (512 * 512) =>
    let a : PackedPoint := ⟨i.val / 512, by have hi := i.isLt; omega⟩
    let b : PackedPoint := ⟨i.val % 512, Nat.mod_lt _ (by decide)⟩
    a != 0 && b != 0 && a != b && !(reached.seen[i.val]?.getD false)
  ⟨reached.steps, reached.roots, reached.locations, table⟩

def pairCaseCheck (family dimension : Nat) : Bool :=
  pairDataCheck family dimension (findPairData family)

def tripleCaseCheck (family : Nat) : Bool :=
  tripleDataCheck family (findTripleData family)

def pilotCheck (family26 family28 : Nat) : Bool :=
  decide ((Certificate.seed family26).length = 26 ∧
    (Certificate.seed family28).length = 28) &&
    pairCaseCheck family26 8 && pairCaseCheck family28 6 && tripleCaseCheck family28

theorem pairCaseCheck_completion (i : Fin 348) (dimension : Nat)
    (hcheck : pairCaseCheck (i.val + 1) dimension = true)
    (P : Finset (Point 9)) (hcard : P.card = dimension + 1)
    (hAI : AffineIndependent Field ((↑) : P → Point 9)) :
    ∃ G : Finset (Point 9),
      MatchSupportMoments 3 G (decodeWord (Certificate.seed (i.val + 1))) ∧
        (G ∆ P).card ≤ 31 :=
  SimplexSearchCertificates.pair_completion i dimension (findPairData (i.val + 1))
    hcheck P hcard hAI

theorem tripleCaseCheck_completion (i : Fin 348)
    (hcheck : tripleCaseCheck (i.val + 1) = true)
    (P : Finset (Point 9)) (hcard : P.card = 9)
    (hAI : AffineIndependent Field ((↑) : P → Point 9)) :
    ∃ G : Finset (Point 9),
      MatchSupportMoments 3 G (decodeWord (Certificate.seed (i.val + 1))) ∧
        (G ∆ P).card ≤ 31 :=
  SimplexSearchCertificates.triple_completion i (findTripleData (i.val + 1)) hcheck P hcard hAI

end Lemmata.RM59.SimplexSearchFinder
