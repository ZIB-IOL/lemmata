module

public import Lemmata.RM59.Proof.SimplexSearchFinder
public meta import Lemmata.RM59.Proof.SimplexSearchFinder
public meta import Lean.Elab.Tactic.Decide

@[expose] public section

namespace Lemmata.RM59.SimplexSearchChecks

open scoped symmDiff
open Packed SimplexSearchFinder

def families (weight : Nat) : List Nat :=
  (List.range 348).filterMap fun i =>
    if (Certificate.seed (i + 1)).length = weight then some (i + 1) else none

def cases : List (Nat × Nat) :=
  (families 26).map (fun family => (family, 0)) ++
    (families 28).map (fun family => (family, 1)) ++
    (families 28).map (fun family => (family, 2))

def caseCheck (entry : Nat × Nat) : Bool :=
  match entry.2 with
  | 0 => pairCaseCheck entry.1 8
  | 1 => pairCaseCheck entry.1 6
  | 2 => tripleCaseCheck entry.1
  | _ => false

theorem cases_count : cases.length = 243 := by native_decide

theorem weight26_cases_complete : ∀ i : Fin 348,
    (Certificate.seed (i.val + 1)).length = 26 →
      ∃ j : Fin 243, cases[j.val]?.getD (0, 0) = (i.val + 1, 0) := by
  native_decide

theorem weight28_pair_cases_complete : ∀ i : Fin 348,
    (Certificate.seed (i.val + 1)).length = 28 →
      ∃ j : Fin 243, cases[j.val]?.getD (0, 0) = (i.val + 1, 1) := by
  native_decide

theorem weight28_triple_cases_complete : ∀ i : Fin 348,
    (Certificate.seed (i.val + 1)).length = 28 →
      ∃ j : Fin 243, cases[j.val]?.getD (0, 0) = (i.val + 1, 2) := by
  native_decide

def chunkCheck (chunk : Nat) : Bool :=
  (List.finRange 243).all fun i =>
    if i.val % 4 = chunk then caseCheck (cases[i.val]?.getD (0, 0)) else true

theorem chunk_case (chunk : Nat) (h : chunkCheck chunk = true)
    (i : Fin 243) (hi : i.val % 4 = chunk) :
    caseCheck (cases[i.val]?.getD (0, 0)) = true := by
  have hc := List.all_eq_true.mp h i (List.mem_finRange i)
  simpa only [if_pos hi] using hc

theorem all_cases_checked (hchunks : ∀ chunk : Fin 4, chunkCheck chunk.val = true)
    (i : Fin 243) : caseCheck (cases[i.val]?.getD (0, 0)) = true :=
  chunk_case (i.val % 4) (hchunks ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩) i rfl

theorem weight26_completion (hchunks : ∀ chunk : Fin 4, chunkCheck chunk.val = true)
    (i : Fin 348) (hweight : (Certificate.seed (i.val + 1)).length = 26)
    (P : Finset (Point 9)) (hAI : AffineIndependent Field ((↑) : P → Point 9))
    (hcard : P.card = 9) :
    ∃ G : Finset (Point 9),
      MatchSupportMoments 3 G (decodeWord (Certificate.seed (i.val + 1))) ∧
        (G ∆ P).card ≤ 31 := by
  obtain ⟨j, hj⟩ := weight26_cases_complete i hweight
  have hc := all_cases_checked hchunks j
  rw [hj] at hc
  exact pairCaseCheck_completion i 8 hc P hcard hAI

theorem weight28_seven_completion (hchunks : ∀ chunk : Fin 4, chunkCheck chunk.val = true)
    (i : Fin 348) (hweight : (Certificate.seed (i.val + 1)).length = 28)
    (P : Finset (Point 9)) (hAI : AffineIndependent Field ((↑) : P → Point 9))
    (hcard : P.card = 7) :
    ∃ G : Finset (Point 9),
      MatchSupportMoments 3 G (decodeWord (Certificate.seed (i.val + 1))) ∧
        (G ∆ P).card ≤ 31 := by
  obtain ⟨j, hj⟩ := weight28_pair_cases_complete i hweight
  have hc := all_cases_checked hchunks j
  rw [hj] at hc
  exact pairCaseCheck_completion i 6 hc P hcard hAI

theorem weight28_nine_completion (hchunks : ∀ chunk : Fin 4, chunkCheck chunk.val = true)
    (i : Fin 348) (hweight : (Certificate.seed (i.val + 1)).length = 28)
    (P : Finset (Point 9)) (hAI : AffineIndependent Field ((↑) : P → Point 9))
    (hcard : P.card = 9) :
    ∃ G : Finset (Point 9),
      MatchSupportMoments 3 G (decodeWord (Certificate.seed (i.val + 1))) ∧
        (G ∆ P).card ≤ 31 := by
  obtain ⟨j, hj⟩ := weight28_triple_cases_complete i hweight
  have hc := all_cases_checked hchunks j
  rw [hj] at hc
  exact tripleCaseCheck_completion i hc P hcard hAI

end Lemmata.RM59.SimplexSearchChecks
