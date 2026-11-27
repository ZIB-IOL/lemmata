module

public import Lemmata.FrankWolfePS.Lower.Numerical
public import Lemmata.FrankWolfePS.Lower.Transcript
@[expose] public section

namespace Lemmata.FrankWolfePS
open Finset
variable {ι : Type*}

section Scan
variable [DecidableEq ι]

def scanBits (I : Finset ι) : List ι → List (ι × Bool)
  | [] => []
  | i::l => if i ∈ I then [(i, true)] else (i, false)::scanBits I l

private theorem winner_mem (I : Finset ι) (l : List ι) {j : ι} (hj : first I l = some j) :
    j ∈ I := by
  induction l with
  | nil => simp [first] at hj
  | cons i l ih =>
    by_cases h : i ∈ I
    · simp [first, h] at hj; simpa [← hj] using h
    · exact ih (by simpa [first, h] using hj)

theorem first_eq_iff_agrees (I J : Finset ι) (l : List ι) :
    first J l = first I l ↔ agrees J (scanBits I l) := by
  induction l with
  | nil => simp [first, agrees, scanBits]
  | cons i l ih =>
    by_cases hi : i ∈ I <;> by_cases hj : i ∈ J
    · simp [first, agrees, scanBits, hi, hj]
    · have ne : first J l ≠ some i := fun e => hj (winner_mem J l e)
      simp [first, agrees, scanBits, hi, hj, ne]
    · have ne : some i ≠ first I l := fun e => hi (winner_mem I l e.symm)
      simp [first, agrees, scanBits, hi, hj, ne]
    · simp [first, agrees, scanBits, hi, hj, ih]
end Scan

variable [Fintype ι] [LinearOrder ι]

theorem decode_some_injective (R : ℝ) (a : ι) (q : Ambient ι) :
    Function.Injective (fun i => decode R a q (some i)) := by
  intro i j h
  have e : embed (atom i, R) = embed (atom j, R) := sub_left_injective h
  by_contra ne
  have z := congrArg (fun w : Ambient ι => w (some i)) e
  simp [embed, atom, ne] at z

theorem oracle_eq_iff_agrees (R : ℝ) (a : ι) {I J : Finset ι} (hi : a ∈ I) (hj : a ∈ J)
    (q : Ambient ι) :
    oracle R a J q = oracle R a I q ↔ agrees J (scanBits I (orderFor q)) := by
  rw [← first_eq_iff_agrees]
  by_cases hz : q = 0
  · simp [oracle, orderFor, hz, first]
  · obtain ⟨i, _, ei, _⟩ := first_rank_spec (fun i => q (some i)) ⟨a, hi⟩
    obtain ⟨j, _, ej, _⟩ := first_rank_spec (fun i => q (some i)) ⟨a, hj⟩
    simp only [oracle, orderFor, ite_eq_right hz, ei, ej, Option.some.injEq]
    exact (decode_some_injective R a q).eq_iff

noncomputable def Method.numericTrace {t} (s : Method (Ambient ι) t) (R : ℝ) (a : ι)
    (I : Finset ι) : List (Ambient ι × Ambient ι) :=
  match s with
  | .ret _ => []
  | .ask q next => let v := oracle R a I q
                   (q, v)::(next v).numericTrace R a I

noncomputable def Method.observations {t} (s : Method (Ambient ι) t) (R : ℝ) (a : ι)
    (I : Finset ι) : List (ι × Bool) :=
  match s with
  | .ret _ => []
  | .ask q next => scanBits I (orderFor q) ++ (next (oracle R a I q)).observations R a I

omit [Fintype ι] in
theorem agrees_append (J : Finset ι) (l m : List (ι × Bool)) :
    agrees J (l ++ m) ↔ agrees J l ∧ agrees J m := by
  constructor
  · intro H
    exact ⟨fun e he => H e (List.mem_append.mpr (.inl he)), fun e he =>
        H e (List.mem_append.mpr (.inr he))⟩
  · rintro ⟨hl, hm⟩ e he
    exact (List.mem_append.mp he).elim (hl e) (hm e)

/-- Equality of full real-valued numerical histories, in both directions,
is exactly satisfaction of all tested membership literals. -/
theorem numerical_trace_fiber {t} (s : Method (Ambient ι) t) (R : ℝ) (a : ι) {I J : Finset ι}
    (hi : a ∈ I) (hj : a ∈ J) :
    s.numericTrace R a J = s.numericTrace R a I ↔ agrees J (s.observations R a I) := by
  induction s with
  | ret z => simp [Method.numericTrace, Method.observations, agrees]
  | ask q next ih =>
    simp only [Method.numericTrace, Method.observations, List.cons.injEq, Prod.mk.injEq, true_and,
        agrees_append]
    have e := oracle_eq_iff_agrees R a hi hj q
    constructor
    · rintro ⟨h, ht⟩
      rw [h] at ht
      exact ⟨e.mp h, (ih _).mp ht⟩
    · rintro ⟨h, ht⟩
      have he := e.mpr h
      exact ⟨he, by rw [he]; exact (ih _).mpr ht⟩

/-- Under the finite uniform prior, both filters give the actual posterior
support, each listed completion having the same prior weight. -/
theorem numerical_posterior (T : ℕ) (s : Method (Ambient ι) T) (R : ℝ) (a : ι) {I : Finset ι}
    (hi : a ∈ I) :
    (instanceSets T a).filter (fun S => s.numericTrace R a (insert a S) = s.numericTrace R a I) =
    (instanceSets T a).filter
      (fun S => ∀ e ∈ s.observations R a I, decide (e.1 ∈ insert a S) = e.2) := by
  ext S
  simp only [mem_filter, numerical_trace_fiber s R a hi (mem_insert_self _ _), agrees]
end Lemmata.FrankWolfePS
