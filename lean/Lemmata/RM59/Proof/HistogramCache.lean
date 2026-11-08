module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Init.Data.Array.OfFn
public import Init.Data.List.Monadic

@[expose] public section

namespace Lemmata.RM59.HistogramCache

open scoped BigOperators

variable {α : Type*}

def step (color : α → ℕ) (predicate : α → Bool) (histogram : Array ℕ) (w : α) : Array ℕ :=
  if predicate w then histogram.modify (color w) (· + 1) else histogram

@[simp] theorem step_size (color : α → ℕ) (predicate : α → Bool)
    (histogram : Array ℕ) (w : α) :
    (step color predicate histogram w).size = histogram.size := by
  unfold step
  cases h : predicate w <;> simp

theorem modify_getD (histogram : Array ℕ) (index r : ℕ) (hr : r < histogram.size) :
    (histogram.modify index (· + 1))[r]?.getD 0 =
      histogram[r]?.getD 0 + if index = r then 1 else 0 := by
  rw [Array.getElem?_modify]
  by_cases h : index = r
  · simp [h, Array.getElem?_eq_some_getElem histogram r hr]
  · simp [h]

def accumulate (color : α → ℕ) (predicate : α → Bool) (vertices : List α)
    (histogram : Array ℕ) : Array ℕ :=
  vertices.foldl (step color predicate) histogram

theorem accumulate_size (color : α → ℕ) (predicate : α → Bool) (vertices : List α)
    (histogram : Array ℕ) :
    (accumulate color predicate vertices histogram).size = histogram.size := by
  induction vertices generalizing histogram with
  | nil => rfl
  | cons w vertices ih =>
    change (accumulate color predicate vertices (step color predicate histogram w)).size = _
    rw [ih, step_size]

theorem accumulate_getD (color : α → ℕ) (predicate : α → Bool) (vertices : List α)
    (histogram : Array ℕ) (r : ℕ) (hr : r < histogram.size) :
    (accumulate color predicate vertices histogram)[r]?.getD 0 = histogram[r]?.getD 0 +
      (vertices.map fun w => if predicate w ∧ color w = r then 1 else 0).sum := by
  induction vertices generalizing histogram with
  | nil => simp [accumulate]
  | cons w vertices ih =>
    change (accumulate color predicate vertices (step color predicate histogram w))[r]?.getD 0 = _
    have hr' : r < (step color predicate histogram w).size := by simpa using hr
    rw [ih _ hr']
    cases h : predicate w <;>
      simp [step, h, modify_getD histogram (color w) r hr, Nat.add_assoc]

def histogram (classes : ℕ) (vertices : List α) (color : α → ℕ) (predicate : α → Bool) :
    Array ℕ := Id.run do
  let mut result := Array.replicate classes 0
  for w in vertices do
    if predicate w then result := result.modify (color w) (· + 1)
  return result

theorem histogram_eq_accumulate (classes : ℕ) (vertices : List α)
    (color : α → ℕ) (predicate : α → Bool) :
    histogram classes vertices color predicate =
      accumulate color predicate vertices (Array.replicate classes 0) := by
  let loop (vertices : List α) (initial : Array ℕ) : Array ℕ := Id.run do
    let mut result := initial
    for w in vertices do
      if predicate w then result := result.modify (color w) (· + 1)
    return result
  have hloop : ∀ vertices initial, loop vertices initial =
      accumulate color predicate vertices initial := by
    intro vertices
    induction vertices with
    | nil => intro initial; rfl
    | cons w vertices ih =>
      intro initial
      cases h : predicate w
      · simpa [loop, accumulate, step, List.forIn_cons, h] using ih initial
      · simpa [loop, accumulate, step, List.forIn_cons, h] using
          ih (initial.modify (color w) (· + 1))
  exact hloop vertices (Array.replicate classes 0)

@[simp] theorem histogram_size (classes : ℕ) (vertices : List α)
    (color : α → ℕ) (predicate : α → Bool) :
    (histogram classes vertices color predicate).size = classes := by
  rw [histogram_eq_accumulate, accumulate_size]
  simp

theorem histogram_getD (classes : ℕ) (vertices : List α) (color : α → ℕ)
    (predicate : α → Bool) (r : ℕ) (hr : r < classes) :
    (histogram classes vertices color predicate)[r]?.getD 0 =
      (vertices.map fun w => if predicate w ∧ color w = r then 1 else 0).sum := by
  rw [histogram_eq_accumulate, accumulate_getD color predicate vertices _ r (by simpa using hr)]
  simp [hr]

theorem histogram_eq_ofFn (classes : ℕ) (vertices : List α) (color : α → ℕ)
    (predicate : α → Bool) :
    histogram classes vertices color predicate = Array.ofFn (fun r : Fin classes =>
      (vertices.map fun w => if predicate w ∧ color w = r.val then 1 else 0).sum) := by
  apply Array.ext
  · simp
  · intro r hr₁ hr₂
    rw [Array.getElem_ofFn]
    have hr : r < classes := by simpa using hr₁
    have h := histogram_getD classes vertices color predicate r hr
    simpa only [Array.getElem?_eq_some_getElem _ _ hr₁, Option.getD_some] using h

theorem histogram_toList (classes : ℕ) (vertices : List α) (color : α → ℕ)
    (predicate : α → Bool) :
    (histogram classes vertices color predicate).toList = List.ofFn (fun r : Fin classes =>
      (vertices.map fun w => if predicate w ∧ color w = r.val then 1 else 0).sum) := by
  rw [histogram_eq_ofFn, Array.toList_ofFn]

theorem range_sum_eq (count : ℕ) (f : ℕ → ℕ) :
    ((List.range count).map f).sum = ∑ w : Fin count, f w.val := by
  calc
    ((List.range count).map f).sum = ∑ w ∈ Finset.range count, f w := by
      simpa only [List.toFinset_range] using
        (List.sum_toFinset f (l := List.range count) List.nodup_range).symm
    _ = ∑ w : Fin count, f w.val := Finset.sum_range f

theorem histogram_range_getD (classes count : ℕ) (color : ℕ → ℕ)
    (predicate : ℕ → Bool) (r : ℕ) (hr : r < classes) :
    (histogram classes (List.range count) color predicate)[r]?.getD 0 =
      ∑ w : Fin count, if predicate w.val ∧ color w.val = r then 1 else 0 := by
  rw [histogram_getD classes _ color predicate r hr]
  exact range_sum_eq count _

theorem histogram_range_toList (classes count : ℕ) (color : ℕ → ℕ)
    (predicate : ℕ → Bool) :
    (histogram classes (List.range count) color predicate).toList = List.ofFn
      (fun r : Fin classes => ∑ w : Fin count,
        if predicate w.val ∧ color w.val = r.val then 1 else 0) := by
  rw [histogram_toList]
  apply congrArg List.ofFn
  funext r
  exact range_sum_eq count _

end Lemmata.RM59.HistogramCache
