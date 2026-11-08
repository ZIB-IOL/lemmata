module

public import Lemmata.RM59.Proof.CatalogUniformCheck
public import Lemmata.RM59.Proof.CatalogRunBound
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace Lemmata.RM59.CatalogUniform

open scoped BigOperators
open CatalogForms CatalogSeparation

def catalogResults : Array Result := Array.ofFn fun i : Fin 348 => run (i.val + 1)

def catalogUpper (family : Fin 348) : Nat := (run (family.val + 1)).bound

def catalogOrbitLower (family : Fin 348) : Nat := generalLinearOrder 9 / catalogUpper family

def resultsCheck (results : Array Result) (gl : Nat) : Bool :=
  results.all (fun result => result.valid && result.bound > 0 && gl % result.bound == 0) &&
    results.foldl (fun mass result => mass + gl / result.bound) 1 == 2 ^ 84 &&
    (results.toList.map Result.invariant).Nodup

theorem resultsCheck_parts (results : Array Result) (gl : Nat)
    (hcheck : resultsCheck results gl = true) :
    results.all (fun result => result.valid && result.bound > 0 && gl % result.bound == 0) = true ∧
    results.foldl (fun mass result => mass + gl / result.bound) 1 = 2 ^ 84 ∧
    (results.toList.map Result.invariant).Nodup := by
  unfold resultsCheck at hcheck
  have h := Bool.and_eq_true_iff.mp hcheck
  have hleft := Bool.and_eq_true_iff.mp h.1
  exact ⟨hleft.1, beq_iff_eq.mp hleft.2, of_decide_eq_true h.2⟩

theorem catalogCheck_eq_resultsCheck :
    catalogCheck = resultsCheck catalogResults (generalLinearOrder 9) := by
  unfold catalogCheck resultsCheck catalogResults
  rfl

theorem checked_parts :
    catalogResults.all (fun result => result.valid && result.bound > 0 &&
      generalLinearOrder 9 % result.bound == 0) = true ∧
    catalogResults.foldl (fun mass result => mass + generalLinearOrder 9 / result.bound) 1 = 2 ^ 84 ∧
    (catalogResults.toList.map Result.invariant).Nodup := by
  apply resultsCheck_parts
  exact catalogCheck_eq_resultsCheck ▸ catalog_checked

theorem checked_result (family : Fin 348) :
    (run (family.val + 1)).valid = true ∧ 0 < catalogUpper family ∧
      generalLinearOrder 9 % catalogUpper family = 0 := by
  have hi : family.val < catalogResults.size := by simp [catalogResults]
  have h := Array.all_eq_true.mp checked_parts.1 family.val hi
  have hget : catalogResults[family.val] = run (family.val + 1) := by
    simp only [catalogResults, Array.getElem_ofFn]
  rw [hget] at h
  simp only [Bool.and_eq_true_iff, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem fold_add_eq_sum {α : Type*} (values : List α) (f : α → Nat) (start : Nat) :
    values.foldl (fun acc value => acc + f value) start = start + (values.map f).sum := by
  induction values generalizing start with
  | nil => simp
  | cons value values ih => simp [List.foldl_cons, ih, Nat.add_assoc]

theorem fold_mul_eq_prod {α : Type*} (values : List α) (f : α → Nat) (start : Nat) :
    values.foldl (fun acc value => acc * f value) start = start * (values.map f).prod := by
  induction values generalizing start with
  | nil => simp
  | cons value values ih => simp [List.foldl_cons, ih, Nat.mul_assoc]

theorem array_fold_add_sum {α : Type*} (n : Nat) (values : Fin n → α)
    (f : α → Nat) (start : Nat) :
    (Array.ofFn values).foldl (fun acc value => acc + f value) start =
      start + ∑ i, f (values i) := by
  rw [← Array.foldl_toList, Array.toList_ofFn, fold_add_eq_sum, List.map_ofFn, List.sum_ofFn]
  rfl

theorem mass_bridge {n : Nat} (results : Array Result) (values : Fin n → Result)
    (lower : Fin n → Nat) (gl target : Nat)
    (hresults : results = Array.ofFn values)
    (hterms : ∀ i, lower i = gl / (values i).bound)
    (hmass : results.foldl (fun mass result => mass + gl / result.bound) 1 = target) :
    1 + ∑ i, lower i = target := by
  rw [hresults, ← Array.foldl_toList, Array.toList_ofFn, fold_add_eq_sum,
    List.map_ofFn, List.sum_ofFn] at hmass
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hterms i)
  exact (congrArg (fun k : Nat => 1 + k) hsum).trans hmass

theorem checked_mass : 1 + ∑ family : Fin 348, catalogOrbitLower family = 2 ^ 84 := by
  apply mass_bridge catalogResults (fun family : Fin 348 => run (family.val + 1))
    catalogOrbitLower (generalLinearOrder 9) (2 ^ 84)
  · unfold catalogResults
    rfl
  · intro family
    unfold catalogOrbitLower catalogUpper
    rfl
  · exact checked_parts.2.1

theorem generalLinearOrder_eq_binary (n : Nat) :
    generalLinearOrder n = binaryGeneralLinearOrder n := by
  rw [generalLinearOrder, fold_mul_eq_prod, Nat.one_mul]
  change ((List.range n).map (fun j => 2 ^ n - 2 ^ j)).prod = _
  calc
    ((List.range n).map (fun j => 2 ^ n - 2 ^ j)).prod =
        ∏ j ∈ Finset.range n, (2 ^ n - 2 ^ j) := by
      simpa only [List.toFinset_range] using
        (List.prod_toFinset (fun j => 2 ^ n - 2 ^ j)
          (l := List.range n) List.nodup_range).symm
    _ = binaryGeneralLinearOrder n := Finset.prod_range _

theorem checked_product (family : Fin 348) :
    catalogOrbitLower family * catalogUpper family = Fintype.card (CoordinateGroup 9) := by
  calc
    catalogOrbitLower family * catalogUpper family = generalLinearOrder 9 :=
      Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero (checked_result family).2.2)
    _ = Fintype.card (CoordinateGroup 9) := by
      rw [generalLinearOrder_eq_binary, ← coordinateGroup_card, Nat.card_eq_fintype_card]

theorem checked_invariant_injective :
    Function.Injective (fun family : Fin 348 => (run (family.val + 1)).invariant) := by
  have h := checked_parts.2.2
  have hlist : catalogResults.toList.map Result.invariant =
      List.ofFn (fun family : Fin 348 => (run (family.val + 1)).invariant) := by
    rw [catalogResults, Array.toList_ofFn, List.map_ofFn]
    apply congrArg List.ofFn
    funext family
    rfl
  rw [hlist] at h
  exact List.nodup_ofFn.mp h

theorem run_formInvariant (family : Fin 348) :
    (run (family.val + 1)).invariant = formInvariant (representative family) := by
  rw [run_invariant]
  exact geometry_invariant_semantic family

theorem representative_invariant_injective :
    Function.Injective (fun family : Fin 348 => formInvariant (representative family)) := by
  intro i j hij
  apply checked_invariant_injective
  exact (run_formInvariant i).trans (hij.trans (run_formInvariant j).symm)

theorem representative_orbits_separate (i j : Fin 348) (hij : i ≠ j) :
    representative i ∉ MulAction.orbit (CoordinateGroup 9) (representative j) :=
  orbit_separation_of_invariant representative formInvariant formInvariant_action
    representative_invariant_injective i j hij

theorem catalog_cover : ∀ T : CubicForm, T = 0 ∨
    ∃ family : Fin 348, T ∈ MulAction.orbit (CoordinateGroup 9) (representative family) := by
  apply catalog_covering_of_orbit_mass_fixed (G := CoordinateGroup 9)
    (0 : CubicForm) representative catalogUpper catalogOrbitLower
  · exact cubicForm_smul_zero
  · exact representative_ne_zero
  · exact representative_orbits_separate
  · intro family
    exact (checked_result family).2.1
  · exact checked_product
  · intro family
    exact run_stabilizer_bound family (checked_result family).1
  · exact cubicForm_card_le.trans (le_of_eq checked_mass.symm)

end Lemmata.RM59.CatalogUniform
