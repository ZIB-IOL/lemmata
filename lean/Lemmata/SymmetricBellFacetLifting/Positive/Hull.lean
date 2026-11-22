module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Tactic.NormNum
public import Lemmata.SymmetricBellFacetLifting.Positive.Finite

/-! Convex-hull consequence of checked integer one-norm bounds and axis witnesses. -/

@[expose] public section
noncomputable section
namespace Lemmata.SymmetricBellFacetLifting.Positive

open scoped BigOperators

def axisVec {d : Nat} (i : Fin d) : Fin d → ℝ := fun j => if j = i then 1 else 0

def signedSet (d : Nat) : Set (Fin d → ℝ) :=
  {x | ∃ i, x = axisVec i ∨ x = -axisVec i}

/-- The ordinary real coordinate cross-polytope. -/
def unitCross (d : Nat) : Set (Fin d → ℝ) := convexHull ℝ (signedSet d)

private theorem axis_mem {d : Nat} (i : Fin d) :
    axisVec i ∈ unitCross d ∧ -axisVec i ∈ unitCross d := by
  exact ⟨subset_convexHull ℝ _ ⟨i, Or.inl rfl⟩,
         subset_convexHull ℝ _ ⟨i, Or.inr rfl⟩⟩

private theorem origin_mem {d : Nat} (hd : 0 < d) : (0 : Fin d → ℝ) ∈ unitCross d := by
  let i : Fin d := ⟨0, hd⟩
  have h := (convex_convexHull ℝ (signedSet d)) (axis_mem i).1 (axis_mem i).2
    (a := (1/2 : ℝ)) (b := (1/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  simpa [unitCross] using h

/-- A point satisfying the one-norm inequality is a convex combination of
the signed coordinate vectors. Residual mass is placed at their midpoint. -/
theorem mem_unitCross_of_sum_abs {d : Nat} (hd : 0 < d) (x : Fin d → ℝ)
    (h : ∑ i, |x i| ≤ 1) : x ∈ unitCross d := by
  let w : Option (Fin d) → ℝ := fun j => match j with
    | none => 1 - ∑ i, |x i|
    | some i => |x i|
  let v : Option (Fin d) → (Fin d → ℝ) := fun j => match j with
    | none => 0
    | some i => if 0 ≤ x i then axisVec i else -axisVec i
  have hn (j) : 0 ≤ w j := by cases j <;> simp [w, sub_nonneg, h]
  have hs : ∑ j, w j = 1 := by rw [Fintype.sum_option]; simp [w]
  have hv (j) : v j ∈ unitCross d := by
    cases j with
    | none => exact origin_mem hd
    | some i =>
      dsimp [v]
      split_ifs <;> first | exact (axis_mem i).1 | exact (axis_mem i).2
  have hh := (convex_convexHull ℝ (signedSet d)).sum_mem
    (t := Finset.univ) (fun j _ => hn j) hs (fun j _ => hv j)
  have he : (∑ j, w j • v j) = x := by
    rw [Fintype.sum_option]
    ext k
    simp only [v, w, smul_zero, zero_add, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single k]
    · split_ifs with hk <;> simp [axisVec, abs_of_nonneg, abs_of_neg, hk, lt_of_not_ge]
    · intro j _ hne
      split_ifs <;> simp [axisVec, Ne.symm hne]
    · simp
  simpa [he, unitCross] using hh

/-- A generic convex-hull certificate. A one-norm bound on every atom gives
one containment and signed-axis realization gives the reverse. -/
theorem hull_eq_unitCross {d : Nat} (hd : 0 < d) {S : Set (Fin d → ℝ)}
    (bound : ∀ x ∈ S, ∑ i, |x i| ≤ 1) (attained : signedSet d ⊆ S) :
    convexHull ℝ S = unitCross d := by
  apply Set.Subset.antisymm
  · exact convexHull_min (fun x hx => mem_unitCross_of_sum_abs hd x (bound x hx))
      (convex_convexHull ℝ _)
  · exact convexHull_mono attained

/-- Set of real atoms in the integer certificate chart. The list equation states
exactly which integer vectors are the chart images of triples of sign rows. -/
def chartAtoms (m d D : Nat) (M : List (List Int)) : Set (Fin d → ℝ) :=
  {x | ∃ a ∈ signRows m, ∃ b ∈ signRows m, ∃ c ∈ signRows m, ∃ z : Fin d → ℤ,
    integerImage M (threeCoords m a b c) = List.ofFn z ∧
    ∀ i, x i = (z i : ℝ) / D}

/-- Convert an integer gauge certificate to the real norm inequality. -/
theorem norm_chartAtoms {m d D : Nat} {M : List (List Int)} (hD : 0 < D)
    (hb : ∀ a ∈ signRows m, ∀ b ∈ signRows m, ∀ c ∈ signRows m,
      gauge M (threeCoords m a b c) ≤ D) {x} (hx : x ∈ chartAtoms m d D M) :
    ∑ i, |x i| ≤ 1 := by
  obtain ⟨a,ha,b,hb',c,hc,z,hz,hx⟩ := hx
  have hs := hb a ha b hb' c hc
  unfold gauge at hs
  rw [hz, List.map_ofFn, List.sum_ofFn] at hs
  have hR : (0 : ℝ) < D := by exact_mod_cast hD
  simp_rw [hx, abs_div, abs_of_pos hR]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← div_eq_mul_inv, div_le_one hR]
  have ht : ∑ i, ((z i).natAbs : ℝ) ≤ D := by exact_mod_cast hs
  simpa [Nat.cast_natAbs, Int.cast_abs] using ht

private def listAxis {d : Nat} (i : Fin d) (v : ℤ) : List ℤ :=
  (List.range d).map fun j => if i.val = j then v else 0

private theorem axis_eq_ofFn {d : Nat} (i : Fin d) (v : ℤ) :
    listAxis i v = List.ofFn (fun j : Fin d => if i = j then v else 0) := by
  apply List.ext_getElem
  · simp [listAxis]
  · intro j hj hj'
    simp [listAxis, Fin.ext_iff]

private theorem axes_pos_neg {d : Nat} (i : Fin d) (v : ℤ) :
    listAxis i v ∈ axes d v ∧ (listAxis i v).map Neg.neg ∈ axes d v := by
  constructor <;>
    apply List.mem_flatMap.mpr <;>
    exact ⟨i.val,List.mem_range.mpr i.isLt,by simp [listAxis]⟩

/-- From the verified finite gauge and its signed-axis witnesses one obtains
a real convex-hull equality, in the certificate's normalized coordinates. -/
theorem hull_of_integer_certificate {m d D : Nat} {M : List (List Int)}
    (hd : 0 < d) (hD : 0 < D)
    (hb : ∀ a ∈ signRows m, ∀ b ∈ signRows m, ∀ c ∈ signRows m,
      gauge M (threeCoords m a b c) ≤ D)
    (hw : ∀ v ∈ axes d (D : ℤ),
      ∃ a ∈ signRows m, ∃ b ∈ signRows m, ∃ c ∈ signRows m,
        integerImage M (threeCoords m a b c) = v) :
    convexHull ℝ (chartAtoms m d D M) = unitCross d := by
  apply hull_eq_unitCross hd (fun _ hx => norm_chartAtoms hD hb hx)
  rintro x ⟨i, hp | hn⟩
  · obtain ⟨a,ha,b,hb',c,hc,he⟩ := hw _ (axes_pos_neg i (D : ℤ)).1
    refine ⟨a,ha,b,hb',c,hc,_,he.trans (axis_eq_ofFn i _),?_⟩
    intro j
    by_cases h : i = j <;> simp [hp, axisVec, h, eq_comm, hD.ne', Ne.symm]
  · obtain ⟨a,ha,b,hb',c,hc,he⟩ := hw _ (axes_pos_neg i (D : ℤ)).2
    rw [axis_eq_ofFn, List.map_ofFn] at he
    refine ⟨a,ha,b,hb',c,hc,_,he,?_⟩
    intro j
    by_cases h : i = j <;> simp [hn, axisVec, h, eq_comm, hD.ne', Ne.symm]

end Lemmata.SymmetricBellFacetLifting.Positive
