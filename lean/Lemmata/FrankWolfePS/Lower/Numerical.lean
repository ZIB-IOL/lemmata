module

public import Lemmata.FrankWolfePS.Lower.Geometry
public import Lemmata.FrankWolfePS.Lower.Random
public import Lemmata.FrankWolfePS.Model
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Data.Finset.Sort

@[expose] public section

namespace Lemmata.FrankWolfePS
open Finset
open scoped BigOperators RealInnerProductSpace

variable {ι : Type*} [Fintype ι]

def atom [DecidableEq ι] (i : ι) (j : ι) : ℝ := if j = i then 1 else 0

omit [Fintype ι] in
theorem atom_base [DecidableEq ι] {I : Finset ι} {i : ι} (hi : i ∈ I) : Base I (atom i) := by
  classical
  refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
  · unfold atom; split <;> norm_num
  · have ne : j ≠ i := fun he => hj (he ▸ hi)
    simp [atom, ne]
  · simp [atom, hi]

theorem anchor_feasible [DecidableEq ι] (R : ℝ) {I : Finset ι} {anchor : ι}
    (h : anchor ∈ I) : Feasible R I (atom anchor, 0) :=
  ⟨atom anchor, atom_base h, by simp [sq]⟩

theorem inner_embed (q : Ambient ι) (z : Pt ι) :
    ⟪q, embed z⟫ = (∑ i, q (some i) * z.1 i) + q none * z.2 := by
  rw [PiLp.inner_apply, Fintype.sum_option]
  simp [embed, mul_comm, add_comm]

theorem atom_core_min [DecidableEq ι] {I : Finset ι} {i : ι}
    (q : Ambient ι) (R : ℝ) (hm : ∀ j ∈ I, q (some i) ≤ q (some j)) :
    ∀ v ∈ core R I, ⟪q, embed (atom i, R)⟫ ≤ ⟪q, v⟫ := by
  classical
  rintro _ ⟨u, hu, rfl⟩
  simp only [inner_embed, add_le_add_iff_right]
  have hr : (∑ j ∈ I, q (some j) * u j) = ∑ j, q (some j) * u j :=
    sum_subset (subset_univ _) (fun j _ hj => by rw [hu.2.1 j hj, mul_zero])
  have H := sum_le_sum (s := I) (fun j hj => mul_le_mul_of_nonneg_right (hm j hj) (hu.1 j))
  rw [← mul_sum, hu.2.2, mul_one, hr] at H
  simpa [atom, mul_ite] using H

/-- Keep the original label order explicitly when constructing the query-specific key. -/
@[reducible] noncomputable def rankOrder (o : LinearOrder ι) (q : ι → ℝ) : LinearOrder ι := by
  letI := o
  exact LinearOrder.lift' (fun i => toLex (q i, i)) (fun a b h =>
    congrArg (fun z : Lex (ℝ × ι) => (ofLex z).2) h)

noncomputable def listing (o : LinearOrder ι) : List ι := by
  letI := o
  exact univ.sort (· ≤ ·)

theorem mem_listing (o : LinearOrder ι) (i : ι) : i ∈ listing o := by
  let := o
  simp [listing]

omit [Fintype ι] in
theorem first_some_min [DecidableEq ι] (r : ι → ι → Prop) (refl : ∀ i, r i i)
    (I : Finset ι) (l : List ι) (hs : l.Pairwise r)
    {i : ι} (ha : first I l = some i) :
    i ∈ I ∧ ∀ j ∈ l, j ∈ I → r i j := by
  induction l with
  | nil => simp [first] at ha
  | cons a l ih =>
    obtain ⟨hall, ht⟩ := List.pairwise_cons.mp hs
    by_cases haI : a ∈ I
    · simp [first, haI] at ha
      subst i
      refine ⟨haI, ?_⟩
      intro j hj _
      rcases List.mem_cons.mp hj with rfl | h
      · exact refl _
      · exact hall j h
    · have h := ih ht (by simpa [first, haI] using ha)
      refine ⟨h.1, ?_⟩
      intro j hj hjI
      rcases List.mem_cons.mp hj with rfl | h'
      · exact (haI hjI).elim
      · exact h.2 j h' hjI

omit [Fintype ι] in
theorem first_ne_none [DecidableEq ι] (I : Finset ι) (l : List ι) (i : ι) (hi : i ∈ I)
    (hl : i ∈ l) :
    first I l ≠ none := by
  induction l with
  | nil => simp at hl
  | cons a l ih =>
    by_cases ha : a ∈ I
    · simp [first, ha]
    · have h : i ∈ l := (List.mem_cons.mp hl).resolve_left (fun e => ha (e ▸ hi))
      simpa [first, ha] using ih h

theorem pairwise_listing (o : LinearOrder ι) : (listing o).Pairwise o.le := by
  let := o
  exact Finset.pairwise_sort _ _

theorem first_rank_spec [LinearOrder ι] (q : ι → ℝ) {I : Finset ι} (hne : I.Nonempty) :
    ∃ i ∈ I, first I (listing (rankOrder (inferInstance : LinearOrder ι) q)) = some i ∧
      ∀ j ∈ I, q i ≤ q j ∧ (q i = q j → i ≤ j) := by
  let l := listing (rankOrder (inferInstance : LinearOrder ι) q)
  obtain ⟨a, ha⟩ := hne
  have hne' := first_ne_none I l a ha (mem_listing _ a)
  obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hne'
  have hh := first_some_min _ (rankOrder (inferInstance : LinearOrder ι) q).le_refl I l
    (pairwise_listing (rankOrder (inferInstance : LinearOrder ι) q)) hi
  refine ⟨i, hh.1, hi, ?_⟩
  intro j hj
  have H := hh.2 j (mem_listing _ j) hj
  exact Prod.Lex.toLex_le_toLex'.mp H

section Numeric
variable [LinearOrder ι]
noncomputable def orderFor (q : Ambient ι) : List ι :=
  if q = 0 then [] else listing (rankOrder (inferInstance : LinearOrder ι) (fun i => q (some i)))

noncomputable def decode (R : ℝ) (anchor : ι) (q : Ambient ι) : Option ι → Ambient ι
  | none => embed (atom anchor, 0)
  | some i => embed (atom i, R) - R • unit q

noncomputable def oracle (R : ℝ) (anchor : ι) (I : Finset ι) (q : Ambient ι) : Ambient ι :=
  decode R anchor q (first I (orderFor q))

theorem oracle_correct (R : ℝ) (hR : 0 < R) (anchor : ι) (I : Finset ι) (hI : anchor ∈ I)
    (q : Ambient ι) :
    oracle R anchor I q ∈ Rounded (core R I) R ∧
    ∀ v ∈ Rounded (core R I) R, ⟪q, oracle R anchor I q⟫ ≤ ⟪q, v⟫ := by
  by_cases hq : q = 0
  · subst q
    simp only [oracle, orderFor, ite_true, first, decode, inner_zero_left, le_refl, implies_true,
        and_true]
    exact (feasible_iff_rounded hR _ _).mp (anchor_feasible R hI)
  · obtain ⟨i, hi, hfirst, hm⟩ := first_rank_spec (fun i => q (some i)) ⟨anchor, hI⟩
    simp only [oracle, orderFor, ite_eq_right hq, hfirst, decode]
    exact rounded_minimizer hq hR ⟨_, atom_base hi, rfl⟩ (atom_core_min q R fun j hj =>
        (hm j hj).1)

/-- A method against the vertex oracle, compiled into ordered membership scans: each call scans
the labels in the order of its direction and continues with the decoded reply. -/
noncomputable def Method.orders {t} (s : Method (Ambient ι) t) (R : ℝ) (a : ι) :
    Orders ι (Pt ι) t :=
  match s with
  | .ret z => .ret (coords z)
  | .ask q next => .ask (orderFor q) (fun j => (next (decode R a q j)).orders R a)

theorem Method.orders_run {t} (s : Method (Ambient ι) t) (R : ℝ) (a : ι) (I : Finset ι) :
    (s.orders R a).run I = coords (s.run (oracle R a I)) := by
  induction s with
  | ret => rfl
  | ask q next ih => simp [orders, Orders.run, Method.run, oracle, ih]

variable {Ω : Type*} [MeasurableSpace Ω]
open MeasureTheory

theorem numerical_randomized_lower_bound (T : ℕ) (a : ι) (hN : Fintype.card ι = 256 * (T + 1))
    (R : ℝ) (hR : 0 < R) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Ω → Method (Ambient ι) T)
    (meas : ∀ S ∈ shells T a, MeasurableSet {ω | failure R (T + 1) (insert a S)
      (coords ((s ω).run (oracle R a (insert a S))))}) :
    (↑(shells T a).card : ℝ) / 4 ≤ ∑ S ∈ shells T a,
      μ.real {ω | failure R (T + 1) (insert a S) (coords ((s ω).run (oracle R a (insert a S))))} ∧
      ∃ S ∈ shells T a, 1 / 4 ≤ μ.real {ω | failure R (T + 1) (insert a S)
        (coords ((s ω).run (oracle R a (insert a S))))} := by
  simpa only [badSeeds, Method.orders_run] using
    randomized_lower_bound T a hN R hR μ (fun ω => (s ω).orders R a)
      (by simpa only [badSeeds, Method.orders_run] using meas)
end Numeric
end Lemmata.FrankWolfePS
