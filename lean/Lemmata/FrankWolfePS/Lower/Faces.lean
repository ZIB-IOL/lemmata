module

public import Lemmata.FrankWolfePS.Lower.Numerical
@[expose] public section

namespace Lemmata.FrankWolfePS
open Finset
open scoped RealInnerProductSpace BigOperators
section Ball
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem rolling_ball {K : Set E} {R : ℝ} {z n : E} (hR : 0 < R) (hz : z ∈ Rounded K R)
    (hn : ‖n‖ = 1) (hs : Supports (Rounded K R) z n) :
    Metric.closedBall (z - R • n) R ⊆ Rounded K R := by
  obtain ⟨u, hu, e, _⟩ := tangent_center hR hz hn hs
  rw [e, add_sub_cancel_right]
  exact fun w hw => ⟨u, hu, by simpa [Metric.mem_closedBall, dist_eq_norm] using hw⟩

omit [InnerProductSpace ℝ E] in
theorem rounded_interior_nonempty {K : Set E} {R : ℝ} (hR : 0 < R) (ne : K.Nonempty) :
    (interior (Rounded K R)).Nonempty := by
  obtain ⟨u, hu⟩ := ne
  refine ⟨u, mem_interior_iff_mem_nhds.mpr ?_⟩
  apply Filter.mem_of_superset (Metric.ball_mem_nhds u hR)
  exact fun w hw => ⟨u, hu, le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hw)⟩
end Ball

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem bottom_face (I : Finset ι) (R : ℝ) (x : ι → ℝ) :
    Feasible R I (x, 0) ↔ Base I x := by
  constructor
  · rintro ⟨u, hu, hb⟩
    have hd : sq (fun i => x i - u i) ≤ 0 := by simpa using hb
    have eq : x = u := by
      funext i
      have hi := single_le_sum (s := univ) (f := fun j => (x j - u j) ^ 2)
        (fun j _ => _root_.sq_nonneg _) (mem_univ i)
      change _ ≤ sq (fun i => x i - u i) at hi
      nlinarith [hi.trans hd]
    simpa [eq] using hu
  · intro hx; exact ⟨x, hx, by simp [sq]⟩

/-- A legal response to the nonzero vertical query reveals the whole hidden set. -/
theorem vertical_barycenter_reveals {I : Finset ι} (hne : I.Nonempty) {R : ℝ} (hR : 0 < R) :
    Feasible R I (simplexBarycenter I, 0) ∧
      (∀ z : Pt ι, Feasible R I z → 0 ≤ z.2) ∧
      univ.filter (fun i => simplexBarycenter I i ≠ 0) = I := by
  have hc : 0 < (I.card : ℝ) := by exact_mod_cast card_pos.mpr hne
  refine ⟨(bottom_face I R _).mpr (barycenter_base hne), fun _ hz => (horizontal_cost hR hz).1, ?_⟩
  ext i
  by_cases hi : i ∈ I <;> simp [simplexBarycenter, hi, hc.ne']

/-- A nonzero vertical direction has two distinct minimizing points when I has
two labels. This identifies the exact obstruction in this family. -/
theorem vertical_multiple_minimizers {I : Finset ι} (hc : 1 < I.card) {R : ℝ} (hR : 0 < R) :
    ∃ x y : Pt ι, x ≠ y ∧ Feasible R I x ∧ Feasible R I y ∧
      x.2 = 0 ∧ y.2 = 0 ∧ ∀ z : Pt ι, Feasible R I z → 0 ≤ z.2 := by
  obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.mp hc
  refine ⟨(atom i, 0), (atom j, 0), ?_, anchor_feasible R hi, anchor_feasible R hj, rfl, rfl, ?_⟩
  · intro he
    have h := congrArg (fun z : Pt ι => z.1 i) he
    simp [atom, hij] at h
  · intro z hz; exact (horizontal_cost hR hz).1
end Lemmata.FrankWolfePS
