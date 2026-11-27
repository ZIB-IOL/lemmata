module

public import Lemmata.FrankWolfePS.Unique.Stability

@[expose] public section

/-!
# Transferring a failure from the base body to the jittered body

If the repaired output fails on the base body (it is infeasible there, or its gap is at least
`A² / (16 k)`), the original output fails on the jittered body at any threshold `θ` that leaves
room for the perturbation: `θ + (A + 35)(2A + 5) h ≤ A² / (16 k)`.
-/

namespace Lemmata.FrankWolfePS.Unique
open Finset
open scoped BigOperators RealInnerProductSpace
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Failure on a body: the point is infeasible, or its gap for `cost` is at least `θ`. -/
def Bad (C : Set (Ambient ι)) (θ : ℝ) (x : Ambient ι) : Prop := x ∉ C ∨ θ ≤ cost x - valC C

/-- The public repair towards the anchor vertex `(A e_a, 1)`. -/
noncomputable def repaired (A : ℝ) (a : ι) (h : ℝ) (x : Ambient ι) : Ambient ι :=
  repair (baseV A a) h x

theorem jitter_nonneg {A : ℝ} {I : Finset ι} (hne : I.Nonempty) {v : ι → Ambient ι} {η : ℝ}
    (near : ∀ j, ‖v j - baseV A j‖ ≤ η) : 0 ≤ η :=
  (norm_nonneg _).trans (near hne.choose)

/-- The jittered bodies are within `2h` of the base diameter `2 + √2 A`. -/
theorem smooth_diameter {A : ℝ} (hA : 0 < A) {I : Finset ι} (size : 1 < I.card)
    {v : ι → Ambient ι} {η s h : ℝ} (hs : 0 ≤ s) (hclose : η + s ≤ h)
    (near : ∀ j, ‖v j - baseV A j‖ ≤ η) :
    Metric.diam (Body v s I) ≤ 2 + Real.sqrt 2 * A + 2 * h := by
  have hη := jitter_nonneg (Finset.card_pos.mp (by omega : 0 < I.card)) near
  have h0 : 0 ≤ h := by linarith
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  intro x hx y hy
  obtain ⟨w, hw, hw'⟩ := near_old hA hs near hx
  obtain ⟨z, hz, hz'⟩ := near_old hA hs near hy
  have hd := Metric.dist_le_diam_of_mem
    (physical_body_compact_convex (a := A) (r := 1) I).1.isBounded hw hz
  rw [(physical_parameters hA one_pos I size).1] at hd
  have H := dist_triangle x w y
  have G := dist_triangle w z y
  rw [← dist_eq_norm] at hw' hz'
  rw [dist_comm z y] at G
  linarith

/-- The base optimum is attained. -/
theorem old_min {A : ℝ} (hA : 0 < A) {I : Finset ι} {a : ι} (ai : a ∈ I) :
    ∃ m ∈ Old A I, cost m = physicalOpt 1 A 1 I := by
  have hs : embed (coords (start A a)) ∈ physicalBody A 1 I := by
    rw [embed_coords]
    refine (mem_old hA I _).mpr ⟨atom a, atom_base ai, ?_⟩
    have H := embed_dist_sq ((A • atom a, 0) : Pt ι) (A • atom a, 1)
    simp [sq] at H
    change ‖embed (A • atom a, 0) - embed (A • atom a, 1)‖ ≤ 1
    rcases H with h | h <;> linarith
  have hcont : Continuous fun z : Pt ι => 1 * obj 1 z := continuous_const.mul (obj_continuous 1)
  obtain ⟨z, hz, hmin⟩ := (physical_compact_points hA one_pos I).exists_isMinOn ⟨_, hs⟩
    hcont.continuousOn
  refine ⟨embed z, hz, ?_⟩
  rw [cost_obj, coords_embed]
  refine Eq.symm (IsLeast.csInf_eq ⟨⟨z, hz, ?_⟩, ?_⟩)
  · simp
  · rintro _ ⟨w, hw, rfl⟩
    simpa using hmin hw

/-- A failure of the repaired output on the base body is a failure of the output on the
jittered body, at any threshold `θ` with room for the perturbation. -/
theorem loss_transfer {A : ℝ} (hA : 0 < A) {a : ι} {I : Finset ι} (ai : a ∈ I)
    {v : ι → Ambient ι} {s η h θ : ℝ} {k : ℕ} (hs : 0 ≤ s) (hp : 0 < h) (h1 : h ≤ 1)
    (close : η + s ≤ h) (room : θ + (A + 35) * (2 * A + 5) * h ≤ A ^ 2 / (16 * k))
    (near : ∀ j, ‖v j - baseV A j‖ ≤ η) {x : Ambient ι}
    (bad : physicalFailure 1 A 1 k I (coords (repaired A a h x))) : Bad (Body v s I) θ x := by
  classical
  by_cases hx : x ∈ Body v s I
  · right
    obtain ⟨z, hz, hd⟩ := near_old hA hs near hx
    have nx : ‖x‖ ≤ A + 3 := by
      have H := norm_add_le (x - z) z
      simp only [sub_add_cancel] at H
      linarith [old_norm hA hz]
    have ball : ∀ y, ‖y - baseV A a‖ ≤ 1 → y ∈ Old A I := fun y hy =>
      (mem_old hA I y).mpr ⟨atom a, atom_base ai, by simpa [baseV] using hy⟩
    generalize hx' : repaired A a h x = x' at bad
    rw [repaired] at hx'
    have xm : x' ∈ Old A I :=
      hx' ▸ repair_mem (physical_body_compact_convex I).2 ball hp hz (hd.trans close)
    have gap := bad.resolve_left (by rw [embed_coords]; exact not_not.mpr xm)
    rw [← cost_obj, one_mul, one_mul] at gap
    obtain ⟨m, hm, em⟩ := old_min hA ai
    obtain ⟨y, hy, yd⟩ := near_new hA hs near hm
    have hη : 0 ≤ η := jitter_nonneg ⟨a, ai⟩ near
    have ny : ‖y‖ ≤ A + 3 := by
      have H := norm_add_le (y - m) m
      simp only [sub_add_cancel] at H
      linarith [old_norm hA hm]
    have yu := cost_diff (x := y) (y := m) ny
    have hco : Continuous (cost (ι := ι)) := by unfold cost quadratic; fun_prop
    have inf : valC (Body v s I) ≤ cost y :=
      csInf_le ((geometry v hs I).1.bddBelow_image hco.continuousOn) ⟨y, hy, rfl⟩
    have diff := cost_diff (x := x') (y := x) (old_norm hA xm)
    have dr := hx' ▸ repair_dist (baseV A a) x hp
    have nb : ‖baseV A a‖ ≤ A + 1 := base_norm hA.le (atom_base ai)
    have e1 : ‖x' - x‖ ≤ h * (2 * A + 4) :=
      dr.trans (mul_le_mul_of_nonneg_left (by linarith) hp.le)
    have e2 : (A + 2 + 32) * ‖x' - x‖ ≤ (A + 2 + 32) * (h * (2 * A + 4)) :=
      mul_le_mul_of_nonneg_left e1 (by linarith)
    have e3 : (A + 3 + 32) * ‖y - m‖ ≤ (A + 3 + 32) * h :=
      mul_le_mul_of_nonneg_left (yd.trans (by linarith)) (by linarith)
    have e4 : (A + 2 + 32) * (h * (2 * A + 4)) + (A + 3 + 32) * h ≤
        (A + 35) * (2 * A + 5) * h := by
      nlinarith
    linarith
  · exact Or.inl hx

end Lemmata.FrankWolfePS.Unique
