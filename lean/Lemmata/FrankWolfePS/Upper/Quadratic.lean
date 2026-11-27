module

public import Lemmata.FrankWolfePS.Upper.FW
@[expose] public section

namespace Lemmata.FrankWolfePS.Upper
open scoped RealInnerProductSpace Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def iso (L : ℝ) (u x : E) : ℝ := L / 2 * ‖x - u‖ ^ 2
def isoGrad (L : ℝ) (u x : E) : E := L • (x - u)
noncomputable def liftInner (r : ℝ) (u a : E) : E := a + clip r (u - a)
noncomputable def envelope (L r : ℝ) (u a : E) : ℝ := iso L u (liftInner r u a)
noncomputable def envGrad (L r : ℝ) (u a : E) : E := isoGrad L u (liftInner r u a)

theorem iso_taylor (L : ℝ) (u x y : E) :
    iso L u y = iso L u x + ⟪isoGrad L u x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  unfold iso isoGrad
  rw [show y - u = (x - u) + (y - x) by abel, norm_add_sq_real, real_inner_smul_left]
  ring

theorem lift_mem {K : Set E} {r : ℝ} (hr : 0 ≤ r) (u : E) {a : E} (ha : a ∈ K) :
    liftInner r u a ∈ Rounded K r := ⟨a, ha, by simpa [liftInner] using norm_clip hr (u - a)⟩

theorem lift_vi {L r : ℝ} (hL : 0 ≤ L) (hr : 0 ≤ r) (u a b : E) (hb : ‖b‖ ≤ r) :
    0 ≤ ⟪envGrad L r u a, b - clip r (u - a)⟫ := by
  have h := clip_vi hr (u - a) b hb
  unfold envGrad isoGrad liftInner
  rw [show a + clip r (u - a) - u =
      -((u - a) - clip r (u - a)) by abel, real_inner_smul_left, inner_neg_left]
  exact mul_nonneg hL (neg_nonneg.mpr h)

theorem lift_min {L r : ℝ} (hL : 0 ≤ L) (hr : 0 ≤ r) (u a b : E) (hb : ‖b‖ ≤ r) :
    envelope L r u a ≤ iso L u (a + b) := by
  have H := iso_taylor L u (liftInner r u a) (a + b)
  have e : a + b - liftInner r u a = b - clip r (u - a) := by unfold liftInner; abel
  rw [e] at H
  have h := lift_vi hL hr u a b hb
  unfold envelope
  change 0 ≤ ⟪isoGrad L u (liftInner r u a), _⟫ at h
  nlinarith [mul_nonneg (show 0 ≤ L / 2 by positivity) (_root_.sq_nonneg ‖b - clip r (u - a)‖)]

theorem envelope_models {L r : ℝ} (hL : 0 ≤ L) (hr : 0 ≤ r) (u : E) (K : Set E) :
    Models K (envelope L r u) (envGrad L r u) L := by
  constructor
  · intro a _ v _
    have h := iso_taylor L u (liftInner r u a) (liftInner r u v)
    have e : liftInner r u v - liftInner r u a = (v - a) + (clip r (u - v) - clip r (u - a)) := by
      unfold liftInner; abel
    rw [e, inner_add_right] at h
    have pos := lift_vi hL hr u a _ (norm_clip hr (u - v))
    unfold envelope envGrad at *
    nlinarith [mul_nonneg (show 0 ≤ L / 2 by positivity) (_root_.sq_nonneg ‖v - a +
        (clip r (u - v) - clip r (u - a))‖)]
  · intro a _ v _
    apply (lift_min hL hr u v _ (norm_clip hr (u - a))).trans
    have h := iso_taylor L u (liftInner r u a) (v + clip r (u - a))
    rw [show v + clip r (u - a) - liftInner r u a = v - a by unfold liftInner; abel] at h
    exact h.le

noncomputable def realQueryCost (q : E) : ℕ := if q = 0 then 0 else 1
omit [InnerProductSpace ℝ E] in
theorem realQueryCost_le (q : E) : realQueryCost q ≤ 1 := by unfold realQueryCost; split <;> omega

/-- Only this simulator is used by the algorithm; its inputs contain no core.
The first query and its gradient are shared, and zero directions reuse p. -/
noncomputable def quadraticRun {C : Set E} (O : LMO C) (gradient : E → E) (L r : ℝ)
    (e : E) (steps : ℕ) : E × ℕ × ℕ :=
  let z := O.query e
  let p := z + r • unit e
  let u := z - L⁻¹ • gradient z
  let coreQuery := fun q => if q = 0 then p else unwrap O r q
  let v := fwRun (envGrad L r u) coreQuery realQueryCost p steps
  (liftInner r u v.1, 1 + v.2, 1)

theorem recover_center {L : ℝ} (hL : 0 < L) (u z : E) : z - L⁻¹ • isoGrad L u z = u := by
  simp [isoGrad, smul_smul, hL.ne']

/-- One initialization call and n+1 core steps. The returned objective bound
holds against every feasible comparator and for every exact oracle selector. -/
theorem quadratic_parallel_upper {K : Set E} (hK : Convex ℝ K) {r D L : ℝ}
    (hr : 0 < r) (hD : 2 * r ≤ D) (hL : 0 < L)
    (width : ∀ x ∈ Rounded K r, ∀ y ∈ Rounded K r, ‖x - y‖ ≤ D)
    (O : LMO (Rounded K r)) (u e : E) (he : e ≠ 0) (n : ℕ) :
    let result := quadraticRun O (isoGrad L u) L r e (n + 1)
    result.1 ∈ Rounded K r ∧ result.2.1 ≤ n + 2 ∧ result.2.2 = 1 ∧
    ∀ w ∈ Rounded K r, iso L u result.1 - iso L u w ≤ 2 * L * (D - 2 * r) ^ 2 / ((n : ℝ) + 3) := by
  let p := unwrap O r e
  have hp : p ∈ K := (unwrap_spec hr O he).1
  let V := coreLMO hr O p hp
  let v := fwRun (envGrad L r u) V.query realQueryCost p (n + 1)
  simp only [quadraticRun, recover_center hL]
  change liftInner r u v.1 ∈ _ ∧ 1 + v.2 ≤ n + 2 ∧ _ ∧ _
  have hmem : v.1 ∈ K := fwRun_mem hK V _ _ hp _
  have cnt : v.2 ≤ n + 1 := fwRun_cost _ _ _ realQueryCost_le _ _
  refine ⟨lift_mem hr.le u hmem, by omega, trivial, ?_⟩
  rintro w ⟨a, ha, haw⟩
  have h := fw_rate hK (envelope_models hL.le hr.le u K) hL.le
    (fun _ hx _ hy => core_width hr hD width hx hy) V realQueryCost hp ha n
  have comp := lift_min hL.le hr.le u a (w - a) haw
  rw [show a + (w - a) = w by abel] at comp
  change envelope L r u v.1 - iso L u w ≤ _
  change envelope L r u v.1 - envelope L r u a ≤ _ at h
  rw [mul_assoc 2 L]
  linarith only [h, comp]

/-- At D=2r the very same black-box procedure with zero FW steps is exact. -/
theorem quadratic_ball_exact {K : Set E} {r L : ℝ} (hr : 0 < r) (hL : 0 < L)
    (width : ∀ x ∈ Rounded K r, ∀ y ∈ Rounded K r, ‖x - y‖ ≤ 2 * r)
    (O : LMO (Rounded K r)) (u e : E) (he : e ≠ 0) :
    let z := quadraticRun O (isoGrad L u) L r e 0
    z.1 ∈ Rounded K r ∧ z.2 = (1, 1) ∧ ∀ w ∈ Rounded K r, iso L u z.1 ≤ iso L u w := by
  let p := unwrap O r e
  have hp : p ∈ K := (unwrap_spec hr O he).1
  simp only [quadraticRun, recover_center hL, fwRun]
  refine ⟨lift_mem hr.le u hp, trivial, ?_⟩
  rintro w ⟨a, ha, haw⟩
  have h := core_width hr (by rfl : 2 * r ≤ 2 * r) width ha hp
  rw [sub_self, norm_le_zero_iff, sub_eq_zero] at h
  subst a
  have best := lift_min hL.le hr.le u p (w - p) haw
  rw [show p + (w - p) = w by abel] at best
  exact best

end Lemmata.FrankWolfePS.Upper
