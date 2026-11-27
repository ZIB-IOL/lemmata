module
public import Lemmata.FrankWolfePS.Joint.Geometry
@[expose] public section
namespace Lemmata.FrankWolfePS.Joint
open Upper
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Chord-ball convention with strong-convexity parameter 1/R. -/
def ChordBall (C : Set E) (R : ℝ) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ b : E,
    ‖b‖ ≤ t * (1 - t) * (‖y - x‖ ^ 2 / (2 * R)) → blend t x y + b ∈ C

theorem outer_of_chord {C : Set E} {R : ℝ} (hR : 0 < R) (chord : ChordBall C R) :
    OuterBall C R := by
  intro s hs n hn sup a ha
  let A := ‖a - s‖ ^ 2 / (2 * R)
  let B := ⟪n, s - a⟫
  have b0 : 0 ≤ B := by dsimp [B]; rw [inner_sub_right]; linarith [sup a ha]
  have limit : A ≤ B := by
    by_contra! h
    have a0 := b0.trans_lt h
    let t := (A - B) / (2 * A)
    have h0 : 0 < t := div_pos (sub_pos.mpr h) (by positivity)
    have h1 : t ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    let rad := t * (1 - t) * A
    have rad0 : 0 ≤ rad := mul_nonneg (mul_nonneg h0.le (sub_nonneg.mpr h1)) a0.le
    have mem :=
        chord s hs a ha t h0.le h1 (rad • n)
          (by change ‖rad • n‖ ≤ rad; simp [norm_smul, hn, abs_of_nonneg rad0])
    have S := sup _ mem
    simp only [blend, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hn] at S
    have bound : t * ((1 - t) * A) ≤ t * B := by
      dsimp [rad] at S; dsimp [B]; rw [inner_sub_right]; linarith only [S]
    have H := (mul_le_mul_iff_right₀ h0).mp bound
    have e : t * (2 * A) = A - B := by dsimp [t]; field_simp
    linarith only [H, e, h]
  have mul := (div_le_iff₀ (by positivity : 0 < 2 * R)).mp limit
  change ‖a - (s - R • n)‖ ≤ R
  rw [show a - (s - R • n) = (a - s) + R • n by abel]
  have sq : ‖(a - s) + R • n‖ ^ 2 ≤ R ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, real_inner_comm n (a - s), norm_smul,
      Real.norm_eq_abs, abs_of_pos hR, hn, inner_sub_right]
    dsimp [B] at mul; rw [inner_sub_right] at mul
    nlinarith only [mul]
  nlinarith only [sq, hR.le, norm_nonneg ((a - s) + R • n)]

/-- Interior rolling at each supporting normal, in radius units. -/
def InnerBall (C : Set E) (r : ℝ) : Prop :=
  ∀ z ∈ C, ∀ n : E, ‖n‖ = 1 → Supports C z n →
    ∀ b : E, ‖b‖ ≤ r → z - r • n + b ∈ C

theorem normals_of_inner {C : Set E} {r : ℝ} (hr : 0 ≤ r) (innerBall : InnerBall C r) :
    NormalBound C r := by
  intro z hz y hy n m hn hm ns ms
  have tangent (x y v w : E) (hx : x ∈ C) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
      (hxs : Supports C x v) (hys : Supports C y w) :
      r * (1 - ⟪w, v⟫) ≤ ⟪w, y - x⟫ := by
    have S := hys _ (innerBall x hx v hv hxs (r • w) (by simp [norm_smul, abs_of_nonneg hr, hw]))
    simp only [inner_add_right, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
        hw] at S
    rw [inner_sub_right]; linarith
  have h1 := tangent z y n m hz hn hm ns ms
  have h2 := tangent y z m n hy hm hn ms ns
  have N : r * ‖m - n‖ ^ 2 ≤ ⟪m - n, y - z⟫ := by
    rw [norm_sub_sq_real, hm, hn, inner_sub_left, real_inner_comm n m]
    simp only [inner_sub_right] at *
    rw [real_inner_comm n m] at h1
    linarith
  have H := N.trans (real_inner_le_norm _ _)
  by_cases zero : ‖m - n‖ = 0
  · simp [zero]
  · apply le_of_mul_le_mul_left (a := ‖m - n‖) _ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm zero))
    linarith only [H]

theorem inner_of_normals [ProperSpace E] {C : Set E} (hc : IsCompact C) (hv : Convex ℝ C)
    {r : ℝ} (hr : 0 < r) (reg : NormalBound C r) : InnerBall C r := by
  intro z hz n hn ns b hb
  apply rolling_of_normals hc hv hr reg hz hn ns
  simpa [Metric.mem_closedBall, dist_eq_norm] using hb

end Lemmata.FrankWolfePS.Joint
