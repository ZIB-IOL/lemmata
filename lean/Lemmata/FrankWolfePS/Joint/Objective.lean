module
public import Lemmata.FrankWolfePS.Joint.Model
public import Lemmata.FrankWolfePS.Upper.Joint
public import Mathlib.Analysis.Convex.Strong
@[expose] public section
namespace Lemmata.FrankWolfePS.Joint
open Upper
open scoped RealInnerProductSpace Gradient NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def StrongLower (C : Set E) (f : E → ℝ) (g : E → E) (μ : ℝ) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, f x + ⟪g x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y

theorem strong_lower_of_strongConvexOn [ProperSpace E] {f : E → ℝ} {μ : ℝ}
    (hf : Differentiable ℝ f) (strong : StrongConvexOn Set.univ μ f) (C : Set E) :
    StrongLower C f (∇ f) μ := by
  let P := quadratic μ (0 : E)
  have cv : ConvexOn ℝ Set.univ (fun x => f x - P x) := by
    simpa [P, quadratic] using strongConvexOn_iff_convex.mp strong
  have df (x : E) : HasGradientAt (fun y => f y - P y) (∇ f x - grad μ 0 x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have a := (hf x).hasGradientAt.hasFDerivAt
    have b := quadratic_derivative μ (0 : E) x
    convert a.sub b using 1
    ext v
    simp [innerSL_apply_apply]
  have subgrad := Lemmata.FrankWolfeLDS.IsFirstOrderConvex.of_convexOn_hasGradientAt cv df
  intro x _ y _
  have G := subgrad x y
  change f x - P x + ⟪∇ f x - grad μ 0 x, y - x⟫ ≤ f y - P y at G
  rw [inner_sub_left] at G
  have H := quadratic_taylor μ (0 : E) x y
  change P y = P x + _ + _ at H
  linarith only [G, H]

noncomputable def target (L : ℝ) (g x : E) := x - L⁻¹ • g

theorem target_grad {L : ℝ} (hL : 0 < L) (g x : E) :
    isoGrad L (target L g x) x = g := by simp [isoGrad, target, smul_smul, hL.ne']

/-- A relative reduction of the squared-distance model yields the same
fraction of the ideal projected-gradient decrease against every comparator. -/
theorem objective_step {C : Set E} (conv : Convex ℝ C) {f : E → ℝ} {g : E → E} {L μ c : ℝ}
    (mdl : Models C f g L) (strong : StrongLower C f g μ)
    (hμ : 0 < μ) (hLμ : μ ≤ L) (hc : 0 ≤ c)
    {x y : E} (hx : x ∈ C) (hy : y ∈ C)
    (partialStep : ∀ z ∈ C, let u := target L (g x) x
      ‖y - u‖ ^ 2 ≤ (1 - c) * ‖x - u‖ ^ 2 + c * ‖z - u‖ ^ 2) :
    ∀ w ∈ C, f y - f w ≤ (1 - c * (μ / L)) * (f x - f w) := by
  intro w hw
  let u := target L (g x) x
  let t := μ / L
  have hL := hμ.trans_le hLμ
  have h0 : 0 ≤ t := (div_pos hμ hL).le
  have h1 : t ≤ 1 := (div_le_one hL).mpr hLμ
  have ltEq : L * t = μ := by dsimp [t]; field_simp
  let z := blend t x w
  have H := mul_le_mul_of_nonneg_left (partialStep z (blend_mem conv h0 h1 hx hw)) (show 0 ≤
      L / 2 by positivity)
  have model : iso L u y ≤ (1 - c) * iso L u x + c * iso L u z := by
    dsimp only [iso]; linarith only [H]
  have Ty := iso_taylor L u x y
  have Tz := iso_taylor L u x z
  rw [target_grad hL] at Ty Tz
  have E : ‖z - x‖ ^ 2 = t ^ 2 * ‖w - x‖ ^ 2 := by
    dsimp [z]; rw [blend_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg h0, mul_pow]
  have Z : ⟪g x, z - x⟫ = t * ⟪g x, w - x⟫ := by dsimp [z]; rw [blend_sub, real_inner_smul_right]
  rw [E, Z] at Tz
  have id : L / 2 * (t ^ 2 * ‖w - x‖ ^ 2) = t * (μ / 2 * ‖w - x‖ ^ 2) := by rw [← ltEq]; ring
  rw [id] at Tz
  have gain : iso L u z - iso L u x ≤ t * (f w - f x) := by
    linarith only [Tz, mul_le_mul_of_nonneg_left (strong x hx w hw) h0]
  change f y - f w ≤ (1 - c * t) * (f x - f w)
  linarith only [model, Ty, mdl.upper x hx y hy, mul_le_mul_of_nonneg_left gain hc]

end Lemmata.FrankWolfePS.Joint
