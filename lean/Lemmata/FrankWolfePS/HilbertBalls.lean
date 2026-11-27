module
public import Lemmata.FrankWolfePS.HilbertSupport
public import Lemmata.FrankWolfePS.Unique.Support
public import Lemmata.FrankWolfePS.Upper.Geometry

/-! Passing from a parameter maximizer to the unique exposed point of a union of Hilbert balls. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.Hilbert
open Filter
open scoped RealInnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def ballUnion (c : (ℕ → ℝ) → E) (r : (ℕ → ℝ) → ℝ) : Set E :=
  {z | ∃ u ∈ simplex, ‖z-c u‖ ≤ r u}

noncomputable def tip (c : E) (r : ℝ) (q : E) : E := c + r • unit q

theorem tip_mem {c : (ℕ → ℝ) → E} {r : (ℕ → ℝ) → ℝ} {q : E} (hq : q ≠ 0)
    {u : ℕ → ℝ} (hu : u ∈ simplex) (hr : 0 ≤ r u) : tip (c u) (r u) q ∈ ballUnion c r := by
  exact ⟨u,hu,by simp [tip,norm_smul,norm_unit hq,abs_of_nonneg hr]⟩

theorem tip_value {q : E} (hq : q ≠ 0) (c : E) (r : ℝ) : ⟪q,tip c r q⟫ = ⟪q,c⟫+‖q‖*r := by
  have hn := norm_ne_zero_iff.mpr hq
  simp [tip,unit,inner_add_right,real_inner_smul_right ]
  field_simp

theorem ball_value_le {q y c : E} {r : ℝ} (hy : ‖y-c‖ ≤ r) : ⟪q,y⟫ ≤ ⟪q,c⟫+‖q‖*r := by
  have h := (real_inner_le_norm q (y-c)).trans (mul_le_mul_of_nonneg_left hy (norm_nonneg q))
  rwa [inner_sub_right, sub_le_iff_le_add'] at h

/-- A unique maximizing parameter and the unique supporting point of its Hilbert ball
yield the actual exposed point and its representation. -/
theorem unique_tip_of_parameter {c : (ℕ → ℝ) → E} {r : (ℕ → ℝ) → ℝ} {q : E}
    (hq : q ≠ 0) (hr : ∀ u ∈ simplex, 0 ≤ r u) {u : ℕ → ℝ} (hu : u ∈ simplex)
    (opt : IsMaxOn (fun v => ⟪q,c v⟫+‖q‖*r v) simplex u)
    (uniq : ∀ v ∈ simplex, IsMaxOn (fun z => ⟪q,c z⟫+‖q‖*r z) simplex v → v=u) :
    tip (c u) (r u) q ∈ ballUnion c r ∧ IsMaxOn (fun y => ⟪q,y⟫) (ballUnion c r) (tip (c u) (r u) q) ∧
    ∀ y ∈ ballUnion c r, IsMaxOn (fun z => ⟪q,z⟫) (ballUnion c r) y → y=tip (c u) (r u) q := by
  have val := tip_value hq
  refine ⟨tip_mem hq hu (hr u hu), isMaxOn_iff.mpr ?_, ?_⟩
  · rintro y ⟨v,hv,hy⟩
    simpa only [val] using (ball_value_le (q:=q) hy).trans (isMaxOn_iff.mp opt v hv)
  · rintro y ⟨v,hv,hy⟩ hymax
    have win (j) (hj : j ∈ simplex) : ⟪q,c j⟫+‖q‖*r j ≤ ⟪q,y⟫ := by
      simpa only [val] using isMaxOn_iff.mp hymax _ (tip_mem hq hj (hr j hj))
    have vu := uniq v hv (isMaxOn_iff.mpr (fun j hj => (win j hj).trans (ball_value_le hy)))
    subst v
    have near : ⟪q,tip (c u) (r u) q⟫ ≤ ⟪q,y⟫ := by rw [val]; exact win u hu
    have norm1 : ‖-unit q‖=1 := by simp [norm_unit hq]
    have un : ⟪-unit q,y⟫ ≤ ⟪-unit q,c u-r u • (-unit q)⟫ := by
      simp only [smul_neg,sub_neg_eq_add,inner_neg_left,neg_le_neg_iff]
      change ⟪‖q‖⁻¹ • q,tip (c u) (r u) q⟫ ≤ ⟪‖q‖⁻¹ • q,y⟫
      simpa only [real_inner_smul_left] using mul_le_mul_of_nonneg_left near (inv_nonneg.mpr (norm_nonneg q))
    simpa [tip] using Unique.ball_eq (hr u hu) norm1 hy un

/-- Every nonzero direction with a null-coefficient diagonal support representation
has a unique maximizing point of the actual ball union. -/
theorem unique_ball_oracle {c : (ℕ → ℝ) → E} {r : (ℕ → ℝ) → ℝ} {q : E} (hq : q ≠ 0)
    (hr : ∀ u ∈ simplex, 0 ≤ r u) {l b : ℕ → ℝ} (hl : Tendsto l atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0)) (hp : ∀ i, 0 < b i) {a : ℝ}
    (value : ∀ u ∈ simplex, ⟪q,c u⟫+‖q‖*r u=a+score l b u) :
    ∃! y, y ∈ ballUnion c r ∧ IsMaxOn (fun z => ⟪q,z⟫) (ballUnion c r) y := by
  have eq (u) (hu : u∈simplex) : IsMaxOn (fun z => ⟪q,c z⟫+‖q‖*r z) simplex u ↔
      IsMaxOn (score l b) simplex u := by
    simp only [isMaxOn_iff]
    constructor <;> intro h j hj
    · have H := h j hj
      rw [value j hj,value u hu] at H; linarith
    · rw [value j hj,value u hu]; exact add_le_add_right (h j hj) _
  obtain ⟨u,⟨hu,ho⟩,uniq⟩ := unique_parameter hl hb hp
  obtain ⟨hy,hm,hun⟩ := unique_tip_of_parameter hq hr hu ((eq u hu).mpr ho)
    (fun v hv hvmax => uniq v ⟨hv,(eq v hv).mp hvmax⟩)
  exact ⟨_,⟨hy,hm⟩,fun z hz => hun z hz.1 hz.2⟩

/-- A unit inner parallel decomposition for any Hilbert ball union with all radii at least one. -/
theorem ballUnion_rounded (c : (ℕ → ℝ) → E) (r₀ : (ℕ → ℝ) → ℝ) (hr : ∀ u∈simplex,1≤r₀ u) :
    ballUnion c r₀=Rounded (ballUnion c (fun u => r₀ u-1)) 1 := by
  ext z; constructor
  · rintro ⟨u,hu,hd⟩
    let r := r₀ u
    have one : 1≤r := hr u hu
    have rp : 0<r := by linarith
    let k := c u+((r-1)/r) • (z-c u)
    have a : 0≤(r-1)/r := div_nonneg (by linarith) rp.le
    have b : 0≤1/r := by positivity
    refine ⟨k,⟨u,hu,?_⟩,?_⟩
    · change ‖c u+_ - c u‖≤r-1
      rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg a]
      have h := mul_le_mul_of_nonneg_left hd a
      change _≤(r-1)/r*r at h
      rwa [div_mul_cancel₀ _ rp.ne'] at h
    · have e : z-k=(1/r) • (z-c u) := by
        have one' : 1/r+(r-1)/r=1 := by field_simp; ring
        have eq := congrArg (fun v : ℝ => v • (z-c u)) one'
        simp only [add_smul,one_smul] at eq
        change z-(c u+_) = _
        rw [show z-(c u+((r-1)/r) • (z-c u)) = (z-c u)-((r-1)/r) • (z-c u) by abel]
        exact sub_eq_iff_eq_add.mpr eq.symm
      rw [e,norm_smul,Real.norm_eq_abs,abs_of_nonneg b]
      have h := mul_le_mul_of_nonneg_left hd b
      change _≤1/r*r at h
      rwa [div_mul_cancel₀ _ rp.ne'] at h
  · rintro ⟨k,⟨u,hu,hk⟩,hz⟩
    refine ⟨u,hu,?_⟩
    have h := norm_add_le (z-k) (k-c u)
    rw [sub_add_sub_cancel] at h
    linarith

end Lemmata.FrankWolfePS.Hilbert
