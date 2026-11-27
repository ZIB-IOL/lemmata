module
public import Lemmata.FrankWolfePS.HilbertFixed

/-! Every gradient-directed query on the stored physical hull obeys the same lower bound. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.Hilbert
open Finset Filter
open scoped Topology RealInnerProductSpace BigOperators

def box (z : Ambient) : Prop := -1 ≤ z.fst ∧ z.fst ≤ 2 ∧ ‖z.snd‖ ≤ 21/10

def physicalSlice (n : ℕ) : Set Ambient :=
  {z | box z ∧ ∃ x ∈ prefixSlice n, z.snd=synth x}

theorem convex_physicalSlice (n : ℕ) : Convex ℝ (physicalSlice n) := by
  rintro y ⟨hy, x,hx,ex⟩ z ⟨hz, v,hv,ev⟩ a b ha hb hab
  rcases hy with ⟨yl,yu,yn⟩
  rcases hz with ⟨zl,zu,zn⟩
  have mix := convex_prefixSlice n hx hv ha hb hab
  refine ⟨?_,a • x+b • v,mix,?_⟩
  · change -1 ≤ a*y.fst+b*z.fst ∧ a*y.fst+b*z.fst ≤ 2 ∧ ‖a • y.snd+b • z.snd‖ ≤ 21/10
    refine ⟨by nlinarith [mul_le_mul_of_nonneg_left yl ha,mul_le_mul_of_nonneg_left zl hb],
      by nlinarith [mul_le_mul_of_nonneg_left yu ha,mul_le_mul_of_nonneg_left zu hb],?_⟩
    have h := norm_add_le (a • y.snd) (b • z.snd)
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb] at h
    nlinarith [mul_le_mul_of_nonneg_left yn ha,mul_le_mul_of_nonneg_left zn hb]
  · change a • y.snd+b • z.snd=_
    rw [ex,ev,synth_finite hx.1,synth_finite hv.1,synth_finite mix.1,smul_sum,smul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro i _
    simp [Pi.add_apply,Pi.smul_apply,smul_smul,add_smul]

theorem increasing_physicalSlice (n : ℕ) : physicalSlice n ⊆ physicalSlice (n+1) :=
  fun _ ⟨h,x,hx,ex⟩ => ⟨h,x,prefix_mono n hx,ex⟩

private theorem grad_bounds {z : Ambient} (hz : box z) :
    3 ≤ z.fst+4 ∧ z.fst+4 ≤ 6 ∧ z.fst+4 ≤ ‖grad z‖ ∧ ‖grad z‖ ≤ 7 := by
  rcases hz with ⟨hl,hu,hs⟩
  have h := WithLp.norm_fst_le (p:=2) (α:=ℝ) (β:=Horizontal) (x:=grad z)
  change |z.fst+4| ≤ ‖grad z‖ at h
  have e := WithLp.prod_norm_sq_eq_of_L2 (grad z)
  change ‖grad z‖^2=‖z.fst+4‖^2+‖z.snd‖^2 at e
  rw [Real.norm_eq_abs, sq_abs] at e
  refine ⟨by linarith,by linarith,(le_abs_self _).trans h,?_⟩
  nlinarith [mul_nonneg (show 0 ≤ 2-z.fst by linarith) (show 0 ≤ z.fst+10 by linarith),
    mul_nonneg (show 0 ≤ 21/10-‖z.snd‖ by linarith) (show 0 ≤ 21/10+‖z.snd‖ by positivity)]

/-- A minimizing point of the true Hilbert ball union can introduce only the next label. -/
theorem physical_step {n : ℕ} {z y : Ambient} (hz : z ∈ physicalSlice n)
    (hy : y ∈ fixedBody) (oracle : IsMinOn (fun v => ⟪grad z,v⟫) fixedBody y) :
    y ∈ physicalSlice (n+1) := by
  obtain ⟨bounds,x,hx,ex⟩ := hz
  obtain ⟨g₀,g₁,qg,q₁⟩ := grad_bounds bounds
  let G := z.fst+4
  let Q := ‖grad z‖
  have qp : 0<Q := by dsimp [Q]; linarith
  have nz : -grad z ≠ 0 := neg_ne_zero.mpr (norm_pos_iff.mp qp)
  let u := gradientParameter x G Q
  have us := gradientParameter_spec hx.1 G qp
  have dl : dirLinear (-grad z)=linearTerm x G Q := by
    funext i
    simp only [dirLinear,linearTerm,norm_neg,WithLp.neg_fst,WithLp.neg_snd,inner_neg_left]
    change (-G)*(weight i)^2-⟪z.snd,axis i⟫+penalty Q i=_
    rw [ex,synth_inner_axis hx.1]
    ring
  have iffmax (v) (hv : v∈simplex) : IsMaxOn (fun j => ⟪-grad z,center j⟫+‖-grad z‖*radius j) simplex v ↔
      IsMaxOn (score (linearTerm x G Q) (penalty Q)) simplex v := by
    simp only [isMaxOn_iff]
    constructor <;> intro h j hj
    · have h' := h j hj
      rw [fixed_value _ hj,fixed_value _ hv,dl,norm_neg] at h'
      exact (add_le_add_iff_left _).mp h'
    · rw [fixed_value _ hj,fixed_value _ hv,dl,norm_neg]
      exact add_le_add_right (h j hj) _
  obtain ⟨_,_,uniq⟩ := unique_tip_of_parameter nz (c:=center) (r:=radius)
    (fun _ hv => by linarith [(radius_bounds hv).1]) (u:=u) us.1 ((iffmax u us.1).mpr us.2)
    (fun v hv hvmax => (unique_gradient_parameter hx.1 G qp).unique
      ⟨hv,(iffmax v hv).mp hvmax⟩ us)
  have ym : IsMaxOn (fun v => ⟪-grad z,v⟫) fixedBody y := by
    simpa only [isMaxOn_iff,isMinOn_iff,inner_neg_left,neg_le_neg_iff] using oracle
  have tipEq := uniq y hy ym
  let d := radius u / Q
  have db := radius_bounds us.1
  have hd₀ : 0 ≤ d := div_nonneg (by linarith [db.1]) qp.le
  have hd₁ : d ≤ 2/5 := (div_le_iff₀ qp).mpr (by
    dsimp [Q]; linarith [db.2,(height_bounds us.1).2])
  have rx := gradientReply_mem hx g₀ g₁ qp q₁ hd₀ hd₁
  obtain ⟨uj,_⟩ := gradient_prefix hx g₀ g₁ qp q₁ us.1 us.2
  have uz (i : ℕ) (hi : n+1 ≤ i) : u i=0 := uj i (by omega)
  have xz (i : ℕ) (hi : n+1 ≤ i) : x i=0 := hx.1 i (by omega)
  refine ⟨body_bounds hy,gradientReply x G Q d,rx,?_⟩
  have sy : y.snd=synth u-d • z.snd := by
    rw [tipEq]
    change synth u + radius u • (‖-grad z‖⁻¹ • (-z.snd))=_
    rw [norm_neg,smul_neg,smul_neg,smul_smul]
    simp only [d,Q,div_eq_mul_inv,sub_eq_add_neg]
  rw [sy,ex,synth_finite uz,synth_finite xz,synth_finite rx.1,smul_sum,←sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  simp [gradientReply,u,G,smul_smul,sub_smul]

/-- All hull outputs of every legal gradient query stream, at every budget on this fixed body. -/
theorem fixed_hull_lower {seed : Ambient} (hs : seed ∈ physicalSlice 1)
    (query reply : ℕ → Ambient)
    (hq : ∀ t, query t ∈ convexHull ℝ (insert seed (reply '' Set.Iio t)))
    (hr : ∀ t, reply t ∈ fixedBody ∧ IsMinOn (fun v => ⟪grad (query t),v⟫) fixedBody (reply t))
    (t : ℕ) {z : Ambient} (hz : z ∈ convexHull ℝ (insert seed (reply '' Set.Iio t))) :
    31 / (256 * ((t:ℝ)+1)) ≤ objective z-objective optimum := by
  have hull (k : ℕ) : convexHull ℝ (insert seed (reply '' Set.Iio k)) ⊆ physicalSlice (k+1) := by
    induction k with
    | zero =>
      apply convexHull_min _ (convex_physicalSlice _)
      rintro v (rfl|⟨j,hj,rfl⟩)
      · exact hs
      · exact False.elim (Nat.not_lt_zero _ hj)
    | succ k ih =>
      apply convexHull_min _ (convex_physicalSlice _)
      have old := (subset_convexHull ℝ _).trans ih
      rintro v (rfl|⟨j,hj,rfl⟩)
      · exact increasing_physicalSlice _ (old (Set.mem_insert _ _))
      · change j < k+1 at hj
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with h | eq
        · exact increasing_physicalSlice _ (old (Set.mem_insert_of_mem _ ⟨j,h,rfl⟩))
        · subst j
          exact physical_step (ih (hq k)) (hr k).1 (hr k).2
  obtain ⟨boxz,x,hx,ex⟩ := hull t hz
  have gap := objective_gap boxz.1
  rw [ex,synth_energy hx.1] at gap
  exact prefix_gap t x _ hx (by linarith [energy_lower hx.1])

end Lemmata.FrankWolfePS.Hilbert
