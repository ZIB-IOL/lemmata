module
public import Lemmata.FrankWolfePS.HilbertSupport
public import Lemmata.FrankWolfePS.HilbertGram
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Lemmata.FrankWolfePS.HilbertBalls

/-! The strictly concave bonus and the projection of the deterministic arbitrary-direction amendment. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.Hilbert.Anytime
open Lemmata.FrankWolfePS.Hilbert Finset Filter
open scoped Topology RealInnerProductSpace BigOperators

noncomputable def bonus (i : ℕ) : ℝ := weight i/8
noncomputable def lin (a : ℕ → ℝ) (Q : ℝ) (i : ℕ) : ℝ := a i + Q*bonus i
noncomputable def pen (Q : ℝ) (i : ℕ) : ℝ := Q*bonus i/8
theorem bonus_pos (i : ℕ) : 0<bonus i := by have := weight_pos i; unfold bonus; positivity

theorem bonus_limit : Tendsto bonus atTop (𝓝 0) := by unfold bonus; simpa using weight_limit.div_const 8
theorem lin_limit {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) (Q : ℝ) :
    Tendsto (lin a Q) atTop (𝓝 0) := by unfold lin; simpa using ha.add (bonus_limit.const_mul Q)
theorem pen_limit (Q : ℝ) : Tendsto (pen Q) atTop (𝓝 0) := by
  unfold pen; simpa using (bonus_limit.const_mul Q).div_const 8

/-- The perturbed support objective of the amendment has a unique parameter even off transcript. -/
theorem unique_reply_parameter {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) {Q : ℝ} (hp : 0<Q) :
    ∃! u, u∈simplex ∧ IsMaxOn (score (lin a Q) (pen Q)) simplex u :=
  unique_parameter (lin_limit ha Q) (pen_limit Q) (fun i => by
    have := bonus_pos i; unfold pen; positivity)

/-- The zero coefficients of the unseen orthogonal directions force full mass on at most one
additional label, with the very same unique oracle used off transcript. -/
theorem exact_reply_prefix {a u : ℕ → ℝ} {k : ℕ} {Q : ℝ} (hp : 0<Q)
    (hidden : ∀ i, k ≤ i → a i=0) (hu : u ∈ simplex)
    (opt : IsMaxOn (score (lin a Q) (pen Q)) simplex u) :
    (∀ j, k < j → u j=0) ∧ ∑ i ∈ range (k+1),u i=1 := by
  have ha : Tendsto a atTop (𝓝 0) := tendsto_const_nhds.congr' (by
    filter_upwards [eventually_ge_atTop k] with i hi using (hidden i hi).symm)
  apply maximizer_prefix hu (null_terms_summable (lin_limit ha Q) (pen_limit Q) hu) opt
  · intro i; have := bonus_pos i; unfold pen; positivity
  · simp only [lin,pen,hidden k le_rfl,zero_add]
    nlinarith [mul_pos hp (bonus_pos k)]
  · intro j hj
    simp only [lin,pen,hidden j hj.le,hidden k le_rfl,zero_add,bonus]
    nlinarith [mul_le_mul_of_nonneg_left (weight_half hj) hp.le,mul_pos hp (weight_pos k)]

noncomputable def size (u : ℕ → ℝ) : ℝ := Real.sqrt (1090+∑' i,(u i)^2)
noncomputable def rad (u : ℕ → ℝ) : ℝ := 1+score bonus (pen 1) u
noncomputable def residual (u : ℕ → ℝ) : ℝ := size u-rad u

theorem ss {u : ℕ → ℝ} (hu : u∈simplex) : Summable (fun i => (u i)^2) :=
  (mass_summable hu).of_nonneg_of_le (fun _ => _root_.sq_nonneg _) (fun i => by
    nlinarith [mul_nonneg (hu.1 i) (sub_nonneg.mpr (coord_le_one hu i))])

theorem size_bounds {u : ℕ → ℝ} (hu : u∈simplex) :
    33 ≤ size u ∧ size u ≤ 34 ∧ (size u)^2=1090+∑' i,(u i)^2 := by
  have lo : 0≤∑' i,(u i)^2 := tsum_nonneg (fun _ => _root_.sq_nonneg _)
  have hi := (ss hu).tsum_le_tsum (fun i => show (u i)^2 ≤ u i by
    nlinarith [mul_nonneg (hu.1 i) (sub_nonneg.mpr (coord_le_one hu i))]) (mass_summable hu)
  have sq : (size u)^2=1090+∑' i,(u i)^2 := Real.sq_sqrt (by linarith)
  have z := Real.sqrt_nonneg (1090+∑' i,(u i)^2)
  change 0≤size u at z
  exact ⟨by nlinarith,by nlinarith [mass_le_one hu],sq⟩

theorem bonus_sum (s : Finset ℕ) : ∑ i ∈ s,bonus i ≤ 1/256 := by
  unfold bonus
  simp only [div_eq_mul_inv,←sum_mul]
  linarith [sum_weight_le s]

/-- A finite decrease in a single coordinate proves the bound on every closest-ball parameter,
without assuming the one-sided optimality inequality. -/
theorem optimizer_coordinate {u : ℕ → ℝ} (hu : u∈simplex) (opt : IsMinOn residual simplex u)
    (j : ℕ) : u j ≤ 34*bonus j := by
  by_contra! large
  let d := (u j-34*bonus j)/2
  have dp : 0<d := by dsimp [d]; linarith
  have du : d≤u j := by dsimp [d]; linarith [bonus_pos j]
  let v := bump u j (-d)
  have hv : v∈simplex := by
    apply mem_simplex_of_hasSum _ (bump_hasSum (mass_summable hu).hasSum j (-d)) (by linarith [mass_le_one hu])
    intro i
    by_cases eq : i=j
    · subst i; simp [bump]; linarith
    · simpa [v,bump,eq] using hu.1 i
  have sa : HasSum (fun i => (0:ℝ)*u i-(-1)*(u i)^2) (∑' i,(u i)^2) := by simpa using (ss hu).hasSum
  have sq := (term_bump_hasSum sa j (-d)).tsum_eq
  simp only [zero_mul,neg_one_mul,sub_neg_eq_add,zero_add] at sq
  have br := null_terms_summable bonus_limit (pen_limit 1) hu
  have dr := (term_bump_hasSum br.hasSum j (-d)).tsum_eq
  change score bonus (pen 1) v = score bonus (pen 1) u + _ at dr
  have vu : size u ^2 - size v ^2=d*(2*u j-d) := by
    rw [(size_bounds hu).2.2,(size_bounds hv).2.2]
    change (1090+_) - (1090+∑' i,(bump u j (-d) i)^2) = _
    rw [sq]; ring
  have rd : rad u-rad v ≤ d*bonus j := by
    unfold rad; rw [dr]
    have p : 0≤pen 1 j := by unfold pen; have := bonus_pos j; positivity
    nlinarith [mul_nonneg (mul_nonneg dp.le p) (show 0≤2*u j-d by linarith [hu.1 j])]
  have vs := isMinOn_iff.mp opt v hv
  change size u-rad u ≤ size v-rad v at vs
  have close : size u-size v ≤ d*bonus j := by linarith
  have t := mul_le_mul_of_nonneg_right close (show 0 ≤ size u+size v by linarith [(size_bounds hu).1,(size_bounds hv).1])
  have z := mul_le_mul_of_nonneg_left (show size u+size v ≤ 68 by linarith [(size_bounds hu).2.1,(size_bounds hv).2.1])
    (mul_nonneg dp.le (bonus_pos j).le)
  have big : 68*bonus j < 2*u j-d := by dsimp [d]; linarith
  nlinarith [mul_lt_mul_of_pos_left big dp]

theorem optimizer_mass {u : ℕ → ℝ} (hu : u∈simplex) (opt : IsMinOn residual simplex u) :
    (∑' i,u i) ≤ 34/256 := by
  apply (mass_summable hu).tsum_le_of_sum_le
  intro s
  have le := sum_le_sum (s:=s) (fun i _ => optimizer_coordinate hu opt i)
  rw [←mul_sum] at le
  linarith [bonus_sum s]


theorem rad_le {u : ℕ → ℝ} (hu : u∈simplex) : rad u ≤ 1+1/256 := by
  have sm := null_terms_summable bonus_limit (pen_limit 1) hu
  have le (s : Finset ℕ) : ∑ i ∈ s,(bonus i*u i-pen 1 i*(u i)^2) ≤ 1/256 := by
    apply le_trans (sum_le_sum (g:=bonus) _ ) (bonus_sum s)
    intro i _
    unfold pen
    nlinarith [mul_le_mul_of_nonneg_left (coord_le_one hu i) (bonus_pos i).le,
      mul_nonneg (bonus_pos i).le (_root_.sq_nonneg (u i))]
  unfold rad score
  linarith [sm.tsum_le_of_sum_le le]

theorem theta_lower {u : ℕ → ℝ} (hu : u∈simplex) : (24:ℝ)/25 < 1-rad u/size u := by
  have h := size_bounds hu
  have pos : 0<size u := by linarith [h.1]
  have := (div_lt_iff₀ pos).mpr (show rad u < (1/25)*size u by linarith [rad_le hu,h.1])
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A target distinguished vector and a countable orthonormal system in the horizontal space. -/
structure Frame (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  h : E
  e : ℕ → E
  orth : Orthonormal ℝ e
  unit_h : ‖h‖=1
  perp : ∀ i, ⟪h,e i⟫=0

noncomputable def reservoir (F : Frame E) (u : ℕ → ℝ) : E := ∑' i,u i • F.e i
noncomputable def witness (F : Frame E) (k : ℕ) : E := F.h-∑ i ∈ range k,F.e i

omit [CompleteSpace E] in
theorem witness_h (F : Frame E) (k : ℕ) : ⟪F.h,witness F k⟫=1 := by
  simp [witness,inner_sub_right,inner_sum,F.perp,F.unit_h]

omit [CompleteSpace E] in
theorem witness_e (F : Frame E) (k i : ℕ) : ⟪F.e i,witness F k⟫ = if i<k then -1 else 0 := by
  have eq (j) : ⟪F.e i,F.e j⟫=(if j=i then 1 else 0) := by
    by_cases h : j=i
    · subst j; simp [F.orth.norm_eq_one]
    · simp [h,F.orth.inner_eq_zero (Ne.symm h)]
  have hp : ⟪F.e i,F.h⟫=0 := (real_inner_comm F.h (F.e i)).trans (F.perp i)
  simp [witness,inner_sub_right,inner_sum,hp,eq]; split <;> norm_num

omit [CompleteSpace E] in
theorem witness_sq (F : Frame E) (k : ℕ) : ‖witness F k‖^2 = (k:ℝ)+1 := by
  rw [←real_inner_self_eq_norm_sq]
  nth_rw 1 [witness]
  rw [inner_sub_left,witness_h,sum_inner]
  simp [witness_e, sum_congr rfl (fun i (hi : i ∈ range k) => ite_eq_left (mem_range.mp hi))]
  ring

theorem reservoir_sm (F : Frame E) {u : ℕ → ℝ} (hu : u∈simplex) : Summable (fun i => u i • F.e i) := by
  apply (mass_summable hu).of_norm_bounded
  intro i; simp [norm_smul,F.orth.norm_eq_one,abs_of_nonneg (hu.1 i)]

theorem reservoir_witness (F : Frame E) {u : ℕ → ℝ} (hu : u∈simplex) (k : ℕ) :
    ⟪witness F k,F.h+reservoir F u⟫=1-∑ i ∈ range k,u i := by
  have hs := (reservoir_sm F hu).hasSum.mapL (innerSL ℝ (witness F k))
  have eq (i) : (innerSL ℝ (witness F k)) (u i • F.e i)=if i<k then -u i else 0 := by
    change ⟪witness F k,u i • F.e i⟫=_
    rw [real_inner_smul_right, real_inner_comm (F.e i) (witness F k),witness_e]; split <;> ring
  have h := hs.tsum_eq
  simp only [eq] at h
  rw [tsum_eq_sum (s:=range k) (fun i hi => by simp [show ¬ i<k by simpa using hi])] at h
  have g : (∑ i ∈ range k,if i<k then -u i else 0) = -(∑ i ∈ range k,u i) := by
    rw [←sum_neg_distrib]; exact sum_congr rfl (fun i hi => ite_eq_left (mem_range.mp hi))
  rw [g] at h
  change _=⟪witness F k,reservoir F u⟫ at h
  rw [inner_add_right,real_inner_comm F.h (witness F k),witness_h,←h]; ring

omit [CompleteSpace E] in
/-- The stored atoms and the orthogonal dummy directions all annihilate the same witness. -/
theorem stored_span (F : Frame E) (k : ℕ) (D : Set E)
    (hd : ∀ z∈D, ⟪witness F k,z⟫=0) {y : E}
    (hy : y∈Submodule.span ℝ ((fun i => F.h+F.e i) '' Set.Iio k ∪ D)) : ⟪witness F k,y⟫=0 := by
  have incl : Submodule.span ℝ ((fun i => F.h+F.e i) '' Set.Iio k ∪ D) ≤ (innerSL ℝ (witness F k)).ker := by
    apply Submodule.span_le.mpr
    rintro z (⟨i,hi,rfl⟩|hz)
    · change ⟪witness F k,F.h+F.e i⟫=0
      rw [inner_add_right,real_inner_comm F.h (witness F k),witness_h,
        real_inner_comm (F.e i) (witness F k),witness_e,ite_eq_left (show i<k from hi)]; norm_num
    · exact hd _ hz
  exact incl hy

/-- The projection parameter and the encoded output span imply the all-budget numerical gap.
The construction of a single embedding for an arbitrary deterministic strategy is separate. -/
theorem span_gap (F : Frame E) {u : ℕ → ℝ} (hu : u∈simplex) (opt : IsMinOn residual simplex u)
    (T : ℕ) (D : Set E) (hd : ∀ z∈D, ⟪witness F (T+1),z⟫=0) {y : E}
    (hy : y∈Submodule.span ℝ ((fun i => F.h+F.e i) '' Set.Iio (T+1) ∪ D)) :
    1/(4*((T:ℝ)+2)) ≤ ‖(1-rad u/size u) • (F.h+reservoir F u)-y‖^2/2 := by
  let v := witness F (T+1)
  let z := (1-rad u/size u) • (F.h+reservoir F u)-y
  have ip : ⟪v,z⟫=(1-rad u/size u)*(1-∑ i ∈ range (T+1),u i) := by
    dsimp [v,z]; rw [inner_sub_right,real_inner_smul_right,reservoir_witness F hu,stored_span F _ D hd hy,sub_zero]
  have mass := (mass_summable hu).sum_le_tsum (range (T+1)) (fun i _ => hu.1 i)
  have m : 5/6 ≤ 1-∑ i ∈ range (T+1),u i := by linarith [optimizer_mass hu opt]
  have q := theta_lower hu
  have low : (4:ℝ)/5 ≤ ⟪v,z⟫ := by rw [ip]; nlinarith [mul_le_mul_of_nonneg_left m (show 0≤1-rad u/size u by linarith)]
  have cs := real_inner_mul_inner_self_le v z
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,witness_sq] at cs
  push_cast at cs
  apply (div_le_iff₀ (by positivity : 0 < 4*((T:ℝ)+2))).mpr
  change _ ≤ ‖z‖^2/2 * _
  nlinarith [_root_.sq_nonneg (⟪v,z⟫-4/5)]

end Lemmata.FrankWolfePS.Hilbert.Anytime
