module
public import Lemmata.FrankWolfePS.HilbertResistance

/-! One fixed exact, unique nonzero-direction oracle for the whole run of a deterministic strategy. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.Hilbert.Anytime
open Lemmata.FrankWolfePS.Hilbert Finset Filter
open scoped Topology RealInnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem public_start_mem {d : ℕ → E} (on : Orthonormal ℝ d) :
    start (d 0)∈body (triangularFrame d on) := by
  let F := triangularFrame d on
  have h : reservoir F (delta 0)=F.e 0 := by
    unfold reservoir; rw [tsum_eq_single 0]
    · simp [delta]
    · intro i hi; simp [delta,hi]
  have c : (ballCenter F (delta 0)).snd=(2*coef 0) • d 0 := by
    change F.h+reservoir F (delta 0)=_
    rw [h]
    change hidden d+(atom d 0-hidden d)=_
    simp [atom,mean]
  refine ⟨delta 0,delta_mem 0,le_trans ?_ (rad_pos (delta_mem 0))⟩
  have ex := WithLp.prod_norm_sq_eq_of_L2 (start (d 0)-ballCenter F (delta 0))
  change ‖start (d 0)-ballCenter F (delta 0)‖^2=‖(0:ℝ)-1‖^2+‖(2*coef 0) • d 0-(ballCenter F (delta 0)).snd‖^2 at ex
  rw [c] at ex; norm_num at ex
  rcases ex with ex|ex <;> linarith

theorem partial_reply_exact {d : ℕ → E} (on : Orthonormal ℝ d) (k : ℕ) (q : World E)
    (qp : q≠0) (captured : ∀ j, k ≤ j → ⟪q.snd,d j⟫=0) :
    let F := triangularFrame d on
    let y := partialReply (d 0) d k q
    y∈body F ∧ IsMaxOn (fun x => ⟪q,x⟫) (body F) y := by
  let F := triangularFrame d on
  let a := finiteCoeff d k q
  let u := select a ‖q‖
  have finite (i) (hi : k ≤ i) : a i=0 := by simp [a,finiteCoeff,not_lt.mpr hi]
  have us := select_spec finite (norm_pos_iff.mpr qp)
  have spec (i) : a i=⟪q.snd,F.e i⟫ := by
    by_cases hi : i<k
    · change finiteCoeff d k q i=⟪q.snd,atom d i-hidden d⟫
      simp only [finiteCoeff,ite_eq_left hi,inner_sub_right,hidden_test on captured]
    · simp [a,finiteCoeff,hi,F,unseen_test on captured i (not_lt.mp hi)]
  obtain ⟨tail,mass⟩ := exact_reply_prefix (norm_pos_iff.mpr qp) finite us.1 us.2
  have sc : reservoir F u=∑ i ∈ range (k+1),u i • (atom d i-hidden d) :=
    tsum_eq_sum (fun i hi => by simp [u,tail i (by simpa using hi)])
  have c : ballCenter F u=WithLp.toLp 2 ((1:ℝ),∑ i ∈ range (k+1),u i • atom d i) := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · rfl
    · change hidden d+reservoir F u=_
      rw [sc]; simp only [smul_sub,sum_sub_distrib,←sum_smul]
      change hidden d+(_-(∑ i ∈ range (k+1),select a ‖q‖ i) • hidden d)=_
      rw [mass,one_smul]; abel
  have eq : partialReply (d 0) d k q=tip (ballCenter F u) (rad u) q := by
    rw [c]; simp [partialReply,qp,a,u]
  change partialReply (d 0) d k q∈body F ∧ IsMaxOn _ _ _
  rw [eq]
  refine ⟨tip_mem qp us.1 (by linarith [rad_pos us.1]),isMaxOn_iff.mpr ?_⟩
  rintro z ⟨v,hv,hd⟩
  have h := ball_value_le (q:=q) hd
  have s := isMaxOn_iff.mp us.2 v hv
  rw [frame_value F q hv] at h
  rw [tip_value qp,frame_value F q us.1]
  have ae : a=(fun i => ⟪q.snd,F.e i⟫) := funext spec
  rw [←ae] at h ⊢
  linarith

noncomputable def frameOracle (F : Frame E) (s : World E) (hs : s∈body F) : Upper.LMO (body F) := by
  classical
  let o := fun q : World E => if h : q=0 then s else (frame_unique_oracle F (-q) (neg_ne_zero.mpr h)).exists.choose
  have ok (q : World E) : o q∈body F ∧ IsMinOn (fun z => ⟪q,z⟫) (body F) (o q) := by
    by_cases h : q=0
    · subst q; simp [o,hs,isMinOn_iff]
    · have e := (frame_unique_oracle F (-q) (neg_ne_zero.mpr h)).exists.choose_spec
      simpa only [o,dite_eq_right h,inner_neg_left,isMinOn_iff,isMaxOn_iff,neg_le_neg_iff] using e
  exact ⟨o,fun q => (ok q).1,fun q => isMinOn_iff.mp (ok q).2⟩

theorem frameOracle_zero (F : Frame E) (s : World E) (hs : s∈body F) :
    (frameOracle F s hs).query 0=s := by simp [frameOracle]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Two transcripts of the same deterministic strategy against the same total oracle coincide. -/
theorem identical_history (M : Strategy E) (o : World E → World E) {r s : ℕ → World E}
    (hr : ∀ t,r t=o (queryAt M r t)) (hs : ∀ t,s t=o (queryAt M s t)) : r=s := by
  funext t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    rw [hr t,hs t]
    apply congrArg o
    apply congrArg (M.ask t)
    exact funext (fun i => ih i i.isLt)

/-- For every deterministic anytime method there is one fixed body with a single exact oracle,
a public start, and one optimizer. All actual outputs along its run at all budgets are covered. -/
theorem deterministic_anytime (inf : ¬FiniteDimensional ℝ E) (v : E) (hv : ‖v‖=1) (M : Strategy E) :
    ∃ (F : Frame E) (O : Upper.LMO (body F)) (z : World E),
      start v∈body F ∧ O.query 0=start v ∧
      (∀ q : World E, q ≠ 0 → ∃! x, x∈body F ∧ IsMinOn (fun y => ⟪q,y⟫) (body F) x) ∧
      z∈body F ∧ IsMinOn (fun y => ‖y-target‖^2/2) (body F) z ∧
      (∃ r : ℕ → World E, ∀ t,r t=O.query (queryAt M r t)) ∧
      ∀ r : ℕ → World E, (∀ t,r t=O.query (queryAt M r t)) → ∀ T : ℕ,
        let y := outputAt M r T
        y∉body F ∨ 1/(4*((T:ℝ)+2)) ≤ ‖y-target‖^2/2-‖z-target‖^2/2 := by
  classical
  let d := directions inf M v
  let r := answers inf M v
  have on : Orthonormal ℝ d := directions_on inf M v hv
  let F := triangularFrame d on
  have hs : start v∈body F := public_start_mem on
  let O := frameOracle F (start v) hs
  have unique (q : World E) (h : q≠0) : ∃! x, x∈body F ∧ IsMinOn (fun y => ⟪q,y⟫) (body F) x := by
    simpa only [isMaxOn_iff,isMinOn_iff,inner_neg_left,neg_le_neg_iff] using frame_unique_oracle F (-q) (neg_ne_zero.mpr h)
  have consistent (t : ℕ) : r t=O.query (queryAt M r t) := by
    have er := answers_rule inf M v t
    change r t=partialReply v d (t+1) (-(queryAt M r t)) at er
    rw [er]
    by_cases h : queryAt M r t=0
    · rw [h,neg_zero]; simp [partialReply,O,frameOracle_zero]
    · have hz (j : ℕ) (hj : t+1≤j) : ⟪(-(queryAt M r t)).snd,d j⟫=0 := by
        change ⟪-(queryAt M r t).snd,d j⟫=0
        rw [inner_neg_left,(captured_input inf M v hj).1,neg_zero]
      have sol := partial_reply_exact on (t+1) (-(queryAt M r t)) (neg_ne_zero.mpr h) hz
      apply (unique _ h).unique _ ⟨O.mem _,isMinOn_iff.mpr (O.least _)⟩
      have d0 : d 0=v := rfl
      rw [d0] at sol
      simpa only [F,isMaxOn_iff,isMinOn_iff,inner_neg_left,neg_le_neg_iff] using sol
  obtain ⟨z,hz,hm,gap⟩ := frame_all_budgets F
  refine ⟨F,O,z,hs,frameOracle_zero _ _ _,unique,hz,hm,⟨r,consistent⟩,?_⟩
  intro s run T
  have eq := identical_history M O.query run consistent
  subst s
  by_cases ok : outputAt M r T ∈ body F
  · right
    let y := outputAt M r T
    have wy : ⟪witness F (T+1),y.snd⟫=0 := captured_witness on (fun j hj => (captured_input inf M v hj).2)
    apply gap T {y.snd} (fun x hx => by simpa only [Set.mem_singleton_iff.mp hx] using wy) y ok
    exact Submodule.subset_span (Or.inr (Set.mem_singleton _))
  · exact Or.inl ok

end Lemmata.FrankWolfePS.Hilbert.Anytime
