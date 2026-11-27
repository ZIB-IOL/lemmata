module
public import Lemmata.FrankWolfePS.RandomHilbert.Model
/-! The blockwise optimizer gives the exact, unique support point of the physical ball union. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.RandomHilbert
open Finset Filter
open scoped Topology BigOperators RealInnerProductSpace
noncomputable def raw (q : World) (j : ℕ) (i : Label j) : ℝ := amp j*(unit q).snd j i
noncomputable def coeff (d : Data) (q : World) (j : ℕ) : Label j → ℝ := fun i =>
  raw q j i-noise 0 (spacing j) (d j).1 i
noncomputable def choice (d : Data) (q : World) : Param d := fun j =>
  ⟨arg (allowed (d j)) (coeff d q j) (kappa j),(arg_spec (insert_nonempty 0 _) _ _).1⟩
noncomputable def localValue {d : Data} (q : World) (u : Param d) (j : ℕ) :=
  ⟪(unit q).snd j,horizontal u j⟫-bonus (d j).1 (u j)
theorem local_criterion {d : Data} (q : World) (u : Param d) (j : ℕ) :
    localValue q u j=criterion (coeff d q j) (kappa j) (u j)-kappa j := by
  simp only [localValue,horizontal_apply,real_inner_smul_right,lift_inner,criterion,bonus,linear,
    coeff,raw,sub_mul,sum_sub_distrib,mul_assoc,← mul_sum]
  ring
theorem local_sm {d : Data} (q : World) (u : Param d) : Summable (localValue q u) :=
  (lp.summable_inner (𝕜:=ℝ) (unit q).snd (horizontal u)).sub (bonus_sm u)
theorem parameter_value {d : Data} (q : World) (u : Param d) :
    ⟪unit q,ctr u⟫-rad u=(unit q).fst-1+∑' j,localValue q u j := by
  rw [show (∑' j,localValue q u j) = ⟪(unit q).snd,horizontal u⟫-∑' j,bonus (d j).1 (u j) from
    (lp.summable_inner (𝕜:=ℝ) (unit q).snd (horizontal u)).tsum_sub (bonus_sm u)]
  change ⟪(unit q).fst,(1:ℝ)⟫+⟪(unit q).snd,horizontal u⟫-rad u=_
  rw [Real.inner_apply,rad]; ring
theorem parameter_order {d : Data} (q : World) (u : Param d) :
    ⟪unit q,ctr (choice d q)⟫-rad (choice d q) ≤ ⟪unit q,ctr u⟫-rad u := by
  simp only [parameter_value,add_le_add_iff_left]
  apply (local_sm q _).tsum_le_tsum _ (local_sm q u)
  intro j; rw [local_criterion,local_criterion]
  apply sub_le_sub_right
  exact (arg_spec (insert_nonempty 0 _) _ _).2 _ (u j).property
theorem parameter_eq {d : Data} {q : World} (u : Param d)
    (back : ⟪unit q,ctr u⟫-rad u≤⟪unit q,ctr (choice d q)⟫-rad (choice d q)) :
    u=choice d q := by
  simp only [parameter_value,add_le_add_iff_left] at back
  funext j; apply Subtype.ext; apply arg_eq (small j).1 (u j).property _ (insert_nonempty _ _)
  intro v hv
  have le (i) : localValue q (choice d q) i ≤ localValue q u i := by
    rw [local_criterion,local_criterion]; exact sub_le_sub_right ((arg_spec (insert_nonempty 0 _) _ _).2 _ (u i).property) _
  have same : localValue q (choice d q) j = localValue q u j := by
    apply eq_of_le_of_not_lt (le j); intro lt
    exact not_lt_of_ge back ((local_sm q _).tsum_lt_tsum le lt (local_sm q u))
  rw [local_criterion,local_criterion,sub_left_inj] at same
  rw [← same]; exact (arg_spec (insert_nonempty 0 _) _ _).2 v hv

noncomputable def oracle (d : Data) (q : World) : World := by
  classical exact if q=0 then publicStart else ctr (choice d q)-rad (choice d q) • unit q
@[simp] theorem oracle_zero (d : Data) : oracle d 0=publicStart := by simp [oracle]
theorem ball_lower {d : Data} (q : World) (hq : q≠0) {u : Param d} {x : World}
    (close : ‖x-ctr u‖ ≤ rad u) : ⟪unit q,ctr u⟫-rad u≤⟪unit q,x⟫ := by
  have z := real_inner_le_norm (-(unit q)) (x-ctr u)
  rw [norm_neg,norm_unit hq,one_mul,inner_neg_left,inner_sub_right] at z; linarith
theorem oracle_spec (d : Data) (q : World) : Unique.MinAt (body d) q (oracle d q) := by
  by_cases ne : q=0
  · subst q; simp [Unique.MinAt,public_mem]
  let u := choice d q
  have pos : 0≤rad u := by linarith [(rad_bounds u).1]
  apply (Unique.normalize_min ne).mp
  rw [oracle,ite_eq_right ne]
  refine ⟨⟨u,?_⟩,?_⟩
  · change ‖ctr u-rad u • unit q-ctr u‖≤rad u
    simp [sub_sub_cancel_left,norm_smul,abs_of_nonneg pos,norm_unit ne]
  · rintro y ⟨v,hv⟩
    simpa only [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,norm_unit ne,one_pow,mul_one] using
      (parameter_order q v).trans (ball_lower q ne hv)
theorem oracle_unique (d : Data) {q : World} (ne : q≠0) :
    ∃! x,Unique.MinAt (body d) q x := by
  refine ⟨_,oracle_spec d q,?_⟩
  rintro x hx
  have hx' := (Unique.normalize_min ne).mpr hx
  obtain ⟨v,hv⟩ := hx.1
  have min := hx'.2 _ (oracle_spec d q).1
  rw [oracle,ite_eq_right ne] at min ⊢
  have val : ⟪unit q,ctr (choice d q)-rad (choice d q) • unit q⟫=
      ⟪unit q,ctr (choice d q)⟫-rad (choice d q) := by simp only [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,norm_unit ne,one_pow,mul_one]
  have eq := parameter_eq v ((ball_lower q ne hv).trans (min.trans val.le))
  subst v
  exact Unique.ball_eq (by linarith [(rad_bounds (choice d q)).1]) (norm_unit ne) hv min

noncomputable def withBlock (d : Data) (j) (R : Finset (Label j)) (G : Table j) :=
  Function.update d j (G,R)
private theorem assembly_eq {d f : Data} (q : World)
    (eq : ∀ j,(choice d q j).val=(choice f q j).val)
    (score : ∀ j,linear (noise 0 (spacing j) (d j).1) (choice d q j).val =
      linear (noise 0 (spacing j) (f j).1) (choice f q j).val) : oracle d q=oracle f q := by
  by_cases hq : q=0
  · simp [hq]
  have he : horizontal (choice d q)=horizontal (choice f q) := by
    apply Subtype.ext; funext j; change amp j • liftVec _ = amp j • liftVec _; rw [eq j]
  have rr : rad (choice d q)=rad (choice f q) := by
    unfold rad; congr 1; apply tsum_congr; intro j
    unfold bonus; rw [score j,eq j]
  simp [oracle,hq,ctr,he,rr]

noncomputable def block_scanner (d : Data) (j : ℕ) : Scanner (Label j) World (levels (Label j) (budget j)) where
  anchor := 0
  step := spacing j
  bulge := kappa j
  score := fun q => raw q j
  reply := fun R G q => oracle (withBlock d j R G) q
  localReply := by
    intro R q G F agree
    have loc (i) (hi : i∈insert (0:Label j) R) : noise 0 (spacing j) G i=noise 0 (spacing j) F i := by
      rcases mem_insert.mp hi with rfl|hin
      · simp [noise]
      · simp only [noise,agree i hin]
    have h (l) : (choice (withBlock d j R G) q l).val=(choice (withBlock d j R F) q l).val := by
      change arg (allowed ((withBlock d j R G) l)) (fun i => raw q l i-noise 0 (spacing l) ((withBlock d j R G) l).1 i) (kappa l)=
        arg (allowed ((withBlock d j R F) l)) (fun i => raw q l i-noise 0 (spacing l) ((withBlock d j R F) l).1 i) (kappa l)
      by_cases eq : l=j
      · subst l; simp only [withBlock,Function.update_self,allowed]
        apply arg_congr (insert_nonempty _ _) (small _).1; intro i hi; rw [loc i hi]
      · simp [withBlock,Function.update_of_ne eq]
    apply assembly_eq q h; intro l
    rw [h l]; by_cases eq : l=j
    · subst l; apply linear_eq_on (choice (withBlock d j R F) q j).property
      simpa [withBlock,allowed] using loc
    · simp [withBlock,Function.update_of_ne eq]
  restrictReply := by
    intro R I G q i ha sub hi sep
    have ai : (0:Label j)∈I := sub ha
    have h (l) : (choice (withBlock d j I G) q l).val=(choice (withBlock d j R G) q l).val := by
      change arg (allowed ((withBlock d j I G) l)) (fun i => raw q l i-noise 0 (spacing l) ((withBlock d j I G) l).1 i) (kappa l)=
        arg (allowed ((withBlock d j R G) l)) (fun i => raw q l i-noise 0 (spacing l) ((withBlock d j R G) l).1 i) (kappa l)
      by_cases eq : l=j
      · subst l; simp only [withBlock,Function.update_self,allowed,insert_eq_of_mem ha,insert_eq_of_mem ai]
        exact arg_restrict (l:=fun i => raw q j i-noise 0 (spacing j) G i) sub hi (small j).1 sep
      · simp [withBlock,Function.update_of_ne eq]
    apply assembly_eq q h; intro l; rw [h l]
    by_cases eq : l=j
    · subst l; simp [withBlock]
    · simp [withBlock,Function.update_of_ne eq]
end Lemmata.FrankWolfePS.RandomHilbert
