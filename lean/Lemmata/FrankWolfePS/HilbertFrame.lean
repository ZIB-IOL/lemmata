module
public import Lemmata.FrankWolfePS.HilbertAnytimeBody
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! A triangular orthonormal realization lets one rotate the as-yet unused coordinates
of the arbitrary-query instance without changing any previous measurement. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.Hilbert.Anytime
open Finset Filter Submodule
open scoped Topology RealInnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One fresh direction can be chosen orthogonal to any finite transcript. -/
theorem fresh_exists (inf : ¬ FiniteDimensional ℝ E) (S : Finset E) :
    ∃ d : E, ‖d‖=1 ∧ ∀ x∈S, ⟪x,d⟫=0 := by
  let W := Submodule.span ℝ (S : Set E)
  have fd : FiniteDimensional ℝ W := FiniteDimensional.span_finset ℝ S
  have nt : W ≠ ⊤ := by
    intro eq
    have : FiniteDimensional ℝ (⊤ : Submodule ℝ E) := eq ▸ fd
    exact inf (FiniteDimensional.of_surjective Submodule.topEquiv.toLinearMap Submodule.topEquiv.surjective)
  have nb : Wᗮ ≠ ⊥ := fun eq => nt (Submodule.orthogonal_eq_bot_iff.mp eq)
  obtain ⟨v,hv,nz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot nb
  exact ⟨unit v,norm_unit nz,fun x hx => by
    rw [unit,real_inner_smul_right,(W.mem_orthogonal _).mp hv x (Submodule.subset_span hx),mul_zero]⟩

noncomputable def coef (i : ℕ) : ℝ := Real.sqrt (1/(((i:ℝ)+1)*((i:ℝ)+2)))
private theorem coef_sq (i : ℕ) : (coef i)^2 = 1/(((i:ℝ)+1)*((i:ℝ)+2)) :=
  Real.sq_sqrt (by positivity)

theorem coef_partial (n : ℕ) : ∑ i ∈ range n,(coef i)^2 = 1-1/((n:ℝ)+1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ,ih,coef_sq,Nat.cast_succ]
    field_simp
    ring

theorem coef_hasSum : HasSum (fun i => (coef i)^2) 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun _ => _root_.sq_nonneg _) _).mpr
  simp only [coef_partial]
  have lim := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp (tendsto_add_atTop_nat 1)
  simpa [Function.comp_def] using lim.const_sub 1

noncomputable def mean (d : ℕ → E) (k : ℕ) : E := ∑ i ∈ range k,coef i • d i
noncomputable def atom (d : ℕ → E) (i : ℕ) : E := mean d i+(((i:ℝ)+2)*coef i) • d i
noncomputable def hidden (d : ℕ → E) : E := ∑' i,coef i • d i

variable [CompleteSpace E]
private theorem hidden_sum {d : ℕ → E} (on : Orthonormal ℝ d) : Summable (fun i => coef i • d i) := by
  apply (on.orthogonalFamily.summable_iff_norm_sq_summable coef).mpr
  simpa [Real.norm_eq_abs,sq_abs] using coef_hasSum.summable

private theorem dot_hidden {d : ℕ → E} (on : Orthonormal ℝ d) (i) : ⟪d i,hidden d⟫=coef i := by
  have e := ((hidden_sum on).hasSum.mapL (innerSL ℝ (d i))).tsum_eq
  rw [tsum_eq_single i] at e
  · simpa [hidden,on.norm_eq_one] using e.symm
  · intro j hj; simp [on.inner_eq_zero (Ne.symm hj)]

theorem hidden_unit {d : ℕ → E} (on : Orthonormal ℝ d) : ‖hidden d‖=1 := by
  have e := ((hidden_sum on).hasSum.mapL (innerSL ℝ (hidden d))).tsum_eq
  have h (i) : (innerSL ℝ (hidden d)) (coef i • d i)=(coef i)^2 := by
    change ⟪hidden d,coef i • d i⟫=_
    rw [real_inner_smul_right,real_inner_comm (d i) (hidden d),dot_hidden on,pow_two]
  rw [tsum_congr h,coef_hasSum.tsum_eq] at e
  change 1=⟪hidden d,hidden d⟫ at e
  rw [real_inner_self_eq_norm_sq] at e
  nlinarith [norm_nonneg (hidden d)]

theorem atom_hidden {d : ℕ → E} (on : Orthonormal ℝ d) (i) : ⟪atom d i,hidden d⟫=1 := by
  simp only [atom,mean,inner_add_left,sum_inner,real_inner_smul_left,dot_hidden on,←pow_two]
  rw [coef_partial]
  rw [mul_assoc,←pow_two,coef_sq]
  field_simp; ring

omit [CompleteSpace E] in
private theorem dot_atom {d : ℕ → E} (on : Orthonormal ℝ d) (i j : ℕ) :
    ⟪d i,atom d j⟫ = if i<j then coef i else if i=j then ((j:ℝ)+2)*coef j else 0 := by
  simp [atom,mean,inner_add_right,inner_sum,real_inner_smul_right,orthonormal_iff_ite.mp on]
  split <;> split <;> simp_all

omit [CompleteSpace E] in
private theorem atom_dot_of_le {d : ℕ → E} (on : Orthonormal ℝ d) {i j : ℕ} (ij : i≤j) :
    ⟪atom d i,atom d j⟫ = if i=j then 2 else 1 := by
  have h (a) (ha : a∈range i) : ⟪d a,atom d j⟫=coef a := by
    rw [dot_atom on,ite_eq_left (lt_of_lt_of_le (mem_range.mp ha) ij)]
  change ⟪mean d i+(((i:ℝ)+2)*coef i) • d i,atom d j⟫=_
  rw [inner_add_left,real_inner_smul_left,mean,sum_inner]
  have sum : (∑ a ∈ range i,⟪coef a • d a,atom d j⟫)=1-1/((i:ℝ)+1) := by
    rw [←coef_partial]
    exact sum_congr rfl fun a ha => by rw [real_inner_smul_left,h a ha,pow_two]
  rw [sum,dot_atom on]
  rcases lt_or_eq_of_le ij with lt|rfl
  · rw [ite_eq_left lt,ite_eq_right lt.ne,mul_assoc,←pow_two,coef_sq]
    field_simp; ring
  · simp; ring_nf
    rw [coef_sq]
    field_simp; ring

omit [CompleteSpace E] in
theorem atom_dot {d : ℕ → E} (on : Orthonormal ℝ d) (i j : ℕ) :
    ⟪atom d i,atom d j⟫ = if i=j then 2 else 1 := by
  rcases le_total i j with h|h
  · exact atom_dot_of_le on h
  · rw [real_inner_comm (atom d j) (atom d i),atom_dot_of_le on h]; simp [eq_comm]

/-- A fixed target frame from any orthonormal sequence of fresh directions. -/
noncomputable def triangularFrame (d : ℕ → E) (on : Orthonormal ℝ d) : Frame E where
  h := hidden d
  e i := atom d i-hidden d
  unit_h := hidden_unit on
  orth := by
    apply orthonormal_iff_ite.mpr
    intro i j
    rw [inner_sub_left,inner_sub_right,inner_sub_right,atom_dot on,atom_hidden on,
      real_inner_comm (atom d j) (hidden d),atom_hidden on,real_inner_self_eq_norm_sq,hidden_unit on]
    split <;> norm_num
  perp i := by
    rw [inner_sub_right,real_inner_comm (atom d i) (hidden d),atom_hidden on,real_inner_self_eq_norm_sq,hidden_unit on]
    norm_num

/-- Every measurement captured by time k has the same value on the final hidden mean
and the known finite mean. -/
theorem hidden_test {d : ℕ → E} (on : Orthonormal ℝ d) {v : E} {k : ℕ}
    (hz : ∀ j, k≤j → ⟪v,d j⟫=0) : ⟪v,hidden d⟫=⟪v,mean d k⟫ := by
  have e := ((hidden_sum on).hasSum.mapL (innerSL ℝ v)).tsum_eq
  rw [tsum_eq_sum (s:=range k) (fun i hi => by simp [hz i (by simpa using hi)])] at e
  change (∑ i ∈ range k,_) = ⟪v,hidden d⟫ at e
  rw [←e,mean,inner_sum]
  rfl

theorem unseen_test {d : ℕ → E} (on : Orthonormal ℝ d) {v : E} {k : ℕ}
    (hz : ∀ j, k≤j → ⟪v,d j⟫=0) (i : ℕ) (hi : k ≤ i) :
    ⟪v,(triangularFrame d on).e i⟫=0 := by
  change ⟪v,atom d i-hidden d⟫=0
  rw [inner_sub_right,atom,inner_add_right,real_inner_smul_right,hz i hi,mul_zero,add_zero,
    ←hidden_test on (k:=i) (fun j hj => hz j (hi.trans hj)),sub_self]

/-- This measurement annihilates the exact distance witness at that budget. -/
theorem captured_witness {d : ℕ → E} (on : Orthonormal ℝ d) {v : E} {k : ℕ}
    (hz : ∀ j, k≤j → ⟪v,d j⟫=0) : ⟪witness (triangularFrame d on) k,v⟫=0 := by
  have id (n : ℕ) : ∑ i ∈ range n,atom d i = ((n:ℝ)+1) • mean d n := by
    induction n with
    | zero => simp [mean]
    | succ n ih =>
      rw [sum_range_succ,ih,atom,Nat.cast_succ,show mean d (n+1)=mean d n+coef n • d n by simp [mean,sum_range_succ]]
      rw [smul_add,smul_smul,show (n:ℝ)+1+1=(n:ℝ)+2 by ring]
      rw [show ((n:ℝ)+2) • mean d n = ((n:ℝ)+1) • mean d n+mean d n by
        rw [show (n:ℝ)+2=((n:ℝ)+1)+1 by ring,add_smul,one_smul]]
      abel
  rw [real_inner_comm v, witness,inner_sub_right]
  change ⟪v,hidden d⟫-⟪v,∑ i ∈ range k,(atom d i-hidden d)⟫=0
  rw [sum_sub_distrib,id,inner_sub_right,real_inner_smul_right,sum_const,card_range,←Nat.cast_smul_eq_nsmul ℝ]
  rw [real_inner_smul_right,hidden_test on hz]
  ring

end Lemmata.FrankWolfePS.Hilbert.Anytime
