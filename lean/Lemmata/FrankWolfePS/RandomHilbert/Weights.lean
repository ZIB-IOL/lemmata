module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic
/-! The energy on consecutive dyadic scales telescopes. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.RandomHilbert
open Filter Finset
open scoped BigOperators Topology
def K (j : ℕ) : ℕ := 2^j
def budget (j : ℕ) : ℕ := K j-1
theorem K_pos (j : ℕ) : 0<K j := pow_pos (by decide) _
@[simp] theorem budget_succ (j : ℕ) : budget j+1=K j := by
  have := K_pos j; unfold budget; omega
noncomputable def tail (j : ℕ) := 1/(Real.log ((j:ℝ)+4))
noncomputable def energy (j : ℕ) := tail j-tail (j+1)
noncomputable def amp (j : ℕ) := Real.sqrt (energy j)
theorem energy_pos (j : ℕ) : 0<energy j := by
  have l : 0<Real.log ((j:ℝ)+4) := Real.log_pos (by linarith [Nat.cast_nonneg (α:=ℝ) j])
  have m : Real.log ((j:ℝ)+4)<Real.log (((j+1:ℕ):ℝ)+4) := by
    apply Real.log_lt_log (by positivity); push_cast; linarith
  exact sub_pos.mpr ((one_div_lt_one_div_of_lt (by positivity) (m)))
@[simp] theorem amp_sq (j : ℕ) : amp j^2=energy j := Real.sq_sqrt (energy_pos j).le
theorem amp_pos (j : ℕ) : 0<amp j := Real.sqrt_pos.mpr (energy_pos j)
theorem tail_pos (j : ℕ) : 0<tail j := by
  unfold tail; have := Real.log_pos (show (1:ℝ)<(j:ℝ)+4 by linarith [Nat.cast_nonneg (α:=ℝ) j]); positivity
theorem sum_energy : Summable energy := by
  apply summable_of_sum_range_le (fun j => (energy_pos j).le) (c:=tail 0)
  intro n
  have h : ∑ j∈range n,energy j=tail 0-tail n := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ,ih,energy]; ring
  linarith [tail_pos n]
theorem total_energy : ∑' j,energy j ≤ 3/4 := by
  have h : ∑' j,energy j ≤ tail 0 := by
    apply sum_energy.tsum_le_of_sum_range_le
    intro n
    have e : ∑ j∈range n,energy j=tail 0-tail n := by
      induction n with
      | zero => simp
      | succ n ih => rw [sum_range_succ,ih,energy]; ring
    linarith [tail_pos n]
  apply h.trans
  unfold tail; norm_num only [Nat.cast_zero,zero_add]
  have l : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  apply (div_le_iff₀ (by positivity : (0:ℝ)<Real.log 4)).mpr
  rw [l]; linarith [Real.log_two_gt_d9]
/-- A lower estimate with the exact logarithmic rather than polynomial cost per scale. -/
theorem energy_lower (j : ℕ) :
    1/(((j:ℝ)+5)*Real.log ((j:ℝ)+5)^2) ≤ energy j := by
  let x : ℝ := j+4
  have xp : 0<x := by dsimp [x]; positivity
  have x1 : 0<x+1 := by positivity
  have lp : 0<Real.log x := Real.log_pos (by dsimp [x]; linarith [Nat.cast_nonneg (α:=ℝ) j])
  have lm : Real.log x≤Real.log (x+1) := Real.log_le_log xp (by linarith)
  have lk := Real.log_le_sub_one_of_pos (div_pos xp x1)
  rw [Real.log_div xp.ne' x1.ne'] at lk
  have diff : 1/(x+1) ≤ Real.log (x+1)-Real.log x := by
    have e : x/(x+1)-1= -(1/(x+1)) := by field_simp; ring
    rw [e] at lk; linarith
  have lp' : 0<Real.log (x+1) := lp.trans_le lm
  have r : 1/((x+1)*Real.log (x+1)^2) ≤ 1/Real.log x-1/(Real.log (x+1)) := by
    have d := (div_le_iff₀ x1).mp diff
    have m := mul_le_mul_of_nonneg_right d lp'.le
    field_simp [lp.ne',lp'.ne',x1.ne'] at ⊢
    all_goals try nlinarith only [m,lm]
  have e : x+1=(j:ℝ)+5 := by dsimp [x]; ring
  have m : ((j+1:ℕ):ℝ)+4=(j:ℝ)+5 := by push_cast; ring
  simpa only [energy,tail,m,e,x] using r
end Lemmata.FrankWolfePS.RandomHilbert
