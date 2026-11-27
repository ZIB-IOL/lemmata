module
public import Lemmata.FrankWolfePS.RandomHilbert.Block
public import Lemmata.FrankWolfePS.RandomHilbert.Coupling
public import Lemmata.FrankWolfePS.RandomHilbert.Weights
public import Lemmata.FrankWolfePS.HilbertWeak
public import Lemmata.FrankWolfePS.HilbertAnytimeBody
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Group.FunctionSeries
/-! Product of finite hidden simplexes in the Hilbert direct sum. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.RandomHilbert
open Finset Filter
open scoped Topology BigOperators RealInnerProductSpace
abbrev Label (j : ℕ) := Fin (256*K j)
instance (j : ℕ) : NeZero (256*K j) := ⟨Nat.ne_of_gt (Nat.mul_pos (by decide) (K_pos j))⟩
abbrev Block (j : ℕ) := EuclideanSpace ℝ (Label j)
noncomputable abbrev Horiz := lp Block 2
abbrev World := WithLp 2 (ℝ × Horiz)
abbrev Table (j : ℕ) := Grid (Label j) (levels (Label j) (budget j))
abbrev Datum (j : ℕ) := Table j × Finset (Label j)
abbrev Data := ∀ j, Datum j
def allowed {j : ℕ} (d : Datum j) := insert 0 d.2
abbrev Param (d : Data) := ∀ j, {u : Label j → ℝ // Base (allowed (d j)) u}
instance (d : Data) (j : ℕ) : CompactSpace {u : Label j → ℝ // Base (allowed (d j)) u} :=
  isCompact_iff_compactSpace.mp (base_compact _)
def seedPar (d : Data) : Param d := fun _ => ⟨atom 0,atom_base (mem_insert_self _ _)⟩
noncomputable def eta (j : ℕ) := energy j/(10000000*(K j:ℝ))
noncomputable def spacing (j : ℕ) := eta j/(levels (Label j) (budget j):ℝ)
noncomputable def kappa (j : ℕ) := spacing j/10
theorem eta_pos (j : ℕ) : 0<eta j := div_pos (energy_pos j) (by have := K_pos j; positivity)
theorem spacing_pos (j : ℕ) : 0<spacing j := by
  have := eta_pos j; have : 0<levels (Label j) (budget j) := Nat.pos_of_ne_zero (NeZero.ne _)
  unfold spacing; positivity
theorem small (j : ℕ) : 0<kappa j ∧ 4*kappa j<spacing j ∧ kappa j≤eta j := by
  have h : (1:ℝ)≤levels (Label j) (budget j) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne _))
  have e := div_le_self (eta_pos j).le h
  have b := spacing_pos j
  change spacing j≤eta j at e
  unfold kappa; constructor <;> [skip;constructor] <;> linarith
theorem eta_le (j : ℕ) : 2*eta j≤energy j/1000 := by
  have k : (1:ℝ)≤K j := by exact_mod_cast K_pos j
  unfold eta; rw [mul_div_assoc',div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith only [mul_le_mul_of_nonneg_left k (energy_pos j).le,energy_pos j]
noncomputable def bonus {j : ℕ} (D : Table j) (u : Label j → ℝ) : ℝ :=
  linear (noise 0 (spacing j) D) u+kappa j*(1-sq u)
theorem bonus_bound {j : ℕ} {D : Table j} {I : Finset (Label j)} {u : Label j → ℝ}
    (hu : Base I u) : 0≤bonus D u ∧ bonus D u≤2*eta j := by
  have weight (i : Label j) : 0≤noise 0 (spacing j) D i ∧ noise 0 (spacing j) D i≤eta j := by
    unfold noise; split
    · exact ⟨le_rfl,(eta_pos j).le⟩
    · have lev : (0:ℝ)<levels (Label j) (budget j) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne _))
      have hi : ((D i).val:ℝ)≤levels (Label j) (budget j) := by exact_mod_cast (D i).isLt.le
      refine ⟨mul_nonneg (spacing_pos j).le (Nat.cast_nonneg _),?_⟩
      calc _ ≤ spacing j * (levels (Label j) (budget j):ℝ) := mul_le_mul_of_nonneg_left hi (spacing_pos j).le
           _ = eta j := div_mul_cancel₀ _ lev.ne'
  have t := weighted_bound hu weight
  unfold bonus
  have ks := small j
  constructor
  · exact add_nonneg t.1 (mul_nonneg ks.1.le (sub_nonneg.mpr (sq_base_le_one hu)))
  · nlinarith [mul_nonneg ks.1.le (sq_nonneg u)]
theorem bonus_sm {d : Data} (u : Param d) : Summable (fun j => bonus (d j).1 (u j)) :=
  (sum_energy.div_const 1000).of_nonneg_of_le (fun j => (bonus_bound (u j).property).1)
    (fun j => (bonus_bound (u j).property).2.trans (eta_le j))
noncomputable def rad {d : Data} (u : Param d) := 1+∑' j,bonus (d j).1 (u j)
theorem rad_bounds {d : Data} (u : Param d) : 1≤rad u ∧ rad u≤1001/1000 := by
  have e := (bonus_sm u).tsum_le_tsum (fun j => (bonus_bound (u j).property).2.trans (eta_le j))
    (sum_energy.div_const 1000)
  rw [tsum_div_const] at e
  have p : 0≤∑' j,bonus (d j).1 (u j) := tsum_nonneg (fun j => (bonus_bound (D:=(d j).1) (u j).property).1)
  unfold rad; constructor <;> linarith [total_energy]

theorem norm_sq_sum (x : Horiz) : ‖x‖^2=∑' j, ‖x j‖^2 := by
  simpa using lp.norm_rpow_eq_tsum (p:=2) (by norm_num) x
theorem sq_blocks_sm (x : Horiz) : Summable (fun j => ‖x j‖^2) := by
  simpa using ((lp.memℓp x).summable (by norm_num : 0<(2:ENNReal).toReal))
noncomputable def horizontal {d : Data} (u : Param d) : Horiz :=
  ⟨fun j => amp j • liftVec (u j),by
    apply (memℓp_gen_iff (p:=2) (by norm_num)).mpr
    simp only [ENNReal.toReal_ofNat,Real.rpow_two]
    apply sum_energy.of_nonneg_of_le (fun j => _root_.sq_nonneg _)
    intro j
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (amp_pos j),mul_pow,amp_sq]
    exact mul_le_of_le_one_right (energy_pos j).le (by nlinarith [lift_sq (u j).val,sq_base_le_one (u j).property])⟩
@[simp] theorem horizontal_apply {d : Data} (u : Param d) (j : ℕ) :
    horizontal u j=amp j • liftVec (u j) := rfl
theorem horizontal_bound {d : Data} (u : Param d) : ‖horizontal u‖≤87/100 := by
  have e := (sq_blocks_sm (horizontal u)).tsum_le_tsum (g:=energy) (fun j => by
    rw [horizontal_apply,norm_smul,Real.norm_eq_abs,abs_of_pos (amp_pos j),mul_pow,amp_sq]
    exact mul_le_of_le_one_right (energy_pos j).le (by nlinarith [lift_sq (u j).val,sq_base_le_one (u j).property])) sum_energy
  rw [← norm_sq_sum] at e; nlinarith [total_energy,norm_nonneg (horizontal u)]
noncomputable def ctr {d : Data} (u : Param d) : World := WithLp.toLp 2 (1,horizontal u)
noncomputable def target : World := WithLp.toLp 2 (-32,0)
noncomputable def publicStart : World := WithLp.toLp 2 (0,horizontal (seedPar (fun _ => (fun _ => 0,∅))))
def body (d : Data) : Set World := {x | ∃ u : Param d, ‖x-ctr u‖ ≤ rad u}
noncomputable def cost (x : World) := ‖x-target‖^2/2
theorem public_mem (d : Data) : publicStart∈body d := by
  refine ⟨seedPar d,?_⟩
  have e : publicStart-ctr (seedPar d)=WithLp.toLp 2 ((-1:ℝ),(0:Horiz)) := by
    apply WithLp.ofLp_injective
    ext1
    · norm_num [publicStart,ctr]
    · change horizontal _-horizontal _=0
      ext j i; simp [seedPar]
  rw [e,WithLp.norm_toLp_fst]; norm_num; exact (rad_bounds (seedPar d)).1
end Lemmata.FrankWolfePS.RandomHilbert
