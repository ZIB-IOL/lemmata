module
public import Lemmata.FrankWolfePS.RandomHilbert.Model
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Basic.Denumerable
/-! The block realization is linearly isometric to the usual scalar sequence Hilbert space. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.RandomHilbert
abbrev ScalarL2 := lp (fun _ : ℕ => ℝ) 2
abbrev PaperSpace := WithLp 2 (ScalarL2 × ℝ)
noncomputable def indices : (Σ j,Label j) ≃ ℕ := nonempty_equiv_of_countable.some
private theorem scalar_mem (f : ℕ → ℝ) :
    Memℓp f 2 ↔ Summable (fun n => f n^2) := by
  rw [memℓp_gen_iff (by norm_num : 0<(2:ENNReal).toReal)]
  simp [Real.norm_eq_abs]
private theorem grouped (f : (Σ j,Label j) → ℝ) :
    Summable (fun s => f s^2) ↔ Summable (fun j => ‖liftVec (fun i => f ⟨j,i⟩)‖^2) := by
  rw [summable_sigma_of_nonneg (fun _ => _root_.sq_nonneg _)]
  have h (j) : Summable (fun i => f ⟨j,i⟩^2) := (hasSum_fintype _).summable
  simp [lift_sq,sq,tsum_fintype,h]
noncomputable def flatten (x : Horiz) : ScalarL2 :=
  ⟨fun n => x (indices.symm n).1 (indices.symm n).2,by
    apply (scalar_mem _).mpr
    have sm := (grouped (fun s => x s.1 s.2)).mpr (sq_blocks_sm x)
    exact indices.symm.summable_iff.mpr sm⟩
noncomputable def group (y : ScalarL2) : Horiz :=
  ⟨fun j => liftVec (fun i => y (indices ⟨j,i⟩)),by
    apply (memℓp_gen_iff (p:=2) (by norm_num)).mpr
    simp only [ENNReal.toReal_ofNat,Real.rpow_two]
    have sm := (scalar_mem (fun n => y n)).mp (lp.memℓp y)
    have se : Summable (fun s => y (indices s)^2) := indices.summable_iff.mpr sm
    exact (grouped (fun s => y (indices s))).mp se⟩
theorem flatten_norm (x : Horiz) : ‖flatten x‖=‖x‖ := by
  let f := fun s : Σ j,Label j => x s.1 s.2^2
  have sm : Summable f := (grouped (fun s => x s.1 s.2)).mpr (sq_blocks_sm x)
  have a : ‖flatten x‖^2=∑' n,f (indices.symm n) := by
    simpa [f,Real.norm_eq_abs,flatten] using lp.norm_rpow_eq_tsum (p:=2) (by norm_num) (flatten x)
  rw [indices.symm.tsum_eq f,sm.tsum_sigma' (fun j => (hasSum_fintype (fun i => f ⟨j,i⟩)).summable)] at a
  have b (j) : ∑' i,f ⟨j,i⟩=‖x j‖^2 := by simp [f,EuclideanSpace.real_norm_sq_eq,tsum_fintype]
  simp_rw [b] at a; rw [←norm_sq_sum] at a
  nlinarith only [a,norm_nonneg (flatten x),norm_nonneg x]
noncomputable def horizontalIsometry : Horiz ≃ₗᵢ[ℝ] ScalarL2 where
  toFun := flatten
  invFun := group
  left_inv x := by
    apply Subtype.ext; funext j; ext i
    exact congrArg (fun s : Σ j, Label j => x s.1 s.2) (indices.symm_apply_apply ⟨j,i⟩)
  right_inv x := by apply Subtype.ext; funext n; change x (indices (indices.symm n))=x n; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' := flatten_norm
noncomputable def paperIsometry : World ≃ₗᵢ[ℝ] PaperSpace :=
  (LinearIsometryEquiv.withLpProdComm 2 ℝ ℝ Horiz).trans
    (LinearIsometryEquiv.withLpProdCongr 2 horizontalIsometry (LinearIsometryEquiv.refl ℝ ℝ))
@[simp] theorem paper_target : paperIsometry target=WithLp.toLp 2 ((0:ScalarL2),(-32:ℝ)) := by
  change WithLp.toLp 2 (horizontalIsometry 0,(-32:ℝ))=_; rw [map_zero]
end Lemmata.FrankWolfePS.RandomHilbert
