module
public import Lemmata.FrankWolfePS.HilbertGeometry
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.WeakDual

/-! Weak compactness of the explicit ball union. The unit ball uses Banach–Alaoglu and Riesz. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.Hilbert
open Filter InnerProductSpace
open scoped Topology RealInnerProductSpace
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
private abbrev W (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] := WeakSpace ℝ E
private abbrev D (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] := WeakDual ℝ E
private noncomputable def weakVec (φ : D E) : W E :=
  toWeakSpace ℝ E ((toDual ℝ E).symm φ.toStrongDual)

private theorem weakVec_cont : Continuous (weakVec (E:=E)) := by
  apply WeakBilin.continuous_of_continuous_eval (topDualPairing ℝ E).flip
  intro l
  let q := (toDual ℝ E).symm l
  have e (φ : D E) : l ((toDual ℝ E).symm φ.toStrongDual) = φ q := by
    rw [← toDual_symm_apply (x:=((toDual ℝ E).symm φ.toStrongDual)) (y:=l),
      real_inner_comm ((toDual ℝ E).symm φ.toStrongDual) q,toDual_symm_apply]
    rfl
  change Continuous (fun φ : D E => l ((toDual ℝ E).symm φ.toStrongDual))
  simpa only [e] using (WeakDual.eval_continuous (𝕜:=ℝ) q)

set_option backward.isDefEq.respectTransparency false in
/-- Compactness in the ordinary weak topology for a weakly continuous family of centers
and a continuous radius bounded below by one on the compact countable simplex. -/
theorem ballUnion_weakly_compact (c : (ℕ → ℝ) → E) (r₀ : (ℕ → ℝ) → ℝ) (hr : ∀ u∈simplex,1≤r₀ u)
    (hc : Continuous (fun u : simplex => toWeakSpace ℝ E (c u)))
    (rc : Continuous (fun u : simplex => r₀ u)) : IsCompact (toWeakSpace ℝ E '' ballUnion c r₀) := by
  let B : Set (D E) := WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) 1
  have hb : IsCompact B := WeakDual.isCompact_closedBall 0 1
  let I : Set (simplex × D E) := (Set.univ : Set simplex) ×ˢ B
  let F := fun p : simplex × D E => toWeakSpace ℝ E (c p.1)+r₀ p.1 • weakVec p.2
  let : CompactSpace simplex := isCompact_iff_compactSpace.mp simplex_compact
  have hi : IsCompact I := isCompact_univ.prod hb
  have hf : Continuous F := (hc.comp continuous_fst).add
    ((rc.comp continuous_fst).smul (weakVec_cont.comp continuous_snd))
  suffices e : toWeakSpace ℝ E '' ballUnion c r₀=F '' I by rw [e]; exact hi.image hf
  ext w; constructor
  · rintro ⟨z,⟨u,hu,hd⟩,rfl⟩
    let r := r₀ u
    have rp : 0<r := by linarith [hr u hu]
    let v := r⁻¹ • (z-c u)
    let φ := StrongDual.toWeakDual ((toDual ℝ E) v)
    refine ⟨(⟨u,hu⟩,φ),⟨Set.mem_univ _,?_⟩,?_⟩
    · change dist ((toDual ℝ E) v) 0≤1
      rw [dist_zero_right,(toDual ℝ E).norm_map,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr rp)]
      exact (inv_mul_le_iff₀ rp).mpr (by simpa [r] using hd)
    · apply (toWeakSpace ℝ E).symm.injective
      change c u+r • (toDual ℝ E).symm ((toDual ℝ E) v)=z
      simp [v,smul_smul,rp.ne']
  · rintro ⟨⟨u,φ⟩,⟨_,hφ⟩,rfl⟩
    let v := (toDual ℝ E).symm φ.toStrongDual
    refine ⟨c u+r₀ u • v,⟨u,u.property,?_⟩,rfl⟩
    have hv : ‖v‖≤1 := by
      have bh : dist ((toDual ℝ E) v) 0 ≤ 1 := by
        change dist φ.toStrongDual 0≤1 at hφ
        simpa only [v,LinearIsometryEquiv.apply_symm_apply] using hφ
      rwa [dist_zero_right,(toDual ℝ E).norm_map] at bh
    simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg (show 0≤r₀ u by linarith [hr u u.property])]
    simpa using mul_le_mul_of_nonneg_left hv (show 0≤r₀ u by linarith [hr u u.property])

end

private theorem radius_cont : Continuous (fun u : simplex => radius u) := by
  have hs := (score_continuousOn (penalty_limit 1) (penalty_limit 1)).domRestrict
  exact continuous_const.add hs

private theorem center_cont : Continuous (fun u : simplex => toWeakSpace ℝ Ambient (center u)) := by
  apply WeakBilin.continuous_of_continuous_eval (topDualPairing ℝ Ambient).flip
  intro l
  let q := (toDual ℝ Ambient).symm l
  have hs := (score_continuousOn (dirLinear_limit q) (penalty_limit ‖q‖)).domRestrict
  have e (u : simplex) : l (center u) = ‖q‖+score (dirLinear q) (penalty ‖q‖) u-‖q‖*radius u := by
    rw [← toDual_symm_apply (x:=center u) (y:=l)]
    linarith [fixed_value q u.property]
  change Continuous (fun u : simplex => l (center u))
  simp only [e]
  exact (continuous_const.add hs).sub (continuous_const.mul radius_cont)

/-- Compactness in the standard weak topology on the actual ambient Hilbert space. -/
theorem fixed_weakly_compact : IsCompact (toWeakSpace ℝ Ambient '' fixedBody) :=
  ballUnion_weakly_compact center radius (fun _ hu => (radius_bounds hu).1) center_cont radius_cont

end Lemmata.FrankWolfePS.Hilbert
