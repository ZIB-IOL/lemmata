module

public import Lemmata.ModifiedE8Bell.VisibilityData
public import Lemmata.ModifiedE8Bell.Main
public import Lemmata.ModifiedE8Bell.VectorProof

public section
namespace Lemmata.ModifiedE8Bell
open scoped BigOperators

/-- Correlations of the 120 normalized E₈ root directions. -/
noncomputable def rootCorrelation : Correlation := fun i j =>
  ((∑ k, root i k * root j k : ℤ) : ℝ) / 8

/-- The endpoint is local, and no larger visibility is local. -/
def ExactVisibility : Prop :=
  IsLocal ((109/165 : ℝ) • rootCorrelation) ∧
  ∀ v : ℝ, IsLocal (v • rootCorrelation) → v ≤ 109/165

lemma tableMatrix_average (rs : Array Relabel) (M : IntegerTable) :
    tableMatrix (averageTable rs M) = averageNumerator rs (tableMatrix M) := by
  funext i j
  simp [tableMatrix, averageTable, averageNumerator]

lemma tableMatrix_initial : tableMatrix initialTable = initialMixture := by
  funext i j
  simp [tableMatrix, initialTable]

lemma runAverages_local (rs : List (Array Relabel)) (hrs : ∀ r ∈ rs, 0 < r.size)
    (M : IntegerTable) (d : ℕ) (hd : 0 < d) (hm : IsLocal (normalized (tableMatrix M) d)) :
    0 < (runAverages rs M d).2 ∧
    IsLocal (normalized (tableMatrix (runAverages rs M d).1) (runAverages rs M d).2) := by
  induction rs generalizing M d with
  | nil => exact ⟨hd,hm⟩
  | cons r rs ih =>
    have hr : 0 < r.size := hrs r (by simp)
    apply ih (fun x hx => hrs x (by simp [hx])) _ _ (Nat.mul_pos hr hd)
    simpa only [tableMatrix_average] using average_local r hr (tableMatrix M) d hd hm

lemma initial_local : IsLocal (normalized initialMixture 11) := by
  have h := local_mix (deterministic_local tournamentA tournamentB)
    (deterministic_local witnessA witnessB)
    (by norm_num : (0:ℝ) ≤ 8/11) (by norm_num : (0:ℝ) ≤ 3/11)
    (by norm_num : (8/11:ℝ)+3/11=1)
  have he : normalized initialMixture 11 =
      (8/11:ℝ) • deterministic tournamentA tournamentB + (3/11:ℝ) • deterministic witnessA witnessB := by
    ext i j
    simp only [normalized, initialMixture, deterministic, Int.cast_add, Int.cast_mul,
      Int.cast_ofNat, Nat.cast_ofNat, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he]
  exact h

lemma visibility_endpoint : IsLocal ((109/165 : ℝ) • rootCorrelation) := by
  have h := runAverages_local visibilityStages.toList visibility_stages_nonempty
    initialTable 11 (by decide) (by simpa only [tableMatrix_initial] using initial_local)
  change 0 < visibilityResult.2 ∧ IsLocal (normalized (tableMatrix visibilityResult.1) visibilityResult.2) at h
  have hd : (visibilityResult.2 : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt h.1
  have he : normalized (tableMatrix visibilityResult.1) visibilityResult.2 = (109/165 : ℝ) • rootCorrelation := by
    ext i j
    have hij : (1320:ℝ) * (tableMatrix visibilityResult.1 i j : ℝ) =
        109 * (visibilityResult.2 : ℝ) * ((∑ k, root i k * root j k : ℤ) : ℝ) := by
      exact_mod_cast visibility_entries i j
    simp only [normalized, Pi.smul_apply, smul_eq_mul, rootCorrelation]
    field_simp
    nlinarith
  simpa only [he] using h.2

noncomputable def bellFunctional : Correlation →ₗ[ℝ] ℝ where
  toFun M := ∑ i, ∑ j, realMatrix i j * M i j
  map_add' A B := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c A := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

lemma bellFunctional_deterministic (a b : Signing) :
    bellFunctional (deterministic a b) = (fourBell a b : ℝ)/4 := by
  simp only [bellFunctional, LinearMap.coe_mk, AddHom.coe_mk, deterministic, realMatrix,
    fourBell, Int.cast_sum, Int.cast_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma local_bell_upper {M : Correlation} (hm : IsLocal M) : bellFunctional M ≤ 6104 := by
  apply convexHull_min (t := bellFunctional ⁻¹' Set.Iic 6104) ?_
    ((convex_Iic (6104 : ℝ)).linear_preimage bellFunctional) hm
  rintro _ ⟨⟨a,b⟩,rfl⟩
  change bellFunctional (deterministic a b) ≤ 6104
  rw [bellFunctional_deterministic]
  have h : (fourBell a b : ℝ) ≤ 24416 := by exact_mod_cast fourBell_upper a b
  linarith

lemma bellFunctional_rootCorrelation : bellFunctional rootCorrelation = 9240 := by
  have h : (∑ i, ∑ j, (fourMatrix i j : ℝ) * (∑ k, (root i k : ℝ) * (root j k : ℝ))) = 295680 := by
    exact_mod_cast vector_witness_integer
  change (∑ i, ∑ j, ((fourMatrix i j : ℝ)/4) *
    (((∑ k, root i k * root j k : ℤ) : ℝ)/8)) = 9240
  simp only [Int.cast_sum, Int.cast_mul, div_mul_div_comm, ← Finset.sum_div]
  norm_num
  linarith

/-- Exact local visibility of the fixed E₈ root correlation matrix. -/
theorem exact_visibility : ExactVisibility := by
  refine ⟨visibility_endpoint, ?_⟩
  intro v hv
  have h := local_bell_upper hv
  rw [map_smul, bellFunctional_rootCorrelation] at h
  change v * 9240 ≤ 6104 at h
  linarith

end Lemmata.ModifiedE8Bell
