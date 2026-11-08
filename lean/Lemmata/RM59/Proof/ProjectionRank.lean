module

public import Lemmata.RM59.Proof.ProjectionEquivalence
public import Lemmata.RM59.Proof.FieldRank
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

namespace Lemmata.RM59.ProjectionRank

open scoped BigOperators Matrix

abbrev FieldPoint := TraceGeometry.FieldPoint
abbrev Plane := Fin 2 → F8Scalar

def projection : FieldPoint →ₗ[Field] Plane where
  toFun x := ![x 0, x 1]
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' r x := by ext i; fin_cases i <;> rfl

def inclusion : Plane →ₗ[Field] FieldPoint where
  toFun x := ![x 0, x 1, 0]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' r x := by ext i; fin_cases i <;> simp

theorem projection_inclusion (x : Plane) : projection (inclusion x) = x := by
  ext i
  fin_cases i <;> rfl

theorem inclusion_injective : Function.Injective inclusion := by
  intro x y h
  simpa only [projection_inclusion] using congrArg projection h

def verticalEquiv : F8Scalar ≃ₗ[Field] LinearMap.ker projection where
  toFun c := ⟨TraceGeometry.vertical c, by ext i; fin_cases i <;> rfl⟩
  invFun x := x.val 2
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    have h0 : x.val 0 = 0 := congrFun x.property 0
    have h1 : x.val 1 = 0 := congrFun x.property 1
    ext i
    fin_cases i <;> simp [TraceGeometry.vertical, h0, h1]
  map_add' a b := by apply Subtype.ext; ext i; fin_cases i <;> simp [TraceGeometry.vertical]
  map_smul' r a := by apply Subtype.ext; ext i; fin_cases i <;> simp [TraceGeometry.vertical]

theorem kernel_finrank : Module.finrank Field (LinearMap.ker projection) = 3 := by
  rw [← verticalEquiv.finrank_eq, FieldRank.scalar_finrank]

theorem plane_finrank : Module.finrank Field Plane = 6 := by
  norm_num [Plane, Module.finrank_pi_fintype, FieldRank.scalar_finrank]

theorem projected_rank_bound {ι : Type*} [Fintype ι] (v : ι → FieldPoint)
    (hv : LinearIndependent Field v) :
    Fintype.card ι ≤ Module.finrank Field
      (Submodule.span Field (Set.range (fun i => projection (v i)))) + 3 := by
  let S := Submodule.span Field (Set.range v)
  let f := projection.domRestrict S
  let g : LinearMap.ker f →ₗ[Field] LinearMap.ker projection := {
    toFun := fun x => ⟨x.val.val, x.property⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : LinearMap.ker projection => z.val) h
  have hker : Module.finrank Field (LinearMap.ker f) ≤ 3 := by
    exact (LinearMap.finrank_le_finrank_of_injective hg).trans_eq kernel_finrank
  have hrange : LinearMap.range f =
      Submodule.span Field (Set.range (fun i => projection (v i))) := by
    rw [LinearMap.range_domRestrict, ← Submodule.span_image]
    congr 1
    exact (Set.range_comp projection v).symm
  have hr := f.finrank_range_add_finrank_ker
  have hS : Module.finrank Field S = Fintype.card ι := finrank_span_eq_card hv
  rw [hrange, hS] at hr
  omega

theorem exists_projected_subfamily {ι : Type*} [Fintype ι] (v : ι → FieldPoint)
    (hv : LinearIndependent Field v) (k : Nat) (hk : k + 3 ≤ Fintype.card ι) :
    ∃ f : Fin k → ι, LinearIndependent Field (fun j => projection (v (f j))) := by
  classical
  have hdim := projected_rank_bound v hv
  have hkr : k ≤ Module.finrank Field
      (Submodule.span Field (Set.range (fun i => projection (v i)))) := by omega
  obtain ⟨g, hgmem, _, hg⟩ := Submodule.exists_fun_fin_finrank_span_eq Field
    (Set.range (fun i => projection (v i)))
  have hgk := hg.comp (Fin.castLE hkr) (Fin.castLE_injective hkr)
  let f : Fin k → ι := fun i => Classical.choose (hgmem (Fin.castLE hkr i))
  have hf : ∀ i, projection (v (f i)) = g (Fin.castLE hkr i) :=
    fun i => Classical.choose_spec (hgmem (Fin.castLE hkr i))
  refine ⟨f, ?_⟩
  have he : (fun i : Fin k => projection (v (f i))) =
      (fun i => g (Fin.castLE hkr i)) := funext hf
  rwa [he]

theorem exists_projected_differences {ι : Type*} [Fintype ι] (p : ι → FieldPoint)
    (hp : AffineIndependent Field p) (base : ι) (k : Nat)
    (hk : k + 3 ≤ Fintype.card ι - 1) :
    ∃ f : Fin k → ι,
      LinearIndependent Field (fun j => projection (p (f j) - p base)) := by
  classical
  let v : {i : ι // i ≠ base} → FieldPoint := fun i => p i - p base
  have hv : LinearIndependent Field v :=
    (affineIndependent_iff_linearIndependent_vsub Field p base).mp hp
  have hcard : Fintype.card {i : ι // i ≠ base} = Fintype.card ι - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  obtain ⟨f, hf⟩ := exists_projected_subfamily v hv k (by simpa only [hcard] using hk)
  exact ⟨fun j => (f j).val, hf⟩

theorem centered_zero_independent {M : Type*} [AddCommGroup M] [Module Field M]
    (p : Fin 5 → M) (hp : AffineIndependent Field p) (hsum : ∑ i, p i = 0) :
    LinearIndependent Field (fun j : Fin 4 => p j.castSucc) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  let w : Fin 5 → Field := Fin.snoc c 0
  let total : Field := ∑ j, c j
  have hw : (∑ i, w i) = total := by
    rw [Fin.sum_univ_castSucc]
    simp only [w, Fin.snoc_castSucc, Fin.snoc_last, add_zero, total]
  have hwp : (∑ i, w i • p i) = 0 := by
    rw [Fin.sum_univ_castSucc]
    simpa only [w, Fin.snoc_castSucc, Fin.snoc_last, zero_smul, add_zero] using hc
  have h5 : (5 : Nat) • total = total := by
    rw [nsmul_eq_mul]
    have hfive : ((5 : Nat) : Field) = 1 := by decide
    rw [hfive, one_mul]
  have hw' : (∑ i, (w i + total)) = 0 := by
    rw [Finset.sum_add_distrib, hw, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, h5]
    exact field_add_self total
  have hwp' : (∑ i, (w i + total) • p i) = 0 := by
    simp only [add_smul, Finset.sum_add_distrib]
    rw [hwp, ← Finset.smul_sum, hsum, smul_zero, add_zero]
  have hz := hp.eq_zero_of_sum_eq_zero hw' hwp'
  have ht : total = 0 := by
    simpa only [w, Fin.snoc_last, zero_add] using hz (Fin.last 4) (Finset.mem_univ _)
  intro j
  simpa only [w, Fin.snoc_castSucc, ht, add_zero] using hz j.castSucc (Finset.mem_univ _)

theorem affineIndependent_of_differences (p : Fin 5 → Plane)
    (hp : LinearIndependent Field (fun j : Fin 4 => p j.succ - p 0)) :
    AffineIndependent Field p := by
  apply (affineIndependent_iff_linearIndependent_vsub Field p 0).2
  apply (linearIndependent_equiv (finSuccAboveEquiv (0 : Fin 5))).1
  simpa only [Function.comp_def, finSuccAboveEquiv_apply, Fin.zero_succAbove,
    vsub_eq_sub] using hp

theorem projected_five_independent (p : Fin 5 → FieldPoint)
    (hp : LinearIndependent Field (fun j : Fin 4 => projection (p j.succ - p 0))) :
    LinearIndependent Field (ProjectionGeometry.column
      (ProjectionEquivalence.rows p 0) (ProjectionEquivalence.rows p 1) 0) := by
  have ha : AffineIndependent Field (fun i => projection (p i)) :=
    affineIndependent_of_differences _ (by simpa only [map_sub] using hp)
  have hat : AffineIndependent Field
      (fun i => projection (ProjectionEquivalence.centered p i)) := by
    have hv := ha.vadd (v := projection (ProjectionEquivalence.center p))
    change AffineIndependent Field
      (fun i => projection (ProjectionEquivalence.center p) + projection (p i)) at hv
    simpa only [ProjectionEquivalence.centered, map_add, add_comm] using hv
  have hs : (∑ i, projection (ProjectionEquivalence.centered p i)) = 0 := by
    rw [← map_sum, ProjectionEquivalence.sum_centered, map_zero]
  have hi := (centered_zero_independent _ hat hs).map' inclusion
    (LinearMap.ker_eq_bot.mpr inclusion_injective)
  convert hi using 1
  funext j
  ext i
  fin_cases i <;> rfl

end Lemmata.RM59.ProjectionRank
