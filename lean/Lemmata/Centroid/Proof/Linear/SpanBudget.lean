module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.Centroid.Linear

variable {F L α : Type*} [Field F] [AddCommGroup L] [Module F L]
  [Module.Finite F L]

theorem exists_small_submodule_cover (S : α → Submodule F L)
    (E : Submodule F L) (hE : E ≤ ⨆ a, S a) :
    ∃ s : Finset α, s.card + Module.finrank F E ≤
      Module.finrank F (⨆ a, S a : Submodule F L) ∧
      E ⊔ s.sup S = ⨆ a, S a := by
  generalize hd : Module.finrank F (⨆ a, S a : Submodule F L) - Module.finrank F E = d
  induction d using Nat.strong_induction_on generalizing E with
  | h d ih =>
    by_cases he : E = ⨆ a, S a
    · refine ⟨∅, ?_, ?_⟩
      · simpa only [Finset.card_empty, zero_add] using Submodule.finrank_mono hE
      · simpa only [Finset.sup_empty, sup_bot_eq] using he
    have hw : ∃ a, ¬ S a ≤ E := by
      by_contra! hn
      exact he (le_antisymm hE (iSup_le hn))
    obtain ⟨a, ha⟩ := hw
    have he' : E ⊔ S a ≤ ⨆ a, S a := sup_le hE (le_iSup S a)
    have hlt : E < E ⊔ S a := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro h
      exact ha (le_sup_right.trans_eq h.symm)
    have hdim := Submodule.finrank_lt_finrank_of_lt hlt
    have hdim' := Submodule.finrank_mono he'
    have hgap : Module.finrank F (⨆ a, S a : Submodule F L) -
        Module.finrank F (E ⊔ S a : Submodule F L) < d := by
      omega
    obtain ⟨s, hs, hspan⟩ := ih _ hgap (E ⊔ S a) he' rfl
    refine ⟨insert a s, ?_, ?_⟩
    · have hcard : (insert a s).card ≤ s.card + 1 := Finset.card_insert_le _ _
      omega
    · rw [Finset.sup_insert, ← sup_assoc]
      exact hspan

section Restrictions

variable {D P : Type*} [AddCommGroup D] [Module F D] [Module.Finite F D]
  [AddCommGroup P] [Module F P]

def restriction (B : D →ₗ[F] L →ₗ[F] P) (E : Submodule F L) :
    D →ₗ[F] E →ₗ[F] P where
  toFun c := (B c).comp E.subtype
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

def jointRestriction (B : D →ₗ[F] L →ₗ[F] P) (R : α → Submodule F L) :
    D →ₗ[F] ∀ i, LinearMap.range (restriction B (R i)) where
  toFun c i := ⟨restriction B (R i) c, LinearMap.mem_range_self _ _⟩
  map_add' c d := by
    funext i
    apply Subtype.ext
    change restriction B (R i) (c + d) = restriction B (R i) c + restriction B (R i) d
    exact map_add _ _ _
  map_smul' c d := by
    funext i
    apply Subtype.ext
    change restriction B (R i) (c • d) = c • restriction B (R i) d
    exact map_smul _ _ _

omit [Module.Finite F L] [Module.Finite F D] in
theorem jointRestriction_injective (B : D →ₗ[F] L →ₗ[F] P)
    (R : α → Submodule F L) (J : Submodule F L)
    (hspan : J ≤ ⨆ i, R i)
    (hB : ∀ c, (∀ x ∈ J, B c x = 0) → c = 0) :
    Function.Injective (jointRestriction B R) := by
  intro c d h
  apply sub_eq_zero.mp
  apply hB
  intro x hx
  have hker : (⨆ i, R i) ≤ LinearMap.ker (B (c - d)) := by
    apply iSup_le
    intro i y hy
    have hi := congrArg (fun f => (f i).val ⟨y, hy⟩) h
    change B c y = B d y at hi
    change B (c - d) y = 0
    simpa only [map_sub, LinearMap.sub_apply] using sub_eq_zero.mpr hi
  exact hker (hspan hx)

omit [Module.Finite F L] in
theorem finrank_le_sum_restriction_ranks [Fintype α]
    (B : D →ₗ[F] L →ₗ[F] P) (R : α → Submodule F L) (J : Submodule F L)
    (hspan : J ≤ ⨆ i, R i)
    (hB : ∀ c, (∀ x ∈ J, B c x = 0) → c = 0) :
    Module.finrank F D ≤ ∑ i, Module.finrank F (LinearMap.range (restriction B (R i))) := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (jointRestriction_injective B R J hspan hB)
  simpa only [Module.finrank_pi_fintype] using h

variable {W : Type*} [AddCommGroup W] [Module F W]

def evaluateFamily (A : D →ₗ[F] W →ₗ[F] L) (w : W) : D →ₗ[F] L where
  toFun c := A c w
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

omit [Module.Finite F L] in
theorem restriction_rank_le_evaluation_rank
    (B : D →ₗ[F] L →ₗ[F] P) (A : D →ₗ[F] W →ₗ[F] L)
    (hcomm : ∀ c d, (B c).comp (A d) = (B d).comp (A c)) (w : W) :
    Module.finrank F (LinearMap.range (restriction B (LinearMap.range (evaluateFamily A w)))) ≤
      Module.finrank F (LinearMap.range (evaluateFamily A w)) := by
  have hker : LinearMap.ker (evaluateFamily A w) ≤
      LinearMap.ker (restriction B (LinearMap.range (evaluateFamily A w))) := by
    intro c hc
    change restriction B (LinearMap.range (evaluateFamily A w)) c = 0
    ext x
    obtain ⟨d, hd⟩ := x.property
    change A d w = x.val at hd
    change B c x.val = 0
    rw [← hd]
    have hs := LinearMap.congr_fun (hcomm c d) w
    change B c (A d w) = B d (A c w) at hs
    rw [hs]
    change A c w = 0 at hc
    rw [hc, map_zero]
  have hk := Submodule.finrank_mono hker
  have h1 := (evaluateFamily A w).finrank_range_add_finrank_ker
  have h2 := (restriction B (LinearMap.range (evaluateFamily A w))).finrank_range_add_finrank_ker
  omega

theorem symmetric_composition_bound
    (B : D →ₗ[F] L →ₗ[F] P) (A : D →ₗ[F] W →ₗ[F] L)
    (hcomm : ∀ c d, (B c).comp (A d) = (B d).comp (A c))
    (hnondeg : ∀ c, (∀ d, (B c).comp (A d) = 0) → c = 0) :
    Module.finrank F D ≤ (Module.finrank F L + 1) ^ 2 / 4 := by
  let S : W → Submodule F L := fun w => LinearMap.range (evaluateFamily A w)
  let Q : ℕ → Prop := fun n => ∃ w : W, Module.finrank F (S w) = n
  have hzero : Q 0 := by
    refine ⟨0, ?_⟩
    have he : evaluateFamily A (0 : W) = 0 := by ext; simp [evaluateFamily]
    simp [S, he]
  obtain ⟨w, hw⟩ := Nat.findGreatest_spec (P := Q) (Nat.zero_le (Module.finrank F L)) hzero
  have hmax (x : W) : Module.finrank F (S x) ≤ Module.finrank F (S w) := by
    rw [hw]
    exact Nat.le_findGreatest (Submodule.finrank_le _) ⟨x, rfl⟩
  let J : Submodule F L := ⨆ x, S x
  obtain ⟨s, hs, hspan⟩ := exists_small_submodule_cover S (S w) (le_iSup S w)
  let R : Option s → Submodule F L := fun i => Option.elim i (S w) (fun x => S x.val)
  have hcover : J ≤ ⨆ i, R i := by
    change (⨆ a, S a : Submodule F L) ≤ ⨆ i, R i
    rw [← hspan]
    apply sup_le
    · exact le_iSup R none
    · apply Finset.sup_le
      intro x hx
      exact le_iSup R (some ⟨x, hx⟩)
  have hB : ∀ c, (∀ x ∈ J, B c x = 0) → c = 0 := by
    intro c hc
    apply hnondeg c
    intro d
    ext x
    apply hc
    exact (le_iSup S x) (LinearMap.mem_range_self (evaluateFamily A x) d)
  have hdim := finrank_le_sum_restriction_ranks B R J hcover hB
  have hr (i : Option s) : Module.finrank F (LinearMap.range (restriction B (R i))) ≤
      Module.finrank F (S w) := by
    cases i with
    | none => exact restriction_rank_le_evaluation_rank B A hcomm w
    | some i => exact (restriction_rank_le_evaluation_rank B A hcomm i.val).trans (hmax i.val)
  have htotal : Module.finrank F D ≤ (s.card + 1) * Module.finrank F (S w) := by
    calc
      _ ≤ ∑ i, Module.finrank F (LinearMap.range (restriction B (R i))) := hdim
      _ ≤ ∑ _i : Option s, Module.finrank F (S w) := Finset.sum_le_sum (fun i _ => hr i)
      _ = _ := by simp
  have hJ := Submodule.finrank_le J
  have hsum : Module.finrank F (S w) + (s.card + 1) ≤ Module.finrank F L + 1 := by
    change s.card + Module.finrank F (S w) ≤ Module.finrank F J at hs
    omega
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 4)).mpr
  calc
    Module.finrank F D * 4 ≤ ((s.card + 1) * Module.finrank F (S w)) * 4 :=
      Nat.mul_le_mul_right 4 htotal
    _ = 4 * Module.finrank F (S w) * (s.card + 1) := by ring
    _ ≤ (Module.finrank F (S w) + (s.card + 1)) ^ 2 := four_mul_le_sq_add _ _
    _ ≤ (Module.finrank F L + 1) ^ 2 := Nat.pow_le_pow_left hsum 2

end Restrictions

theorem commutative_algebra_dimension_bound {A : Type*} [CommRing A] [Algebra F A]
    [Module.Finite F A] (ρ : A →ₐ[F] Module.End F L) (hρ : Function.Injective ρ) :
    Module.finrank F A ≤ (Module.finrank F L + 1) ^ 2 / 4 := by
  apply symmetric_composition_bound ρ.toLinearMap ρ.toLinearMap
  · intro c d
    change ρ c * ρ d = ρ d * ρ c
    rw [← map_mul, ← map_mul, mul_comm]
  · intro c hc
    apply hρ
    have h : ρ c * ρ 1 = 0 := hc 1
    simpa only [map_one, mul_one, map_zero] using h

end Lemmata.Centroid.Linear
