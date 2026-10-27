module

public import Lemmata.CocubicCovering.Proof.DAG
public meta import Lemmata.CocubicCovering.Proof.DAG
public import Lemmata.CocubicCovering.Proof.Search
public meta import Lemmata.CocubicCovering.Proof.Search
public import Lemmata.CocubicCovering.Proof.PackedWitness
public meta import Lemmata.CocubicCovering.Proof.PackedWitness
public import Lemmata.CocubicCovering.Proof.PackedLeaf
public meta import Lemmata.CocubicCovering.Proof.PackedLeaf

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringFiniteDAG

open Module CoveringBits CoveringWitness CoveringPackedWitness CoveringAffine
open CoveringPackedAction CoveringBranching

structure Root where
  assignment : ℕ
  radical : List ℕ
  required : ℕ

structure State (r : ℕ) where
  root : Fin r
  core : List ℕ

structure Branch (n : ℕ) where
  fresh : List ℕ
  inRadical : List ℕ
  dual : List ℕ
  children : Fin (2 ^ fresh.length - 1) → Fin n
  coefficients : Fin (2 ^ fresh.length - 1) → List ℕ

inductive Rule (n w : ℕ) where
  | leaf (path selected coefficients : List ℕ)
  | branch (data : Branch n)
  | orbit (target : Fin n) (word : Fin w) (coefficients : List ℕ)

def premises {n w : ℕ} : Rule n w → List (Fin n)
  | .leaf _ _ _ => []
  | .branch data => List.ofFn data.children
  | .orbit target _ _ => [target]

def imageColumns {c : ℕ} (columns : Fin 12 → ℕ) (core : Fin c → ℕ) : Fin c → ℕ :=
  fun i => composeRow (core i) columns

def checkNode {r n w : ℕ} (roots : Fin r → Root) (states : Fin n → State r)
    (columns : Fin w → Fin 12 → ℕ) (guard : Fin w → Fin r → Bool)
    (i : Fin n) : Rule n w → Bool
  | .leaf path selected coefficients =>
      CoveringPackedLeaf.check (roots (states i).root).assignment path selected &&
        listCheckSpan path (states i).core coefficients
  | .orbit target word coefficients =>
      (guard word (states i).root && decide ((states target).root = (states i).root)) &&
        checkSpan (listColumns (states target).core)
          (imageColumns (columns word) (listColumns (states i).core))
          (fun j => coefficients[j.val]?.getD 0)
  | .branch data =>
      ((listCheckSpan data.fresh (roots (states i).root).radical data.inRadical &&
        listCheckCombinedDual 12 (states i).core data.fresh data.dual) &&
        decide ((roots (states i).root).radical.length <
          data.fresh.length + (roots (states i).root).required)) &&
        (List.finRange (2 ^ data.fresh.length - 1)).all fun j =>
          decide ((states (data.children j)).root = (states i).root) &&
            checkSpan (listColumns (states (data.children j)).core)
              (appendColumns (listColumns (states i).core)
                (fun _ : Fin 1 => composeRow (j.val + 1) (listColumns data.fresh)))
              (fun k => (data.coefficients j)[k.val]?.getD 0)

def feasible {r : ℕ} (allowed : Fin r → Vector 127 → Prop)
    (kernel : Vector 127 → Submodule Field (Vector 12)) (state : State r) : Prop :=
  CoveringSearch.Feasible (allowed state.root) kernel (decoded (listColumns state.core))

theorem append_span_single_le {c : ℕ} (core : Fin c → ℕ) (mask : ℕ) :
    familySpan (decoded (n := 12) (appendColumns core (fun _ : Fin 1 => mask))) ≤
      familySpan (decoded (n := 12) core) ⊔
        Submodule.span Field {(decodeMask mask : Vector 12)} := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  obtain ⟨s, rfl⟩ := (finSumFinEquiv : Fin c ⊕ Fin 1 ≃ Fin (c + 1)).surjective i
  cases s with
  | inl j =>
      simp only [decoded, appendColumns, Equiv.symm_apply_apply, Sum.elim_inl]
      exact (le_sup_left : familySpan (decoded (n := 12) core) ≤ _)
        (Submodule.subset_span ⟨j, rfl⟩)
  | inr j =>
      simp only [decoded, appendColumns, Equiv.symm_apply_apply, Sum.elim_inr]
      exact (le_sup_right : Submodule.span Field {(decodeMask mask : Vector 12)} ≤ _)
        (Submodule.subset_span (Set.mem_singleton _))

theorem image_span_le {c : ℕ} (columns : Fin 12 → ℕ) (core : Fin c → ℕ)
    (action : Vector 12 →ₗ[Field] Vector 12)
    (h : ∀ mask, action (decodeMask mask) = decodeMask (composeRow mask columns)) :
    familySpan (decoded (n := 12) (imageColumns columns core)) ≤
      (familySpan (decoded (n := 12) core)).map action := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  refine ⟨decodeMask (core i), Submodule.subset_span ⟨i, rfl⟩, ?_⟩
  exact h (core i)

section Soundness

variable {r n w : ℕ} (roots : Fin r → Root) (states : Fin n → State r)
  (columns : Fin w → Fin 12 → ℕ) (guard : Fin w → Fin r → Bool)
  (allowed : Fin r → Vector 127 → Prop)
  (kernel : Vector 127 → Submodule Field (Vector 12))
  (transform : Fin w → Vector 127 → Vector 127)
  (action : Fin w → Vector 12 →ₗ[Field] Vector 12)

variable
  (hkernel : ∀ root p, allowed root p →
    kernel p ≤ familySpan (decoded (n := 12) (listColumns (roots root).radical)))
  (hdimension : ∀ root p, allowed root p →
    (roots root).required ≤ finrank Field (kernel p))
  (hpoint : ∀ root p, allowed root p → p (Fin.last 126) = 1)
  (hroot : ∀ root p, allowed root p → ∀ i : Fin 15,
    p ⟨111 + i.val, by omega⟩ = CoveringPolynomial.ofBool ((roots root).assignment.testBit i.val))
  (hrow : ∀ p mask, (decodeMask mask : Vector 12) ∈ kernel p →
    ∀ column, evalRow (CoveringPackedLeaf.kernelRow mask column) p = 0)
  (haction : ∀ word mask, action word (decodeMask mask) =
    decodeMask (composeRow mask (columns word)))
  (hallowed : ∀ word root, guard word root = true → ∀ p,
    allowed root p → allowed root (transform word p))
  (htransport : ∀ word root, guard word root = true → ∀ p,
    allowed root p → (kernel p).map (action word) ≤ kernel (transform word p))

include transform action hkernel hdimension hpoint hroot hrow haction hallowed htransport

theorem step_sound (i : Fin n) (rule : Rule n w)
    (accepted : checkNode roots states columns guard i rule = true)
    (possible : feasible allowed kernel (states i)) :
    ∃ j ∈ premises rule, feasible allowed kernel (states j) := by
  cases rule with
  | leaf path selected coefficients =>
      obtain ⟨hcheck, hspan⟩ := Bool.and_eq_true_iff.mp accepted
      obtain ⟨p, hp, hcore⟩ := possible
      have hpath := (listCheckSpan_sound 12 path (states i).core coefficients hspan).trans hcore
      apply False.elim
      apply CoveringPackedLeaf.check_sound _ path selected hcheck
      refine ⟨p, hpoint _ _ hp, hroot _ _ hp, ?_⟩
      intro mask hmask column
      apply hrow p mask
      apply hpath
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hmask
      rw [← hj]
      exact Submodule.subset_span ⟨j, rfl⟩
  | orbit target word coefficients =>
      obtain ⟨hfirst, hspan⟩ := Bool.and_eq_true_iff.mp accepted
      obtain ⟨hguard, hsame⟩ := Bool.and_eq_true_iff.mp hfirst
      have hsame' : (states target).root = (states i).root := of_decide_eq_true hsame
      have htarget := checkSpan_sound (n := 12) _ _ _ hspan
      have hmapped := image_span_le (columns word) (listColumns (states i).core)
        (action word) (haction word)
      have hf := CoveringSearch.transport (allowed (states i).root) (allowed (states i).root)
        kernel kernel (decoded (listColumns (states i).core))
        (decoded (listColumns (states target).core)) (transform word) (action word)
        (hallowed word _ hguard) (htransport word _ hguard) (htarget.trans hmapped) possible
      refine ⟨target, by simp [premises], ?_⟩
      simpa only [feasible, hsame'] using hf
  | branch data =>
      obtain ⟨hfirst, hchildren⟩ := Bool.and_eq_true_iff.mp accepted
      obtain ⟨hsecond, hnumeric⟩ := Bool.and_eq_true_iff.mp hfirst
      obtain ⟨hin, hdual⟩ := Bool.and_eq_true_iff.mp hsecond
      obtain ⟨p, hp, hcore⟩ := possible
      have hcombined := listCheckCombinedDual_sound 12 (states i).core data.fresh data.dual hdual
      have hambient : finrank Field
          (familySpan (decoded (n := 12) (listColumns (roots (states i).root).radical))) <
          data.fresh.length + (roots (states i).root).required := by
        have hupper := finrank_range_le_card (R := Field)
          (decoded (n := 12) (listColumns (roots (states i).root).radical))
        have hn := of_decide_eq_true hnumeric
        change finrank Field _ ≤ _ at hupper
        simp only [Fintype.card_fin] at hupper
        exact lt_of_le_of_lt hupper hn
      obtain ⟨b, hb, _, _, hnext⟩ := exists_kernel_branch
        (decoded (n := 12) (listColumns data.fresh))
        (familySpan (decoded (n := 12) (listColumns (roots (states i).root).radical)))
        (kernel p) (familySpan (decoded (n := 12) (listColumns (states i).core)))
        (listCheckSpan_sound 12 _ _ _ hin) (hkernel _ _ hp) hcore
        hcombined.1 hcombined.2 (hdimension _ _ hp) hambient
      obtain ⟨mask, hbound, hdecode⟩ := exists_bounded_mask b
      have hpositive : 0 < mask := by
        by_contra hzero
        have hz : mask = 0 := by omega
        have hbzero : b = 0 := by simpa only [hz, decodeMask_zero] using hdecode.symm
        exact (mem_branches b).mp hb hbzero
      let j : Fin (2 ^ data.fresh.length - 1) := ⟨mask - 1, by omega⟩
      have hj : j.val + 1 = mask := by dsimp [j]; omega
      obtain ⟨hsame, hspan⟩ := Bool.and_eq_true_iff.mp
        ((List.all_eq_true.mp hchildren) j (List.mem_finRange _))
      have hsame' : (states (data.children j)).root = (states i).root := of_decide_eq_true hsame
      have htarget := checkSpan_sound (n := 12) _ _ _ hspan
      rw [hj] at htarget
      have hsup := append_span_single_le (listColumns (states i).core)
        (composeRow (j.val + 1) (listColumns data.fresh))
      rw [hj, decodeMask_composeRow_familyLinear, hdecode] at hsup
      refine ⟨data.children j, List.mem_ofFn.mpr ⟨j, rfl⟩, ?_⟩
      refine ⟨p, ?_, htarget.trans (hsup.trans hnext)⟩
      simpa only [hsame'] using hp

theorem check_sound (rules : Fin n → Rule n w)
    (accepted : CoveringDAG.check (fun i => checkNode roots states columns guard i (rules i))
      (fun i => premises (rules i)) = true) :
    ∀ i, ¬feasible allowed kernel (states i) := by
  exact CoveringDAG.check_sound states _ _ (feasible allowed kernel)
    (fun i => step_sound roots states columns guard allowed kernel transform action
      hkernel hdimension hpoint hroot hrow haction hallowed htransport i (rules i)) accepted

end Soundness

end Lemmata.CocubicCovering.CoveringFiniteDAG
