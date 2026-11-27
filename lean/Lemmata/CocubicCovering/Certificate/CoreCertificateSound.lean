module

public import Lemmata.CocubicCovering.Certificate.CoreCertificate
public meta import Lemmata.CocubicCovering.Certificate.CoreCertificate
public import Lemmata.CocubicCovering.Certificate.PureDualSemantics
public meta import Lemmata.CocubicCovering.Certificate.PureDualSemantics
public import Lemmata.CocubicCovering.Proof.FiniteDAG
public meta import Lemmata.CocubicCovering.Proof.FiniteDAG

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.Certificate.CoreCertificate

open Module CoveringBits CoveringWitness CoveringPackedWitness CoveringBranching

theorem xorRows_eq (rows : List Nat) : xorRows rows = CoveringAffine.xorRows rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp only [xorRows, CoveringAffine.xorRows, ih]

theorem composeRow_eq {m : Nat} (mask : Nat) (columns : Fin m → Nat) :
    composeRow mask columns = CoveringAffine.composeRow mask columns :=
  xorRows_eq _

theorem checkSpan_eq {c d : Nat} (source : Fin c → Nat) (target : Fin d → Nat)
    (coefficients : Fin c → Nat) :
    checkSpan source target coefficients = CoveringPackedWitness.checkSpan source target coefficients := by
  simp only [checkSpan, CoveringPackedWitness.checkSpan, composeRow_eq]

theorem listCheckSpan_eq (source target coefficients : List Nat) :
    listCheckSpan source target coefficients = CoveringPackedWitness.listCheckSpan source target coefficients := by
  rw [listCheckSpan, checkSpan_eq]
  rfl

def feasible {r : Nat} (allowed : Fin r → Vector 127 → Prop)
    (kernel : Vector 127 → Submodule Field (Vector 12)) (state : State r) : Prop :=
  ∃ v, allowed state.root v ∧ familySpan (decoded (n := 12) state.core.get) ≤ kernel v

theorem obstruction_sound (rows : Nat → Row) (obstruction : Obstruction)
    (kernel : Vector 127 → Submodule Field (Vector 12))
    (hrow : ∀ i v, (decodeMask (rows i).mask : Vector 12) ∈ kernel v →
      CoveringAffine.evalRow (rows i).value v = 0)
    (accepted : obstructionCheck rows obstruction = true) :
    ¬ ∃ v : Vector 127, v (Fin.last 126) = 1 ∧
      familySpan (decoded (n := 12) obstruction.core.get) ≤ kernel v := by
  obtain ⟨hmembers, hx⟩ := Bool.and_eq_true_iff.mp accepted
  have hx' := of_decide_eq_true hx
  rw [xorRows_eq] at hx'
  rintro ⟨v, hpoint, hcore⟩
  have hz : CoveringAffine.evalRow
      (CoveringAffine.xorRows (obstruction.selected.map fun i => (rows i).value)) v = 0 := by
    rw [CoveringAffine.evalRow_xorRows, List.map_map]
    apply List.sum_eq_zero
    intro value hvalue
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hvalue
    apply hrow i v
    apply hcore
    have hm := List.contains_iff_mem.mp ((List.all_eq_true.mp hmembers) i hi)
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
    rw [← hj]
    exact Submodule.subset_span ⟨j, rfl⟩
  rw [hx'] at hz
  have hc : CoveringAffine.evalRow (2 ^ 126) v = 1 :=
    (CoveringEncoding.evalRow_two_pow (Fin.last 126) v).trans hpoint
  exact one_ne_zero (hc.symm.trans hz)

section Soundness

variable {r n l w t : Nat} (roots : Fin r → Root) (states : Fin n → State r)
  (obstructions : Fin l → Obstruction) (terminals : Fin t → State r)
  (columns : Fin w → Fin 12 → Nat) (guard : Fin w → Fin r → Fin r → Bool)
  (allowed : Fin r → Vector 127 → Prop)
  (kernel : Vector 127 → Submodule Field (Vector 12))
  (transform : Fin w → Vector 127 → Vector 127)
  (action : Fin w → Vector 12 →ₗ[Field] Vector 12)

variable
  (hkernel : ∀ root v, allowed root v →
    kernel v ≤ familySpan (decoded (n := 12) (roots root).radical.get))
  (hdimension : ∀ root v, allowed root v → (roots root).required ≤ finrank Field (kernel v))
  (hpoint : ∀ root v, allowed root v → v (Fin.last 126) = 1)
  (haction : ∀ word mask, action word (decodeMask mask) =
    decodeMask (CoveringAffine.composeRow mask (columns word)))
  (hallowed : ∀ word source target, guard word source target = true → ∀ v,
    allowed source v → allowed target (transform word v))
  (htransport : ∀ word source target, guard word source target = true → ∀ v,
    allowed source v → (kernel v).map (action word) ≤ kernel (transform word v))
  (hleaf : ∀ i, ¬ ∃ v : Vector 127, v (Fin.last 126) = 1 ∧
    familySpan (decoded (n := 12) (obstructions i).core.get) ≤ kernel v)
  (hterminal : ∀ i, ¬ feasible allowed kernel (terminals i))

include transform action haction hallowed htransport in
theorem transformed_core {c d : Nat} (source target : Fin r) (word : Option (Fin w))
    (core : Fin c → Nat) (next : Fin d → Nat) (coefficients : Fin d → Nat)
    (hguard : (match word with
      | none => decide (source = target)
      | some word => guard word source target) = true)
    (hspan : checkSpan next (edgeColumns columns word core) coefficients = true)
    (v : Vector 127) (hv : allowed source v) (hcore : familySpan (decoded core) ≤ kernel v) :
    ∃ v', allowed target v' ∧ familySpan (decoded next) ≤ kernel v' := by
  rw [checkSpan_eq] at hspan
  have hnext := checkSpan_sound (n := 12) _ _ _ hspan
  cases word with
  | none =>
      have he : source = target := of_decide_eq_true hguard
      exact ⟨v, he ▸ hv, hnext.trans hcore⟩
  | some word =>
      have he : edgeColumns columns (some word) core =
          CoveringFiniteDAG.imageColumns (columns word) core := by
        funext i
        exact composeRow_eq _ _
      rw [he] at hnext
      have himage := CoveringFiniteDAG.image_span_le (columns word) core (action word) (haction word)
      exact ⟨transform word v, hallowed word source target hguard v hv,
        hnext.trans (himage.trans ((Submodule.map_mono hcore).trans
          (htransport word source target hguard v hv)))⟩

include transform action hpoint haction hallowed htransport hleaf in
theorem edge_sound (i : Fin n) {c : Nat} (core : Fin c → Nat) (edge : Edge n l w)
    (accepted : edgeCheck states obstructions columns guard i core edge = true)
    (v : Vector 127) (hv : allowed (states i).root v)
    (hcore : familySpan (decoded core) ≤ kernel v) :
    ∃ j : Fin n, j.val < i.val ∧ feasible allowed kernel (states j) := by
  obtain ⟨hfirst, ho⟩ := Bool.and_eq_true_iff.mp accepted
  obtain ⟨hg, hs⟩ := Bool.and_eq_true_iff.mp hfirst
  obtain ⟨v', hv', hc'⟩ := transformed_core columns guard allowed kernel transform action
    haction hallowed htransport (states i).root (targetRoot states (states i).root edge.target)
    edge.word core (targetCore states obstructions edge.target).get
    (fun j => edge.coefficients[j.val]?.getD 0) hg hs v hv hcore
  rcases edge with ⟨target, word, coefficients⟩
  cases target with
  | inl j =>
      exact ⟨j, of_decide_eq_true ho, v', hv', hc'⟩
  | inr j =>
      apply False.elim
      apply hleaf j
      exact ⟨v', hpoint _ _ hv', hc'⟩

include transform action hkernel hdimension hpoint haction hallowed htransport hleaf hterminal in
theorem step_sound (i : Fin n) (rule : Rule n l w t)
    (accepted : nodeCheck roots states obstructions terminals columns guard i rule = true)
    (possible : feasible allowed kernel (states i)) :
    ∃ j : Fin n, j.val < i.val ∧ feasible allowed kernel (states j) := by
  obtain ⟨v, hv, hcore⟩ := possible
  cases rule with
  | terminal reference word coefficients =>
      obtain ⟨hg, hs⟩ := Bool.and_eq_true_iff.mp accepted
      apply False.elim
      apply hterminal reference
      exact transformed_core columns guard allowed kernel transform action haction hallowed htransport
        (states i).root (terminals reference).root (some word) (states i).core.get
        (terminals reference).core.get (fun j => coefficients[j.val]?.getD 0) hg hs v hv hcore
  | branch data =>
      obtain ⟨hfirst, hchildren⟩ := Bool.and_eq_true_iff.mp accepted
      obtain ⟨hsecond, hnumeric⟩ := Bool.and_eq_true_iff.mp hfirst
      obtain ⟨hin, hdual⟩ := Bool.and_eq_true_iff.mp hsecond
      rw [listCheckSpan_eq] at hin
      rw [PureDual.listCheckCombinedDual_eq] at hdual
      have hcombined := listCheckCombinedDual_sound 12 (states i).core data.fresh data.dual hdual
      have hambient : finrank Field
          (familySpan (decoded (n := 12) (roots (states i).root).radical.get)) <
          data.fresh.length + (roots (states i).root).required := by
        have hupper := finrank_range_le_card (R := Field)
          (decoded (n := 12) (roots (states i).root).radical.get)
        have hn := of_decide_eq_true hnumeric
        change finrank Field _ ≤ _ at hupper
        simp only [Fintype.card_fin] at hupper
        exact lt_of_le_of_lt hupper hn
      obtain ⟨b, hb, _, _, hnext⟩ := exists_kernel_branch
        (decoded (n := 12) data.fresh.get)
        (familySpan (decoded (n := 12) (roots (states i).root).radical.get))
        (kernel v) (familySpan (decoded (n := 12) (states i).core.get))
        (listCheckSpan_sound 12 _ _ _ hin) (hkernel _ _ hv) hcore
        hcombined.1 hcombined.2 (hdimension _ _ hv) hambient
      obtain ⟨mask, hbound, hdecode⟩ := exists_bounded_mask b
      have hpositive : 0 < mask := by
        by_contra hzero
        have hz : mask = 0 := by omega
        have hbzero : b = 0 := by simpa only [hz, decodeMask_zero] using hdecode.symm
        exact (mem_branches b).mp hb hbzero
      let j : Fin (2 ^ data.fresh.length - 1) := ⟨mask - 1, by omega⟩
      have hj : j.val + 1 = mask := by dsimp [j]; omega
      have hsup := CoveringFiniteDAG.append_span_single_le (states i).core.get
        (CoveringAffine.composeRow (j.val + 1) data.fresh.get)
      rw [hj, CoveringPackedAction.decodeMask_composeRow_familyLinear, hdecode] at hsup
      apply edge_sound states obstructions columns guard allowed kernel transform action
        hpoint haction hallowed htransport hleaf i _ (data.children j)
        ((List.all_eq_true.mp hchildren) j (List.mem_finRange _)) v hv
      rw [PureDual.appendColumns_eq, composeRow_eq, hj]
      exact hsup.trans hnext

include transform action hkernel hdimension hpoint haction hallowed htransport hleaf hterminal in
theorem check_sound (rules : Fin n → Rule n l w t)
    (accepted : ∀ i, nodeCheck roots states obstructions terminals columns guard i (rules i) = true) :
    ∀ i, ¬ feasible allowed kernel (states i) := by
  intro i
  induction hi : i.val using Nat.strong_induction_on generalizing i with
  | h k ih =>
      intro possible
      obtain ⟨j, hj, hpossible⟩ := step_sound roots states obstructions terminals columns guard
        allowed kernel transform action hkernel hdimension hpoint haction hallowed htransport
        hleaf hterminal i (rules i) (accepted i) possible
      exact ih j.val (hi ▸ hj) j rfl hpossible

end Soundness

end Lemmata.CocubicCovering.Certificate.CoreCertificate
