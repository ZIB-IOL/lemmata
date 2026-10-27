module

public import Lemmata.CocubicCovering.Proof.PackedAction
public meta import Lemmata.CocubicCovering.Proof.PackedAction
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringPackedWitness

open Module CoveringAffine CoveringBits CoveringWitness CoveringPackedAction

def decoded {n k : ℕ} (columns : Fin k → ℕ) : Fin k → Vector n :=
  fun i => decodeMask (columns i)

def checkSpan {c d : ℕ} (source : Fin c → ℕ) (target : Fin d → ℕ)
    (coefficients : Fin c → ℕ) : Bool :=
  (List.finRange c).all fun i => decide (composeRow (coefficients i) target = source i)

theorem checkSpan_sound {n c d : ℕ} (source : Fin c → ℕ) (target : Fin d → ℕ)
    (coefficients : Fin c → ℕ) (accepted : checkSpan source target coefficients = true) :
    familySpan (decoded (n := n) source) ≤ familySpan (decoded (n := n) target) := by
  apply familySpan_le_of_coefficients _ _ (fun i => decodeMask (coefficients i))
  intro i
  have h : composeRow (coefficients i) target = source i :=
    of_decide_eq_true ((List.all_eq_true.mp accepted) i (List.mem_finRange _))
  change (familyLinear (fun j : Fin d => (decodeMask (target j) : Vector n)))
    (decodeMask (coefficients i)) = decodeMask (source i)
  have he := decodeMask_composeRow_familyLinear (n := n) (coefficients i) target
  rw [h] at he
  exact he.symm

def checkDual (n : ℕ) {k : ℕ} (columns rows : Fin k → ℕ) : Bool :=
  decide (∀ i : Fin k, rowMap rows (decoded (n := n) columns i) = Pi.single i 1)

theorem checkDual_sound (n : ℕ) {k : ℕ} (columns rows : Fin k → ℕ)
    (accepted : checkDual n columns rows = true) :
    Function.Injective (familyLinear (decoded (n := n) columns)) ∧
      finrank Field (familySpan (decoded (n := n) columns)) = k := by
  exact packed_dual_witness _ rows (of_decide_eq_true accepted)

def appendColumns {c d : ℕ} (core : Fin c → ℕ) (fresh : Fin d → ℕ) :
    Fin (c + d) → ℕ :=
  fun i => Sum.elim core fresh (finSumFinEquiv.symm i)

theorem decoded_append_sum {n c d : ℕ} (core : Fin c → ℕ) (fresh : Fin d → ℕ) :
    decoded (n := n) (appendColumns core fresh) ∘ finSumFinEquiv =
      Sum.elim (decoded (n := n) core) (decoded (n := n) fresh) := by
  funext i
  cases i <;> simp [decoded, appendColumns]

theorem checkCombinedDual_sound (n : ℕ) {c d : ℕ} (core : Fin c → ℕ)
    (fresh : Fin d → ℕ) (rows : Fin (c + d) → ℕ)
    (accepted : checkDual n (appendColumns core fresh) rows = true) :
    familySpan (decoded (n := n) fresh) ⊓ familySpan (decoded (n := n) core) = ⊥ ∧
      finrank Field (familySpan (decoded (n := n) fresh)) = d := by
  have hinjective := (checkDual_sound n (appendColumns core fresh) rows accepted).1
  have hindependent := (familyLinear_injective_iff _).mp hinjective
  have hsum := hindependent.comp
    (finSumFinEquiv : Fin c ⊕ Fin d ≃ Fin (c + d)) finSumFinEquiv.injective
  rw [decoded_append_sum] at hsum
  exact combined_family _ _ ((familyLinear_injective_iff _).mpr hsum)

def listColumns (columns : List ℕ) : Fin columns.length → ℕ := columns.get

def listCheckSpan (source target coefficients : List ℕ) : Bool :=
  checkSpan (listColumns source) (listColumns target)
    fun i => coefficients[i.val]?.getD 0

theorem listCheckSpan_sound (n : ℕ) (source target coefficients : List ℕ)
    (accepted : listCheckSpan source target coefficients = true) :
    familySpan (decoded (n := n) (listColumns source)) ≤
      familySpan (decoded (n := n) (listColumns target)) :=
  checkSpan_sound _ _ _ accepted

def listCheckDual (n : ℕ) (columns rows : List ℕ) : Bool :=
  checkDual n (listColumns columns) fun i => rows[i.val]?.getD 0

theorem listCheckDual_sound (n : ℕ) (columns rows : List ℕ)
    (accepted : listCheckDual n columns rows = true) :
    Function.Injective (familyLinear (decoded (n := n) (listColumns columns))) ∧
      finrank Field (familySpan (decoded (n := n) (listColumns columns))) = columns.length :=
  checkDual_sound n _ _ accepted

def listCheckCombinedDual (n : ℕ) (core fresh rows : List ℕ) : Bool :=
  checkDual n (appendColumns (listColumns core) (listColumns fresh))
    fun i => rows[i.val]?.getD 0

theorem listCheckCombinedDual_sound (n : ℕ) (core fresh rows : List ℕ)
    (accepted : listCheckCombinedDual n core fresh rows = true) :
    familySpan (decoded (n := n) (listColumns fresh)) ⊓
        familySpan (decoded (n := n) (listColumns core)) = ⊥ ∧
      finrank Field (familySpan (decoded (n := n) (listColumns fresh))) = fresh.length :=
  checkCombinedDual_sound n _ _ _ accepted

end Lemmata.CocubicCovering.CoveringPackedWitness
