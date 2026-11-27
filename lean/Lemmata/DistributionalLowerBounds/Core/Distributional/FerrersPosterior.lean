module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.Scaling
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic

@[expose] public section

/-!
# Nested (Ferrers) permutation posteriors

This module formalizes the product count for the nested posterior family in
`lem:count`.  Indices are zero-based: `lower i = ℓᵢ-1`, so feasibility is
`lower i ≤ i.val` and `choices i = i.val+1-lower i`.
-/

open Equiv Set

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

/-! ## Order-preserving deletion of the last row -/

/-- Insert a last row with image `p`, relabeling all other columns in their
original order around the hole `p`. -/
noncomputable def extendLast {n : ℕ} (p : Fin (n + 1))
    (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective (fun i => Fin.lastCases p (fun j => p.succAbove (e j)) i) (by
    constructor
    · intro a
      refine Fin.lastCases ?_ (fun i => ?_) a
      · intro b
        refine Fin.lastCases (fun _ => rfl) (fun j h => ?_) b
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at h ⊢
        exact (p.succAbove_ne (e j) h.symm).elim
      · intro b
        refine Fin.lastCases (fun h => ?_) (fun j h => ?_) b
        · simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at h ⊢
          exact (p.succAbove_ne (e i) h).elim
        · simp only [Fin.lastCases_castSucc] at h ⊢
          exact congrArg Fin.castSucc (e.injective (p.succAbove_right_injective h))
    · intro q
      refine Fin.succAboveCases p ⟨Fin.last n, by simp⟩ (fun k => ?_) q
      refine ⟨(e.symm k).castSucc, ?_⟩
      simp)

@[simp] lemma extendLast_last {n : ℕ} (p : Fin (n + 1))
    (e : Equiv.Perm (Fin n)) : extendLast p e (Fin.last n) = p := by
  simp [extendLast]

@[simp] lemma extendLast_castSucc {n : ℕ} (p : Fin (n + 1))
    (e : Equiv.Perm (Fin n)) (i : Fin n) :
    extendLast p e i.castSucc = p.succAbove (e i) := by
  simp [extendLast]

/-- Product decomposition of permutations, using order-preserving deletion of
the image of the last row. -/
noncomputable def lastExtendEquiv {n : ℕ} :
    (Fin (n + 1) × Equiv.Perm (Fin n)) ≃ Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective (fun pe => extendLast pe.1 pe.2) (by
    apply (Fintype.bijective_iff_injective_and_card _).2
    constructor
    · rintro ⟨p, e⟩ ⟨q, f⟩ h
      have hpq : p = q := by
        have := DFunLike.congr_fun h (Fin.last n)
        simpa using this
      subst q
      have hef : e = f := by
        ext i
        have := DFunLike.congr_fun h i.castSucc
        simp only [extendLast_castSucc] at this
        exact congrArg Fin.val (p.succAbove_right_injective this)
      simp [hef]
    · simp [Fintype.card_perm, Nat.factorial_succ])

noncomputable def lastDecompose {n : ℕ} :
    Equiv.Perm (Fin (n + 1)) ≃ Fin (n + 1) × Equiv.Perm (Fin n) :=
  lastExtendEquiv.symm

@[simp] lemma lastDecompose_symm_apply {n : ℕ} (p : Fin (n + 1))
    (e : Equiv.Perm (Fin n)) :
    lastDecompose.symm (p, e) = extendLast p e := rfl

lemma val_le_succAbove {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    i.val ≤ (p.succAbove i).val := by
  rw [Fin.succAbove]
  split <;> simp

lemma le_val_of_le_hole_of_le_succAbove {n k : ℕ}
    (p : Fin (n + 1)) (i : Fin n)
    (hkp : k ≤ p.val) (hkq : k ≤ (p.succAbove i).val) : k ≤ i.val := by
  by_contra hki
  have hik : i.val < k := Nat.lt_of_not_ge hki
  have hip : i.castSucc < p := by exact_mod_cast lt_of_lt_of_le hik hkp
  rw [Fin.succAbove_of_castSucc_lt p i hip] at hkq
  exact (Nat.not_lt_of_ge hkq) hik

/-! ## Ferrers data and compatible permutations -/

structure FerrersData (m : ℕ) where
  lower : Fin m → ℕ
  monotone_lower : Monotone lower
  feasible : ∀ i, lower i ≤ i.val

namespace FerrersData

/-- Hall feasibility for sorted suffix constraints.  A compatible permutation
forces `lower i ≤ i`. -/
theorem feasible_of_compatible {m : ℕ} (lower : Fin m → ℕ)
    (hmono : Monotone lower)
    (sigma : Equiv.Perm (Fin m))
    (hcompat : ∀ i, lower i ≤ (sigma i).val) :
    ∀ i, lower i ≤ i.val := by
  intro i
  by_contra hnot
  have hil : i.val < lower i := Nat.lt_of_not_ge hnot
  have hlm : lower i < m := lt_of_le_of_lt (hcompat i) (sigma i).isLt
  let a : Fin m := ⟨lower i, hlm⟩
  let f : Set.Ici i → Set.Ici a := fun j => ⟨sigma j.1, by
    change a ≤ sigma j.1
    exact_mod_cast (hmono j.2).trans (hcompat j.1)⟩
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact sigma.injective (congrArg Subtype.val hxy)
  have hcard := Fintype.card_le_of_injective f hfinj
  simp [a] at hcard
  omega

/-- Build valid Ferrers data from a sorted lower-bound vector and one compatible
permutation. -/
def ofCompatible {m : ℕ} (lower : Fin m → ℕ)
    (hmono : Monotone lower)
    (sigma : Equiv.Perm (Fin m))
    (hcompat : ∀ i, lower i ≤ (sigma i).val) : FerrersData m where
  lower := lower
  monotone_lower := hmono
  feasible := feasible_of_compatible lower hmono sigma hcompat

/-- Relabel arbitrary rows by increasing lower bound, obtaining Ferrers data. -/
noncomputable def sortedOfCompatible {m : ℕ} (lower : Fin m → ℕ)
    (sigma : Equiv.Perm (Fin m))
    (hcompat : ∀ i, lower i ≤ (sigma i).val) : FerrersData m := by
  let rowSort := Tuple.sort lower
  let sortedLower : Fin m → ℕ := lower ∘ rowSort
  let sortedSigma : Equiv.Perm (Fin m) := rowSort.trans sigma
  exact ofCompatible sortedLower (Tuple.monotone_sort lower) sortedSigma
    (fun i => hcompat (rowSort i))

@[simp] lemma sortedOfCompatible_lower {m : ℕ} (lower : Fin m → ℕ)
    (sigma : Equiv.Perm (Fin m))
    (hcompat : ∀ i, lower i ≤ (sigma i).val) (i : Fin m) :
    (sortedOfCompatible lower sigma hcompat).lower i =
      lower (Tuple.sort lower i) := rfl

/-- Number of choices available when row `i` is assigned in reverse order. -/
def choices {m : ℕ} (D : FerrersData m) (i : Fin m) : ℕ :=
  i.val + 1 - D.lower i

lemma choices_pos {m : ℕ} (D : FerrersData m) (i : Fin m) :
    0 < D.choices i := by
  unfold choices
  exact Nat.sub_pos_of_lt (lt_of_le_of_lt (D.feasible i) (Nat.lt_succ_self _))

/-- Delete the last row. -/
def dropLast {n : ℕ} (D : FerrersData (n + 1)) : FerrersData n where
  lower i := D.lower i.castSucc
  monotone_lower := fun _ _ h => D.monotone_lower (by exact_mod_cast h)
  feasible i := D.feasible i.castSucc

/-- Lower threshold of the last row as an element of `Fin (n+1)`. -/
def lastThreshold {n : ℕ} (D : FerrersData (n + 1)) : Fin (n + 1) :=
  ⟨D.lower (Fin.last n), lt_of_le_of_lt (D.feasible _) (Nat.lt_succ_self n)⟩

/-- Columns allowed for the last row. -/
abbrev AllowedLast {n : ℕ} (D : FerrersData (n + 1)) :=
  Set.Ici D.lastThreshold

lemma card_allowedLast {n : ℕ} (D : FerrersData (n + 1)) :
    Fintype.card D.AllowedLast = D.choices (Fin.last n) := by
  change Fintype.card (Set.Ici D.lastThreshold) = D.choices (Fin.last n)
  rw [Fintype.card_Ici, Fin.card_Ici]
  rfl

/-- Translate the allowed suffix of last-row columns to a zero-based interval. -/
noncomputable def allowedLastEquivFin {n : ℕ} (D : FerrersData (n + 1)) :
    D.AllowedLast ≃ Fin (D.choices (Fin.last n)) where
  toFun p := ⟨p.1.val - D.lower (Fin.last n), by
    have hp : D.lower (Fin.last n) ≤ p.1.val := by exact_mod_cast p.2
    unfold choices
    simp only [Fin.val_last]
    omega⟩
  invFun q := ⟨⟨D.lower (Fin.last n) + q.val, by
    have hq := q.isLt
    unfold choices at hq
    omega⟩, by
      change D.lastThreshold ≤ _
      exact_mod_cast Nat.le_add_right _ _⟩
  left_inv p := by
    apply Subtype.ext
    apply Fin.ext
    have hp : D.lower (Fin.last n) ≤ p.1.val := by exact_mod_cast p.2
    simp
    omega
  right_inv q := by
    apply Fin.ext
    simp

@[simp] lemma allowedLastEquivFin_symm_val {n : ℕ} (D : FerrersData (n + 1))
    (q : Fin (D.choices (Fin.last n))) :
    ((D.allowedLastEquivFin.symm q : D.AllowedLast) : Fin (n + 1)).val =
      D.lower (Fin.last n) + q.val := rfl

end FerrersData

/-- A compatible reduced permutation. -/
def FerrersPerm {m : ℕ} (D : FerrersData m) :=
  {sigma : Equiv.Perm (Fin m) // ∀ i, D.lower i ≤ (sigma i).val}

noncomputable instance {m : ℕ} (D : FerrersData m) : Fintype (FerrersPerm D) := by
  classical
  apply Fintype.ofFinset
    ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
      (fun sigma => ∀ i, D.lower i ≤ (sigma i).val))
  intro sigma
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (∀ i, D.lower i ≤ (sigma i).val) ↔ ∀ i, D.lower i ≤ (sigma i).val
  rfl

namespace FerrersPerm

/-- Extending a compatible dropLast by an allowed last-column choice remains
compatible. -/
lemma extend_mem {n : ℕ} (D : FerrersData (n + 1))
    (p : D.AllowedLast) (e : FerrersPerm D.dropLast) :
    ∀ i, D.lower i ≤ (extendLast p.1 e.1 i).val := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hp := p.2
    change D.lastThreshold ≤ p.1 at hp
    have hpnat : D.lower (Fin.last n) ≤ p.1.val := by exact_mod_cast hp
    simpa only [extendLast_last] using hpnat
  · have hdropLast := e.2 j
    have hs := val_le_succAbove p.1 (e.1 j)
    simpa only [extendLast_castSucc, FerrersData.dropLast] using hdropLast.trans hs

/-- Conversely, compatibility of an extension implies compatibility of both
components. -/
lemma components_mem {n : ℕ} (D : FerrersData (n + 1))
    (p : Fin (n + 1)) (e : Equiv.Perm (Fin n))
    (h : ∀ i, D.lower i ≤ (extendLast p e i).val) :
    p ∈ D.AllowedLast ∧ (∀ i, D.dropLast.lower i ≤ (e i).val) := by
  constructor
  · have hl := h (Fin.last n)
    simpa [FerrersData.AllowedLast, FerrersData.lastThreshold, Fin.le_def] using hl
  · intro i
    have hlast := h (Fin.last n)
    have hhole : D.lower i.castSucc ≤ p.val := by
      exact (D.monotone_lower (Fin.le_last i.castSucc)).trans (by simpa using hlast)
    have hrow := h i.castSucc
    exact le_val_of_le_hole_of_le_succAbove p (e i) hhole
      (by simpa [FerrersData.dropLast] using hrow)

/-- Recursive equivalence underlying the product formula. -/
noncomputable def decompose {n : ℕ} (D : FerrersData (n + 1)) :
    D.AllowedLast × FerrersPerm D.dropLast ≃ FerrersPerm D :=
  Equiv.ofBijective
    (fun pe => ⟨extendLast pe.1.1 pe.2.1, extend_mem D pe.1 pe.2⟩) (by
      constructor
      · rintro ⟨p, e⟩ ⟨q, f⟩ h
        apply Prod.ext
        · apply Subtype.ext
          have hu : extendLast p.1 e.1 = extendLast q.1 f.1 :=
            congrArg Subtype.val h
          change lastExtendEquiv (p.1, e.1) = lastExtendEquiv (q.1, f.1) at hu
          exact congrArg Prod.fst (lastExtendEquiv.injective hu)
        · apply Subtype.ext
          have hu : extendLast p.1 e.1 = extendLast q.1 f.1 :=
            congrArg Subtype.val h
          change lastExtendEquiv (p.1, e.1) = lastExtendEquiv (q.1, f.1) at hu
          exact congrArg Prod.snd (lastExtendEquiv.injective hu)
      · intro sigma
        let pe := lastDecompose sigma.1
        have hext : extendLast pe.1 pe.2 = sigma.1 := by
          exact lastDecompose.symm_apply_apply sigma.1
        have hc : pe.1 ∈ D.AllowedLast ∧
            ∀ i, D.dropLast.lower i ≤ (pe.2 i).val := by
          apply components_mem D pe.1 pe.2
          intro i
          rw [hext]
          exact sigma.2 i
        refine ⟨⟨⟨pe.1, hc.1⟩, ⟨pe.2, hc.2⟩⟩, ?_⟩
        apply Subtype.ext
        exact hext)

@[simp] lemma decompose_apply_val {n : ℕ} (D : FerrersData (n + 1))
    (pe : D.AllowedLast × FerrersPerm D.dropLast) :
    (decompose D pe).1 = extendLast pe.1.1 pe.2.1 := rfl

/-- Product formula for nested compatible permutations. -/
theorem card_eq_prod_choices : ∀ {m : ℕ} (D : FerrersData m),
    Fintype.card (FerrersPerm D) = ∏ i, D.choices i
  | 0, D => by simp [FerrersPerm]
  | n + 1, D => by
      rw [← Fintype.card_congr (decompose D), Fintype.card_prod,
        FerrersData.card_allowedLast, card_eq_prod_choices D.dropLast,
        Fin.prod_univ_castSucc]
      simp [FerrersData.choices, FerrersData.dropLast, mul_comm]

noncomputable instance nonempty {m : ℕ} (D : FerrersData m) :
    Nonempty (FerrersPerm D) :=
  Fintype.card_pos_iff.mp (by
    rw [card_eq_prod_choices]
    exact Finset.prod_pos (fun i _ => D.choices_pos i))

end FerrersPerm
end Lemmata.DistributionalLowerBounds.Core.Distributional
