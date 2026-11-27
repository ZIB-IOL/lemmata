module

public import Lemmata.FrankWolfePS.Lower.Results

@[expose] public section

/-!
# Deterministic methods in dimension `64 (T + 1) + 1`

Against a deterministic method an adversary suffices. It answers every nonzero query by the
first label of the scan order and declares that label present. After at most `T` calls at most
`k = T + 1` labels are declared (with the anchor), and every hidden set containing them gives the
same run. Completing the declared labels uniformly by labels among the remaining `N - b ≥ 63 k`,
the posterior membership vector has squared norm at most `(1 + 64/63) k < 9k/4`, so some
completion is light and the output fails on it. For randomized methods this does not suffice:
the completion would depend on the tape.
-/

namespace Lemmata.FrankWolfePS
open Finset

section Replay
variable {ι O : Type*} [DecidableEq ι]

/-- The labels declared present by the adversary, which answers every scan with its first
label. -/
def Orders.declared {t} : Orders ι O t → Finset ι → Finset ι
  | .ret _, P => P
  | .ask [] next, P => (next none).declared P
  | .ask (j :: _) next, P => (next (some j)).declared (insert j P)

/-- The output of the run that the adversary answers. -/
def Orders.replayOut {t} : Orders ι O t → O
  | .ret x => x
  | .ask [] next => (next none).replayOut
  | .ask (j :: _) next => (next (some j)).replayOut

theorem Orders.subset_declared {t} (s : Orders ι O t) (P : Finset ι) : P ⊆ s.declared P := by
  induction s generalizing P with
  | ret x => exact subset_refl _
  | ask l next ih =>
    cases l with
    | nil => exact ih none P
    | cons j l => exact (subset_insert j P).trans (ih (some j) (insert j P))

theorem Orders.card_declared {t} (s : Orders ι O t) (P : Finset ι) :
    (s.declared P).card ≤ P.card + t := by
  induction s generalizing P with
  | ret x => exact Nat.le_add_right _ _
  | ask l next ih =>
    cases l with
    | nil => exact (ih none P).trans (by omega)
    | cons j l =>
      exact (ih (some j) (insert j P)).trans (by have := card_insert_le j P; omega)

/-- Every hidden set containing the declared labels gives the adversary's run. -/
theorem Orders.run_of_declared {t} (s : Orders ι O t) (P I : Finset ι) (sub : s.declared P ⊆ I) :
    s.run I = s.replayOut := by
  induction s generalizing P with
  | ret x => rfl
  | ask l next ih =>
    cases l with
    | nil => exact ih none P sub
    | cons j l =>
      have hj : j ∈ I := sub ((Orders.subset_declared (next (some j)) (insert j P))
        (mem_insert_self j P))
      simp only [Orders.run, first, hj, ite_true]
      exact ih (some j) (insert j P) sub

end Replay

section Fixed
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Deterministic runs, normalized.** In dimension `64 (T + 1) + 1`, every run requiring no
more than `T` calls fails on some hidden set containing the anchor. -/
theorem deterministic_orders (T : ℕ) (anchor : ι) (hN : Fintype.card ι = 64 * (T + 1))
    {R : ℝ} (hR : 0 < R) (s : Orders ι (Pt ι) T) :
    ∃ I : Finset ι, I.card = 8 * (T + 1) ∧ anchor ∈ I ∧ failure R (T + 1) I (s.run I) := by
  classical
  set k := T + 1 with hk_def
  have hk : 0 < k := Nat.succ_pos T
  set P := s.declared {anchor} with hP_def
  have hPa : anchor ∈ P := s.subset_declared {anchor} (mem_singleton_self _)
  have hPc : P.card ≤ k := (s.card_declared {anchor}).trans (by simp [k]; omega)
  set U := (univ : Finset ι) \ P with hU_def
  have hU : U.card = 64 * k - P.card := by
    rw [hU_def, card_sdiff_of_subset (subset_univ _), card_univ, hN]
  have hPU : Disjoint P U := disjoint_sdiff
  set h := 8 * k - P.card with hh_def
  have small : 4 * ((P.card : ℝ) * U.card + (h : ℝ) ^ 2) ≤ 9 * k * U.card := by
    have b1 : (P.card : ℝ) ≤ k := by exact_mod_cast hPc
    have b2 : (h : ℝ) ≤ 8 * k := by exact_mod_cast (by omega : h ≤ 8 * k)
    have b3 : 63 * (k : ℝ) ≤ U.card := by exact_mod_cast (by omega : 63 * k ≤ U.card)
    have h0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    have k0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  obtain ⟨S, hS, light⟩ :=
    leaf_average hk s.replayOut P U hPU (by omega) (by omega) small
  obtain ⟨hSU, hSc⟩ := mem_powersetCard.mp hS
  have hc : (P ∪ S).card = 8 * k := by
    rw [card_union_of_disjoint (hPU.mono_right hSU), hSc]; omega
  refine ⟨P ∪ S, hc, mem_union_left _ hPa, ?_⟩
  rw [s.run_of_declared {anchor} (P ∪ S) subset_union_left]
  exact small_mass_failure hR hk hc light

end Fixed

section Physical
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **Deterministic methods on the hard family.** In dimension `64 (T + 1) + 1`, every
deterministic method requiring no more than `T` calls to the vertex oracle fails on some
instance: its output is infeasible or has gap at least `L a² / (16 (T + 1))`. -/
theorem deterministic_lower_bound (T : ℕ) (anchor : ι) (hN : Fintype.card ι = 64 * (T + 1))
    {L a r : ℝ} (hL : 0 < L) (ha : 0 < a) (hr : 0 < r) (s : Method (Ambient ι) T) :
    ∃ I : Finset ι, I.card = 8 * (T + 1) ∧ anchor ∈ I ∧
      physicalFailure L a r (T + 1) I (s.physicalRun a r anchor I) := by
  obtain ⟨I, hc, hI, f⟩ := deterministic_orders T anchor hN (div_pos hr ha)
    ((s.simulate a).orders (r / a) anchor)
  refine ⟨I, hc, hI, ?_⟩
  rw [Method.orders_run, Method.simulate_run] at f
  exact (failure_scale hL ha hr _ ⟨anchor, hI⟩ _).mpr f

/-- **Deterministic methods at prescribed parameters.** -/
theorem deterministic_prescribed (T : ℕ) (anchor : ι) (hN : Fintype.card ι = 64 * (T + 1))
    {L β D : ℝ} (hL : 0 < L) (hβ : 0 < β) (hD : 2 < β * D) (s : Method (Ambient ι) T) :
    let r := 1 / β
    let a := (D - 2 / β) / Real.sqrt 2
    ∃ I : Finset ι, I.card = 8 * (T + 1) ∧ anchor ∈ I ∧ Metric.diam (physicalBody a r I) = D ∧
      (embed (s.physicalRun a r anchor I) ∉ physicalBody a r I ∨
        L * (D - 2 / β) ^ 2 / (32 * ((T + 1 : ℕ) : ℝ)) ≤
          L * obj r (s.physicalRun a r anchor I) - physicalOpt L a r I) := by
  dsimp only
  let r := 1 / β
  let a := (D - 2 / β) / Real.sqrt 2
  obtain ⟨hr, ha, -, hdiam, hcut, -⟩ := prescribed_parameters (L := L) hβ hD (T + 1)
  change 0 < r at hr
  change 0 < a at ha
  change 2 * r + Real.sqrt 2 * a = D at hdiam
  change L * a ^ 2 / (16 * ((T + 1 : ℕ) : ℝ)) = _ at hcut
  obtain ⟨I, hc, hI, f⟩ := deterministic_lower_bound T anchor hN hL ha hr s
  refine ⟨I, hc, hI, (physical_parameters ha hr I (by omega)).1.trans hdiam, ?_⟩
  simpa only [physicalFailure, hcut] using f

end Physical

end Lemmata.FrankWolfePS
