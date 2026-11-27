module

public import Lemmata.EnergyShellCrossings.Statement

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lemmata.EnergyShellCrossings.EnergyShell

open Lemmata.FockCircuits
open FiniteIdentity CrossingCircuit Families

noncomputable section

variable {R : Type*} [CommRing R]

/-- Different mode labels have different energy shifts. -/
theorem shift_injective (W : ℕ) : Function.Injective (shift W) := by
  intro r t h
  apply Fin.ext
  dsimp [shift] at h
  omega

/-- Orthogonal mode supports allow the mode sum to be absorbed into both factors. -/
theorem collapse_modes {M : Type*} [Fintype M] [DecidableEq M]
    (f g : M → R) (hzero : ∀ r t, r ≠ t → f r * g t = 0) :
    (∑ r, f r) * (∑ r, g r) = ∑ r, f r * g r := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]
  apply Finset.sum_eq_single r
  · intro t ht htr
    exact hzero r t htr.symm
  · simp

variable {I J ρ : Type*} [Fintype I] [Fintype J] [Fintype ρ]

/-- Sum the mode coordinate, retaining only the occupation-state coordinate. -/
def sumModes {W : ℕ} (a : Fin W × ρ → I → J → R) : ρ → I → J → R :=
  fun s i j => ∑ r, a (r, s) i j

omit [Fintype I] [Fintype J] [Fintype ρ] in
theorem first_cut_off_diagonal {L W V : ℕ}
    (a b : I → State R L) (action : J → Index L) (middle : ρ ↪ Index L)
    (hlevel : ∀ j, doubledEnergy (action j).val = V)
    (s : ρ) (i k : I) (j l : J) (r t : Fin W) (hrt : r ≠ t) :
    coefficientA R a action middle (r, s) i j *
      coefficientB R b action middle (t, s) k l = 0 := by
  by_cases hA : (doubledEnergy (middle s).val : ℤ) - doubledEnergy (action j).val = shift W r
  · by_cases hB : (doubledEnergy (action l).val : ℤ) - doubledEnergy (middle s).val = -shift W t
    · rw [hlevel j] at hA
      rw [hlevel l] at hB
      exact (hrt (shift_injective W (by omega))).elim
    · simp [coefficientB, oppositeMode, diagonal, hB]
  · simp [coefficientA, markedMode, diagonal, hA]

omit [Fintype I] [Fintype J] [Fintype ρ] in
theorem second_cut_off_diagonal {L W V : ℕ}
    (a b : I → State R L) (action : J → Index L) (middle : ρ ↪ Index L)
    (hlevel : ∀ j, doubledEnergy (action j).val = V)
    (s : ρ) (i k : I) (j l : J) (r t : Fin W) (hrt : r ≠ t) :
    coefficientC R a action middle (r, s) i l *
      coefficientD R b action middle (t, s) k j = 0 := by
  by_cases hC : (doubledEnergy (action l).val : ℤ) - doubledEnergy (middle s).val = shift W r
  · by_cases hD : (doubledEnergy (middle s).val : ℤ) - doubledEnergy (action j).val = -shift W t
    · rw [hlevel l] at hC
      rw [hlevel j] at hD
      exact (hrt (shift_injective W (by omega))).elim
    · simp [coefficientD, oppositeMode, diagonal, hD]
  · simp [coefficientC, markedMode, diagonal, hC]

/-- A homogeneous action space makes the intermediate energy determine the mode.
The two cuts therefore need only an occupation-state index. -/
theorem collapsed_family_identity [DecidableEq I] [DecidableEq J] {L E W V : ℕ}
    (B : I ↪ Index L) (action : J ↪ Index L) (middle : ρ ↪ Index L)
    (hW : 0 < W) (hBW : ∀ i, doubledEnergy (B i).val = W)
    (hlevel : ∀ j, doubledEnergy (action j).val = V) (hVE : V ≤ 2 * E)
    (hcover : ∀ s : Index L, doubledEnergy s.val ≤ 2 * L → s ∈ Set.range middle)
    (hcut : 2 * E + W ≤ 2 * L) (i k : I) (j l : J) :
    (∑ s, sumModes (coefficientA R (dualFamily R B) action middle (W := W)) s i j *
      sumModes (coefficientB R (bareFamily R B) action middle (W := W)) s k l) -
      (sigma W : R) *
        (∑ s, sumModes (coefficientC R (dualFamily R B) action middle (W := W)) s i l *
          sumModes (coefficientD R (bareFamily R B) action middle (W := W)) s k j) =
      if i = k then (if j = l then 1 else 0) else 0 := by
  have hfirst :
      (∑ s, sumModes (coefficientA R (dualFamily R B) action middle (W := W)) s i j *
        sumModes (coefficientB R (bareFamily R B) action middle (W := W)) s k l) =
      ∑ z : Fin W × ρ,
        coefficientA R (dualFamily R B) action middle z i j *
          coefficientB R (bareFamily R B) action middle z k l := by
    simp only [sumModes, Fintype.sum_prod_type]
    calc
      _ = ∑ s : ρ, ∑ r : Fin W,
          coefficientA R (dualFamily R B) action middle (r, s) i j *
            coefficientB R (bareFamily R B) action middle (r, s) k l := by
        apply Finset.sum_congr rfl
        intro s hs
        apply collapse_modes
        exact first_cut_off_diagonal (dualFamily R B) (bareFamily R B)
          action middle hlevel s i k j l
      _ = _ := Finset.sum_comm
  have hsecond :
      (∑ s, sumModes (coefficientC R (dualFamily R B) action middle (W := W)) s i l *
        sumModes (coefficientD R (bareFamily R B) action middle (W := W)) s k j) =
      ∑ z : Fin W × ρ,
        coefficientC R (dualFamily R B) action middle z i l *
          coefficientD R (bareFamily R B) action middle z k j := by
    simp only [sumModes, Fintype.sum_prod_type]
    calc
      _ = ∑ s : ρ, ∑ r : Fin W,
          coefficientC R (dualFamily R B) action middle (r, s) i l *
            coefficientD R (bareFamily R B) action middle (r, s) k j := by
        apply Finset.sum_congr rfl
        intro s hs
        apply collapse_modes
        exact second_cut_off_diagonal (dualFamily R B) (bareFamily R B)
          action middle hlevel s i k j l
      _ = _ := Finset.sum_comm
  rw [hfirst, hsecond]
  exact family_coefficient_identity R B action middle hW hBW
    (fun j => by rw [hlevel j]; exact hVE) hcover hcut i k j l

/-- Number a complete energy level inside a finite Fock space. -/
def sliceEmbedding (k L : ℕ) (hk : k ≤ 2 * L) : Fin (partitionDimension k) ↪ Index L :=
  let e : Fin (partitionDimension k) ≃ ↥(partitionSlice k) :=
    (Finset.equivFin (partitionSlice k)).symm
  let f : ↥(partitionSlice k) ↪ ↥(fullCutoff L) :=
    ⟨fun s => ⟨s.val, mem_fullCutoff.mpr ((mem_partitionSlice.mp s.property).le.trans hk)⟩,
      fun _ _ h => Subtype.ext (congrArg (fun z : ↥(fullCutoff L) => z.val) h)⟩
  e.toEmbedding.trans (f.trans (cutoffEmbedding le_rfl))

theorem sliceEmbedding_energy (k L : ℕ) (hk : k ≤ 2 * L)
    (i : Fin (partitionDimension k)) :
    doubledEnergy (sliceEmbedding k L hk i).val = k := by
  exact mem_partitionSlice.mp (((Finset.equivFin (partitionSlice k)).symm i).property)

/-- Two exact energy levels give an integral crossing with at most Q(H+E)
coordinates on each cut, with no multiplicative mode factor. -/
theorem integral_shell_crossing (H E n m : ℕ) (hH : 0 < H)
    (hn : n ≤ partitionDimension (2 * H)) (hm : m ≤ partitionDimension (2 * E)) :
    ∃ a b c d : Fin (stateCount (H + E)) → Fin n → Fin m → ℤ,
      ∀ (i k : Fin n) (j l : Fin m),
        (∑ s, a s i j * b s k l) + (∑ s, c s i l * d s k j) =
          if i = k then (if j = l then 1 else 0) else 0 := by
  classical
  let B : Fin n ↪ Index (H + E) :=
    (Fin.castLEEmb hn).trans (sliceEmbedding (2 * H) (H + E) (by omega))
  let action : Fin m ↪ Index (H + E) :=
    (Fin.castLEEmb hm).trans (sliceEmbedding (2 * E) (H + E) (by omega))
  have hB (i : Fin n) : doubledEnergy (B i).val = 2 * H :=
    sliceEmbedding_energy (2 * H) (H + E) (by omega) (Fin.castLEEmb hn i)
  have haction (j : Fin m) : doubledEnergy (action j).val = 2 * E :=
    sliceEmbedding_energy (2 * E) (H + E) (by omega) (Fin.castLEEmb hm j)
  let middle := cutoffEmbedding (E := H + E) (L := H + E) le_rfl
  let a := sumModes (coefficientA ℤ (dualFamily ℤ B) action middle (W := 2 * H))
  let b := sumModes (coefficientB ℤ (bareFamily ℤ B) action middle (W := 2 * H))
  let c := sumModes (coefficientC ℤ (dualFamily ℤ B) action middle (W := 2 * H))
  let d := sumModes (coefficientD ℤ (bareFamily ℤ B) action middle (W := 2 * H))
  have hcoeff (i k : Fin n) (j l : Fin m) :
      (∑ s, a s i j * b s k l) +
        (∑ s, (-(sigma (2 * H)) * c s i l) * d s k j) =
          if i = k then (if j = l then 1 else 0) else 0 := by
    have h := collapsed_family_identity (R := ℤ) (E := E) (W := 2 * H) (V := 2 * E)
      B action middle (by omega) hB haction le_rfl
      (cutoffEmbedding_covers (H + E)) (by omega) i k j l
    change (∑ s, a s i j * b s k l) - (sigma (2 * H) : ℤ) *
      (∑ s, c s i l * d s k j) = _ at h
    simpa only [mul_assoc, ← Finset.mul_sum, neg_mul, sub_eq_add_neg,
      Finset.sum_neg_distrib] using h
  let e : Fin (stateCount (H + E)) ≃ ↥(fullCutoff (H + E)) :=
    (Finset.equivFin (fullCutoff (H + E))).symm
  refine ⟨(fun s => a (e s)), (fun s => b (e s)),
    (fun s i j => -(sigma (2 * H)) * c (e s) i j), (fun s => d (e s)), ?_⟩
  intro i k j l
  rw [e.sum_comp (fun s => a s i j * b s k l),
    e.sum_comp (fun s => (-(sigma (2 * H)) * c s i l) * d s k j)]
  exact hcoeff i k j l

/-- A finite rectangular sum-of-squares bound obtained from exact energy levels. -/
theorem shell_sum_of_squares (H E n m : ℕ) (hH : 0 < H)
    (hn : n ≤ partitionDimension (2 * H)) (hm : m ≤ partitionDimension (2 * E)) :
    ∃ (s : ℕ) (forms : Fin s → Fin n → Fin m → ℂ),
      s ≤ 4 * stateCount (H + E) ∧
      ∀ (x : Fin n → ℂ) (y : Fin m → ℂ),
        (∑ r, Hurwitz.bilinear (forms r) x y ^ 2) =
          (∑ i, x i ^ 2) * (∑ j, y j ^ 2) := by
  obtain ⟨a, b, c, d, h⟩ := integral_shell_crossing H E n m hH hn hm
  obtain ⟨forms, hforms⟩ := Hurwitz.squares_of_integral_crossing a b c d
    (fun i j k l => h i k j l)
  let T := (Fin (stateCount (H + E)) × Bool) × Bool
  let e : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  refine ⟨Fintype.card T, (fun r => forms (e.symm r)), ?_, ?_⟩
  · simp [T, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega
  · intro x y
    exact (e.symm.sum_comp (fun r => Hurwitz.bilinear (forms r) x y ^ 2)).trans (hforms x y)

end

end Lemmata.EnergyShellCrossings.EnergyShell
