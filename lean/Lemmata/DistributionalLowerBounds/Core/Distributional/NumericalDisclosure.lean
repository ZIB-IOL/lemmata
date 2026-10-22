module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.MeasurableLMO
public import Lemmata.DistributionalLowerBounds.Core.Distributional.PosteriorClosure

@[expose] public section

/-!
# Actual numerical LMO answers and rank disclosures

The decoder takes ONLY the dimension, query and numerical answer. It recovers
its multiplier from all answer coordinates, then exact active ranks and inactive
ceilings. It never reads a hidden permutation. Finite classical search is a
logical exact-rank decoder, not a computability assumption on the algorithm.

The equivalence theorem is for REALIZED answers. An arbitrary malformed vector
need not be rejected by the total decoder; in particular the zero vector gives
a vacuous disclosure even for a nonzero query. No recognition theorem for
arbitrary vectors is asserted. Zero queries and integer threshold ties are
included in the realized-answer theorem.
-/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

lemma softCoordinate_zero_iff (p w lam : ℝ) :
    softCoordinate p w lam = 0 ↔ |p| / lam ≤ w := by
  rw [← abs_eq_zero, abs_softCoordinate]
  simp [softAmount]

/-- Converse of the existing inactive-rank estimate, including equality. -/
lemma inactive_of_waterTau_le {C lam p w r : ℝ}
    (hC : 0 < C) (hlam : 0 < lam) (hw0 : 0 ≤ w)
    (hw : w^2 = 2*C^2*r) (h : waterTau C lam*p^2 ≤ r) : |p|/lam ≤ w := by
  have hd : 0 < 2*C^2*lam^2 := by positivity
  have h' : p^2 / (2*C^2*lam^2) ≤ r := by
    simpa [waterTau, div_eq_mul_inv, mul_comm] using h
  have hp := (div_le_iff₀ hd).mp h'
  have hs : |p|^2 ≤ (w*lam)^2 := by
    rw [sq_abs, mul_pow, hw]
    nlinarith
  apply (div_le_iff₀ hlam).2
  nlinarith [abs_nonneg p, mul_nonneg hw0 hlam.le]

noncomputable def decodedMultiplier {d : ℕ} (C : ℝ) (p z : Fin d → ℝ) : ℝ :=
  (∑ i, |p i| * |z i|) / (C^2 + (1/2 : ℝ)*(∑ i, |z i|^2))

lemma decodedMultiplier_soft {d : ℕ} (p w : Fin d → ℝ) {C lam : ℝ}
    (hC : 0 < C) (hlam : 0 < lam)
    (hb : coordinateEnergy w (fun i => softCoordinate (p i) (w i) lam) = C^2) :
    decodedMultiplier C p (fun i => softCoordinate (p i) (w i) lam) = lam := by
  have hs : ∀ i, softCoordinate (p i) (w i) lam ^ 2 = softAmount (p i) (w i) lam ^ 2 := by
    intro i
    rw [← sq_abs, abs_softCoordinate]
  unfold coordinateEnergy at hb
  simp_rw [hs, abs_softCoordinate] at hb
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hb
  unfold decodedMultiplier
  simp_rw [abs_softCoordinate]
  exact (recover_multiplier_from_soft_answer p w hC hlam hb).symm

/-- Positivity, the soft-coordinate formula and boundary equality now refer to
an actual concrete answer and its NUMERICALLY decoded multiplier. -/
theorem concreteLMO_decoded_spec {d : ℕ} (π : Equiv.Perm (Fin d)) (p : Fin d → ℝ)
    (hp : ∃ i, p i ≠ 0) :
    let z := concreteLMO d π p
    let lam := decodedMultiplier (hardC d) p z
    0 < lam ∧ (∀ i, z i = softCoordinate (p i) (permutedHardWeight d π i) lam) ∧
      coordinateEnergy (permutedHardWeight d π) z = hardC d^2 := by
  dsimp only
  have ht := waterInverse_inv_spec p (permutedRank π)
    (fun i => by dsimp [permutedRank]; positivity) hp
  let lam := multiplierOfTau (hardC d) ((waterInverse (permutedRank π) p)⁻¹)
  have hl : 0 < lam := multiplierOfTau_pos (hardC_pos d) ht.1
  have hprofile : waterProfile p (permutedRank π) (waterTau (hardC d) lam) = 1 := by
    rw [waterTau_multiplierOfTau (hardC_pos d) ht.1]
    exact ht.2
  have hb := softCoordinate_boundary_of_waterProfile p (permutedHardWeight d π) (permutedRank π)
    (hardC_pos d) hl (fun i => hardWeight_nonneg d (π i)) (permutedHardWeight_sq_rank π) hprofile
  have he : concreteLMO d π p = fun i => softCoordinate (p i) (permutedHardWeight d π i) lam := rfl
  have hr : decodedMultiplier (hardC d) p (concreteLMO d π p) = lam := by
    rw [he]
    exact decodedMultiplier_soft p _ (hardC_pos d) hl hb
  rw [hr]
  exact ⟨hl, fun _ => rfl, hb⟩

/-- Total finite search for a zero-based index encoding the recovered one-based
rank. Its fallback is ignored for inactive coordinates and for realized active
coordinates the correct index is proved to exist and be unique. -/
noncomputable def decodedRankIndex {d : ℕ} (i : Fin d) (value : ℝ) : Fin d :=
  if h : ∃ k : Fin d, ((k.val + 1 : ℕ) : ℝ) = value then Classical.choose h else i

lemma decodedRankIndex_eq {d : ℕ} (i k : Fin d) {value : ℝ}
    (h : ((k.val + 1 : ℕ) : ℝ) = value) : decodedRankIndex i value = k := by
  have he : ∃ k : Fin d, ((k.val + 1 : ℕ) : ℝ) = value := ⟨k, h⟩
  rw [decodedRankIndex, dif_pos he]
  apply Fin.ext
  have hr : (Classical.choose he).val + 1 = k.val + 1 := by
    exact_mod_cast (Classical.choose_spec he).trans h.symm
  omega

noncomputable def decodedRankValue (d : ℕ) (p z : Fin d → ℝ) (i : Fin d) : ℝ :=
  (|p i| / decodedMultiplier (hardC d) p z - |z i|)^2 / (2*hardC d^2)

noncomputable def numericalDisclosure (d : ℕ) (p z : Fin d → ℝ) : RankDisclosure d where
  active := Finset.univ.filter (fun i => z i ≠ 0)
  activeRank i := decodedRankIndex i (decodedRankValue d p z i)
  inactiveLower i := Nat.ceil (waterTau (hardC d) (decodedMultiplier (hardC d) p z)*p i^2)

lemma decoded_activeRank_eq {d : ℕ} (π : Equiv.Perm (Fin d)) (p : Fin d → ℝ)
    (hp : ∃ i, p i ≠ 0) (i : Fin d) (hi : concreteLMO d π p i ≠ 0) :
    (numericalDisclosure d p (concreteLMO d π p)).activeRank i = π i := by
  have hs := concreteLMO_decoded_spec π p hp
  have ha : |concreteLMO d π p i| =
      softAmount (p i) (permutedHardWeight d π i)
        (decodedMultiplier (hardC d) p (concreteLMO d π p)) := by
    rw [hs.2.1 i, abs_softCoordinate]
  have hpos : 0 < softAmount (p i) (permutedHardWeight d π i)
      (decodedMultiplier (hardC d) p (concreteLMO d π p)) := by
    rw [← ha]
    exact abs_pos.mpr hi
  apply decodedRankIndex_eq
  unfold decodedRankValue
  rw [ha]
  exact recover_active_rank (hardC_pos d).ne' hpos (permutedHardWeight_sq_rank π i)

/-- This is intentionally not a test of answer realizability. -/
lemma numericalDisclosure_zero_agrees (d : ℕ) (p : Fin d → ℝ) (π : Equiv.Perm (Fin d)) :
    (numericalDisclosure d p 0).Agrees π := by
  intro i
  simp [numericalDisclosure, decodedMultiplier, waterTau]

/-- A zero answer leaves the posterior STATE unchanged, not just its local
drop. For an actual oracle this applies to zero-direction padding. -/
lemma numericalDisclosure_zero_refine (d : ℕ) (p : Fin d → ℝ) (S : RankConstraint d) :
    (numericalDisclosure d p 0).refine S = S := by
  cases S
  simp [RankDisclosure.refine, numericalDisclosure, decodedMultiplier, waterTau]

lemma concreteLMO_ne_zero {d : ℕ} (π : Equiv.Perm (Fin d)) (p : Fin d → ℝ)
    (hp : ∃ i, p i ≠ 0) : concreteLMO d π p ≠ 0 := by
  intro he
  have hb := (concreteLMO_decoded_spec π p hp).2.2
  rw [he] at hb
  simp only [coordinateEnergy, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
    mul_zero, abs_zero, add_zero, Finset.sum_const_zero] at hb
  nlinarith [sq_pos_of_pos (hardC_pos d)]

/-- Formal adversary: agreement is not recognition of an arbitrary vector. -/
theorem numericalDisclosure_zero_not_recognition {d : ℕ}
    (π : Equiv.Perm (Fin d)) (p : Fin d → ℝ) (hp : ∃ i, p i ≠ 0) :
    (numericalDisclosure d p 0).Agrees π ∧ concreteLMO d π p ≠ 0 :=
  ⟨numericalDisclosure_zero_agrees d p π, concreteLMO_ne_zero π p hp⟩

/-- Every realized answer yields a disclosure satisfied by its true instance. -/
theorem numericalDisclosure_agrees {d : ℕ} (π : Equiv.Perm (Fin d)) (p : Fin d → ℝ) :
    (numericalDisclosure d p (concreteLMO d π p)).Agrees π := by
  by_cases hp : ∃ i, p i ≠ 0
  · have hs := concreteLMO_decoded_spec π p hp
    intro i
    by_cases hi : concreteLMO d π p i ≠ 0
    · have hr := decoded_activeRank_eq π p hp i hi
      simpa [numericalDisclosure, hi] using hr.symm
    · have hz : concreteLMO d π p i = 0 := not_ne_iff.mp hi
      have hin : |p i| / decodedMultiplier (hardC d) p (concreteLMO d π p) ≤
          permutedHardWeight d π i := by
        apply (softCoordinate_zero_iff _ _ _).mp
        rw [← hs.2.1 i, hz]
      have hl := inactive_rank_ceiling (hardC_pos d) hs.1
        (hardWeight_nonneg d (π i)) (permutedHardWeight_sq_rank π i) hin
      simpa [numericalDisclosure, hi] using hl
  · have hp0 : p = 0 := by
      push Not at hp
      funext i
      exact hp i
    subst p
    rw [concreteLMO_zero]
    exact numericalDisclosure_zero_agrees _ _ _

/-- The scalar decoder's converse: no additional real-valued information is
left in a REALIZED answer beyond its active ranks and inactive lower bounds.
The reference permutation is used only in this correctness proof, not by the decoder. -/
theorem numericalDisclosure_agrees_iff {d : ℕ}
    (π₀ π : Equiv.Perm (Fin d)) (p : Fin d → ℝ) :
    (numericalDisclosure d p (concreteLMO d π₀ p)).Agrees π ↔
      concreteLMO d π p = concreteLMO d π₀ p := by
  constructor
  · intro hA
    by_cases hp : ∃ i, p i ≠ 0
    · let z := concreteLMO d π₀ p
      let lam := decodedMultiplier (hardC d) p z
      have hs := concreteLMO_decoded_spec π₀ p hp
      have hl : 0 < lam := hs.1
      have hactive : ∀ i, z i ≠ 0 → π i = π₀ i := by
        intro i hi
        have ha := hA i
        have hr := decoded_activeRank_eq π₀ p hp i hi
        have ha' : π i = (numericalDisclosure d p z).activeRank i := by
          have hi' : concreteLMO d π₀ p i ≠ 0 := hi
          simpa [numericalDisclosure, hi'] using ha
        exact ha'.trans hr
      have hz : (fun i => softCoordinate (p i) (permutedHardWeight d π i) lam) = z := by
        funext i
        by_cases hi : z i ≠ 0
        · have he := hactive i hi
          simpa only [permutedHardWeight, he] using (hs.2.1 i).symm
        · have hzi : z i = 0 := not_ne_iff.mp hi
          have ha := hA i
          have hceil : Nat.ceil (waterTau (hardC d) lam*p i^2) ≤ (π i).val+1 := by
            have hi' : concreteLMO d π₀ p i = 0 := hzi
            simpa [numericalDisclosure, hi', lam, z] using ha
          have hin := inactive_of_waterTau_le (hardC_pos d) hl
            (hardWeight_nonneg d (π i)) (permutedHardWeight_sq_rank π i) (Nat.ceil_le.mp hceil)
          exact ((softCoordinate_zero_iff _ _ _).2 hin).trans hzi.symm
      have hb : coordinateEnergy (permutedHardWeight d π) z = hardC d^2 := by
        calc
          _ = coordinateEnergy (permutedHardWeight d π₀) z := by
            unfold coordinateEnergy
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : z i = 0
            · simp [hi]
            · simp only [permutedHardWeight, hactive i hi]
          _ = _ := hs.2.2
      have hbsoft : coordinateEnergy (permutedHardWeight d π)
          (fun i => softCoordinate (p i) (permutedHardWeight d π i) lam) = hardC d^2 := by
        rw [hz]
        exact hb
      have hc := concreteLMO_correct d π p
      have hmin := softCoordinate_is_LMO p (permutedHardWeight d π)
        (fun i => hardWeight_nonneg d (π i)) hl hbsoft
      have hv : (∑ i, p i*concreteLMO d π p i) =
          ∑ i, p i*softCoordinate (p i) (permutedHardWeight d π i) lam := by
        apply le_antisymm
        · change _ ≤ ∑ i, p i*((fun i => softCoordinate (p i) (permutedHardWeight d π i) lam) i)
          rw [hz]
          exact hc.2 z hb.le
        · exact hmin _ hc.1
      exact (softCoordinate_unique_LMO p (permutedHardWeight d π)
        (fun i => hardWeight_nonneg d (π i)) hl hbsoft hc.1 hv).trans hz
    · have hp0 : p = 0 := by
        push Not at hp
        funext i
        exact hp i
      subst p
      simp [concreteLMO_zero]
  · intro he
    rw [← he]
    exact numericalDisclosure_agrees π p

/-- General realized-vector form. Realizability cannot be dropped for arbitrary
malformed `(p,z)` inputs to this total decoder. -/
theorem numericalDisclosure_realized_iff {d : ℕ} (p z : Fin d → ℝ)
    (hreal : ∃ π₀, concreteLMO d π₀ p = z) (π : Equiv.Perm (Fin d)) :
    (numericalDisclosure d p z).Agrees π ↔ concreteLMO d π p = z := by
  obtain ⟨π₀, rfl⟩ := hreal
  exact numericalDisclosure_agrees_iff π₀ π p

/-- The actual numerical answer now instantiates the previously supplied
`RankDisclosure` interface. Prior fixed coordinates and lower bounds are retained. -/
theorem numerical_refine_compatible_iff {d : ℕ} (S : RankConstraint d)
    (π₀ π : Equiv.Perm (Fin d)) (p : Fin d → ℝ) :
    ((numericalDisclosure d p (concreteLMO d π₀ p)).refine S).Compatible π ↔
      S.Compatible π ∧ concreteLMO d π p = concreteLMO d π₀ p := by
  rw [RankDisclosure.compatible_refine_iff, numericalDisclosure_agrees_iff]

end Lemmata.DistributionalLowerBounds.Core.Distributional
