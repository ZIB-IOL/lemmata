module

public import Lemmata.RM59.Proof.FlagCover
public import Lemmata.RM59.Proof.FlagSelectionChecks
public import Lemmata.RM59.Proof.RankSelection
public meta import Lemmata.RM59.Proof.FlagGeometry
public meta import Lemmata.RM59.Proof.FlagSelectionChecks

@[expose] public section

namespace Lemmata.RM59.FlagNine

open Lemmata.RM59.Packed Lemmata.RM59.FlagActions Lemmata.RM59.FlagGeometry Lemmata.RM59.FlagCover Lemmata.RM59.FlagSelectionChecks
open Lemmata.RM59.BinaryQuadGeometry
open scoped BigOperators Matrix

def quotientIndex : Fin 7 → Fin 9 := ![1, 3, 4, 5, 6, 7, 8]

def quotient : Point 9 →ₗ[Field] Point 7 where
  toFun x i := x (quotientIndex i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem quotient_kernel_checked : ∀ x : PackedPoint,
    quotient (decodePoint x) = 0 ↔ decodePoint x ∈ space 0 := by native_decide

theorem quotient_kernel : LinearMap.ker quotient = space 0 := by
  ext x
  change quotient x = 0 ↔ x ∈ space 0
  simpa only [decodePoint_encodePoint] using quotient_kernel_checked (encodePoint x)

theorem quotient_kernel_finrank : Module.finrank Field (LinearMap.ker quotient) = 2 := by
  rw [quotient_kernel]
  exact space_finrank 0

theorem coefficient_expansion_checked : ∀ i : Fin 6,
    coefficient i = Pi.single (triple i 0) 1 + Pi.single (triple i 1) 1 +
      Pi.single (triple i 2) 1 := by decide

theorem coefficient_expansion (v : Fin 6 → Point 9) (i : Fin 6) :
    Fintype.linearCombination Field v (coefficient i) =
      v (triple i 0) + v (triple i 1) + v (triple i 2) := by
  rw [coefficient_expansion_checked]
  simp only [map_add, Fintype.linearCombination_apply_single, one_smul]

theorem triple_sums_independent (v : Fin 6 → Point 9) (hv : LinearIndependent Field v) :
    LinearIndependent Field (fun i => v (triple i 0) + v (triple i 1) + v (triple i 2)) := by
  have hinj := linearIndependent_iff_injective_fintypeLinearCombination.mp hv
  have hi := coefficients_independent.map' (Fintype.linearCombination Field v)
    (LinearMap.ker_eq_bot.mpr hinj)
  simpa only [Function.comp_def, coefficient_expansion] using hi

theorem triple_outside_W (v : Fin 6 → Point 9) (hv : LinearIndependent Field v) :
    ∃ i, v (triple i 0) + v (triple i 1) + v (triple i 2) ∉ space 1 := by
  have hi := triple_sums_independent v hv
  by_contra hn
  push_neg at hn
  let w : Fin 6 → space 1 := fun i => ⟨_, hn i⟩
  have hw : LinearIndependent Field w := by
    apply LinearIndependent.of_comp (space 1).subtype
    exact hi
  have hbound := hw.fintype_card_le_finrank
  have hdim : Module.finrank Field (space 1) = 5 := space_finrank 1
  rw [Fintype.card_fin, hdim] at hbound
  omega

theorem cover_nine (p : Fin 9 → Point 9) (hp : AffineIndependent Field p) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G seed ∧ G.card = 30 ∧
      ∃ q : Fin 4 → Fin 9, Function.Injective q ∧ ∀ i, p (q i) ∈ G := by
  by_cases hmixed : ∃ i j, p i 1 ≠ p j 1
  · obtain ⟨indices, hinj, hsum⟩ := mixed_exists (fun i => p i 1) hmixed
    let q : Fin 4 → Fin 9 := fun i => indices.get i
    have hq : AffineIndependent Field (p ∘ q) := hp.comp_embedding ⟨q, hinj⟩
    have hsumH : sumFour (p ∘ q) ∉ space 2 := by
      intro hh
      have hz := (hyperplane_mem _).1 hh
      have ho : sumFour (p ∘ q) 1 = 1 := hsum
      rw [ho] at hz
      exact one_ne_zero hz
    obtain ⟨G, hG, hc, hg⟩ := cover_A (p ∘ q) hq hsumH
    exact ⟨G, hG, hc, q, hinj, hg⟩
  · have hconst (i : Fin 9) : p i 1 = p 0 1 := by
      by_contra hi
      exact hmixed ⟨i, 0, hi⟩
    let v : Fin 8 → Point 9 := fun j => p 0 + p j.succ
    have hv : LinearIndependent Field v := by
      have hd := (affineIndependent_iff_linearIndependent_vsub Field p 0).mp hp
      let select : Fin 8 → {i : Fin 9 // i ≠ 0} := fun j => ⟨j.succ, Fin.succ_ne_zero j⟩
      have hs : Function.Injective select := by
        intro i j h
        exact (Fin.succ_injective 8) (congrArg Subtype.val h)
      have hi := hd.comp select hs
      convert hi using 1
      funext j
      simp only [v, select, Function.comp_def, vsub_eq_sub, sub_eq_add_neg, point_neg_self]
      ac_rfl
    have hvH (i : Fin 8) : v i ∈ space 2 := by
      apply (hyperplane_mem _).2
      change p 0 1 + p i.succ 1 = 0
      exact (congrArg (fun z : Field => p 0 1 + z) (hconst i.succ)).trans (field_add_self _)
    obtain ⟨selection, hselection⟩ := RankSelection.independent_subfamily v hv quotient 6
      (by rw [quotient_kernel_finrank, Fintype.card_fin] <;> decide)
    let w : Fin 6 → Point 9 := v ∘ selection
    have hprojected : LinearIndependent Field (quotient ∘ w) := hselection
    have hw : LinearIndependent Field w := LinearIndependent.of_comp quotient hprojected
    let S := Submodule.span Field (Set.range w)
    have hSH : S ≤ space 2 := by
      apply Submodule.span_le.mpr
      rintro x ⟨i, rfl⟩
      exact hvH (selection i)
    have hSU : Disjoint S (space 0) := by
      have hs := Submodule.range_ker_disjoint hprojected
      rw [quotient_kernel] at hs
      exact hs
    obtain ⟨j, hj⟩ := triple_outside_W w hw
    have hsel : Function.Injective selection := by
      intro a b he
      exact hselection.injective (congrArg (fun i => quotient (v i)) he)
    let q : Fin 4 → Fin 9 := Fin.cases 0 (fun r => (selection (triple j r)).succ)
    have hqinj : Function.Injective q := by
      intro a b he
      cases a using Fin.cases with
      | zero =>
        cases b using Fin.cases with
        | zero => rfl
        | succ b => exact (Fin.succ_ne_zero _ he.symm).elim
      | succ a =>
        cases b using Fin.cases with
        | zero => exact (Fin.succ_ne_zero _ he).elim
        | succ b =>
          have hab := triple_injective j (hsel ((Fin.succ_injective 8) he))
          exact congrArg Fin.succ hab
    have hq : AffineIndependent Field (p ∘ q) := hp.comp_embedding ⟨q, hqinj⟩
    have hsum : sumFour (p ∘ q) = w (triple j 0) + w (triple j 1) + w (triple j 2) := by
      rw [← directions_sum]
      rfl
    have hwS (i : Fin 6) : w i ∈ S := Submodule.subset_span ⟨i, rfl⟩
    have haS : (p ∘ q) 0 + (p ∘ q) 1 ∈ S := hwS (triple j 0)
    have hbS : (p ∘ q) 0 + (p ∘ q) 2 ∈ S := hwS (triple j 1)
    have htS : sumFour (p ∘ q) ∈ S := by
      rw [hsum]
      exact S.add_mem (S.add_mem (hwS _) (hwS _)) (hwS _)
    obtain ⟨G, hG, hc, hg⟩ := cover_B (p ∘ q) hq S haS hbS htS hSH hSU (by rwa [hsum])
    exact ⟨G, hG, hc, q, hqinj, hg⟩

end Lemmata.RM59.FlagNine
