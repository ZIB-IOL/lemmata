module

public import Lemmata.RM59.Proof.ProjectionRank
public import Lemmata.RM59.Proof.Family53Small

@[expose] public section

namespace Lemmata.RM59.Family53Selection

open scoped BigOperators Matrix symmDiff
open Lemmata.RM59.Family53Five Lemmata.RM59.ProjectionRank

abbrev FieldPoint := TraceGeometry.FieldPoint

theorem extend_four (k : Nat) (hk2 : 2 ≤ k) (hk4 : k ≤ 4) (v : Fin k → Plane)
    (hv : LinearIndependent Field v) :
    ∃ d : Fin 4 → Plane, LinearIndependent Field d ∧ ∀ i, d (Fin.castLE hk4 i) = v i := by
  have hcases : k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hcases with rfl | rfl | rfl
  · obtain ⟨x, hx⟩ := exists_linearIndependent_snoc_of_lt_finrank hv
      (by rw [plane_finrank]; decide)
    obtain ⟨y, hy⟩ := exists_linearIndependent_snoc_of_lt_finrank hx
      (by rw [plane_finrank]; decide)
    refine ⟨Fin.snoc (Fin.snoc v x) y, hy, ?_⟩
    intro i
    fin_cases i <;> rfl
  · obtain ⟨x, hx⟩ := exists_linearIndependent_snoc_of_lt_finrank hv
      (by rw [plane_finrank]; decide)
    refine ⟨Fin.snoc v x, hx, ?_⟩
    intro i
    fin_cases i <;> rfl
  · exact ⟨v, hv, fun _ => rfl⟩

theorem cover_projected_prefix (k : Nat) (hk2 : 2 ≤ k) (hk4 : k ≤ 4)
    (base : FieldPoint) (points : Fin k → FieldPoint)
    (hi : LinearIndependent Field (fun j => projection (points j - base))) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G seed ∧ G.card = 32 ∧
      FieldCoordinates.pointEquiv.symm base ∈ G ∧
      ∀ j, FieldCoordinates.pointEquiv.symm (points j) ∈ G := by
  obtain ⟨d, hd, he⟩ := extend_four k hk2 hk4 _ hi
  let other : Fin 4 → FieldPoint := fun j =>
    if h : j.val < k then points ⟨j.val, h⟩ else base + inclusion (d j)
  let target : Fin 5 → FieldPoint := Fin.cases base other
  have hdiff : (fun j : Fin 4 => projection (target j.succ - target 0)) = d := by
    funext j
    change projection (other j - base) = d j
    dsimp only [other]
    split_ifs with hj
    · have hv := he ⟨j.val, hj⟩
      change d j = projection (points ⟨j.val, hj⟩ - base) at hv
      exact hv.symm
    · rw [add_sub_cancel_left, projection_inclusion]
  have ht : LinearIndependent Field (fun j : Fin 4 => projection (target j.succ - target 0)) := by
    rw [hdiff]
    exact hd
  obtain ⟨G, hG, hc, hm⟩ := cover_projected_five target (projected_five_independent target ht)
  refine ⟨G, hG, hc, hm 0, ?_⟩
  intro j
  have hj := hm (Fin.castLE hk4 j).succ
  simpa only [target, Fin.cases_succ, other, Fin.val_castLE, j.isLt,
    dite_true] using hj

theorem prefix_injective {k : Nat} (base : FieldPoint) (points : Fin k → FieldPoint)
    (hi : LinearIndependent Field (fun j => projection (points j - base))) :
    Function.Injective (Fin.cases base points) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => rfl
    | succ b =>
      exfalso
      apply hi.ne_zero b
      change base = points b at hij
      rw [← hij, sub_self, map_zero]
  | succ a =>
    cases j using Fin.cases with
    | zero =>
      exfalso
      apply hi.ne_zero a
      change points a = base at hij
      rw [hij, sub_self, map_zero]
    | succ b =>
      have hab : a = b := hi.injective (by
        change points a = points b at hij
        rw [hij])
      exact congrArg Fin.succ hab

theorem prefix_intersection (k : Nat) (P G : Finset (Point 9))
    (base : FieldPoint) (points : Fin k → FieldPoint)
    (hi : LinearIndependent Field (fun j => projection (points j - base)))
    (hbaseP : FieldCoordinates.pointEquiv.symm base ∈ P)
    (hpointsP : ∀ j, FieldCoordinates.pointEquiv.symm (points j) ∈ P)
    (hbaseG : FieldCoordinates.pointEquiv.symm base ∈ G)
    (hpointsG : ∀ j, FieldCoordinates.pointEquiv.symm (points j) ∈ G) :
    k + 1 ≤ (G ∩ P).card := by
  let q : Fin (k + 1) → Point 9 :=
    fun i => FieldCoordinates.pointEquiv.symm (Fin.cases base points i)
  have hq : Function.Injective q := FieldCoordinates.pointEquiv.symm.injective.comp
    (prefix_injective base points hi)
  have hs : Finset.univ.image q ⊆ G ∩ P := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    cases i using Fin.cases with
    | zero => exact Finset.mem_inter.mpr ⟨hbaseG, hbaseP⟩
    | succ j => exact Finset.mem_inter.mpr ⟨hpointsG j, hpointsP j⟩
  have hc := Finset.card_le_card hs
  simpa only [Finset.card_image_of_injective _ hq, Finset.card_univ, Fintype.card_fin] using hc

theorem completion_of_differences (P : Finset (Point 9))
    (base : P) (k : Nat) (hk2 : 2 ≤ k) (hk4 : k ≤ 4) (points : Fin k → P)
    (hi : LinearIndependent Field (fun j => projection
      (FieldCoordinates.pointEquiv (points j).val - FieldCoordinates.pointEquiv base.val)))
    (hcard : P.card + 1 ≤ 2 * (k + 1)) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G seed ∧ (G ∆ P).card ≤ 31 := by
  obtain ⟨G, hG, hc, hb, hm⟩ := cover_projected_prefix k hk2 hk4
    (FieldCoordinates.pointEquiv base.val)
    (fun j => FieldCoordinates.pointEquiv (points j).val) hi
  have hn := prefix_intersection k P G (FieldCoordinates.pointEquiv base.val)
    (fun j => FieldCoordinates.pointEquiv (points j).val) hi
    (by simpa only [FieldCoordinates.pointEquiv.symm_apply_apply] using base.property)
    (fun j => by simpa only [FieldCoordinates.pointEquiv.symm_apply_apply] using (points j).property)
    hb hm
  refine ⟨G, hG, ?_⟩
  apply symmDiff_card_le_of_intersection
  omega

theorem completion_large (P : Finset (Point 9))
    (hp : AffineIndependent Field ((↑) : P → Point 9))
    (hcard : P.card ∈ ({7, 9} : Finset Nat)) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G seed ∧ (G ∆ P).card ≤ 31 := by
  classical
  have hpos : 0 < P.card := by
    have hc : P.card = 7 ∨ P.card = 9 := by simpa using hcard
    omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  let base : P := ⟨a, ha⟩
  have hpf : AffineIndependent Field (fun x : P => FieldCoordinates.pointEquiv x.val) :=
    hp.map' FieldCoordinates.pointEquiv.toAffineEquiv.toAffineMap
      FieldCoordinates.pointEquiv.injective
  have hcases : P.card = 7 ∨ P.card = 9 := by simpa using hcard
  rcases hcases with h7 | h9
  · obtain ⟨points, hi⟩ := exists_projected_differences
      (fun x : P => FieldCoordinates.pointEquiv x.val) hpf base 3
      (by simpa only [Fintype.card_coe, h7] using (show 3 + 3 ≤ 7 - 1 by decide))
    exact completion_of_differences P base 3 (by decide) (by decide) points hi (by omega)
  · obtain ⟨points, hi⟩ := exists_projected_differences
      (fun x : P => FieldCoordinates.pointEquiv x.val) hpf base 4
      (by simpa only [Fintype.card_coe, h9] using (show 4 + 3 ≤ 9 - 1 by decide))
    exact completion_of_differences P base 4 (by decide) (by decide) points hi (by omega)

theorem module_add_self {M : Type*} [AddCommGroup M] [Module Field M] (x : M) : x + x = 0 := by
  calc
    x + x = (1 + 1 : Field) • x := by rw [add_smul, one_smul]
    _ = 0 := by rw [show (1 + 1 : Field) = 0 by decide, zero_smul]

theorem independent_pair_of_distinct {M : Type*} [AddCommGroup M] [Module Field M]
    (x y : M) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    LinearIndependent Field ![x, y] := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  rcases field_eq_zero_or_one (c 0) with h0 | h0 <;>
    rcases field_eq_zero_or_one (c 1) with h1 | h1
  · fin_cases i
    · exact h0
    · exact h1
  · have he : y = 0 := by simpa only [Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, h0, h1, zero_smul, one_smul, zero_add] using hc
    exact (hy he).elim
  · have he : x = 0 := by simpa only [Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, h0, h1, zero_smul, one_smul, add_zero] using hc
    exact (hx he).elim
  · have he : x + y = 0 := by simpa only [Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, h0, h1, one_smul] using hc
    have hh := congrArg (fun z => z + y) he
    rw [add_assoc, module_add_self, add_zero, zero_add] at hh
    exact (hxy hh).elim

theorem horizontal_sub_eq_zero (x y : FieldPoint) :
    VerticalFrames.horizontal (x - y) = 0 ↔ projection x = projection y := by
  rw [VerticalFrames.horizontal_eq_zero]
  constructor
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i
    · exact sub_eq_zero.mp h0
    · exact sub_eq_zero.mp h1
  · intro h
    exact ⟨sub_eq_zero.mpr (congrFun h 0), sub_eq_zero.mpr (congrFun h 1)⟩

theorem completion_from_three (P : Finset (Point 9)) (hcard : P.card = 5)
    (a b c : P) (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val)
    (G : Finset (Point 9)) (hG : MatchSupportMoments 3 G seed) (hc : G.card = 32)
    (haG : a.val ∈ G) (hbG : b.val ∈ G) (hcG : c.val ∈ G) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G seed ∧ (G ∆ P).card ≤ 31 := by
  have hs : ({a.val, b.val, c.val} : Finset (Point 9)) ⊆ G ∩ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_inter.mpr ⟨haG, a.property⟩
    · exact Finset.mem_inter.mpr ⟨hbG, b.property⟩
    · exact Finset.mem_inter.mpr ⟨hcG, c.property⟩
  have hn : 3 ≤ (G ∩ P).card := by
    have hthree : ({a.val, b.val, c.val} : Finset (Point 9)).card = 3 := by
      simp [hab, hac, hbc]
    simpa only [hthree] using Finset.card_le_card hs
  refine ⟨G, hG, ?_⟩
  apply symmDiff_card_le_of_intersection
  omega

theorem completion_five (P : Finset (Point 9))
    (hp : AffineIndependent Field ((↑) : P → Point 9)) (hcard : P.card = 5) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G seed ∧ (G ∆ P).card ≤ 31 := by
  classical
  let f : P → Plane := fun x => projection (FieldCoordinates.pointEquiv x.val)
  by_cases hthree : ∃ a b c : P, f a ≠ f b ∧ f a ≠ f c ∧ f b ≠ f c
  · obtain ⟨a, b, c, hab, hac, hbc⟩ := hthree
    have hi : LinearIndependent Field ![f b - f a, f c - f a] :=
      independent_pair_of_distinct _ _ (sub_ne_zero.mpr hab.symm)
        (sub_ne_zero.mpr hac.symm) (fun he => hbc (sub_left_injective he))
    let points : Fin 2 → P := ![b, c]
    have hind : LinearIndependent Field (fun j => projection
        (FieldCoordinates.pointEquiv (points j).val - FieldCoordinates.pointEquiv a.val)) := by
      convert hi using 1
      funext j
      fin_cases j <;> simp only [points, Matrix.cons_val_zero, Matrix.cons_val_one, map_sub, f] <;> rfl
    exact completion_of_differences P a 2 (by decide) (by decide) points hind (by omega)
  · obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < P.card)
    let a : P := ⟨x, hx⟩
    have hpf : AffineIndependent Field (fun x : P => FieldCoordinates.pointEquiv x.val) :=
      hp.map' FieldCoordinates.pointEquiv.toAffineEquiv.toAffineMap
        FieldCoordinates.pointEquiv.injective
    obtain ⟨selected, hselected⟩ := exists_projected_differences
      (fun x : P => FieldCoordinates.pointEquiv x.val) hpf a 1
      (by simpa only [Fintype.card_coe, hcard] using (show 1 + 3 ≤ 5 - 1 by decide))
    let b := selected 0
    have hab : f a ≠ f b := by
      intro he
      apply hselected.ne_zero 0
      change projection (FieldCoordinates.pointEquiv b.val - FieldCoordinates.pointEquiv a.val) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr he.symm
    have habv : a.val ≠ b.val := fun he => hab (congrArg (fun y => projection
      (FieldCoordinates.pointEquiv y)) he)
    have hpair : ({a.val, b.val} : Finset (Point 9)).card = 2 := by simp [habv]
    obtain ⟨z, hzP, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (by rw [hpair, hcard]; decide : ({a.val, b.val} : Finset (Point 9)).card < P.card)
    let c : P := ⟨z, hzP⟩
    have hz' : z ≠ a.val ∧ z ≠ b.val := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hz
    have hca : c.val ≠ a.val := hz'.1
    have hcb : c.val ≠ b.val := hz'.2
    have hcolors : f c = f a ∨ f c = f b := by
      by_cases hca' : f c = f a
      · exact Or.inl hca'
      · by_cases hcb' : f c = f b
        · exact Or.inr hcb'
        · exact (hthree ⟨a, b, c, hab, Ne.symm hca', Ne.symm hcb'⟩).elim
    rcases hcolors with hca' | hcb'
    · obtain ⟨G, hG, hc, haG, hcG, hbG⟩ := Family53Small.cover_vertical_pair_triple
        (FieldCoordinates.pointEquiv a.val) (FieldCoordinates.pointEquiv c.val)
        (FieldCoordinates.pointEquiv b.val)
        (fun he => hca (FieldCoordinates.pointEquiv.injective he).symm)
        ((horizontal_sub_eq_zero _ _).2 hca')
        (fun he => hab ((horizontal_sub_eq_zero _ _).1 he).symm)
      simp only [FieldCoordinates.pointEquiv.symm_apply_apply] at haG hbG hcG
      exact completion_from_three P hcard a b c habv hca.symm hcb.symm G hG hc haG hbG hcG
    · obtain ⟨G, hG, hc, hbG, hcG, haG⟩ := Family53Small.cover_vertical_pair_triple
        (FieldCoordinates.pointEquiv b.val) (FieldCoordinates.pointEquiv c.val)
        (FieldCoordinates.pointEquiv a.val)
        (fun he => hcb (FieldCoordinates.pointEquiv.injective he).symm)
        ((horizontal_sub_eq_zero _ _).2 hcb')
        (fun he => hab ((horizontal_sub_eq_zero _ _).1 he))
      simp only [FieldCoordinates.pointEquiv.symm_apply_apply] at haG hbG hcG
      exact completion_from_three P hcard a b c habv hca.symm hcb.symm G hG hc haG hbG hcG

theorem completion (P : Finset (Point 9))
    (hp : AffineIndependent Field ((↑) : P → Point 9))
    (hcard : P.card ∈ ({1, 3, 5, 7, 9} : Finset Nat)) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G seed ∧ (G ∆ P).card ≤ 31 := by
  have hcases : P.card = 1 ∨ P.card = 3 ∨ P.card = 5 ∨ P.card = 7 ∨ P.card = 9 := by
    simpa using hcard
  rcases hcases with h1 | h3 | h5 | h7 | h9
  · exact Family53Small.completion_small P (by simp [h1])
  · exact Family53Small.completion_small P (by simp [h3])
  · exact completion_five P hp h5
  · exact completion_large P hp (by simp [h7])
  · exact completion_large P hp (by simp [h9])

end Lemmata.RM59.Family53Selection
