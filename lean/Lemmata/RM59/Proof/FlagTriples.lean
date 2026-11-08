module

public import Lemmata.RM59.Proof.FlagCover
public import Lemmata.RM59.Proof.BinaryAffineFour
public import Lemmata.RM59.Proof.FlagSelectionChecks
public import Lemmata.RM59.Proof.Intersections
public meta import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Lemmata.RM59.FlagTriples

open Lemmata.RM59.FlagActions Lemmata.RM59.FlagGeometry Lemmata.RM59.FlagCover Lemmata.RM59.FlagSelectionChecks
open Lemmata.RM59.BinaryQuadGeometry
open scoped Matrix symmDiff

def forbidden (p : Fin 3 → Point 9) : Finset (Point 9) :=
  Finset.univ.image (![p 0, p 1, p 2, p 0 + p 1 + p 2] : Fin 4 → Point 9)

theorem forbidden_card (p : Fin 3 → Point 9) : (forbidden p).card ≤ 4 := by
  calc
    _ ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
    _ = 4 := by simp

theorem cube_sum : ∀ a b c : Field, a + b + c + (1 + a + b + c) = 1 := by decide

theorem cover_triple (p : Fin 3 → Point 9) (hp : Function.Injective p) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G seed ∧ G.card = 30 ∧ ∀ i, p i ∈ G := by
  let r : Field := 1 + p 0 1 + p 1 1 + p 2 1
  have hlt : (forbidden p).card < (cube r).card := by
    rw [(cube_checked r).1]
    have hc := forbidden_card p
    omega
  obtain ⟨x, hx, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hxbit : x 1 = r := (cube_checked r).2 x hx
  have hp01 : p 0 ≠ p 1 := fun he => (by decide : (0 : Fin 3) ≠ 1) (hp he)
  have hp02 : p 0 ≠ p 2 := fun he => (by decide : (0 : Fin 3) ≠ 2) (hp he)
  have hp12 : p 1 ≠ p 2 := fun he => (by decide : (1 : Fin 3) ≠ 2) (hp he)
  have hx0 : p 0 ≠ x := fun he => hnot (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, he⟩)
  have hx1 : p 1 ≠ x := fun he => hnot (Finset.mem_image.mpr ⟨1, Finset.mem_univ _, he⟩)
  have hx2 : p 2 ≠ x := fun he => hnot (Finset.mem_image.mpr ⟨2, Finset.mem_univ _, he⟩)
  let q : Fin 4 → Point 9 := ![p 0, p 1, p 2, x]
  have hqinj : Function.Injective q := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [q]
  have hsum1 : sumFour q 1 = 1 := by
    change p 0 1 + p 1 1 + p 2 1 + x 1 = 1
    rw [hxbit]
    exact cube_sum _ _ _
  have hsumH : sumFour q ∉ space 2 := by
    intro hh
    have hz := (hyperplane_mem _).1 hh
    rw [hsum1] at hz
    exact one_ne_zero hz
  have hsum : sumFour q ≠ 0 := by
    intro hz
    apply hsumH
    rw [hz]
    exact (space 2).zero_mem
  obtain ⟨G, hG, hc, hm⟩ := cover_A q (affineIndependent_of_injective_sum q hqinj hsum) hsumH
  refine ⟨G, hG, hc, ?_⟩
  intro i
  fin_cases i
  · exact hm 0
  · exact hm 1
  · exact hm 2

theorem completion_small (P : Finset (Point 9))
    (hcard : P.card ∈ ({1, 3, 5, 7} : Finset Nat)) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G seed ∧ (G ∆ P).card ≤ 31 := by
  have hcases : P.card = 1 ∨ P.card = 3 ∨ P.card = 5 ∨ P.card = 7 := by simpa using hcard
  by_cases h1 : P.card = 1
  · refine ⟨seed, MatchSupportMoments.refl _ _, ?_⟩
    apply symmDiff_card_le_of_intersection
    rw [seed_card, h1]
    omega
  · have hpos : 2 < P.card := by omega
    have hbound : P.card ≤ 7 := by omega
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hpos
    let p : Fin 3 → Point 9 := ![a, b, c]
    have hp : Function.Injective p := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [p]
    obtain ⟨G, hG, hn, hm⟩ := cover_triple p hp
    have hs : ({a, b, c} : Finset (Point 9)) ⊆ G ∩ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hm 0, ha⟩
      · exact Finset.mem_inter.mpr ⟨hm 1, hb⟩
      · exact Finset.mem_inter.mpr ⟨hm 2, hc⟩
    have hthree : ({a, b, c} : Finset (Point 9)).card = 3 := by simp [hab, hac, hbc]
    have hi : 3 ≤ (G ∩ P).card := by
      simpa only [hthree] using Finset.card_le_card hs
    refine ⟨G, hG, ?_⟩
    apply symmDiff_card_le_of_intersection
    omega

end Lemmata.RM59.FlagTriples
