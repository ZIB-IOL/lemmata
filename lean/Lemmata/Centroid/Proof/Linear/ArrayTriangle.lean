module

public import Lemmata.Centroid.Proof.Linear.ArraySubspaces
public import Lemmata.Centroid.Proof.Linear.Leading
public import Lemmata.Centroid.Proof.Combinatorics.TripartiteDeficits
public import Mathlib.Order.Prod.Lex.Basic

@[expose] public section

open Classical

noncomputable section

namespace Lemmata.Centroid.Linear

variable {F α β γ : Type*} [Field F] [Fintype α] [Fintype β] [Fintype γ]
  [LinearOrder α] [LinearOrder β] [LinearOrder γ]

def tripleLexEquiv : (α × β × γ) ≃ (α ×ₗ β ×ₗ γ) where
  toFun p := toLex (p.1, toLex p.2)
  invFun x := ((ofLex x).1, ofLex ((ofLex x).2))
  left_inv _ := rfl
  right_inv _ := rfl

def arrayLexCoordinates : (α × β × γ → F) ≃ₗ[F] (α ×ₗ β ×ₗ γ → F) :=
  LinearEquiv.funCongrLeft F F tripleLexEquiv.symm

def pairLexCoordinates : (α × β → F) ≃ₗ[F] (α ×ₗ β → F) :=
  LinearEquiv.funCongrLeft F F ofLex

omit [Fintype α] [Fintype β] [Fintype γ] in
private theorem first_insert_strictMono (a : α) : StrictMono (fun q : β ×ₗ γ => toLex (a, q)) := by
  intro q r hqr
  exact Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, hqr⟩)

omit [Fintype α] [Fintype β] [Fintype γ] in
private theorem second_insert_strictMono (b : β) :
    StrictMono (fun q : α ×ₗ γ => toLex ((ofLex q).1, toLex (b, (ofLex q).2))) := by
  intro q r hqr
  rcases Prod.Lex.lt_iff.1 hqr with h | ⟨h, hγ⟩
  · exact Prod.Lex.toLex_lt_toLex.2 (Or.inl h)
  · exact Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨h, Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, hγ⟩)⟩)

def arrayLexLeading (S : Submodule F (α × β × γ → F)) : Finset (α × β × γ) :=
  (leadingPositions (S.map arrayLexCoordinates.toLinearMap)).image tripleLexEquiv.symm

theorem card_arrayLexLeading (S : Submodule F (α × β × γ → F)) :
    (arrayLexLeading S).card = Module.finrank F S := by
  rw [arrayLexLeading, Finset.card_image_of_injective _ tripleLexEquiv.symm.injective, card_leadingPositions]
  exact arrayLexCoordinates.finrank_map_eq S

theorem arrayLexLeading_first_support (S : Submodule F (α × β × γ → F)) :
    ((arrayLexLeading S).image (fun p => (p.2.1, p.2.2))).card ≤ Module.finrank F (arraySupport S) := by
  have hsub : (arrayLexLeading S).image (fun p => toLex p.2) ⊆
      leadingPositions ((arraySupport S).map pairLexCoordinates.toLinearMap) := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
    have hzlead : IsLeading (S.map arrayLexCoordinates.toLinearMap)
        (toLex ((ofLex z).1, (ofLex z).2)) := by
      simpa only [Prod.mk.eta, toLex_ofLex] using (mem_leadingPositions _ _).1 hz
    have hlead := hzlead.pullback (j := (ofLex z).2) (first_insert_strictMono (ofLex z).1)
    apply (mem_leadingPositions _ _).2
    apply hlead.mono
    rintro f ⟨g, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨arraySlice (ofLex z).1 v, Submodule.mem_iSup_of_mem _ ⟨v, hv, rfl⟩, ?_⟩
    rfl
  have hcard := Finset.card_le_card hsub
  rw [card_leadingPositions, pairLexCoordinates.finrank_map_eq] at hcard
  have heq : (arrayLexLeading S).image (fun p => toLex p.2) =
      ((arrayLexLeading S).image (fun p => p.2)).map toLex.toEmbedding := by
    simp only [Finset.map_eq_image, Finset.image_image]
    rfl
  rw [heq, Finset.card_map] at hcard
  exact hcard

theorem arrayLexLeading_second_support (S : Submodule F (α × β × γ → F)) :
    ((arrayLexLeading S).image (fun p => (p.1, p.2.2))).card ≤
      Module.finrank F (arraySupport (S.map swapFirstTwo.toLinearMap)) := by
  have hsub : (arrayLexLeading S).image (fun p => toLex (p.1, p.2.2)) ⊆
      leadingPositions ((arraySupport (S.map swapFirstTwo.toLinearMap)).map pairLexCoordinates.toLinearMap) := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
    have hzlead : IsLeading (S.map arrayLexCoordinates.toLinearMap)
        (toLex ((ofLex z).1, toLex ((ofLex ((ofLex z).2)).1, (ofLex ((ofLex z).2)).2))) := by
      simpa only [Prod.mk.eta, toLex_ofLex] using (mem_leadingPositions _ _).1 hz
    have hlead := hzlead.pullback (j := toLex ((ofLex z).1, (ofLex ((ofLex z).2)).2))
      (second_insert_strictMono (ofLex ((ofLex z).2)).1)
    apply (mem_leadingPositions _ _).2
    apply hlead.mono
    rintro f ⟨g, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨arraySlice (ofLex ((ofLex z).2)).1 (swapFirstTwo v),
      Submodule.mem_iSup_of_mem _ ⟨swapFirstTwo v, ⟨v, hv, rfl⟩, rfl⟩, ?_⟩
    rfl
  have hcard := Finset.card_le_card hsub
  rw [card_leadingPositions, pairLexCoordinates.finrank_map_eq] at hcard
  have heq : (arrayLexLeading S).image (fun p => toLex (p.1, p.2.2)) =
      ((arrayLexLeading S).image (fun p => (p.1, p.2.2))).map toLex.toEmbedding := by
    simp only [Finset.map_eq_image, Finset.image_image]
    rfl
  rw [heq, Finset.card_map] at hcard
  exact hcard

theorem array_triangle_bound_ordered (S : Submodule F (α × β × γ → F)) {n e₁ e₂ : ℕ}
    (hα : Fintype.card α ≤ n) (hβ : Fintype.card β ≤ n) (he₂ : e₂ ≤ e₁) (he₁ : e₁ ≤ n)
    (hP : Module.finrank F (arraySupport S) ≤ n ^ 2 + e₂)
    (hQ : Module.finrank F (arraySupport (S.map swapFirstTwo.toLinearMap)) ≤ n ^ 2 + e₁) :
    Module.finrank F S ≤ n ^ 3 + e₁ * e₂ := by
  let L := arrayLexLeading S
  let AB := L.image (fun p => (p.1, p.2.1))
  let AC := L.image (fun p => (p.1, p.2.2))
  let BC := L.image (fun p => (p.2.1, p.2.2))
  have hAB : AB.card ≤ n ^ 2 := by
    have hcard := Finset.card_le_univ AB
    rw [Fintype.card_prod] at hcard
    exact hcard.trans (by simpa only [pow_two] using Nat.mul_le_mul hα hβ)
  have hAC : AC.card ≤ n ^ 2 + e₁ := (arrayLexLeading_second_support S).trans hQ
  have hBC : BC.card ≤ n ^ 2 + e₂ := (arrayLexLeading_first_support S).trans hP
  have hsub : L ⊆ Combinatorics.triangles AB AC BC := by
    intro p hp
    exact (Combinatorics.mem_triangles_iff _ _ _ p).2
      ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  have hgraph := Combinatorics.positive_budget_finite (Combinatorics.transposeEdges AC)
    (Combinatorics.transposeEdges BC) AB (h := n) (e₁ := e₁) (e₂ := e₂) (e₃ := 0)
    (Nat.zero_le _) he₂ he₁ (by simpa using hAC) (by simpa using hBC) (by simpa using hAB)
  rw [Combinatorics.card_triangles_swap_outer] at hgraph
  rw [← card_arrayLexLeading S]
  exact (Finset.card_le_card hsub).trans hgraph

omit [LinearOrder α] [LinearOrder β] [LinearOrder γ] in
theorem array_triangle_bound (S : Submodule F (α × β × γ → F)) {n e₁ e₂ : ℕ}
    (hα : Fintype.card α ≤ n) (hβ : Fintype.card β ≤ n) (he₂ : e₂ ≤ e₁) (he₁ : e₁ ≤ n)
    (hP : Module.finrank F (arraySupport S) ≤ n ^ 2 + e₂)
    (hQ : Module.finrank F (arraySupport (S.map swapFirstTwo.toLinearMap)) ≤ n ^ 2 + e₁) :
    Module.finrank F S ≤ n ^ 3 + e₁ * e₂ := by
  let _ := LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective
  let _ := LinearOrder.lift' (Fintype.equivFin β) (Fintype.equivFin β).injective
  let _ := LinearOrder.lift' (Fintype.equivFin γ) (Fintype.equivFin γ).injective
  exact array_triangle_bound_ordered S hα hβ he₂ he₁ hP hQ

end Lemmata.Centroid.Linear
