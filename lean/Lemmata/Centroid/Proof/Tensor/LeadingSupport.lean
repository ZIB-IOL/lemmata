module

public import Lemmata.Centroid.Proof.Tensor.Support
public import Lemmata.Centroid.Proof.Linear.Leading
public import Mathlib.Order.PiLex

@[expose] public section

open Classical

noncomputable section

namespace Lemmata.Centroid.Tensor

variable {F ι : Type*} [Field F] [Fintype ι] [LinearOrder ι] [WellFoundedLT ι]
variable {V : ι → Type*} [∀ i, Fintype (V i)] [∀ i, LinearOrder (V i)]

local instance : DecidableEq ι := Classical.decEq _

def lexCoordinates : Tensor F ι V ≃ₗ[F] (Lex (∀ i, V i) → F) :=
  LinearEquiv.funCongrLeft F F ofLex

omit [Fintype ι] [LinearOrder ι] [WellFoundedLT ι] [∀ i, Fintype (V i)]
  [∀ i, LinearOrder (V i)] in
@[simp] theorem lexCoordinates_apply (T : Tensor F ι V) (x : Lex (∀ i, V i)) :
    lexCoordinates T x = T (ofLex x) := rfl

def lexLeading (S : Submodule F (Tensor F ι V)) : Finset (Lex (∀ i, V i)) :=
  Linear.leadingPositions (S.map lexCoordinates.toLinearMap)

theorem card_lexLeading (S : Submodule F (Tensor F ι V)) :
    (lexLeading S).card = Module.finrank F S := by
  rw [lexLeading, Linear.card_leadingPositions]
  exact lexCoordinates.finrank_map_eq S

theorem lexLeading_oneSupportAt {S : Submodule F (Tensor F ι V)}
    {x : Lex (∀ i, V i)} (hx : x ∈ lexLeading S) (i : ι) :
    ofLex x i ∈ Linear.leadingPositions (oneSupportAt S i) := by
  obtain ⟨f, ⟨T, hT, rfl⟩, hx, hzero⟩ := (Linear.mem_leadingPositions _ _).mp hx
  change T (ofLex x) ≠ 0 at hx
  apply (Linear.mem_leadingPositions _ _).mpr
  refine ⟨oneSlice i (ofLex x) T, Submodule.mem_iSup_of_mem (ofLex x) ⟨T, hT, rfl⟩, ?_, ?_⟩
  · simpa only [oneSlice_apply, lexCoordinates_apply, Function.update_eq_self] using hx
  · intro a ha
    have hlt : toLex (Function.update (ofLex x) i a) < x := by
      refine ⟨i, ?_, ?_⟩
      · intro j hj
        simp only [Pi.toLex_apply, Function.update_of_ne (ne_of_lt hj), Pi.ofLex_apply]
      · simpa using ha
    have hz := hzero (toLex (Function.update (ofLex x) i a)) hlt
    change T (Function.update (ofLex x) i a) = 0 at hz
    exact hz

theorem card_one_projection_le (S : Submodule F (Tensor F ι V)) (i : ι) :
    ((lexLeading S).image (fun x : Lex (∀ i, V i) => ofLex x i)).card ≤
      Module.finrank F (oneSupportAt S i) := by
  rw [← Linear.card_leadingPositions]
  apply Finset.card_le_card
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact lexLeading_oneSupportAt hx i

omit [Fintype ι] [WellFoundedLT ι] [∀ i, Fintype (V i)] in
theorem lex_update_lt_of_lt_minimum (i : ι) (a₀ : V i) (hmin : ∀ a, a₀ ≤ a)
    (x y : Lex (∀ i, V i))
    (hy : y < toLex (Function.update (ofLex x) i a₀)) :
    toLex (Function.update (ofLex y) i (ofLex x i)) < x := by
  obtain ⟨j, hj, hlt⟩ := hy
  have hji : j ≠ i := by
    intro h
    subst j
    exact (not_lt_of_ge (hmin _)) (by simpa using hlt)
  refine ⟨j, ?_, ?_⟩
  · intro k hk
    by_cases hki : k = i
    · subst k; simp
    · simpa only [Pi.toLex_apply, Pi.ofLex_apply, Function.update_of_ne hki] using hj k hk
  · simpa only [Pi.toLex_apply, Pi.ofLex_apply, Function.update_of_ne hji] using hlt

theorem lexLeading_oppositeSupportAt {S : Submodule F (Tensor F ι V)}
    {x : Lex (∀ i, V i)} (hx : x ∈ lexLeading S) (i : ι)
    (a₀ : V i) (hmin : ∀ a, a₀ ≤ a) :
    toLex (Function.update (ofLex x) i a₀) ∈ lexLeading (oppositeSupportAt S i) := by
  obtain ⟨f, ⟨T, hT, rfl⟩, hx, hzero⟩ := (Linear.mem_leadingPositions _ _).mp hx
  change T (ofLex x) ≠ 0 at hx
  apply (Linear.mem_leadingPositions _ _).mpr
  refine ⟨lexCoordinates (oppositeSlice i (ofLex x i) T), ?_, ?_, ?_⟩
  · exact ⟨_, Submodule.mem_iSup_of_mem (ofLex x i) ⟨T, hT, rfl⟩, rfl⟩
  · simpa only [lexCoordinates_apply, oppositeSlice_apply, ofLex_toLex,
      Function.update_idem, Function.update_eq_self] using hx
  · intro y hy
    have hlt := lex_update_lt_of_lt_minimum i a₀ hmin x y hy
    have hz := hzero (toLex (Function.update (ofLex y) i (ofLex x i))) hlt
    change T (Function.update (ofLex y) i (ofLex x i)) = 0 at hz
    exact hz

theorem card_opposite_projection_le (S : Submodule F (Tensor F ι V)) (i : ι)
    (a₀ : V i) (hmin : ∀ a, a₀ ≤ a) :
    ((lexLeading S).image (fun x : Lex (∀ i, V i) =>
      toLex (Function.update (ofLex x) i a₀))).card ≤
      Module.finrank F (oppositeSupportAt S i) := by
  rw [← card_lexLeading]
  apply Finset.card_le_card
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact lexLeading_oppositeSupportAt hx i a₀ hmin

theorem card_projection_le_oppositeSupportAt {J : Type*} [DecidableEq J]
    (S : Submodule F (Tensor F ι V)) (i : ι) (a₀ : V i) (hmin : ∀ a, a₀ ≤ a)
    (f : Lex (∀ i, V i) → J)
    (hf : ∀ x, f (toLex (Function.update (ofLex x) i a₀)) = f x) :
    ((lexLeading S).image f).card ≤ Module.finrank F (oppositeSupportAt S i) := by
  have himg : (lexLeading S).image f =
      ((lexLeading S).image (fun x => toLex (Function.update (ofLex x) i a₀))).image f := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x _
    exact (hf x).symm
  rw [himg]
  exact Finset.card_image_le.trans (card_opposite_projection_le S i a₀ hmin)

omit [Fintype ι] [LinearOrder ι] [WellFoundedLT ι] [∀ i, Fintype (V i)]
  [∀ i, LinearOrder (V i)] in
theorem project_update_of_ne (x : Lex (∀ i, V i)) (i j : ι) (a : V i) (hji : j ≠ i) :
    ofLex (toLex (Function.update (ofLex x) i a)) j = ofLex x j := by
  simp only [ofLex_toLex, Function.update_of_ne hji]

end Lemmata.Centroid.Tensor
