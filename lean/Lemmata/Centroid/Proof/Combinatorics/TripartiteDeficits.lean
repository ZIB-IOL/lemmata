module

public import Lemmata.Centroid.Proof.Combinatorics.TripartiteBudgets
public import Lemmata.Centroid.Proof.Combinatorics.TripartiteStarCount

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Combinatorics

noncomputable section

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [LinearOrder α] [LinearOrder β] [LinearOrder γ]

omit [Fintype α] [Fintype β] in
private theorem complete_card (U : Finset α) (V : Finset β) :
    (U ×ˢ V).card = ((U ×ˢ V).image Prod.fst).card * ((U ×ˢ V).image Prod.snd).card := by
  by_cases hU : U.Nonempty
  · by_cases hV : V.Nonempty
    · rw [Finset.product_image_fst hV, Finset.product_image_snd hU, Finset.card_product]
    · simp [Finset.not_nonempty_iff_eq_empty.mp hV]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hU]

omit [Fintype α] [Fintype β] in
theorem image_fst_lower {E : Finset (α × β)} (hE : DownClosed E) : LowerFinset (E.image Prod.fst) := by
  intro a a' haa ha'
  obtain ⟨p, hp, hpa⟩ := Finset.mem_image.mp ha'
  exact Finset.mem_image.mpr ⟨(a, p.2), hE (hpa.symm ▸ haa) le_rfl hp, rfl⟩

omit [Fintype α] [Fintype β] in
theorem image_snd_lower {E : Finset (α × β)} (hE : DownClosed E) : LowerFinset (E.image Prod.snd) := by
  have h := image_fst_lower hE.transpose
  simpa only [transposeEdges_image_fst] using h

def rowStar (h d : ℕ) : Finset (α × β) :=
  initialSegment α (h - 1) ×ˢ initialSegment β h ∪
    initialSegment α h ×ˢ initialSegment β (h - d)

theorem RowRectangular.subset_rowStar {E : Finset (α × β)} (hr : RowRectangular E)
    (hd : DownClosed E) {h d : ℕ} (hh : 2 ≤ h) (hdpos : 0 < d)
    (hleft : (E.image Prod.fst).card = h) (hright : (E.image Prod.snd).card = h)
    (hbudget : E.card + d ≤ h ^ 2) : E ⊆ rowStar (α := α) (β := β) h d := by
  have hnotcomplete (U : Finset α) (V : Finset β) (heq : E = U ×ˢ V) : False := by
    have hc := complete_card U V
    rw [← heq, hleft, hright] at hc
    nlinarith
  obtain ⟨U, W, V, Z, hdis, hW, hZ, heq⟩ := hr
  have hU : U.Nonempty := by
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    apply hnotcomplete W Z
    simpa only [hz, Finset.empty_product, Finset.empty_union] using heq
  have hZne : Z.Nonempty := by
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    apply hnotcomplete U V
    simpa only [hz, Finset.product_empty, Finset.union_empty] using heq
  have hWne : W.Nonempty := by
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    apply hnotcomplete U V
    simpa only [hz, Finset.empty_product, Finset.union_empty] using heq
  have hV : V.Nonempty := hZne.mono hZ
  have hWcard : W.card = 1 := by have := Finset.card_pos.mpr hWne; omega
  have hfst : E.image Prod.fst = U ∪ W := by
    rw [heq, Finset.image_union, Finset.product_image_fst hV, Finset.product_image_fst hZne]
  have hsnd : E.image Prod.snd = V := by
    rw [heq, Finset.image_union, Finset.product_image_snd hU, Finset.product_image_snd hWne,
      Finset.union_eq_left.mpr hZ]
  have hUcard : U.card = h - 1 := by
    rw [hfst, Finset.card_union_of_disjoint hdis, hWcard] at hleft
    omega
  have hUadd : U.card + 1 = h := by omega
  have hVcard : V.card = h := by simpa only [hsnd] using hright
  have hprod : Disjoint (U ×ˢ V) (W ×ˢ Z) := Finset.disjoint_left.2 (fun _ hx hy =>
    (Finset.disjoint_left.mp hdis) (Finset.mem_product.mp hx).1 (Finset.mem_product.mp hy).1)
  have hZbudget : Z.card + d ≤ h := by
    rw [heq, Finset.card_union_of_disjoint hprod, Finset.card_product,
      Finset.card_product, hWcard, one_mul, hVcard] at hbudget
    nlinarith
  have hZlt : Z.card < V.card := by omega
  have hVnot : ¬V ⊆ Z := fun hv => (not_le_of_gt hZlt) (Finset.card_le_card hv)
  obtain ⟨b, hbV, hbZ⟩ := Finset.not_subset.mp hVnot
  obtain ⟨w, hw⟩ := hWne
  have hwU : w ∉ U := fun h => (Finset.disjoint_left.mp hdis) h hw
  have hUlower : LowerFinset U := by
    intro a a' haa ha'
    have hp : (a', b) ∈ E := heq ▸ Finset.mem_union_left _ (Finset.mem_product.mpr ⟨ha', hbV⟩)
    have h := hd haa le_rfl hp
    rw [heq] at h
    rcases Finset.mem_union.mp h with h | h
    · exact (Finset.mem_product.mp h).1
    · exact False.elim (hbZ (Finset.mem_product.mp h).2)
  have hZlower : LowerFinset Z := by
    intro c c' hcc hc'
    have hp : (w, c') ∈ E := heq ▸ Finset.mem_union_right _ (Finset.mem_product.mpr ⟨hw, hc'⟩)
    have h := hd le_rfl hcc hp
    rw [heq] at h
    rcases Finset.mem_union.mp h with h | h
    · exact False.elim (hwU (Finset.mem_product.mp h).1)
    · exact (Finset.mem_product.mp h).2
  have hUeq : U = initialSegment α (h - 1) := by
    rw [lower_eq_initialSegment hUlower, hUcard]
  have hVeq : V = initialSegment β h := by
    rw [← hsnd, lower_eq_initialSegment (image_snd_lower hd), hright]
  have hUW : U ∪ W = initialSegment α h := by
    rw [← hfst, lower_eq_initialSegment (image_fst_lower hd), hleft]
  have hZsub : Z ⊆ initialSegment β (h - d) := by
    rw [lower_eq_initialSegment hZlower]
    exact initialSegment_mono (by omega)
  intro p hp
  rw [heq] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · apply Finset.mem_union_left
    simpa only [← hUeq, ← hVeq] using hp
  · apply Finset.mem_union_right
    exact Finset.mem_product.mpr ⟨hUW ▸ Finset.mem_union_right U (Finset.mem_product.mp hp).1,
      hZsub (Finset.mem_product.mp hp).2⟩

theorem Rectangular.subset_star {E : Finset (α × β)} (hr : Rectangular E)
    (hd : DownClosed E) {h d : ℕ} (hh : 2 ≤ h) (hdpos : 0 < d)
    (hleft : (E.image Prod.fst).card = h) (hright : (E.image Prod.snd).card = h)
    (hbudget : E.card + d ≤ h ^ 2) :
    E ⊆ rowStar (α := α) (β := β) h d ∨ E ⊆ transposeEdges (rowStar (α := β) (β := α) h d) := by
  rcases hr with hr | hr
  · exact Or.inl (hr.subset_rowStar hd hh hdpos hleft hright hbudget)
  · right
    have hsub := hr.subset_rowStar hd.transpose hh hdpos
      (by simpa only [transposeEdges_image_fst] using hright)
      (by simpa only [transposeEdges_image_snd] using hleft)
      (by simpa only [card_transposeEdges] using hbudget)
    intro p hp
    exact (mem_transposeEdges' _ p).2 (hsub ((mem_transposeEdges E p.1 p.2).2 hp))

private theorem rectangle_large_side {r s e h : ℕ} (hh : 1 ≤ h)
    (hr : h + 1 ≤ r) (hs : h ≤ s) (hcard : r * s + 1 ≤ e + max r s) : h ^ 2 ≤ e := by
  have hr' : (h : ℤ) + 1 ≤ r := by exact_mod_cast hr
  have hs' : (h : ℤ) ≤ s := by exact_mod_cast hs
  have hh' : (1 : ℤ) ≤ h := by exact_mod_cast hh
  by_cases hrs : r ≤ s
  · rw [max_eq_right hrs] at hcard
    have hc : (r : ℤ) * s + 1 ≤ e + s := by exact_mod_cast hcard
    have hp := mul_nonneg (sub_nonneg.mpr hr') (Int.natCast_nonneg s)
    have hq := mul_nonneg (Int.natCast_nonneg h) (sub_nonneg.mpr hs')
    have hz : (h : ℤ) ^ 2 ≤ e := by nlinarith
    exact_mod_cast hz
  · rw [max_eq_left (le_of_not_ge hrs)] at hcard
    have hc : (r : ℤ) * s + 1 ≤ e + r := by exact_mod_cast hcard
    have hp := mul_nonneg (sub_nonneg.mpr hr') (show (0 : ℤ) ≤ (s : ℤ) - 1 by omega)
    have hq := mul_nonneg (show (0 : ℤ) ≤ (h : ℤ) + 1 by omega) (sub_nonneg.mpr hs')
    have hz : (h : ℤ) ^ 2 ≤ e := by nlinarith
    exact_mod_cast hz

omit [Fintype α] [Fintype β] in
theorem rectangular_equal_sizes {E : Finset (α × β)} (hr : Rectangular E) {h d : ℕ}
    (hh : 1 ≤ h) (hd : 0 < d) (hleft : h ≤ (E.image Prod.fst).card)
    (hright : h ≤ (E.image Prod.snd).card) (hbudget : E.card + d ≤ h ^ 2) :
    (E.image Prod.fst).card = h ∧ (E.image Prod.snd).card = h := by
  have hne : E.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he] at hleft
    omega
  have hcard := hr.card_bound hne
  have hfirst : (E.image Prod.fst).card ≤ h := by
    by_contra hn
    have hp := rectangle_large_side (r := (E.image Prod.fst).card)
      (s := (E.image Prod.snd).card) (e := E.card) hh (by omega) hright hcard
    omega
  have hsecond : (E.image Prod.snd).card ≤ h := by
    by_contra hn
    have hp := rectangle_large_side (r := (E.image Prod.snd).card)
      (s := (E.image Prod.fst).card) (e := E.card) hh (by omega) hleft
      (by simpa only [mul_comm, max_comm] using hcard)
    omega
  omega

theorem card_triangles_first_support (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) :
    (triangles AB AC BC).card ≤ (AC.image Prod.fst).card * BC.card := by
  rw [← card_triangles_cycle AB AC BC, card_triangles_neighbors]
  calc
    _ ≤ ∑ _p ∈ BC, (AC.image Prod.fst).card := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.card_le_card
      intro a ha
      have h := (mem_neighbors (transposeEdges AC) p.2 a).1 (Finset.mem_inter.mp ha).2
      exact Finset.mem_image.mpr ⟨(a, p.2), (mem_transposeEdges AC a p.2).1 h, rfl⟩
    _ = _ := by simp [mul_comm]

private theorem small_color_deficit {T e h d : ℕ} (hh : 1 ≤ h)
    (hT : T ≤ (h - 1) * e) (he : e + d ≤ h ^ 2) :
    T + 3 * h * d ≤ h ^ 3 + d ^ 2 + d := by
  have ht' : (T : ℤ) ≤ ((h : ℤ) - 1) * e := by
    have hz : (T : ℤ) ≤ ((h - 1 : ℕ) : ℤ) * e := by exact_mod_cast hT
    simpa only [Nat.cast_sub hh, Nat.cast_one] using hz
  have he' : (e : ℤ) + d ≤ (h : ℤ) ^ 2 := by exact_mod_cast he
  have hh' : (1 : ℤ) ≤ h := by exact_mod_cast hh
  have hp := mul_le_mul_of_nonneg_left he' (show (0 : ℤ) ≤ (h : ℤ) - 1 by omega)
  have hsq := sq_nonneg ((h : ℤ) - d)
  have hz : (T : ℤ) + 3 * h * d ≤ (h : ℤ) ^ 3 + (d : ℤ) ^ 2 + d := by nlinarith
  exact_mod_cast hz

def prefixStarChain (h d : ℕ) (hcap : h ≤ Fintype.card α) (hh : 1 ≤ h)
    (hd : 0 < d) (hdle : d ≤ h) : StarChain α h d where
  full := initialSegment α h
  tail := initialSegment α h \ initialSegment α (h - d)
  center := initialSegment α h \ initialSegment α (h - 1)
  center_tail := by
    intro a ha
    rcases Finset.mem_sdiff.mp ha with ⟨hfull, hnot⟩
    exact Finset.mem_sdiff.mpr ⟨hfull, fun hsmall =>
      hnot (initialSegment_mono (by omega : h - d ≤ h - 1) hsmall)⟩
  tail_full := Finset.sdiff_subset
  card_full := by simp only [card_initialSegment, min_eq_right hcap]
  card_tail := by
    have hc := Finset.card_sdiff_add_card_eq_card (initialSegment_mono (α := α) (Nat.sub_le h d))
    rw [card_initialSegment, card_initialSegment, min_eq_right hcap,
      min_eq_right ((Nat.sub_le h d).trans hcap)] at hc
    omega
  card_center := by
    have hc := Finset.card_sdiff_add_card_eq_card (initialSegment_mono (α := α) (Nat.sub_le h 1))
    rw [card_initialSegment, card_initialSegment, min_eq_right hcap,
      min_eq_right ((Nat.sub_le h 1).trans hcap)] at hc
    omega

def orientedStar (h d : ℕ) (o : Bool) : Finset (α × β) :=
  if o then transposeEdges (rowStar (α := β) (β := α) h d) else rowStar h d

theorem star_triangle_bound {h d : ℕ} (hα : h ≤ Fintype.card α) (hβ : h ≤ Fintype.card β)
    (hγ : h ≤ Fintype.card γ) (hh : 1 ≤ h) (hd : 0 < d) (hdle : d ≤ h)
    (o₁ o₂ o₃ : Bool) :
    (triangles (orientedStar (α := α) (β := β) h d o₁)
      (orientedStar (α := α) (β := γ) h d o₂) (orientedStar (α := β) (β := γ) h d o₃)).card +
      3 * h * d ≤ h ^ 3 + d ^ 2 + d := by
  let A := prefixStarChain h d hα hh hd hdle
  let B := prefixStarChain h d hβ hh hd hdle
  let C := prefixStarChain h d hγ hh hd hdle
  have heq : triangles (orientedStar (α := α) (β := β) h d o₁)
      (orientedStar (α := α) (β := γ) h d o₂) (orientedStar (α := β) (β := γ) h d o₃) =
      StarChain.remaining A B C o₁ o₂ o₃ := by
    ext p
    cases o₁ <;> cases o₂ <;> cases o₃ <;>
      simp only [mem_triangles_iff, orientedStar, Bool.false_eq_true, ite_false, ite_true,
        mem_transposeEdges', rowStar, StarChain.remaining, StarChain.holesAB, StarChain.holesAC,
        StarChain.holesBC, A, B, C, prefixStarChain, Finset.mem_union, Finset.mem_product,
        Finset.mem_sdiff, mem_initialSegment] <;> omega
  rw [heq]
  exact StarChain.remaining_bound A B C o₁ o₂ o₃

theorem equal_deficit_small_first (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) {h d : ℕ} (hh : 1 ≤ h)
    (hsmall : (AC.image Prod.fst).card ≤ h - 1) (hBC : BC.card + d ≤ h ^ 2) :
    (triangles AB AC BC).card + 3 * h * d ≤ h ^ 3 + d ^ 2 + d :=
  small_color_deficit hh ((card_triangles_first_support AB AC BC).trans
    (Nat.mul_le_mul_right BC.card hsmall)) hBC

theorem equal_deficit_additive (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) {h d : ℕ} (hh : 2 ≤ h) (hdle : d ≤ h)
    (hAB : AB.card + d ≤ h ^ 2) (hAC : AC.card + d ≤ h ^ 2) (hBC : BC.card + d ≤ h ^ 2) :
    (triangles AB AC BC).card + 3 * h * d ≤ h ^ 3 + d ^ 2 + d := by
  by_cases hd : d = 0
  · have hp := positive_budget AB AC BC (h := h) (e₁ := 0) (e₂ := 0) (e₃ := 0)
      le_rfl le_rfl (by omega) (by simpa [hd] using hAB) (by simpa [hd] using hAC) (by simpa [hd] using hBC)
    simpa only [hd, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0)] using hp
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  obtain ⟨A, B, C, hA, hB, hC, htri, hrA, hrB, hrC, hdA, hdB, hdC, hfirst, hsecond, hthird⟩ :=
    exists_active_rectangular AB AC BC
  have hAb : A.card + d ≤ h ^ 2 := by omega
  have hBb : B.card + d ≤ h ^ 2 := by omega
  have hCb : C.card + d ≤ h ^ 2 := by omega
  apply (Nat.add_le_add_right htri _).trans
  by_cases hα : h ≤ (A.image Prod.fst).card
  · by_cases hβ : h ≤ (A.image Prod.snd).card
    · by_cases hγ : h ≤ (B.image Prod.snd).card
      · have hAs := rectangular_equal_sizes hrA (by omega) hdpos hα hβ hAb
        have hBs := rectangular_equal_sizes hrB (by omega) hdpos (hfirst ▸ hα) hγ hBb
        have hCs : (C.image Prod.fst).card = h ∧ (C.image Prod.snd).card = h :=
          ⟨hsecond ▸ hAs.2, hthird ▸ hBs.2⟩
        have hAstar : ∃ o, A ⊆ orientedStar (α := α) (β := β) h d o := by
          rcases hrA.subset_star hdA hh hdpos hAs.1 hAs.2 hAb with h | h
          · exact ⟨false, h⟩
          · exact ⟨true, h⟩
        have hBstar : ∃ o, B ⊆ orientedStar (α := α) (β := γ) h d o := by
          rcases hrB.subset_star hdB hh hdpos hBs.1 hBs.2 hBb with h | h
          · exact ⟨false, h⟩
          · exact ⟨true, h⟩
        have hCstar : ∃ o, C ⊆ orientedStar (α := β) (β := γ) h d o := by
          rcases hrC.subset_star hdC hh hdpos hCs.1 hCs.2 hCb with h | h
          · exact ⟨false, h⟩
          · exact ⟨true, h⟩
        obtain ⟨o₁, hsA⟩ := hAstar
        obtain ⟨o₂, hsB⟩ := hBstar
        obtain ⟨o₃, hsC⟩ := hCstar
        have hsub : triangles A B C ⊆ triangles (orientedStar h d o₁) (orientedStar h d o₂)
            (orientedStar h d o₃) := by
          intro p hp
          have h := (mem_triangles_iff A B C p).1 hp
          exact (mem_triangles_iff _ _ _ p).2 ⟨hsA h.1, hsB h.2.1, hsC h.2.2⟩
        apply (Nat.add_le_add_right (Finset.card_le_card hsub) _).trans
        apply star_triangle_bound _ _ _ (by omega) hdpos hdle o₁ o₂ o₃
        · simpa only [hAs.1] using Finset.card_le_univ (A.image Prod.fst)
        · simpa only [hAs.2] using Finset.card_le_univ (A.image Prod.snd)
        · simpa only [hBs.2] using Finset.card_le_univ (B.image Prod.snd)
      · have hp := equal_deficit_small_first (transposeEdges B) (transposeEdges C) A (by omega)
          (by simpa only [transposeEdges_image_fst, ← hthird] using (show (B.image Prod.snd).card ≤ h - 1 by omega)) hAb
        simpa only [card_triangles_swap_outer] using hp
    · have hp := equal_deficit_small_first (transposeEdges A) C B (by omega)
        (hsecond ▸ (show (A.image Prod.snd).card ≤ h - 1 by omega)) hBb
      simpa only [card_triangles_swap_first] using hp
  · exact equal_deficit_small_first A B C (by omega)
      (hfirst ▸ (show (A.image Prod.fst).card ≤ h - 1 by omega)) hCb

theorem equal_deficit (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) {h d : ℕ} (hh : 2 ≤ h) (hdle : d ≤ h)
    (hAB : AB.card ≤ h ^ 2 - d) (hAC : AC.card ≤ h ^ 2 - d) (hBC : BC.card ≤ h ^ 2 - d) :
    (triangles AB AC BC).card ≤ h ^ 3 + d ^ 2 + d - 3 * h * d := by
  have hdsq : d ≤ h ^ 2 := hdle.trans (by nlinarith)
  exact Nat.le_sub_of_add_le (equal_deficit_additive AB AC BC hh hdle (by omega) (by omega) (by omega))

omit [LinearOrder α] [LinearOrder β] [LinearOrder γ] in
theorem positive_budget_finite (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) {h e₁ e₂ e₃ : ℕ}
    (he₃ : e₃ ≤ e₂) (he₂ : e₂ ≤ e₁) (he₁ : e₁ ≤ h)
    (hAB : AB.card ≤ h ^ 2 + e₁) (hAC : AC.card ≤ h ^ 2 + e₂)
    (hBC : BC.card ≤ h ^ 2 + e₃) : (triangles AB AC BC).card ≤ h ^ 3 + e₁ * e₂ := by
  let _ := LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective
  let _ := LinearOrder.lift' (Fintype.equivFin β) (Fintype.equivFin β).injective
  let _ := LinearOrder.lift' (Fintype.equivFin γ) (Fintype.equivFin γ).injective
  exact positive_budget AB AC BC he₃ he₂ he₁ hAB hAC hBC

omit [LinearOrder α] [LinearOrder β] [LinearOrder γ] in
theorem equal_deficit_finite (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) {h d : ℕ} (hh : 2 ≤ h) (hdle : d ≤ h)
    (hAB : AB.card ≤ h ^ 2 - d) (hAC : AC.card ≤ h ^ 2 - d) (hBC : BC.card ≤ h ^ 2 - d) :
    (triangles AB AC BC).card ≤ h ^ 3 + d ^ 2 + d - 3 * h * d := by
  let _ := LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective
  let _ := LinearOrder.lift' (Fintype.equivFin β) (Fintype.equivFin β).injective
  let _ := LinearOrder.lift' (Fintype.equivFin γ) (Fintype.equivFin γ).injective
  exact equal_deficit AB AC BC hh hdle hAB hAC hBC

end

end Lemmata.Centroid.Combinatorics
