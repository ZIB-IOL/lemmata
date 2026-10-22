module

public import Lemmata.Centroid.Proof.Combinatorics.TripartiteCompression
public import Mathlib.Data.Fintype.Sort
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.Linarith

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Combinatorics

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β]

def LowerFinset (S : Finset α) : Prop := ∀ ⦃a b : α⦄, a ≤ b → b ∈ S → a ∈ S

omit [Fintype α] in
theorem LowerFinset.total {S T : Finset α} (hS : LowerFinset S) (hT : LowerFinset T) :
    S ⊆ T ∨ T ⊆ S := by
  by_cases hsub : S ⊆ T
  · exact Or.inl hsub
  · right
    obtain ⟨a, ha, hat⟩ := Finset.not_subset.mp hsub
    intro b hb
    by_cases hba : b ≤ a
    · exact hS hba ha
    · exact False.elim (hat (hT (le_of_lt (lt_of_not_ge hba)) hb))

omit [Fintype α] in
theorem LowerFinset.subset_of_card_le {S T : Finset α}
    (hS : LowerFinset S) (hT : LowerFinset T) (hcard : S.card ≤ T.card) : S ⊆ T := by
  rcases hS.total hT with h | h
  · exact h
  · exact (Finset.eq_of_subset_of_card_le h hcard).symm.subset

def orderRank (a : α) : ℕ := ((monoEquivOfFin α rfl).symm a).val

theorem orderRank_strictMono : StrictMono (orderRank (α := α)) :=
  fun _ _ h => (monoEquivOfFin α rfl).symm.strictMono h

def initialSegment (α : Type*) [Fintype α] [LinearOrder α] (k : ℕ) : Finset α :=
  (Finset.univ.filter fun a : Fin (Fintype.card α) => a.val < k).map
    (monoEquivOfFin α rfl).toEmbedding

@[simp] theorem mem_initialSegment (a : α) (k : ℕ) : a ∈ initialSegment α k ↔ orderRank a < k := by
  simp [initialSegment, orderRank]

@[simp] theorem card_initialSegment (k : ℕ) : (initialSegment α k).card = min (Fintype.card α) k := by
  simp only [initialSegment, Finset.card_map, Fin.card_filter_val_lt]

theorem initialSegment_lower (k : ℕ) : LowerFinset (initialSegment α k) := by
  intro a b hab hb
  exact (mem_initialSegment a k).2 ((orderRank_strictMono.monotone hab).trans_lt ((mem_initialSegment b k).1 hb))

theorem initialSegment_mono {k l : ℕ} (h : k ≤ l) : initialSegment α k ⊆ initialSegment α l := by
  intro a ha
  exact (mem_initialSegment a l).2 (((mem_initialSegment a k).1 ha).trans_le h)

@[simp] theorem initialSegment_zero : initialSegment α 0 = ∅ := by
  ext a
  simp

theorem lower_eq_initialSegment {S : Finset α} (hS : LowerFinset S) : S = initialSegment α S.card := by
  have hcard : (initialSegment α S.card).card = S.card := by
    rw [card_initialSegment, min_eq_right (Finset.card_le_univ S)]
  exact Finset.Subset.antisymm
    (hS.subset_of_card_le (initialSegment_lower _) hcard.ge)
    ((initialSegment_lower _).subset_of_card_le hS hcard.le)

def RowRectangular (E : Finset (α × β)) : Prop :=
  ∃ (U W : Finset α) (V Z : Finset β), Disjoint U W ∧ W.card ≤ 1 ∧ Z ⊆ V ∧
    E = U ×ˢ V ∪ W ×ˢ Z

def Rectangular (E : Finset (α × β)) : Prop :=
  RowRectangular E ∨ RowRectangular (transposeEdges E)

def rowFill (width m : ℕ) : Finset (α × β) :=
  initialSegment α (m / width) ×ˢ initialSegment β width ∪
    (initialSegment α (m / width + 1) \ initialSegment α (m / width)) ×ˢ initialSegment β (m % width)

private theorem initialSegment_step_card (q : ℕ) :
    (initialSegment α (q + 1) \ initialSegment α q).card ≤ 1 := by
  have h := Finset.card_sdiff_add_card_eq_card (initialSegment_mono (α := α) (Nat.le_succ q))
  simp only [Nat.succ_eq_add_one] at h
  rw [card_initialSegment, card_initialSegment] at h
  omega

theorem rowFill_rectangular (width m : ℕ) (hw : 0 < width) :
    RowRectangular (rowFill (α := α) (β := β) width m) := by
  refine ⟨_, _, _, _, ?_, initialSegment_step_card _, ?_, rfl⟩
  · exact Finset.disjoint_left.2 (fun _ hx hy => (Finset.mem_sdiff.mp hy).2 hx)
  · exact initialSegment_mono (Nat.mod_lt m hw).le

theorem rowFill_card {width m : ℕ} (hw : 0 < width) (hwidth : width ≤ Fintype.card β)
    (hm : m ≤ Fintype.card α * width) : (rowFill (α := α) (β := β) width m).card = m := by
  have hq : m / width ≤ Fintype.card α := by
    have hd := Nat.div_mul_le_self m width
    nlinarith
  have hr : m % width < width := Nat.mod_lt m hw
  have hdiv := Nat.mod_add_div m width
  have hdis : Disjoint (initialSegment α (m / width) ×ˢ initialSegment β width)
      ((initialSegment α (m / width + 1) \ initialSegment α (m / width)) ×ˢ initialSegment β (m % width)) := by
    apply Finset.disjoint_left.2
    intro p hp hq
    exact (Finset.mem_sdiff.mp (Finset.mem_product.mp hq).1).2 (Finset.mem_product.mp hp).1
  rw [rowFill, Finset.card_union_of_disjoint hdis, Finset.card_product, Finset.card_product,
    card_initialSegment, card_initialSegment, card_initialSegment, min_eq_right hq, min_eq_right hwidth,
    min_eq_right (hr.le.trans hwidth)]
  have hstep := Finset.card_sdiff_add_card_eq_card (initialSegment_mono (α := α) (Nat.le_succ (m / width)))
  simp only [Nat.succ_eq_add_one] at hstep
  rw [card_initialSegment, card_initialSegment, min_eq_right hq] at hstep
  by_cases hq' : m / width < Fintype.card α
  · rw [min_eq_right (by omega : m / width + 1 ≤ Fintype.card α)] at hstep
    have hstep' : (initialSegment α (m / width + 1) \ initialSegment α (m / width)).card = 1 := by omega
    rw [hstep', one_mul]
    nlinarith
  · have hqeq : m / width = Fintype.card α := by omega
    have hrem : m % width = 0 := by
      rw [hqeq] at hdiv
      rw [Nat.mul_comm width] at hdiv
      omega
    rw [hrem, mul_zero, add_zero]
    nlinarith

theorem rowFill_downClosed {width m : ℕ} (hw : 0 < width) :
    DownClosed (rowFill (α := α) (β := β) width m) := by
  intro a a' b b' haa hbb hp
  have hra := orderRank_strictMono.monotone haa
  have hrb := orderRank_strictMono.monotone hbb
  simp only [rowFill, Finset.mem_union, Finset.mem_product, Finset.mem_sdiff, mem_initialSegment] at hp ⊢
  rcases hp with ⟨ha, hb⟩ | ⟨⟨ha, hna⟩, hb⟩
  · exact Or.inl ⟨hra.trans_lt ha, hrb.trans_lt hb⟩
  · by_cases hqa : orderRank a < m / width
    · exact Or.inl ⟨hqa, (hrb.trans_lt hb).trans_le (Nat.mod_lt m hw).le⟩
    · exact Or.inr ⟨⟨hra.trans_lt ha, hqa⟩, hrb.trans_lt hb⟩

theorem rowFill_subset {width m r s : ℕ} (hw : 0 < width)
    (hwidth : width ≤ s) (hm : m ≤ r * width) :
    rowFill (α := α) (β := β) width m ⊆ initialSegment α r ×ˢ initialSegment β s := by
  have hq : m / width ≤ r := by
    have hd := Nat.div_mul_le_self m width
    nlinarith
  intro p hp
  simp only [rowFill, Finset.mem_union, Finset.mem_product, Finset.mem_sdiff, mem_initialSegment] at hp ⊢
  rcases hp with ⟨ha, hb⟩ | ⟨⟨ha, hna⟩, hb⟩
  · exact ⟨ha.trans_le hq, hb.trans_le hwidth⟩
  · have hrem : 0 < m % width := (Nat.zero_le _).trans_lt hb
    have hlt : m / width < r := by
      have hd := Nat.mod_add_div m width
      rw [Nat.mul_comm width] at hd
      by_contra h
      have heq : m / width = r := by omega
      rw [heq] at hd
      omega
    exact ⟨ha.trans_le (by omega), (hb.trans_le (Nat.mod_lt m hw).le).trans_le hwidth⟩

theorem rectangle_subset_rowFill {width m r s : ℕ} (hw : 0 < width)
    (hs : s ≤ width) (hm : r * width ≤ m) :
    initialSegment α r ×ˢ initialSegment β s ⊆ rowFill (α := α) (β := β) width m := by
  have hr : r ≤ m / width := (Nat.le_div_iff_mul_le hw).2 hm
  intro p hp
  apply Finset.mem_union_left
  exact Finset.mem_product.mpr ⟨initialSegment_mono hr (Finset.mem_product.mp hp).1,
    initialSegment_mono hs (Finset.mem_product.mp hp).2⟩

omit [Fintype α] [Fintype β] in
theorem DownClosed.transpose {E : Finset (α × β)} (h : DownClosed E) :
    DownClosed (transposeEdges E) := by
  intro u v b c huv hbc hvc
  exact (mem_transposeEdges E b u).2 (h hbc huv ((mem_transposeEdges E c v).1 hvc))

theorem exists_rectangular_between {r s R S m : ℕ} (hr : r ≤ R) (hs : s ≤ S)
    (hR : R ≤ Fintype.card α) (hS : S ≤ Fintype.card β)
    (hinner : r * s ≤ m) (houter : m ≤ R * S) :
    ∃ E : Finset (α × β), E.card = m ∧ Rectangular E ∧ DownClosed E ∧
      initialSegment α r ×ˢ initialSegment β s ⊆ E ∧ E ⊆ initialSegment α R ×ˢ initialSegment β S := by
  by_cases hm : m = 0
  · have hempty : initialSegment α r ×ˢ initialSegment β s = ∅ := by
      apply Finset.card_eq_zero.1
      rw [Finset.card_product, card_initialSegment, card_initialSegment,
        min_eq_right (hr.trans hR), min_eq_right (hs.trans hS)]
      omega
    refine ⟨∅, hm.symm, Or.inl ?_, ?_, ?_, Finset.empty_subset _⟩
    · exact ⟨∅, ∅, ∅, ∅, by simp, by simp, by simp, by simp⟩
    · intro _ _ _ _ _ _ h
      exact False.elim (Finset.notMem_empty _ h)
    · rw [hempty]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hRpos : 0 < R := by nlinarith
    by_cases hrow : 0 < s ∧ m ≤ R * s
    · refine ⟨rowFill s m, rowFill_card hrow.1 (hs.trans hS) ?_,
        Or.inl (rowFill_rectangular s m hrow.1), rowFill_downClosed hrow.1,
        rectangle_subset_rowFill hrow.1 le_rfl hinner, rowFill_subset hrow.1 hs hrow.2⟩
      exact hrow.2.trans (Nat.mul_le_mul_right s hR)
    · have hmore : s * R ≤ m := by
        by_cases hspos : 0 < s
        · have h := (not_and.mp hrow) hspos
          nlinarith
        · have hsz : s = 0 := by omega
          simp [hsz]
      refine ⟨transposeEdges (rowFill (α := β) (β := α) R m), ?_, ?_,
        (rowFill_downClosed hRpos).transpose, ?_, ?_⟩
      · rw [card_transposeEdges]
        exact rowFill_card hRpos hR (by nlinarith)
      · exact Or.inr (by
          simpa only [transposeEdges_transposeEdges] using rowFill_rectangular
            (α := β) (β := α) R m hRpos)
      · intro p hp
        apply (mem_transposeEdges' _ p).2
        exact rectangle_subset_rowFill hRpos hr hmore
          (Finset.mem_product.mpr ⟨(Finset.mem_product.mp hp).2, (Finset.mem_product.mp hp).1⟩)
      · intro p hp
        have h := rowFill_subset (α := β) (β := α) hRpos le_rfl
          (show m ≤ S * R by nlinarith) ((mem_transposeEdges' _ p).1 hp)
        exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp h).2, (Finset.mem_product.mp h).1⟩

private theorem sum_le_sum_threshold {ι : Type*} (E E' : Finset ι) (w : ι → ℕ) (t : ℕ)
    (hcard : E.card = E'.card) (hhigh : ∀ p, t < w p → p ∈ E')
    (hlow : ∀ p ∈ E', t ≤ w p) : (∑ p ∈ E, w p) ≤ ∑ p ∈ E', w p := by
  have hc := Finset.card_sdiff_add_card_inter E E'
  have hc' := Finset.card_sdiff_add_card_inter E' E
  rw [Finset.inter_comm E' E] at hc'
  have hdiff : (E \ E').card = (E' \ E).card := by omega
  have hsum : (∑ p ∈ E \ E', w p) ≤ ∑ p ∈ E' \ E, w p := by
    calc
      _ ≤ ∑ _p ∈ E \ E', t := by
        apply Finset.sum_le_sum
        intro p hp
        exact le_of_not_gt (fun h => (Finset.mem_sdiff.mp hp).2 (hhigh p h))
      _ = (E \ E').card * t := by simp
      _ = (E' \ E).card * t := by rw [hdiff]
      _ = ∑ _p ∈ E' \ E, t := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        exact hlow p (Finset.mem_sdiff.mp hp).1
  have he : (∑ p ∈ E \ E', w p) + ∑ p ∈ E ∩ E', w p = ∑ p ∈ E, w p := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter E E'), Finset.sdiff_union_inter]
  have he' : (∑ p ∈ E' \ E, w p) + ∑ p ∈ E ∩ E', w p = ∑ p ∈ E', w p := by
    rw [Finset.inter_comm E E', ← Finset.sum_union (Finset.disjoint_sdiff_inter E' E),
      Finset.sdiff_union_inter]
  omega

private theorem exists_weight_threshold {ι : Type*} [Fintype ι] (w : ι → ℕ) (cap m : ℕ)
    (hcap : ∀ p, w p ≤ cap) (hm : m ≤ Fintype.card ι) :
    ∃ t, (Finset.univ.filter fun p => t < w p).card ≤ m ∧
      m ≤ (Finset.univ.filter fun p => t ≤ w p).card := by
  let P : ℕ → Prop := fun t => m ≤ (Finset.univ.filter fun p => t ≤ w p).card
  let t := Nat.findGreatest P cap
  have ht : t ≤ cap := Nat.findGreatest_le _
  have hlow : P t := Nat.findGreatest_spec (m := 0) (by omega) (by simpa [P] using hm)
  refine ⟨t, ?_, hlow⟩
  by_cases hnext : t + 1 ≤ cap
  · have hnot : ¬P (t + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self t) hnext
    have heq : (Finset.univ.filter fun p => t < w p) =
        (Finset.univ.filter fun p => t + 1 ≤ w p) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [heq]
    exact Nat.le_of_lt (Nat.lt_of_not_ge hnot)
  · have heq : (Finset.univ.filter fun p => t < w p) = ∅ := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      have := hcap p
      omega
    simp [heq]

theorem exists_rectangular_optimal (a : α → ℕ) (b : β → ℕ)
    (ha : Antitone a) (hb : Antitone b) (cap : ℕ) (hcap : ∀ i, a i ≤ cap)
    (E : Finset (α × β)) :
    ∃ E' : Finset (α × β), E'.card = E.card ∧ Rectangular E' ∧ DownClosed E' ∧
      (∑ p ∈ E, min (a p.1) (b p.2)) ≤ ∑ p ∈ E', min (a p.1) (b p.2) := by
  let w : α × β → ℕ := fun p => min (a p.1) (b p.2)
  obtain ⟨t, hinner, houter⟩ := exists_weight_threshold w cap E.card
    (fun p => (Nat.min_le_left _ _).trans (hcap p.1)) (Finset.card_le_univ E)
  let U : Finset α := Finset.univ.filter fun i => t < a i
  let V : Finset β := Finset.univ.filter fun j => t < b j
  let A : Finset α := Finset.univ.filter fun i => t ≤ a i
  let B : Finset β := Finset.univ.filter fun j => t ≤ b j
  have hU : LowerFinset U := by
    intro i j hij hj
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ((Finset.mem_filter.mp hj).2).trans_le (ha hij)⟩
  have hV : LowerFinset V := by
    intro i j hij hj
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ((Finset.mem_filter.mp hj).2).trans_le (hb hij)⟩
  have hA : LowerFinset A := by
    intro i j hij hj
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ((Finset.mem_filter.mp hj).2).trans (ha hij)⟩
  have hB : LowerFinset B := by
    intro i j hij hj
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ((Finset.mem_filter.mp hj).2).trans (hb hij)⟩
  have hUA : U ⊆ A := by
    intro i hi
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.le⟩
  have hVB : V ⊆ B := by
    intro i hi
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.le⟩
  have hi : (Finset.univ.filter fun p => t < w p) = U ×ˢ V := by
    ext p
    simp [w, U, V, lt_min_iff]
  have ho : (Finset.univ.filter fun p => t ≤ w p) = A ×ˢ B := by
    ext p
    simp [w, A, B]
  rw [hi, Finset.card_product] at hinner
  rw [ho, Finset.card_product] at houter
  obtain ⟨E', hcard, hrect, hdown, hcontain, hsubset⟩ := exists_rectangular_between
    (Finset.card_le_card hUA) (Finset.card_le_card hVB)
    (Finset.card_le_univ A) (Finset.card_le_univ B) hinner houter
  rw [← lower_eq_initialSegment hU, ← lower_eq_initialSegment hV] at hcontain
  rw [← lower_eq_initialSegment hA, ← lower_eq_initialSegment hB] at hsubset
  refine ⟨E', hcard, hrect, hdown, sum_le_sum_threshold E E' w t hcard.symm ?_ ?_⟩
  · intro p hp
    apply hcontain
    rw [← hi]
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩
  · intro p hp
    have h := hsubset hp
    rw [← ho] at h
    exact (Finset.mem_filter.mp h).2

def restrictEdges (E : Finset (α × β)) (A : Finset α) (B : Finset β) : Finset (α × β) :=
  E ∩ A ×ˢ B

omit [Fintype α] [Fintype β] in
theorem RowRectangular.restrict {E : Finset (α × β)} (h : RowRectangular E)
    (A : Finset α) (B : Finset β) : RowRectangular (restrictEdges E A B) := by
  obtain ⟨U, W, V, Z, hdis, hW, hZ, rfl⟩ := h
  refine ⟨U ∩ A, W ∩ A, V ∩ B, Z ∩ B, ?_, ?_, ?_, ?_⟩
  · exact hdis.mono Finset.inter_subset_left Finset.inter_subset_left
  · exact (Finset.card_le_card Finset.inter_subset_left).trans hW
  · intro z hz
    exact Finset.mem_inter.2 ⟨hZ (Finset.mem_inter.mp hz).1, (Finset.mem_inter.mp hz).2⟩
  · ext p
    simp only [restrictEdges, Finset.mem_inter, Finset.mem_union, Finset.mem_product]
    constructor
    · rintro ⟨h | h, hp⟩
      · exact Or.inl ⟨⟨h.1, hp.1⟩, ⟨h.2, hp.2⟩⟩
      · exact Or.inr ⟨⟨h.1, hp.1⟩, ⟨h.2, hp.2⟩⟩
    · rintro (h | h)
      · exact ⟨Or.inl ⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩
      · exact ⟨Or.inr ⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩

omit [Fintype α] [Fintype β] in
theorem transposeEdges_restrict (E : Finset (α × β)) (A : Finset α) (B : Finset β) :
    transposeEdges (restrictEdges E A B) = restrictEdges (transposeEdges E) B A := by
  ext p
  simp [restrictEdges, and_assoc, and_comm]

omit [Fintype α] [Fintype β] in
theorem Rectangular.restrict {E : Finset (α × β)} (h : Rectangular E)
    (A : Finset α) (B : Finset β) : Rectangular (restrictEdges E A B) := by
  rcases h with h | h
  · exact Or.inl (h.restrict A B)
  · exact Or.inr (by rw [transposeEdges_restrict]; exact h.restrict B A)

omit [Fintype α] [Fintype β] [LinearOrder α] in
@[simp] theorem transposeEdges_image_fst (E : Finset (α × β)) :
    (transposeEdges E).image Prod.fst = E.image Prod.snd := by
  ext x
  simp only [Finset.mem_image, mem_transposeEdges']
  constructor
  · rintro ⟨⟨b, a⟩, hp, rfl⟩
    exact ⟨(a, b), hp, rfl⟩
  · rintro ⟨⟨a, b⟩, hp, rfl⟩
    exact ⟨(b, a), hp, rfl⟩

omit [Fintype α] [Fintype β] [LinearOrder β] in
@[simp] theorem transposeEdges_image_snd (E : Finset (α × β)) :
    (transposeEdges E).image Prod.snd = E.image Prod.fst := by
  have h := transposeEdges_image_fst (transposeEdges E)
  simpa only [transposeEdges_transposeEdges] using h.symm

omit [Fintype α] [Fintype β] in
private theorem complete_rectangle_bound (U : Finset α) (V : Finset β)
    (hE : (U ×ˢ V).Nonempty) :
    (U ×ˢ V).card + max ((U ×ˢ V).image Prod.fst).card ((U ×ˢ V).image Prod.snd).card ≥
      ((U ×ˢ V).image Prod.fst).card * ((U ×ˢ V).image Prod.snd).card + 1 := by
  obtain ⟨p, hp⟩ := hE
  have hU : U.Nonempty := ⟨p.1, (Finset.mem_product.mp hp).1⟩
  have hV : V.Nonempty := ⟨p.2, (Finset.mem_product.mp hp).2⟩
  rw [Finset.product_image_fst hV, Finset.product_image_snd hU, Finset.card_product]
  have hp := Finset.card_pos.mpr hU
  have hm := le_max_left U.card V.card
  omega

omit [Fintype α] [Fintype β] in
theorem RowRectangular.card_bound {E : Finset (α × β)} (h : RowRectangular E) (hE : E.Nonempty) :
    E.card + max (E.image Prod.fst).card (E.image Prod.snd).card ≥
      (E.image Prod.fst).card * (E.image Prod.snd).card + 1 := by
  obtain ⟨U, W, V, Z, hdis, hW, hZ, rfl⟩ := h
  by_cases hU : U.Nonempty
  · by_cases hZne : Z.Nonempty
    · by_cases hWne : W.Nonempty
      · have hV : V.Nonempty := hZne.mono hZ
        have hWcard : W.card = 1 := by have := Finset.card_pos.mpr hWne; omega
        have hfst : (U ×ˢ V ∪ W ×ˢ Z).image Prod.fst = U ∪ W := by
          rw [Finset.image_union, Finset.product_image_fst hV, Finset.product_image_fst hZne]
        have hsnd : (U ×ˢ V ∪ W ×ˢ Z).image Prod.snd = V := by
          rw [Finset.image_union, Finset.product_image_snd hU, Finset.product_image_snd hWne,
            Finset.union_eq_left.mpr hZ]
        have hprod : Disjoint (U ×ˢ V) (W ×ˢ Z) := by
          exact Finset.disjoint_left.2 (fun _ hx hy =>
            (Finset.disjoint_left.mp hdis) (Finset.mem_product.mp hx).1 (Finset.mem_product.mp hy).1)
        rw [hfst, hsnd, Finset.card_union_of_disjoint hdis, hWcard,
          Finset.card_union_of_disjoint hprod, Finset.card_product, Finset.card_product, hWcard, one_mul]
        have hz := Finset.card_pos.mpr hZne
        have hm := le_max_right (U.card + 1) V.card
        nlinarith
      · have hWe : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hWne
        simp only [hWe, Finset.empty_product, Finset.union_empty] at hE ⊢
        exact complete_rectangle_bound U V hE
    · have hZe : Z = ∅ := Finset.not_nonempty_iff_eq_empty.mp hZne
      simp only [hZe, Finset.product_empty, Finset.union_empty] at hE ⊢
      exact complete_rectangle_bound U V hE
  · have hUe : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    simp only [hUe, Finset.empty_product, Finset.empty_union] at hE ⊢
    exact complete_rectangle_bound W Z hE

omit [Fintype α] [Fintype β] in
theorem Rectangular.card_bound {E : Finset (α × β)} (h : Rectangular E) (hE : E.Nonempty) :
    E.card + max (E.image Prod.fst).card (E.image Prod.snd).card ≥
      (E.image Prod.fst).card * (E.image Prod.snd).card + 1 := by
  rcases h with h | h
  · exact h.card_bound hE
  · have htrans : (transposeEdges E).Nonempty := by
      obtain ⟨p, hp⟩ := hE
      exact ⟨(p.2, p.1), (mem_transposeEdges E p.1 p.2).2 hp⟩
    have hp := h.card_bound htrans
    simpa only [card_transposeEdges, transposeEdges_image_fst, transposeEdges_image_snd,
      max_comm, mul_comm] using hp

end

end Lemmata.Centroid.Combinatorics
