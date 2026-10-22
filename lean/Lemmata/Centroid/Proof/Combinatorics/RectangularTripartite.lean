module

public import Lemmata.Centroid.Proof.Combinatorics.Rectangles

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Combinatorics

noncomputable section

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [LinearOrder α] [LinearOrder β] [LinearOrder γ]

omit [LinearOrder α] [LinearOrder β] [LinearOrder γ] in
@[simp] theorem mem_triangles_iff (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) (p : α × β × γ) :
    p ∈ triangles AB AC BC ↔ (p.1, p.2.1) ∈ AB ∧ (p.1, p.2.2) ∈ AC ∧ (p.2.1, p.2.2) ∈ BC := by
  simp only [triangles, Finset.mem_filter, Finset.mem_univ, true_and]

def neighbors (E : Finset (α × γ)) (a : α) : Finset γ :=
  Finset.univ.filter fun c => (a, c) ∈ E

omit [Fintype α] in
@[simp] theorem mem_neighbors (E : Finset (α × γ)) (a : α) (c : γ) :
    c ∈ neighbors E a ↔ (a, c) ∈ E := by simp [neighbors]

omit [Fintype α] in
theorem neighbors_lower {E : Finset (α × γ)} (hE : DownClosed E) (a : α) :
    LowerFinset (neighbors E a) := by
  intro c d hcd hd
  exact (mem_neighbors E a c).2 (hE le_rfl hcd ((mem_neighbors E a d).1 hd))

omit [Fintype α] in
theorem neighbors_card_antitone {E : Finset (α × γ)} (hE : DownClosed E) :
    Antitone (fun a => (neighbors E a).card) := by
  intro a b hab
  apply Finset.card_le_card
  intro c hc
  exact (mem_neighbors E a c).2 (hE hab le_rfl ((mem_neighbors E b c).1 hc))

omit [Fintype γ] in
theorem lower_inter_card {S T : Finset γ} (hS : LowerFinset S) (hT : LowerFinset T) :
    (S ∩ T).card = min S.card T.card := by
  rcases hS.total hT with h | h
  · rw [Finset.inter_eq_left.mpr h, min_eq_left (Finset.card_le_card h)]
  · rw [Finset.inter_eq_right.mpr h, min_eq_right (Finset.card_le_card h)]

theorem card_triangles_neighbors (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) :
    (triangles AB AC BC).card = ∑ p ∈ AB, (neighbors AC p.1 ∩ neighbors BC p.2).card := by
  calc
    _ = ∑ a : α, ∑ b : β, ∑ c : γ,
        if (a, b) ∈ AB ∧ (a, c) ∈ AC ∧ (b, c) ∈ BC then 1 else 0 := by
      simp only [triangles, Finset.card_filter, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      by_cases h : (a, b) ∈ AB ∧ (a, c) ∈ AC ∧ (b, c) ∈ BC <;> simp [h]
    _ = ∑ p : α × β, if p ∈ AB then (neighbors AC p.1 ∩ neighbors BC p.2).card else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases hab : (a, b) ∈ AB
      · simp only [hab, true_and, ite_true]
        rw [← Finset.card_filter]
        congr 1
        ext c
        simp
      · simp [hab]
    _ = _ := by simp

theorem card_triangles_min_neighbors (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) (hAC : DownClosed AC) (hBC : DownClosed BC) :
    (triangles AB AC BC).card = ∑ p ∈ AB,
      min (neighbors AC p.1).card (neighbors BC p.2).card := by
  rw [card_triangles_neighbors]
  apply Finset.sum_congr rfl
  intro p _
  exact lower_inter_card (neighbors_lower hAC p.1) (neighbors_lower hBC p.2)

theorem exists_rectangular_first (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) (hAC : DownClosed AC) (hBC : DownClosed BC) :
    ∃ A : Finset (α × β), A.card = AB.card ∧ Rectangular A ∧ DownClosed A ∧
      (triangles AB AC BC).card ≤ (triangles A AC BC).card := by
  obtain ⟨A, hcard, hrect, hdown, hsum⟩ := exists_rectangular_optimal
    (fun a => (neighbors AC a).card) (fun b => (neighbors BC b).card)
    (neighbors_card_antitone hAC) (neighbors_card_antitone hBC) (Fintype.card γ)
    (fun a => Finset.card_le_univ (neighbors AC a)) AB
  refine ⟨A, hcard, hrect, hdown, ?_⟩
  simpa only [card_triangles_min_neighbors _ AC BC hAC hBC] using hsum

omit [LinearOrder α] [LinearOrder β] [LinearOrder γ] in
theorem card_triangles_cycle (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) :
    (triangles BC (transposeEdges AB) (transposeEdges AC)).card = (triangles AB AC BC).card := by
  rw [card_triangles_swap_last, card_triangles_swap_first]

theorem exists_rectangular (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) :
    ∃ (A : Finset (α × β)) (B : Finset (α × γ)) (C : Finset (β × γ)),
      A.card = AB.card ∧ B.card = AC.card ∧ C.card = BC.card ∧
      (triangles AB AC BC).card ≤ (triangles A B C).card ∧
      Rectangular A ∧ Rectangular B ∧ Rectangular C ∧ DownClosed A ∧ DownClosed B ∧ DownClosed C := by
  obtain ⟨A₀, B₀, C₀, hA₀, hB₀, hC₀, htri₀, hdownA₀, hdownB₀, hdownC₀⟩ :=
    exists_downClosed orderRank orderRank orderRank orderRank_strictMono
      orderRank_strictMono orderRank_strictMono AB AC BC
  obtain ⟨A, hA, hrectA, hdownA, htriA⟩ := exists_rectangular_first A₀ B₀ C₀ hdownB₀ hdownC₀
  obtain ⟨B, hB, hrectB, hdownB, htriB⟩ := exists_rectangular_first B₀ A (transposeEdges C₀)
    hdownA hdownC₀.transpose
  rw [card_triangles_swap_last, card_triangles_swap_last] at htriB
  obtain ⟨C, hC, hrectC, hdownC, htriC⟩ := exists_rectangular_first C₀ (transposeEdges A)
    (transposeEdges B) hdownA.transpose hdownB.transpose
  rw [card_triangles_cycle, card_triangles_cycle] at htriC
  exact ⟨A, B, C, hA.trans hA₀, hB.trans hB₀, hC.trans hC₀,
    htri₀.trans (htriA.trans (htriB.trans htriC)), hrectA, hrectB, hrectC, hdownA, hdownB, hdownC⟩

omit [Fintype α] [Fintype β] in
private theorem restrict_image_fst {ι : Type*} (S : Finset ι) (x : ι → α) (y : ι → β)
    (E : Finset (α × β)) (h : ∀ p ∈ S, (x p, y p) ∈ E) :
    (restrictEdges E (S.image x) (S.image y)).image Prod.fst = S.image x := by
  ext a
  constructor
  · rintro ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_product.mp (Finset.mem_inter.mp hp).2).1
  · intro ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    apply Finset.mem_image.mpr
    refine ⟨(x p, y p), Finset.mem_inter.mpr ⟨h p hp, ?_⟩, rfl⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩

omit [Fintype α] [Fintype β] in
private theorem restrict_image_snd {ι : Type*} (S : Finset ι) (x : ι → α) (y : ι → β)
    (E : Finset (α × β)) (h : ∀ p ∈ S, (x p, y p) ∈ E) :
    (restrictEdges E (S.image x) (S.image y)).image Prod.snd = S.image y := by
  have h' := restrict_image_fst S y x (transposeEdges E) (by
    intro p hp
    exact (mem_transposeEdges E (x p) (y p)).2 (h p hp))
  rw [← transposeEdges_restrict, transposeEdges_image_fst] at h'
  exact h'

omit [Fintype α] [Fintype β] in
theorem DownClosed.restrict {E : Finset (α × β)} (hE : DownClosed E)
    {A : Finset α} {B : Finset β} (hA : LowerFinset A) (hB : LowerFinset B) :
    DownClosed (restrictEdges E A B) := by
  intro u v b c huv hbc hvc
  rcases Finset.mem_inter.mp hvc with ⟨hEvc, hAB⟩
  exact Finset.mem_inter.mpr ⟨hE huv hbc hEvc,
    Finset.mem_product.mpr ⟨hA huv (Finset.mem_product.mp hAB).1, hB hbc (Finset.mem_product.mp hAB).2⟩⟩

theorem active_first_lower (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) (hAB : DownClosed AB) (hAC : DownClosed AC) :
    LowerFinset ((triangles AB AC BC).image Prod.fst) := by
  intro a a' haa ha'
  obtain ⟨p, hp, hpfirst⟩ := Finset.mem_image.mp ha'
  rcases (mem_triangles_iff AB AC BC p).1 hp with ⟨hab, hac, hbc⟩
  refine Finset.mem_image.mpr ⟨(a, p.2.1, p.2.2), ?_, rfl⟩
  apply (mem_triangles_iff AB AC BC _).2
  exact ⟨hAB (hpfirst.symm ▸ haa) le_rfl hab, hAC (hpfirst.symm ▸ haa) le_rfl hac, hbc⟩

theorem active_second_lower (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) (hAB : DownClosed AB) (hBC : DownClosed BC) :
    LowerFinset ((triangles AB AC BC).image fun p => p.2.1) := by
  intro b b' hbb hb'
  obtain ⟨p, hp, hpsecond⟩ := Finset.mem_image.mp hb'
  rcases (mem_triangles_iff AB AC BC p).1 hp with ⟨hab, hac, hbc⟩
  refine Finset.mem_image.mpr ⟨(p.1, b, p.2.2), ?_, rfl⟩
  apply (mem_triangles_iff AB AC BC _).2
  exact ⟨hAB le_rfl (hpsecond.symm ▸ hbb) hab, hac, hBC (hpsecond.symm ▸ hbb) le_rfl hbc⟩

theorem active_third_lower (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) (hAC : DownClosed AC) (hBC : DownClosed BC) :
    LowerFinset ((triangles AB AC BC).image fun p => p.2.2) := by
  intro c c' hcc hc'
  obtain ⟨p, hp, hpthird⟩ := Finset.mem_image.mp hc'
  rcases (mem_triangles_iff AB AC BC p).1 hp with ⟨hab, hac, hbc⟩
  refine Finset.mem_image.mpr ⟨(p.1, p.2.1, c), ?_, rfl⟩
  apply (mem_triangles_iff AB AC BC _).2
  exact ⟨hab, hAC le_rfl (hpthird.symm ▸ hcc) hac, hBC le_rfl (hpthird.symm ▸ hcc) hbc⟩

theorem triangles_restrict_active (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) :
    let S := triangles AB AC BC
    triangles (restrictEdges AB (S.image Prod.fst) (S.image fun p => p.2.1))
      (restrictEdges AC (S.image Prod.fst) (S.image fun p => p.2.2))
      (restrictEdges BC (S.image fun p => p.2.1) (S.image fun p => p.2.2)) = S := by
  dsimp only
  ext p
  simp only [mem_triangles_iff,
    restrictEdges, Finset.mem_inter, Finset.mem_product]
  constructor
  · rintro ⟨⟨hab, _⟩, ⟨hac, _⟩, ⟨hbc, _⟩⟩
    exact ⟨hab, hac, hbc⟩
  · rintro ⟨hab, hac, hbc⟩
    have hp : p ∈ triangles AB AC BC := (mem_triangles_iff AB AC BC p).2 ⟨hab, hac, hbc⟩
    exact ⟨⟨hab, Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩,
      ⟨hac, Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩,
      ⟨hbc, Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩⟩

theorem exists_active_rectangular (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) :
    ∃ (A : Finset (α × β)) (B : Finset (α × γ)) (C : Finset (β × γ)),
      A.card ≤ AB.card ∧ B.card ≤ AC.card ∧ C.card ≤ BC.card ∧
      (triangles AB AC BC).card ≤ (triangles A B C).card ∧
      Rectangular A ∧ Rectangular B ∧ Rectangular C ∧ DownClosed A ∧ DownClosed B ∧ DownClosed C ∧
      A.image Prod.fst = B.image Prod.fst ∧ A.image Prod.snd = C.image Prod.fst ∧
        B.image Prod.snd = C.image Prod.snd := by
  obtain ⟨A, B, C, hA, hB, hC, htri, hrectA, hrectB, hrectC, hdownA, hdownB, hdownC⟩ :=
    exists_rectangular AB AC BC
  let S := triangles A B C
  let U := S.image Prod.fst
  let V := S.image fun p => p.2.1
  let W := S.image fun p => p.2.2
  have hU := active_first_lower A B C hdownA hdownB
  have hV := active_second_lower A B C hdownA hdownC
  have hW := active_third_lower A B C hdownB hdownC
  have hxy : ∀ p ∈ S, (p.1, p.2.1) ∈ A := fun p hp => ((mem_triangles_iff A B C p).1 hp).1
  have hxz : ∀ p ∈ S, (p.1, p.2.2) ∈ B := fun p hp => ((mem_triangles_iff A B C p).1 hp).2.1
  have hyz : ∀ p ∈ S, (p.2.1, p.2.2) ∈ C := fun p hp => ((mem_triangles_iff A B C p).1 hp).2.2
  refine ⟨restrictEdges A U V, restrictEdges B U W, restrictEdges C V W,
    (Finset.card_le_card Finset.inter_subset_left).trans hA.le,
    (Finset.card_le_card Finset.inter_subset_left).trans hB.le,
    (Finset.card_le_card Finset.inter_subset_left).trans hC.le, ?_,
    hrectA.restrict U V, hrectB.restrict U W, hrectC.restrict V W,
    hdownA.restrict hU hV, hdownB.restrict hU hW, hdownC.restrict hV hW, ?_, ?_, ?_⟩
  · dsimp only [U, V, W, S]
    rw [triangles_restrict_active]
    exact htri
  · exact (restrict_image_fst S _ _ A hxy).trans (restrict_image_fst S _ _ B hxz).symm
  · exact (restrict_image_snd S _ _ A hxy).trans (restrict_image_fst S _ _ C hyz).symm
  · exact (restrict_image_snd S _ _ B hxz).trans (restrict_image_snd S _ _ C hyz).symm

end

end Lemmata.Centroid.Combinatorics
