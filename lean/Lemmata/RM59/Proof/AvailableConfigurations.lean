module

public import Lemmata.RM59.Proof.PullbackEquiv
public import Lemmata.RM59.Proof.Intersections
public import Lemmata.RM59.Proof.SymmetryChecks
public import Lemmata.RM59.Proof.Reachability

@[expose] public section

namespace Lemmata.RM59.AvailableConfigurations

open scoped symmDiff
open SupportForms Packed

def PairAvailable (H : Finset (Point 9)) (weightBound : Nat) (d : Point 9) : Prop :=
  ∃ G : Finset (Point 9), MatchSupportMoments 3 G H ∧ G.card ≤ weightBound ∧
    ∃ x ∈ G, ∃ y ∈ G, x ≠ y ∧ x + y = d

def TripleAvailable (H : Finset (Point 9)) (weightBound : Nat) (a b : Point 9) : Prop :=
  ∃ G : Finset (Point 9), MatchSupportMoments 3 G H ∧ G.card ≤ weightBound ∧
    ∃ x ∈ G, ∃ y ∈ G, ∃ z ∈ G,
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ x + y = a ∧ x + z = b

private theorem point_add_self (x : Point 9) : x + x = 0 := by
  funext i
  exact field_add_self _

private theorem shared_point_sum (x y z : Point 9) : (x + y) + (x + z) = y + z := by
  calc
    _ = (x + x) + (y + z) := by ac_rfl
    _ = _ := by rw [point_add_self, zero_add]

theorem pair_of_points (G H : Finset (Point 9)) (weightBound : Nat)
    (hGH : MatchSupportMoments 3 G H) (hcard : G.card ≤ weightBound)
    (x y : Point 9) (hx : x ∈ G) (hy : y ∈ G) (hne : x ≠ y) :
    PairAvailable H weightBound (x + y) :=
  ⟨G, hGH, hcard, x, hx, y, hy, hne, rfl⟩

theorem triple_of_points (G H : Finset (Point 9)) (weightBound : Nat)
    (hGH : MatchSupportMoments 3 G H) (hcard : G.card ≤ weightBound)
    (x y z : Point 9) (hx : x ∈ G) (hy : y ∈ G) (hz : z ∈ G)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    TripleAvailable H weightBound (x + y) (x + z) :=
  ⟨G, hGH, hcard, x, hx, y, hy, z, hz, hxy, hxz, hyz, rfl, rfl⟩

theorem PairAvailable.map {H : Finset (Point 9)} {weightBound : Nat} {d : Point 9}
    (h : PairAvailable H weightBound d) (g : Point 9 →ₗ[Field] Point 9)
    (hg : Function.Injective g) (hH : MatchSupportMoments 3 (H.image g) H) :
    PairAvailable H weightBound (g d) := by
  obtain ⟨G, hGH, hcard, x, hx, y, hy, hxy, hd⟩ := h
  refine ⟨G.image g, (matchSupportMoments_image hGH g hg).trans hH, ?_,
    g x, Finset.mem_image_of_mem _ hx, g y, Finset.mem_image_of_mem _ hy, ?_, ?_⟩
  · simpa only [Finset.card_image_of_injective G hg] using hcard
  · exact fun heq => hxy (hg heq)
  · rw [← map_add, hd]

theorem TripleAvailable.map {H : Finset (Point 9)} {weightBound : Nat} {a b : Point 9}
    (h : TripleAvailable H weightBound a b) (g : Point 9 →ₗ[Field] Point 9)
    (hg : Function.Injective g) (hH : MatchSupportMoments 3 (H.image g) H) :
    TripleAvailable H weightBound (g a) (g b) := by
  obtain ⟨G, hGH, hcard, x, hx, y, hy, z, hz, hxy, hxz, hyz, ha, hb⟩ := h
  refine ⟨G.image g, (matchSupportMoments_image hGH g hg).trans hH, ?_,
    g x, Finset.mem_image_of_mem _ hx, g y, Finset.mem_image_of_mem _ hy,
    g z, Finset.mem_image_of_mem _ hz, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Finset.card_image_of_injective G hg] using hcard
  · exact fun heq => hxy (hg heq)
  · exact fun heq => hxz (hg heq)
  · exact fun heq => hyz (hg heq)
  · rw [← map_add, ha]
  · rw [← map_add, hb]

theorem TripleAvailable.swap {H : Finset (Point 9)} {weightBound : Nat} {a b : Point 9}
    (h : TripleAvailable H weightBound a b) : TripleAvailable H weightBound b a := by
  obtain ⟨G, hGH, hcard, x, hx, y, hy, z, hz, hxy, hxz, hyz, ha, hb⟩ := h
  exact ⟨G, hGH, hcard, x, hx, z, hz, y, hy, hxz, hxy, hyz.symm, hb, ha⟩

theorem TripleAvailable.shear {H : Finset (Point 9)} {weightBound : Nat} {a b : Point 9}
    (h : TripleAvailable H weightBound a b) : TripleAvailable H weightBound a (a + b) := by
  obtain ⟨G, hGH, hcard, x, hx, y, hy, z, hz, hxy, hxz, hyz, ha, hb⟩ := h
  refine ⟨G, hGH, hcard, y, hy, x, hx, z, hz, hxy.symm, hyz, hxz, ?_, ?_⟩
  · simpa only [add_comm] using ha
  · rw [← ha, ← hb, shared_point_sum]

private theorem member_decodeWord {word : List PackedPoint} {x : PackedPoint}
    (hx : x ∈ word) : decodePoint x ∈ decodeWord word := by
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩)

theorem family_pair_seed (i : Fin 348) (word : List PackedPoint)
    (hword : word ∈ Certificate.familyWords (i.val + 1)) (x y : PackedPoint)
    (hx : x ∈ word) (hy : y ∈ word) (hne : x ≠ y) :
    PairAvailable (decodeWord (Certificate.seed (i.val + 1)))
      (Certificate.seed (i.val + 1)).length (decodePoint (xorPoint x y)) := by
  obtain ⟨_, _, _, _, _, _, hwords⟩ := Certificate.supplied_families_checked i
  obtain ⟨hnodup, hlength, _⟩ := hwords word hword
  rw [decodePoint_xorPoint]
  apply pair_of_points (decodeWord word) _ _
    (Certificate.family_word_same_moments i word hword)
  · exact (decodeWord_card word hnodup).le.trans hlength.le
  · exact member_decodeWord hx
  · exact member_decodeWord hy
  · exact fun h => hne (decodePoint_injective h)

theorem family_triple_seed (i : Fin 348) (word : List PackedPoint)
    (hword : word ∈ Certificate.familyWords (i.val + 1)) (x y z : PackedPoint)
    (hx : x ∈ word) (hy : y ∈ word) (hz : z ∈ word)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    TripleAvailable (decodeWord (Certificate.seed (i.val + 1)))
      (Certificate.seed (i.val + 1)).length (decodePoint (xorPoint x y))
        (decodePoint (xorPoint x z)) := by
  obtain ⟨_, _, _, _, _, _, hwords⟩ := Certificate.supplied_families_checked i
  obtain ⟨hnodup, hlength, _⟩ := hwords word hword
  rw [decodePoint_xorPoint, decodePoint_xorPoint]
  apply triple_of_points (decodeWord word) _ _
    (Certificate.family_word_same_moments i word hword)
  · exact (decodeWord_card word hnodup).le.trans hlength.le
  · exact member_decodeWord hx
  · exact member_decodeWord hy
  · exact member_decodeWord hz
  · exact fun h => hxy (decodePoint_injective h)
  · exact fun h => hxz (decodePoint_injective h)
  · exact fun h => hyz (decodePoint_injective h)

theorem family_pair_move (i : Fin 348) (entry : Nat × List PackedPoint)
    (hentry : entry ∈ Certificate.symmetries.toList) (hfamily : entry.1 = i.val + 1)
    (x : PackedPoint)
    (h : PairAvailable (decodeWord (Certificate.seed (i.val + 1)))
      (Certificate.seed (i.val + 1)).length (decodePoint x)) :
    PairAvailable (decodeWord (Certificate.seed (i.val + 1)))
      (Certificate.seed (i.val + 1)).length
        (decodePoint (evalColumns (Certificate.symmetryColumns entry.2) x)) := by
  obtain ⟨hinj, hsymm⟩ := Certificate.supplied_symmetry_sound entry hentry
  rw [hfamily] at hsymm
  rw [decodePoint_evalColumns]
  exact h.map _ hinj hsymm

theorem family_triple_move (i : Fin 348) (entry : Nat × List PackedPoint)
    (hentry : entry ∈ Certificate.symmetries.toList) (hfamily : entry.1 = i.val + 1)
    (x y : PackedPoint)
    (h : TripleAvailable (decodeWord (Certificate.seed (i.val + 1)))
      (Certificate.seed (i.val + 1)).length (decodePoint x) (decodePoint y)) :
    TripleAvailable (decodeWord (Certificate.seed (i.val + 1)))
      (Certificate.seed (i.val + 1)).length
        (decodePoint (evalColumns (Certificate.symmetryColumns entry.2) x))
        (decodePoint (evalColumns (Certificate.symmetryColumns entry.2) y)) := by
  obtain ⟨hinj, hsymm⟩ := Certificate.supplied_symmetry_sound entry hentry
  rw [hfamily] at hsymm
  rw [decodePoint_evalColumns, decodePoint_evalColumns]
  exact h.map _ hinj hsymm

private theorem translate_pair_point (x y p q : Point 9) (h : x + y = p + q) :
    y + (p + x) = q := by
  calc
    _ = p + (x + y) := by ac_rfl
    _ = p + (p + q) := by rw [h]
    _ = (p + p) + q := by rw [add_assoc]
    _ = q := by rw [point_add_self, zero_add]

private theorem translate_anchor (x p : Point 9) : x + (p + x) = p := by
  calc
    _ = p + (x + x) := by ac_rfl
    _ = p := by rw [point_add_self, add_zero]

theorem PairAvailable.align {H : Finset (Point 9)} {weightBound : Nat} {d : Point 9}
    (h : PairAvailable H weightBound d) (hH : LowerZero H) (p q : Point 9)
    (hd : p + q = d) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G H ∧ G.card ≤ weightBound ∧
      p ∈ G ∧ q ∈ G := by
  obtain ⟨G, hGH, hcard, x, hx, y, hy, hxy, hdir⟩ := h
  have hG : LowerZero G := by
    intro s hs
    rw [hGH s (by omega)]
    exact hH s hs
  let G' := translateSupport G (p + x)
  refine ⟨G', (matchSupportMoments_translate G hG _).trans hGH, ?_, ?_, ?_⟩
  · have hinj : Function.Injective (fun y : Point 9 => y + (p + x)) :=
      fun _ _ h => add_right_cancel h
    exact (Finset.card_image_of_injective G hinj).le.trans hcard
  · exact Finset.mem_image.mpr ⟨x, hx, translate_anchor x p⟩
  · exact Finset.mem_image.mpr ⟨y, hy, translate_pair_point x y p q (hdir.trans hd.symm)⟩

theorem TripleAvailable.align {H : Finset (Point 9)} {weightBound : Nat} {a b : Point 9}
    (h : TripleAvailable H weightBound a b) (hH : LowerZero H) (p q r : Point 9)
    (ha : p + q = a) (hb : p + r = b) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G H ∧ G.card ≤ weightBound ∧
      p ∈ G ∧ q ∈ G ∧ r ∈ G := by
  obtain ⟨G, hGH, hcard, x, hx, y, hy, z, hz, hxy, hxz, hyz, hdirA, hdirB⟩ := h
  have hG : LowerZero G := by
    intro s hs
    rw [hGH s (by omega)]
    exact hH s hs
  let G' := translateSupport G (p + x)
  refine ⟨G', (matchSupportMoments_translate G hG _).trans hGH, ?_, ?_, ?_, ?_⟩
  · have hinj : Function.Injective (fun y : Point 9 => y + (p + x)) :=
      fun _ _ h => add_right_cancel h
    exact (Finset.card_image_of_injective G hinj).le.trans hcard
  · exact Finset.mem_image.mpr ⟨x, hx, translate_anchor x p⟩
  · exact Finset.mem_image.mpr ⟨y, hy, translate_pair_point x y p q (hdirA.trans ha.symm)⟩
  · exact Finset.mem_image.mpr ⟨z, hz, translate_pair_point x z p r (hdirB.trans hb.symm)⟩

theorem pair_completion {H P : Finset (Point 9)} {weightBound : Nat}
    (hH : LowerZero H) (p q : Point 9) (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q)
    (h : PairAvailable H weightBound (p + q)) (hsize : weightBound + P.card ≤ 35) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G H ∧ (G ∆ P).card ≤ 31 := by
  obtain ⟨G, hGH, hcard, hpG, hqG⟩ := h.align hH p q rfl
  have hsubset : ({p, q} : Finset (Point 9)) ⊆ G ∩ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hpG, hp⟩
    · exact Finset.mem_inter.mpr ⟨hqG, hq⟩
  have hinter : 2 ≤ (G ∩ P).card := by
    have hpair : ({p, q} : Finset (Point 9)).card = 2 := by simp [hpq]
    simpa only [hpair] using Finset.card_le_card hsubset
  refine ⟨G, hGH, symmDiff_card_le_of_intersection G P 31 ?_⟩
  omega

theorem triple_completion {H P : Finset (Point 9)} {weightBound : Nat}
    (hH : LowerZero H) (p q r : Point 9) (hp : p ∈ P) (hq : q ∈ P) (hr : r ∈ P)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (h : TripleAvailable H weightBound (p + q) (p + r))
    (hsize : weightBound + P.card ≤ 37) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G H ∧ (G ∆ P).card ≤ 31 := by
  obtain ⟨G, hGH, hcard, hpG, hqG, hrG⟩ := h.align hH p q r rfl rfl
  have hsubset : ({p, q, r} : Finset (Point 9)) ⊆ G ∩ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hpG, hp⟩
    · exact Finset.mem_inter.mpr ⟨hqG, hq⟩
    · exact Finset.mem_inter.mpr ⟨hrG, hr⟩
  have hinter : 3 ≤ (G ∩ P).card := by
    have htriple : ({p, q, r} : Finset (Point 9)).card = 3 := by simp [hpq, hpr, hqr]
    rw [← htriple]
    exact Finset.card_le_card hsubset
  refine ⟨G, hGH, symmDiff_card_le_of_intersection G P 31 ?_⟩
  omega

end Lemmata.RM59.AvailableConfigurations
