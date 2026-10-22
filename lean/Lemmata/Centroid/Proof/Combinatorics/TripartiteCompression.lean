module

public import Lemmata.Centroid.Proof.Combinatorics.Tripartite
public import Mathlib.Data.Fintype.Lattice

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Combinatorics

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

noncomputable section

private theorem sum_split_two (f : α → ℕ) {u v : α} (huv : u ≠ v) :
    ∑ a, f a = f u + f v + ∑ a ∈ (Finset.univ.erase u).erase v, f a := by
  have hu := Finset.sum_erase_add Finset.univ f (Finset.mem_univ u)
  have hv := Finset.sum_erase_add (Finset.univ.erase u) f
    (show v ∈ Finset.univ.erase u by simp [Ne.symm huv])
  omega

private theorem sum_le_of_pair (f g : α → ℕ) {u v : α} (huv : u ≠ v)
    (hout : ∀ a, a ≠ u → a ≠ v → f a = g a)
    (hpair : f u + f v ≤ g u + g v) : ∑ a, f a ≤ ∑ a, g a := by
  rw [sum_split_two f huv, sum_split_two g huv]
  have heq : (∑ a ∈ (Finset.univ.erase u).erase v, f a) =
      ∑ a ∈ (Finset.univ.erase u).erase v, g a := by
    apply Finset.sum_congr rfl
    intro a ha
    have hv := (Finset.mem_erase.mp ha).1
    have hu := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
    exact hout a hu hv
  omega

def compressLeft (E : Finset (α × β)) (u v : α) : Finset (α × β) :=
  Finset.univ.filter fun p => if p.1 = u then (u, p.2) ∈ E ∨ (v, p.2) ∈ E
    else if p.1 = v then (u, p.2) ∈ E ∧ (v, p.2) ∈ E else p ∈ E

@[simp] theorem mem_compressLeft (E : Finset (α × β)) (u v a : α) (b : β) :
    (a, b) ∈ compressLeft E u v ↔
      if a = u then (u, b) ∈ E ∨ (v, b) ∈ E
      else if a = v then (u, b) ∈ E ∧ (v, b) ∈ E else (a, b) ∈ E := by
  simp only [compressLeft, Finset.mem_filter, Finset.mem_univ, true_and]

theorem card_compressLeft (E : Finset (α × β)) {u v : α} (huv : u ≠ v) :
    (compressLeft E u v).card = E.card := by
  have hsplit (S : Finset (α × β)) :
      S.card = ∑ b : β, ∑ a : α, if (a, b) ∈ S then 1 else 0 := by
    calc
      _ = ∑ p : α × β, if p ∈ S then 1 else 0 := by simp
      _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [hsplit, hsplit]
  apply Finset.sum_congr rfl
  intro b _
  apply le_antisymm
  · apply sum_le_of_pair _ _ huv
    · intro a hau hav
      simp [hau, hav]
    · by_cases hu : (u, b) ∈ E <;> by_cases hv : (v, b) ∈ E <;>
        simp [Ne.symm huv, hu, hv]
  · apply sum_le_of_pair _ _ huv
    · intro a hau hav
      simp [hau, hav]
    · by_cases hu : (u, b) ∈ E <;> by_cases hv : (v, b) ∈ E <;>
        simp [Ne.symm huv, hu, hv]

theorem card_triangles_compress_first (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) {u v : α} (huv : u ≠ v) :
    (triangles AB AC BC).card ≤
      (triangles (compressLeft AB u v) (compressLeft AC u v) BC).card := by
  rw [card_triangles_eq_sum, card_triangles_eq_sum]
  apply Finset.sum_le_sum
  intro p _
  apply Nat.mul_le_mul_left
  apply sum_le_of_pair _ _ huv
  · intro a hau hav
    simp [hau, hav]
  · by_cases habu : (u, p.1) ∈ AB <;> by_cases habv : (v, p.1) ∈ AB <;>
      by_cases hacu : (u, p.2) ∈ AC <;> by_cases hacv : (v, p.2) ∈ AC <;>
      simp [Ne.symm huv, habu, habv, hacu, hacv]

def transposeEdges (E : Finset (α × β)) : Finset (β × α) :=
  E.map (Equiv.prodComm α β).toEmbedding

omit [Fintype α] [Fintype β] in
@[simp] theorem mem_transposeEdges' (E : Finset (α × β)) (p : β × α) :
    p ∈ transposeEdges E ↔ (p.2, p.1) ∈ E := by
  rcases p with ⟨b, a⟩
  simp [transposeEdges]

omit [Fintype α] [Fintype β] in
theorem mem_transposeEdges (E : Finset (α × β)) (a : α) (b : β) :
    (b, a) ∈ transposeEdges E ↔ (a, b) ∈ E := by
  simp [transposeEdges]

omit [Fintype α] [Fintype β] in
@[simp] theorem transposeEdges_transposeEdges (E : Finset (α × β)) :
    transposeEdges (transposeEdges E) = E := by
  ext p
  simp

omit [Fintype α] [Fintype β] in
@[simp] theorem card_transposeEdges (E : Finset (α × β)) : (transposeEdges E).card = E.card :=
  Finset.card_map _

theorem card_triangles_swap_first (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) :
    (triangles (transposeEdges AB) BC AC).card = (triangles AB AC BC).card := by
  apply Finset.card_bij (fun p _ => (p.2.1, p.1, p.2.2))
  · intro p hp
    simpa [triangles, and_left_comm, and_assoc, and_comm] using hp
  · intro p _ q _ hpq
    exact Prod.ext (congrArg (fun x : α × β × γ => x.2.1) hpq)
      (Prod.ext (congrArg (fun x : α × β × γ => x.1) hpq)
        (congrArg (fun x : α × β × γ => x.2.2) hpq))
  · intro p hp
    refine ⟨(p.2.1, p.1, p.2.2), ?_, rfl⟩
    simpa [triangles, and_left_comm, and_assoc, and_comm] using hp

theorem card_triangles_swap_last (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) :
    (triangles AC AB (transposeEdges BC)).card = (triangles AB AC BC).card := by
  apply Finset.card_bij (fun p _ => (p.1, p.2.2, p.2.1))
  · intro p hp
    simpa [triangles, and_left_comm, and_assoc, and_comm] using hp
  · intro p _ q _ hpq
    exact Prod.ext (congrArg (fun x : α × β × γ => x.1) hpq)
      (Prod.ext (congrArg (fun x : α × β × γ => x.2.2) hpq)
        (congrArg (fun x : α × β × γ => x.2.1) hpq))
  · intro p hp
    refine ⟨(p.1, p.2.2, p.2.1), ?_, rfl⟩
    simpa [triangles, and_left_comm, and_assoc, and_comm] using hp

def leftWeight (w : α → ℕ) (E : Finset (α × β)) : ℕ :=
  ∑ b : β, ∑ a : α, if (a, b) ∈ E then w a else 0

theorem leftWeight_compress_le (E : Finset (α × β)) (w : α → ℕ)
    {u v : α} (huv : u ≠ v) (hw : w u ≤ w v) :
    leftWeight w (compressLeft E u v) ≤ leftWeight w E := by
  apply Finset.sum_le_sum
  intro b _
  apply sum_le_of_pair _ _ huv
  · intro a hau hav
    simp [hau, hav]
  · by_cases hu : (u, b) ∈ E <;> by_cases hv : (v, b) ∈ E <;>
      simp [Ne.symm huv, hu, hv, hw]

theorem leftWeight_compress_lt (E : Finset (α × β)) (w : α → ℕ)
    {u v : α} (huv : u ≠ v) (hw : w u < w v)
    (hb : ∃ b, (v, b) ∈ E ∧ (u, b) ∉ E) :
    leftWeight w (compressLeft E u v) < leftWeight w E := by
  apply Finset.sum_lt_sum
  · intro b _
    apply sum_le_of_pair _ _ huv
    · intro a hau hav
      simp [hau, hav]
    · by_cases hu : (u, b) ∈ E <;> by_cases hv : (v, b) ∈ E <;>
        simp [Ne.symm huv, hu, hv, hw.le]
  · obtain ⟨b, hv, hu⟩ := hb
    refine ⟨b, Finset.mem_univ _, ?_⟩
    rw [sum_split_two _ huv, sum_split_two _ huv]
    have heq : (∑ a ∈ (Finset.univ.erase u).erase v,
        if (a, b) ∈ compressLeft E u v then w a else 0) =
        ∑ a ∈ (Finset.univ.erase u).erase v, if (a, b) ∈ E then w a else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      have hav := (Finset.mem_erase.mp ha).1
      have hau := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
      simp [hau, hav]
    rw [heq]
    simpa [Ne.symm huv, hu, hv] using Nat.add_lt_add_right hw
      (∑ a ∈ (Finset.univ.erase u).erase v, if (a, b) ∈ E then w a else 0)

theorem rightWeight_compress (E : Finset (α × β)) (w : β → ℕ)
    {u v : α} (huv : u ≠ v) :
    leftWeight w (transposeEdges (compressLeft E u v)) = leftWeight w (transposeEdges E) := by
  unfold leftWeight
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [mem_transposeEdges']
  apply le_antisymm
  · apply sum_le_of_pair _ _ huv
    · intro a hau hav
      simp [hau, hav]
    · by_cases hu : (u, b) ∈ E <;> by_cases hv : (v, b) ∈ E <;>
        simp [Ne.symm huv, hu, hv]
  · apply sum_le_of_pair _ _ huv
    · intro a hau hav
      simp [hau, hav]
    · by_cases hu : (u, b) ∈ E <;> by_cases hv : (v, b) ∈ E <;>
        simp [Ne.symm huv, hu, hv]

def indexPotential (wa : α → ℕ) (wb : β → ℕ) (wc : γ → ℕ)
    (AB : Finset (α × β)) (AC : Finset (α × γ)) (BC : Finset (β × γ)) : ℕ :=
  leftWeight wa AB + leftWeight wb (transposeEdges AB) +
    leftWeight wa AC + leftWeight wc (transposeEdges AC) +
    leftWeight wb BC + leftWeight wc (transposeEdges BC)

theorem indexPotential_swap_first (wa : α → ℕ) (wb : β → ℕ) (wc : γ → ℕ)
    (AB : Finset (α × β)) (AC : Finset (α × γ)) (BC : Finset (β × γ)) :
    indexPotential wb wa wc (transposeEdges AB) BC AC = indexPotential wa wb wc AB AC BC := by
  simp only [indexPotential, transposeEdges_transposeEdges]
  omega

theorem indexPotential_swap_last (wa : α → ℕ) (wb : β → ℕ) (wc : γ → ℕ)
    (AB : Finset (α × β)) (AC : Finset (α × γ)) (BC : Finset (β × γ)) :
    indexPotential wa wc wb AC AB (transposeEdges BC) = indexPotential wa wb wc AB AC BC := by
  simp only [indexPotential, transposeEdges_transposeEdges]
  omega

theorem indexPotential_compress_le (wa : α → ℕ) (wb : β → ℕ) (wc : γ → ℕ)
    (AB : Finset (α × β)) (AC : Finset (α × γ)) (BC : Finset (β × γ))
    {u v : α} (huv : u ≠ v) (hw : wa u ≤ wa v) :
    indexPotential wa wb wc (compressLeft AB u v) (compressLeft AC u v) BC ≤
      indexPotential wa wb wc AB AC BC := by
  have hab := leftWeight_compress_le AB wa huv hw
  have hac := leftWeight_compress_le AC wa huv hw
  simp only [indexPotential, rightWeight_compress _ _ huv]
  omega

theorem indexPotential_compress_lt_left (wa : α → ℕ) (wb : β → ℕ) (wc : γ → ℕ)
    (AB : Finset (α × β)) (AC : Finset (α × γ)) (BC : Finset (β × γ))
    {u v : α} (huv : u ≠ v) (hw : wa u < wa v)
    (hb : ∃ b, (v, b) ∈ AB ∧ (u, b) ∉ AB) :
    indexPotential wa wb wc (compressLeft AB u v) (compressLeft AC u v) BC <
      indexPotential wa wb wc AB AC BC := by
  have hab := leftWeight_compress_lt AB wa huv hw hb
  have hac := leftWeight_compress_le AC wa huv hw.le
  simp only [indexPotential, rightWeight_compress _ _ huv]
  omega

def LeftClosed [Preorder α] (E : Finset (α × β)) : Prop :=
  ∀ ⦃u v : α⦄ ⦃b : β⦄, u ≤ v → (v, b) ∈ E → (u, b) ∈ E

def DownClosed [Preorder α] [Preorder β] (E : Finset (α × β)) : Prop :=
  ∀ ⦃u v : α⦄ ⦃b c : β⦄, u ≤ v → b ≤ c → (v, c) ∈ E → (u, b) ∈ E

omit [Fintype α] [Fintype β] in
theorem DownClosed.of_left_right [Preorder α] [Preorder β] {E : Finset (α × β)}
    (hleft : LeftClosed E) (hright : LeftClosed (transposeEdges E)) : DownClosed E := by
  intro u v b c huv hbc hvc
  have huc := hleft huv hvc
  exact (mem_transposeEdges E u b).1 (hright hbc ((mem_transposeEdges E u c).2 huc))

theorem leftClosed_of_minimal [LinearOrder α]
    (wa : α → ℕ) (wb : β → ℕ) (wc : γ → ℕ) (hwa : StrictMono wa)
    (AB : Finset (α × β)) (AC : Finset (α × γ)) (BC : Finset (β × γ))
    (hmin : ∀ u v, u < v → indexPotential wa wb wc AB AC BC ≤
      indexPotential wa wb wc (compressLeft AB u v) (compressLeft AC u v) BC) :
    LeftClosed AB := by
  intro u v b huv hvb
  by_cases hueq : u = v
  · simpa only [hueq] using hvb
  · by_contra hub
    have hlt := lt_of_le_of_ne huv hueq
    have hp := indexPotential_compress_lt_left wa wb wc AB AC BC hueq (hwa hlt) ⟨b, hvb, hub⟩
    exact (not_lt_of_ge (hmin u v hlt)) hp

theorem leftClosed_pair_of_minimal [LinearOrder α]
    (wa : α → ℕ) (wb : β → ℕ) (wc : γ → ℕ) (hwa : StrictMono wa)
    (AB : Finset (α × β)) (AC : Finset (α × γ)) (BC : Finset (β × γ))
    (hmin : ∀ u v, u < v → indexPotential wa wb wc AB AC BC ≤
      indexPotential wa wb wc (compressLeft AB u v) (compressLeft AC u v) BC) :
    LeftClosed AB ∧ LeftClosed AC := by
  refine ⟨leftClosed_of_minimal wa wb wc hwa AB AC BC hmin, ?_⟩
  apply leftClosed_of_minimal wa wc wb hwa AC AB (transposeEdges BC)
  intro u v huv
  simpa only [indexPotential_swap_last] using hmin u v huv

theorem card_triangles_swap_outer (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) :
    (triangles (transposeEdges AC) (transposeEdges BC) AB).card = (triangles AB AC BC).card := by
  rw [card_triangles_swap_first, card_triangles_swap_last]

theorem indexPotential_swap_outer (wa : α → ℕ) (wb : β → ℕ) (wc : γ → ℕ)
    (AB : Finset (α × β)) (AC : Finset (α × γ)) (BC : Finset (β × γ)) :
    indexPotential wc wa wb (transposeEdges AC) (transposeEdges BC) AB =
      indexPotential wa wb wc AB AC BC := by
  rw [indexPotential_swap_first, indexPotential_swap_last]

theorem downClosed_of_minimal [LinearOrder α] [LinearOrder β] [LinearOrder γ]
    (wa : α → ℕ) (wb : β → ℕ) (wc : γ → ℕ)
    (hwa : StrictMono wa) (hwb : StrictMono wb) (hwc : StrictMono wc)
    (AB : Finset (α × β)) (AC : Finset (α × γ)) (BC : Finset (β × γ))
    (hmin : ∀ (A : Finset (α × β)) (B : Finset (α × γ)) (C : Finset (β × γ)),
      A.card = AB.card → B.card = AC.card → C.card = BC.card →
      (triangles AB AC BC).card ≤ (triangles A B C).card →
      indexPotential wa wb wc AB AC BC ≤ indexPotential wa wb wc A B C) :
    DownClosed AB ∧ DownClosed AC ∧ DownClosed BC := by
  have hfirst := leftClosed_pair_of_minimal wa wb wc hwa AB AC BC (by
    intro u v huv
    exact hmin _ _ _ (card_compressLeft _ huv.ne) (card_compressLeft _ huv.ne) rfl
      (card_triangles_compress_first AB AC BC huv.ne))
  have hsecond := leftClosed_pair_of_minimal wb wa wc hwb (transposeEdges AB) BC AC (by
    intro u v huv
    have htri := card_triangles_compress_first (transposeEdges AB) BC AC huv.ne
    have hp := hmin (transposeEdges (compressLeft (transposeEdges AB) u v)) AC
      (compressLeft BC u v) (by simp [card_compressLeft _ huv.ne]) rfl
      (card_compressLeft _ huv.ne) (by
        rw [card_triangles_swap_first] at htri
        exact htri.trans_eq (by
          simpa only [transposeEdges_transposeEdges] using
            card_triangles_swap_first (transposeEdges (compressLeft (transposeEdges AB) u v))
              AC (compressLeft BC u v)))
    calc
      _ = indexPotential wa wb wc AB AC BC := indexPotential_swap_first wa wb wc AB AC BC
      _ ≤ _ := hp
      _ = _ := by
        symm
        simpa only [transposeEdges_transposeEdges] using
          indexPotential_swap_first wa wb wc (transposeEdges (compressLeft (transposeEdges AB) u v))
            AC (compressLeft BC u v))
  have hthird := leftClosed_pair_of_minimal wc wa wb hwc
    (transposeEdges AC) (transposeEdges BC) AB (by
    intro u v huv
    have htri := card_triangles_compress_first (transposeEdges AC) (transposeEdges BC) AB huv.ne
    have hp := hmin AB (transposeEdges (compressLeft (transposeEdges AC) u v))
      (transposeEdges (compressLeft (transposeEdges BC) u v)) rfl
      (by simp [card_compressLeft _ huv.ne]) (by simp [card_compressLeft _ huv.ne]) (by
        rw [card_triangles_swap_outer] at htri
        exact htri.trans_eq (by
          simpa only [transposeEdges_transposeEdges] using
            card_triangles_swap_outer AB (transposeEdges (compressLeft (transposeEdges AC) u v))
              (transposeEdges (compressLeft (transposeEdges BC) u v))))
    calc
      _ = indexPotential wa wb wc AB AC BC := indexPotential_swap_outer wa wb wc AB AC BC
      _ ≤ _ := hp
      _ = _ := by
        symm
        simpa only [transposeEdges_transposeEdges] using indexPotential_swap_outer wa wb wc AB
          (transposeEdges (compressLeft (transposeEdges AC) u v))
          (transposeEdges (compressLeft (transposeEdges BC) u v)))
  exact ⟨DownClosed.of_left_right hfirst.1 hsecond.1,
    DownClosed.of_left_right hfirst.2 hthird.1,
    DownClosed.of_left_right hsecond.2 hthird.2⟩

theorem exists_downClosed [LinearOrder α] [LinearOrder β] [LinearOrder γ]
    (wa : α → ℕ) (wb : β → ℕ) (wc : γ → ℕ)
    (hwa : StrictMono wa) (hwb : StrictMono wb) (hwc : StrictMono wc)
    (AB : Finset (α × β)) (AC : Finset (α × γ)) (BC : Finset (β × γ)) :
    ∃ (A : Finset (α × β)) (B : Finset (α × γ)) (C : Finset (β × γ)),
      A.card = AB.card ∧ B.card = AC.card ∧ C.card = BC.card ∧
      (triangles AB AC BC).card ≤ (triangles A B C).card ∧
      DownClosed A ∧ DownClosed B ∧ DownClosed C := by
  let P : ℕ → Prop := fun k => ∃ (A : Finset (α × β)) (B : Finset (α × γ)) (C : Finset (β × γ)),
    A.card = AB.card ∧ B.card = AC.card ∧ C.card = BC.card ∧
      (triangles AB AC BC).card ≤ (triangles A B C).card ∧ indexPotential wa wb wc A B C = k
  have hex : ∃ k, P k := ⟨_, AB, AC, BC, rfl, rfl, rfl, le_rfl, rfl⟩
  obtain ⟨A, B, C, hA, hB, hC, htri, hpot⟩ := Nat.find_spec hex
  refine ⟨A, B, C, hA, hB, hC, htri, ?_⟩
  apply downClosed_of_minimal wa wb wc hwa hwb hwc
  intro A' B' C' hA' hB' hC' htri'
  rw [hpot]
  exact Nat.find_min' hex ⟨A', B', C', hA'.trans hA, hB'.trans hB,
    hC'.trans hC, htri.trans htri', rfl⟩
end

end Lemmata.Centroid.Combinatorics
