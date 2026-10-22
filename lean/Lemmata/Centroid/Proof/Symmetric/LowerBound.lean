module

public import Lemmata.Centroid.Proof.Symmetric.Construction

@[expose] public section

namespace Lemmata.Centroid.Symmetric.Construction

open Classical

noncomputable section

variable {F K : Type*} [Field F] [Fintype K]

omit [Fintype K] in theorem exists_map_some_of_not_mem_none {d : ℕ} (s : Sym (Option K) d)
    (h : none ∉ s) :
    ∃ t : Sym K d, t.map some = s := by
  induction d with
  | zero => exact ⟨0, Subsingleton.elim _ _⟩
  | succ d ih =>
    obtain ⟨i, t, rfl⟩ := Sym.exists_eq_cons_of_succ s
    cases i with
    | none => exact False.elim (h (Sym.mem_cons_self _ _))
    | some i =>
      obtain ⟨u, hu⟩ := ih t (fun hn => h (Sym.mem_cons_of_mem hn))
      exact ⟨Sym.cons i u, by rw [Sym.map_cons, hu]⟩

def partialQuadrics (A : Finset K) : Finset (Sym (Option K) 2) :=
  Finset.univ.image (Sym.map some) ∪ A.image (fun i => quadricMonomial none (some i))

def partialCubics (A : Finset K) : Finset (Sym (Option K) 3) :=
  Finset.univ.image (Sym.map some) ∪
    (Finset.univ : Finset (Sym A 2)).image
      (fun q => Sym.cons none (q.map (fun i => some i.val)))

theorem partialQuadrics_card (A : Finset K) :
    (partialQuadrics A).card = (Fintype.card K + 1).choose 2 + A.card := by
  have hdisj : Disjoint
      ((Finset.univ : Finset (Sym K 2)).image (Sym.map some))
      (A.image (fun i => quadricMonomial none (some i))) := by
    apply Finset.disjoint_left.2
    intro q hq hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hq
    obtain ⟨i, hi, he⟩ := Finset.mem_image.1 hn
    have hnone : none ∈ t.map some := he ▸ Sym.mem_cons_self _ _
    simp [Sym.mem_map] at hnone
  have hinj : Function.Injective (fun i : K => quadricMonomial none (some i)) := by
    intro i j he
    have h := (Sym.cons_inj_right none _ _).1 he
    exact Option.some.inj (Sym.oneEquiv.injective h)
  rw [partialQuadrics, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (Sym.map_injective (Option.some_injective K) 2),
    Finset.card_image_of_injective _ hinj, Finset.card_univ, Sym.card_sym_eq_choose]
  congr 2

theorem partialCubics_card (A : Finset K) :
    (partialCubics A).card = (Fintype.card K + 2).choose 3 + (A.card + 1).choose 2 := by
  have hdisj : Disjoint
      ((Finset.univ : Finset (Sym K 3)).image (Sym.map some))
      ((Finset.univ : Finset (Sym A 2)).image
        (fun q => Sym.cons none (q.map (fun i => some i.val)))) := by
    apply Finset.disjoint_left.2
    intro q hq hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hq
    obtain ⟨r, hr, he⟩ := Finset.mem_image.1 hn
    have hnone : none ∈ t.map some := he ▸ Sym.mem_cons_self _ _
    simp [Sym.mem_map] at hnone
  have hinj : Function.Injective (fun q : Sym A 2 =>
      Sym.cons none (q.map (fun i => some i.val))) := by
    intro q r he
    apply Sym.map_injective (fun _ _ h => Subtype.ext (Option.some.inj h)) 2
    exact (Sym.cons_inj_right none _ _).1 he
  rw [partialCubics, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (Sym.map_injective (Option.some_injective K) 3),
    Finset.card_image_of_injective _ hinj, Finset.card_univ, Finset.card_univ,
    Sym.card_sym_eq_choose, Sym.card_sym_eq_choose, Fintype.card_coe]
  congr 2

theorem partialCubics_divisor (A : Finset K) (s : Sym (Option K) 3)
    (hs : s ∈ partialCubics A) (i : Option K) (q : Sym (Option K) 2)
    (he : s = Sym.cons i q) : q ∈ partialQuadrics A := by
  obtain hs | hs := Finset.mem_union.1 hs
  · obtain ⟨t, ht, hts⟩ := Finset.mem_image.1 hs
    have hsnone : none ∉ s := by rw [← hts]; simp [Sym.mem_map]
    have hqnone : none ∉ q := by
      intro hn
      apply hsnone
      rw [he]
      exact Sym.mem_cons_of_mem hn
    obtain ⟨u, hu⟩ := exists_map_some_of_not_mem_none q hqnone
    exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨u, Finset.mem_univ _, hu⟩)
  · obtain ⟨r, hr, hrs⟩ := Finset.mem_image.1 hs
    have hcons : Sym.cons none (r.map (fun j => some j.val)) = Sym.cons i q := hrs.trans he
    cases i with
    | none =>
      have hq : r.map (fun j => some j.val) = q := (Sym.cons_inj_right none _ _).1 hcons
      apply Finset.mem_union_left
      apply Finset.mem_image.2
      refine ⟨r.map Subtype.val, Finset.mem_univ _, ?_⟩
      rw [Sym.map_map]
      exact hq
    | some i =>
      have hn : none ∈ q := by
        have hm : none ∈ Sym.cons (some i) q := hcons ▸ Sym.mem_cons_self _ _
        exact (Sym.mem_cons.1 hm).resolve_left (by intro h; cases h)
      obtain ⟨u, hu⟩ := Sym.exists_cons_of_mem hn
      obtain ⟨x, hx⟩ := Sym.oneEquiv.surjective u
      have hq : q = quadricMonomial none x := by rw [hu, ← hx]; rfl
      have hrest : r.map (fun j => some j.val) = quadricMonomial (some i) x := by
        apply (Sym.cons_inj_right none _ _).1
        rw [hcons, hq]
        exact Sym.cons_swap (some i) none _
      have hxmem : x ∈ r.map (fun j => some j.val) := by
        rw [hrest]
        apply Sym.mem_cons_of_mem
        change x ∈ ({x} : Multiset (Option K))
        simp
      obtain ⟨j, hj, hjx⟩ := Sym.mem_map.1 hxmem
      apply Finset.mem_union_right
      apply Finset.mem_image.2
      exact ⟨j.val, j.property, by rw [hq, hjx]⟩

theorem partial_concise (A : Finset K) (hA : A.Nonempty) :
    Tensor.Concise (tensor (F := F) (partialQuadrics A)) := by
  apply concise
  intro i
  cases i with
  | none =>
    obtain ⟨a, ha⟩ := hA
    exact ⟨some a, Finset.mem_union_right _ (Finset.mem_image.2 ⟨a, ha, rfl⟩)⟩
  | some a =>
    refine ⟨some a, Finset.mem_union_left _ (Finset.mem_image.2 ?_)⟩
    exact ⟨quadricMonomial a a, Finset.mem_univ _, map_quadricMonomial some a a⟩

theorem partial_lower_bound (A : Finset K) :
    1 + (Fintype.card K + 2).choose 3 + (A.card + 1).choose 2 ≤
      Module.finrank F (Tensor.centroid (tensor (F := F) (partialQuadrics A))) := by
  have h := centroid_family_lower_bound (F := F) (partialQuadrics A) (partialCubics A)
    (partialCubics_divisor A)
  rw [partialCubics_card] at h
  omega

theorem partial_format (A : Finset K) :
    Fintype.card (Option K ⊕ partialQuadrics A) = symmetricBase (Fintype.card K) + A.card + 1 := by
  have hbase := full_format (K := K)
  simp only [Fintype.card_sum, Fintype.card_coe, Finset.card_univ,
    Sym.card_sym_eq_choose] at hbase
  have hindex : Fintype.card K + 2 - 1 = Fintype.card K + 1 := by omega
  rw [hindex] at hbase
  rw [Fintype.card_sum, Fintype.card_option, Fintype.card_coe, partialQuadrics_card]
  omega

theorem exists_relabel {α : Type*} [Fintype α] (T : Cubic F α) (N d : ℕ)
    (hcard : Fintype.card α = N) (hc : Tensor.Concise T) (hs : Cubic.IsSymmetric T)
    (hd : d ≤ Module.finrank F (Tensor.centroid T)) :
    ∃ S : Cubic F (Fin N), Tensor.Concise S ∧ Cubic.IsSymmetric S ∧
      d ≤ Module.finrank F (Tensor.centroid S) := by
  let e : α ≃ Fin N := (Fintype.equivFin α).trans (finCongr hcard)
  refine ⟨Tensor.relabel (fun _ => e) T, hc.relabel _, relabel_isSymmetric e hs, ?_⟩
  rw [Tensor.finrank_centroid_relabel]
  exact hd

theorem symmetric_lower_bound (N : ℕ) :
    ∃ T : Cubic F (Fin N), Tensor.Concise T ∧ Cubic.IsSymmetric T ∧
      symmetricBound N ≤ Module.finrank F (Tensor.centroid T) := by
  by_cases hsmall : N ≤ 1
  · refine ⟨Lemmata.Centroid.Construction.diagonal N, Lemmata.Centroid.Construction.diagonal_concise N,
      diagonal_isSymmetric N, ?_⟩
    have hbound : symmetricBound N = N := by simp [symmetricBound, hsmall]
    rw [hbound]
    exact Lemmata.Centroid.Construction.diagonal_centroid_lower_bound N
  · have hN₂ : 2 ≤ N := by omega
    let n := symmetricIndex N
    let s := N - symmetricBase n
    have hn : 0 < n := symmetricIndex_pos hN₂
    have hs : s ≤ n + 1 := symmetric_remainder_le N
    have hN : N = symmetricBase n + s := symmetric_decomposition N
    have hbound : symmetricBound N = symmetricBoundAt n s := symmetricBound_eq hN₂ hs hN
    let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    by_cases hmax : s.choose 2 ≤ s
    · let T := paddedFull (F := F) (K := Fin n) s
      have hcard : Fintype.card (FullCoordinates (Fin n) ⊕ Fin s) = N := by
        exact (paddedFull_format (K := Fin n) s).trans (by
          rw [Fintype.card_fin]
          exact hN.symm)
      apply exists_relabel T N (symmetricBound N) hcard
        (paddedFull_concise (F := F) (K := Fin n) s)
        (paddedFull_isSymmetric (F := F) (K := Fin n) s)
      dsimp only [T]
      have hd := paddedFull_lower_bound (F := F) (K := Fin n) s
      rw [Fintype.card_fin] at hd
      rw [hbound, symmetricBoundAt, max_eq_left hmax]
      omega
    · have hs₂ : 2 ≤ s := by
        by_contra h
        have hcases : s = 0 ∨ s = 1 := by omega
        obtain h0 | h1 := hcases
        · simp [h0] at hmax
        · simp [h1] at hmax
      have hr : s - 1 ≤ (Finset.univ : Finset (Fin n)).card := by
        rw [Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨A, _, hA⟩ := Finset.exists_subset_card_eq hr
      have hAnonempty : A.Nonempty := Finset.card_pos.1 (by rw [hA]; omega)
      let T := tensor (F := F) (partialQuadrics A)
      have hcard : Fintype.card (Option (Fin n) ⊕ partialQuadrics A) = N := by
        rw [partial_format, Fintype.card_fin, hA]
        omega
      apply exists_relabel T N (symmetricBound N) hcard (partial_concise (F := F) A hAnonempty)
        (tensor_isSymmetric (F := F) (partialQuadrics A))
      dsimp only [T]
      have hd := partial_lower_bound (F := F) A
      rw [Fintype.card_fin, hA, Nat.sub_add_cancel (by omega : 1 ≤ s)] at hd
      rw [hbound, symmetricBoundAt, max_eq_right (Nat.le_of_not_ge hmax)]
      omega

end

end Lemmata.Centroid.Symmetric.Construction
