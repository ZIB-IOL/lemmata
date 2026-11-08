module

public import Lemmata.RM59.Proof.SimplexSearch

@[expose] public section

namespace Lemmata.RM59.SimplexSearch

open Packed PlaneCertificates PlaneGeometry

theorem relativeIndependent_of_linearIndependent {ι : Type*} [Fintype ι]
    (v : ι → PackedPoint) (hLI : LinearIndependent Field (fun i => decodePoint (v i))) :
    RelativeIndependent [0] (Finset.univ.image v) := by
  intro x hx hmem
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  have hnot := hLI.notMem_span_image (s := {j | j ≠ i}) (x := i) (by simp)
  apply hnot
  apply (show packedSpan ([0].toFinset ∪ (Finset.univ.image v).erase (v i)) ≤
      Submodule.span Field ((fun j => decodePoint (v j)) '' {j | j ≠ i}) from ?_) hmem
  apply Submodule.span_le.mpr
  rintro _ ⟨y, hy, rfl⟩
  rcases Finset.mem_union.mp hy with hy | hy
  · have hyzero : y = 0 := by simpa using hy
    subst y
    rw [decodePoint_zero]
    exact Submodule.zero_mem _
  · obtain ⟨hyne, hy⟩ := Finset.mem_erase.mp hy
    obtain ⟨j, _, heq⟩ := Finset.mem_image.mp hy
    apply Submodule.subset_span
    refine ⟨j, ?_, congrArg decodePoint heq⟩
    intro hji
    subst j
    exact hyne heq.symm

private theorem centered_linearIndependent {d : Nat} (p : Option (Fin d) → Point 9)
    (hzero : p none = 0) (hAI : AffineIndependent Field p) :
    LinearIndependent Field (fun i : Fin d => p (some i)) := by
  have hd := (affineIndependent_iff_linearIndependent_vsub Field p none).mp hAI
  let inclusion : Fin d → {i : Option (Fin d) // i ≠ none} := fun i => ⟨some i, by simp⟩
  have hinj : Function.Injective inclusion := by
    intro i j hij
    exact Option.some.inj (congrArg Subtype.val hij)
  have hs := hd.comp inclusion hinj
  simpa only [inclusion, Function.comp_def, vsub_eq_sub, hzero, sub_zero] using hs

theorem existsExtension_of_centered_affineIndependent (allowed : PackedAllowed) {d : Nat}
    (hd : 2 ≤ d) (p : Option (Fin d) → Point 9) (hzero : p none = 0)
    (hAI : AffineIndependent Field p) (hplanes : AllTriplePlanes (semantic allowed) p) :
    existsExtension allowed d [0] (rootCandidates allowed) BinarySpan9.empty = true := by
  classical
  let v : Fin d → PackedPoint := fun i => encodePoint (p (some i))
  let extension := Finset.univ.image v
  have hLI : LinearIndependent Field (fun i => decodePoint (v i)) := by
    simpa only [v, decodePoint_encodePoint] using centered_linearIndependent p hzero hAI
  have hind : RelativeIndependent [0] extension := relativeIndependent_of_linearIndependent v hLI
  have hinj : Function.Injective v := by
    intro i j hij
    exact hLI.injective (congrArg decodePoint hij)
  have hcard : extension.card = d := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hpreimage (x : PackedPoint) (hx : x ∈ [0].toFinset ∪ extension) :
      ∃ i : Option (Fin d), encodePoint (p i) = x := by
    rcases Finset.mem_union.mp hx with hx | hx
    · have hxzero : x = 0 := by simpa using hx
      exact ⟨none, by rw [hzero, encodePoint_zero, hxzero]⟩
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
      exact ⟨some i, hi⟩
  have htriples : TripleCompatible allowed ([0].toFinset ∪ extension) := by
    intro x hx y hy z hz hxy hxz hyz
    obtain ⟨i, rfl⟩ := hpreimage x hx
    obtain ⟨j, rfl⟩ := hpreimage y hy
    obtain ⟨k, rfl⟩ := hpreimage z hz
    have hp := hplanes i j k (fun h => hxy (congrArg (fun r => encodePoint (p r)) h))
      (fun h => hxz (congrArg (fun r => encodePoint (p r)) h))
      (fun h => hyz (congrArg (fun r => encodePoint (p r)) h))
    simpa only [semantic, encodePoint_add] using hp
  have hsubset : extension ⊆ (rootCandidates allowed).toFinset := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    apply List.mem_toFinset.mpr
    apply List.mem_filter.mpr
    refine ⟨List.mem_finRange _, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
    · apply bne_iff_ne.mpr
      intro hz
      apply relativeIndependent_not_mem hind hx
      simp [hz]
    · letI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
      obtain ⟨j, hji⟩ := exists_ne i
      apply List.any_eq_true.mpr
      refine ⟨v j, List.mem_finRange _, ?_⟩
      have hp := hplanes none (some i) (some j) (by simp) (by simp)
        (by simpa using hji.symm)
      simpa only [semantic, hzero, zero_add, v] using hp
  exact existsExtension_complete allowed d [0] (rootCandidates allowed) BinarySpan9.empty
    extension hcard hsubset (BinarySpan9.empty_rows_mem _) hind htriples

theorem noSimplex_excludes_centered (allowed : PackedAllowed) {d : Nat} (hd : 2 ≤ d)
    (hcheck : noSimplex allowed d = true) (p : Option (Fin d) → Point 9)
    (hzero : p none = 0) (hAI : AffineIndependent Field p)
    (hplanes : AllTriplePlanes (semantic allowed) p) : False := by
  have hyes := existsExtension_of_centered_affineIndependent allowed hd p hzero hAI hplanes
  simp only [noSimplex, hyes, Bool.not_true, Bool.false_eq_true] at hcheck

private theorem point_add_self (x : Point 9) : x + x = 0 := by
  funext i
  exact field_add_self _

theorem noSimplex_excludes (allowed : PackedAllowed) {d : Nat} (hd : 2 ≤ d)
    (hcheck : noSimplex allowed d = true) (P : Finset (Point 9))
    (hcard : P.card = d + 1) (hAI : AffineIndependent Field ((↑) : P → Point 9))
    (hplanes : AllTriplePlanes (semantic allowed) ((↑) : P → Point 9)) : False := by
  classical
  let e : Option (Fin d) ≃ P := Fintype.equivOfCardEq (by simp [hcard])
  let p : Option (Fin d) → Point 9 := fun i => (e i).val
  have hp : AffineIndependent Field p := hAI.comp_embedding e.toEmbedding
  have hpp : AllTriplePlanes (semantic allowed) p :=
    PlaneDeletion.allTriplePlanes_reindex _ _ e e.injective hplanes
  let q : Option (Fin d) → Point 9 := fun i => p i + p none
  have hqzero : q none = 0 := point_add_self _
  have hq : AffineIndependent Field q := by
    have ht : AffineIndependent Field ((p none) +ᵥ p) :=
      (affineIndependent_vadd (k := Field) (v := p none)).mpr hp
    have heq : ((p none) +ᵥ p) = q := by
      funext i
      exact add_comm _ _
    simpa only [heq] using ht
  have hqp : AllTriplePlanes (semantic allowed) q :=
    (allTriplePlanes_translate (semantic allowed) p (p none)).mpr hpp
  exact noSimplex_excludes_centered allowed hd hcheck q hqzero hq hqp

end Lemmata.RM59.SimplexSearch
