module

public import Lemmata.CocubicCovering.Compute.Encoding
public meta import Lemmata.CocubicCovering.Compute.Encoding
public import Lemmata.CocubicCovering.Compute.Algebra
public meta import Lemmata.CocubicCovering.Compute.Algebra
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Lemmata.CocubicCovering.Compute.Encoding

open Algebra Algebra.Bits

theorem rowCheck_sound (assignment : Nat → Field) (dictionary : Nat → Nat)
    (size : Nat) (row indices : List Nat) (bits : Nat)
    (checked : rowCheck dictionary size row indices bits = true) :
    eval assignment (polynomial dictionary size bits) = eval assignment row := by
  obtain ⟨h, hc⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨hb, hr⟩ := Bool.and_eq_true_iff.mp h
  have hb : ∀ i ∈ indices, i < size :=
    fun i hi => of_decide_eq_true ((List.all_eq_true.mp hb) i hi)
  have hr : indices.map dictionary = row := of_decide_eq_true hr
  have hc : Algebra.Bits.encodeIndices indices = bits := of_decide_eq_true hc
  rw [← hc, eval_encodeIndices assignment dictionary size indices hb, hr]

theorem encode_filtered_pairs (pairs : List (Nat × Nat)) (word : Nat) :
    Algebra.Bits.encodeIndices ((pairs.filter (fun pair => word.testBit pair.1)).map Prod.fst) =
      word &&& Algebra.Bits.encodeIndices (pairs.map Prod.fst) := by
  induction pairs with
  | nil => simp
  | cons pair pairs ih =>
      cases hbit : word.testBit pair.1 <;>
        simp [hbit, Nat.and_xor_distrib_left, Nat.and_two_pow, ih]

private theorem mapAcc_eq (pairs : List (Nat × Nat)) (word accumulator : Nat) :
    mapAcc word pairs accumulator = accumulator ^^^
      Algebra.Bits.encodeIndices ((pairs.filter fun pair => word.testBit pair.1).map Prod.snd) := by
  induction pairs generalizing accumulator with
  | nil => simp [mapAcc]
  | cons pair pairs ih =>
      cases hbit : word.testBit pair.1 <;>
        simp [mapAcc, hbit, ih, Nat.xor_assoc]

theorem mapped_eq (pairs : List (Nat × Nat)) (word : Nat) :
    mapped pairs word =
      Algebra.Bits.encodeIndices ((pairs.filter fun pair => word.testBit pair.1).map Prod.snd) := by
  simp [mapped, mapAcc_eq]

theorem mapped_product (assignment : Nat → Field) (dictionary : Nat → Nat)
    (size coefficient : Nat) (pairs : List (Nat × Nat))
    (checked : mapCheck dictionary size coefficient pairs = true)
    (domain word : Nat) (hdomain : domain = Lemmata.CocubicCovering.Compute.Encoding.encodeIndices (pairs.map Prod.fst))
    (hword : word &&& domain = word) :
    eval assignment (polynomial dictionary size (mapped pairs word)) =
      eval assignment (polynomial dictionary size word) * evalMonomial assignment coefficient := by
  have hc : ∀ pair ∈ pairs, pair.1 < size ∧ pair.2 < size ∧
      dictionary pair.2 = dictionary pair.1 ||| coefficient := by
    intro pair hp
    exact of_decide_eq_true ((List.all_eq_true.mp checked) pair hp)
  let chosen := pairs.filter (fun pair => word.testBit pair.1)
  have hmem : ∀ pair ∈ chosen, pair ∈ pairs := fun pair hp => (List.mem_filter.mp hp).1
  have hencoded : Algebra.Bits.encodeIndices (chosen.map Prod.fst) = word := by
    rw [encode_filtered_pairs]
    change word &&& Lemmata.CocubicCovering.Compute.Encoding.encodeIndices (pairs.map Prod.fst) = word
    rw [← hdomain, hword]
  have hsource : eval assignment (polynomial dictionary size word) =
      eval assignment (chosen.map (fun pair => dictionary pair.1)) := by
    rw [← hencoded, eval_encodeIndices]
    · simp only [List.map_map, Function.comp_def]
    · intro i hi
      obtain ⟨pair, hp, rfl⟩ := List.mem_map.mp hi
      exact (hc pair (hmem pair hp)).1
  rw [mapped_eq, eval_encodeIndices, hsource]
  · simp only [List.map_map, Function.comp_def]
    change eval assignment (chosen.map (fun pair => dictionary pair.2)) = _
    have heval : ∀ selected : List (Nat × Nat),
        (∀ pair ∈ selected, dictionary pair.2 = dictionary pair.1 ||| coefficient) →
        eval assignment (selected.map (fun pair => dictionary pair.2)) =
          eval assignment (selected.map (fun pair => dictionary pair.1)) *
            evalMonomial assignment coefficient := by
      intro selected
      induction selected with
      | nil => intro _; simp
      | cons pair selected ih =>
          intro hs
          simp only [List.map_cons, eval_cons, hs pair (by simp), evalMonomial_or]
          rw [ih (fun p hp => hs p (by simp [hp]))]
          ring
    exact heval chosen (fun pair hp => (hc pair (hmem pair hp)).2.2)
  · intro i hi
    obtain ⟨pair, hp, rfl⟩ := List.mem_map.mp hi
    exact (hc pair (hmem pair hp)).2.1

theorem Derives.sound {dictionary : Nat → Nat} {size : Nat} {inputs : List Nat → Prop}
    {bits : Nat} (certificate : Derives dictionary size inputs bits)
    (assignment : Nat → Field) (hypotheses : ∀ row, inputs row → eval assignment row = 0) :
    eval assignment (polynomial dictionary size bits) = 0 := by
  induction certificate with
  | input encoded premise =>
      exact (rowCheck_sound assignment _ _ _ _ _ encoded).trans
        (hypotheses _ premise)
  | mappedProduct checked encoded contained previous ih =>
      rw [mapped_product assignment _ _ _ _ checked _ _ encoded contained, ih, zero_mul]
  | xor a b ha hb => rw [eval_xor, ha, hb, zero_add]
  | cast equal previous ih => simpa only [← equal] using ih

theorem Derives.refutes {dictionary : Nat → Nat} {size : Nat} {inputs : List Nat → Prop}
    (certificate : Derives dictionary size inputs 1) (hsize : 0 < size)
    (hconstant : dictionary 0 = 0) :
    ¬ ∃ assignment : Nat → Field, ∀ row, inputs row → eval assignment row = 0 := by
  rintro ⟨assignment, hypotheses⟩
  have hz := certificate.sound assignment hypotheses
  have hone : eval assignment (polynomial dictionary size 1) = 1 := by
    change eval assignment (polynomial dictionary size (2 ^ 0)) = 1
    rw [eval_two_pow assignment dictionary size 0 hsize, hconstant]
    simp [evalMonomial, Algebra.Monomial.evalMonomialField]
  exact one_ne_zero (hone.symm.trans hz)

end Lemmata.CocubicCovering.Compute.Encoding
