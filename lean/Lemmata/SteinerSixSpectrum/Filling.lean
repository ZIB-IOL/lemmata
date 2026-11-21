module

public import Lemmata.SteinerSixSpectrum.Assembly
public import Mathlib.Logic.Equiv.Fin.Basic

public section

namespace Lemmata.SteinerSixSpectrum

namespace SteinerSystem

/-- The empty family on at most one point. -/
def empty (X : Type*) [Subsingleton X] : SteinerSystem X where
  blocks := ∅
  six := by simp
  eligible_of_mem := by simp
  cover := fun x y h _ => (h (Subsingleton.elim x y)).elim

/-- The unique block on six points. -/
def single (X : Type*) [Fintype X] (hX : Fintype.card X = 6) : SteinerSystem X where
  blocks := {Finset.univ}
  six := by
    intro B hB
    have h : B = Finset.univ := hB
    simp [h, hX]
  eligible_of_mem := by simp
  cover x y _ _ := ⟨Finset.univ, by simp, fun _ h => h.1⟩

/-- Transport a Steiner system to a point type of the specified cardinality. -/
noncomputable def onType {m : ℕ} (d : SteinerSystem (Fin m)) (X : Type*) [Fintype X]
    (size : Fintype.card X = m) : SteinerSystem X :=
  d.relabel (Fintype.equivOfCardEq (by simpa using size.symm))

private def inside {H G : Type*} (B : Finset (H ⊕ G)) : Prop :=
  ∀ z ∈ B, ∃ a : H, z = Sum.inl a

/-- Delete the blocks entirely in the shared points when all pairs there are already
covered by such blocks. -/
private def punch {H G : Type*} (d : SteinerSystem (H ⊕ G))
    (closed : ∀ x y : H, x ≠ y →
      ∃ B ∈ d.blocks, Sum.inl x ∈ B ∧ Sum.inl y ∈ B ∧ inside B) :
    PairDesign (H ⊕ G) outsideHole where
  blocks := { B | B ∈ d.blocks ∧ ¬inside B }
  six B h := d.six B h.1
  eligible_of_mem := by
    intro B hB x hx y hy hne
    cases x with
    | inr => trivial
    | inl x =>
      cases y with
      | inr => trivial
      | inl y =>
        obtain ⟨C, hC, hcx, hcy, hinside⟩ := closed x y (fun h => hne (congrArg Sum.inl h))
        obtain ⟨A, _, unique⟩ := d.cover (.inl x) (.inl y) hne trivial
        have eq : B = C :=
          (unique B ⟨hB.1, hx, hy⟩).trans (unique C ⟨hC, hcx, hcy⟩).symm
        exact hB.2 (eq ▸ hinside)
  cover := by
    intro x y hne hpair
    obtain ⟨B, ⟨hB, hx, hy⟩, unique⟩ := d.cover x y hne trivial
    have hout : ¬inside B := by
      intro h
      obtain ⟨a, rfl⟩ := h x hx
      obtain ⟨b, rfl⟩ := h y hy
      exact hpair
    exact ⟨B, ⟨⟨hB, hout⟩, hx, hy⟩, fun C h => unique C ⟨h.1.1, h.2⟩⟩

/-- Standard filling for a group with one shared point. -/
noncomputable def onePoint {G : Type*} [Fintype G]
    (d : SteinerSystem (Fin (Fintype.card G + 1))) :
    PairDesign (Fin 1 ⊕ G) outsideHole :=
  (d.onType _ (by simp [Nat.add_comm])).punch
    (fun x y h => (h (Subsingleton.elim x y)).elim)

/-- Standard filling for a group with a shared block. Place any block on the shared
points, then delete that block so it will only be inserted once. -/
noncomputable def sharedBlock {G : Type*} [Fintype G]
    (d : SteinerSystem (Fin (Fintype.card G + 6))) :
    PairDesign (Fin 6 ⊕ G) outsideHole := by
  classical
  let V := Fin (Fintype.card G + 6)
  let x : V := ⟨0, by omega⟩
  let y : V := ⟨1, by omega⟩
  have hxy : x ≠ y := by
    intro h
    have hval : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  let B := (d.cover x y hxy trivial).exists.choose
  have hB : B ∈ d.blocks := (d.cover x y hxy trivial).exists.choose_spec.1
  let U := { z : V // z ∈ B }
  let W := { z : V // z ∉ B }
  let split : U ⊕ W ≃ V := Equiv.sumCompl (fun z => z ∈ B)
  have cardU : Fintype.card U = 6 := by
    change Fintype.card {z : V // z ∈ B} = 6
    rw [Fintype.card_coe, d.six B hB]
  have cardW : Fintype.card W = Fintype.card G := by
    have h := Fintype.card_congr split
    rw [Fintype.card_sum, cardU] at h
    change 6 + Fintype.card W = Fintype.card (Fin (Fintype.card G + 6)) at h
    simp only [Fintype.card_fin] at h
    omega
  let u : Fin 6 ≃ U := Fintype.equivOfCardEq (by simpa using cardU.symm)
  let w : G ≃ W := Fintype.equivOfCardEq cardW.symm
  let e : (Fin 6 ⊕ G) ≃ V := (Equiv.sumCongr u w).trans split
  have memB (z : Fin 6 ⊕ G) : e z ∈ B ↔ ∃ a : Fin 6, z = Sum.inl a := by
    cases z with
    | inl a => exact ⟨fun _ => ⟨a, rfl⟩, fun _ => (u a).property⟩
    | inr b =>
      exact ⟨fun h => ((w b).property h).elim, by rintro ⟨a, he⟩; cases he⟩
  refine punch (d.relabel e.symm) ?_
  intro a b _
  let C := B.map e.symm.toEmbedding
  have hC : C ∈ (d.relabel e.symm).blocks := d.map_mem_relabel e.symm hB
  have memC (z : Fin 6 ⊕ G) : z ∈ C ↔ e z ∈ B := by
    constructor
    · intro h
      obtain ⟨v, hv, eq⟩ := Finset.mem_map.mp h
      change e.symm v = z at eq
      rwa [← eq, e.apply_symm_apply]
    · intro h
      exact Finset.mem_map.mpr ⟨e z, h, e.symm_apply_apply z⟩
  exact ⟨C, hC, (memC _).mpr ((memB _).mpr ⟨a, rfl⟩),
    (memC _).mpr ((memB _).mpr ⟨b, rfl⟩), fun z hz => (memB z).mp ((memC z).mp hz)⟩

end SteinerSystem

/-- Complete a group-divisible design by adjoining zero, one, or six shared points. -/
theorem fillToOrder {I : Type*} [Fintype I] {G : I → Type*} [∀ i, Fintype (G i)]
    {e n : ℕ} (outer : PairDesign (Σ i, G i) (fun x y => x.1 ≠ y.1))
    (shared : e = 0 ∨ e = 1 ∨ e = 6)
    (fill : ∀ i, Nonempty (SteinerSystem (Fin (Fintype.card (G i) + e))))
    (size : Fintype.card (Fin e ⊕ (Σ i, G i)) = n) :
    Nonempty (SteinerSystem (Fin n)) := by
  classical
  suffices result : Nonempty (SteinerSystem (Fin e ⊕ (Σ i, G i))) from
    ⟨result.some.relabel (Fintype.equivOfCardEq (by simpa using size))⟩
  rcases shared with rfl | rfl | rfl
  · refine ⟨fillGroups outer (SteinerSystem.empty (Fin 0)) (fun i => ?_)⟩
    apply ((fill i).some.onType (Fin 0 ⊕ G i) (by simp)).congr
    rintro (x | x) (y | y) <;> first | exact Fin.elim0 x | exact Fin.elim0 y | rfl
  · exact ⟨fillGroups outer (SteinerSystem.empty (Fin 1))
      (fun i => SteinerSystem.onePoint (fill i).some)⟩
  · exact ⟨fillGroups outer (SteinerSystem.single (Fin 6) (Fintype.card_fin _))
      (fun i => SteinerSystem.sharedBlock (fill i).some)⟩

end Lemmata.SteinerSixSpectrum
