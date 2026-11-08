module

public import Lemmata.RM59.Proof.FlagWitnessSound
public import Lemmata.RM59.Proof.BinaryQuadGeometry
public meta import Lemmata.RM59.Proof.FlagWitnessChecks
public meta import Lemmata.RM59.Proof.FlagGeometry

@[expose] public section

namespace Lemmata.RM59.FlagNormalizing

open Lemmata.RM59.Packed Lemmata.RM59.FlagActions Lemmata.RM59.FlagGeometry Lemmata.RM59.FlagWitnessChecks
open Lemmata.RM59.BinaryQuadGeometry
open scoped Matrix

def baseIndex (which : Fin 2) : Fin 9 := if which.val = 0 then 1 else 4

def base (which : Fin 2) : Point 9 := decodePoint (basePoint which)

def clearLinear (which : Fin 2) : Point 9 →ₗ[Field] Point 9 where
  toFun x := x + x (baseIndex which) • base which
  map_add' x y := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' r x := by
    rcases field_eq_zero_or_one r with rfl | rfl <;> simp

theorem clear_decode_checked : ∀ (which : Fin 2) (x : PackedPoint),
    decodePoint (clear which x) = clearLinear which (decodePoint x) := by native_decide

theorem base_coordinate : ∀ which : Fin 2, base which (baseIndex which) = 1 := by native_decide

theorem clear_coordinate (which : Fin 2) (x : Point 9) :
    clearLinear which x (baseIndex which) = 0 := by
  change x (baseIndex which) + x (baseIndex which) * base which (baseIndex which) = 0
  rw [base_coordinate, mul_one, field_add_self]

def Domain (which : Fin 2) (a b : Point 9) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ a (baseIndex which) = 0 ∧ b (baseIndex which) = 0 ∧
    a ∈ space 2 ∧ b ∈ space 2 ∧
    (which.val = 0 ∨ (a ∉ space 0 ∧ b ∉ space 0 ∧ a + b ∉ space 0))

instance (which : Fin 2) (a b : Point 9) : Decidable (Domain which a b) := by
  unfold Domain
  infer_instance

theorem allowed_decode_checked : ∀ (which : Fin 2) (a b : PackedPoint),
    allowed which a b = true ↔ Domain which (decodePoint a) (decodePoint b) := by native_decide

theorem point_allowed_checked : ∀ (which : Fin 2) (x : PackedPoint),
    pointAllowed which x = true ↔
      if which.val = 0 then decodePoint x ∉ space 2 else
        decodePoint x ∈ space 2 ∧ decodePoint x ∉ space 1 := by native_decide

theorem domain_available (which : Fin 2) (a b : Point 9) (hab : Domain which a b) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G seed ∧ G.card = 30 ∧
      quad a b (base which) ⊆ G := by
  have hc : allowed which (encodePoint a) (encodePoint b) = true := by
    apply (allowed_decode_checked _ _ _).2
    simpa only [decodePoint_encodePoint] using hab
  obtain ⟨G, hG, hn, hm⟩ := FlagWitnessSound.canonical_available _ _ _ hc
  exact ⟨G, hG, hn, by simpa only [FlagWitnessSound.canonical, quad,
    decodePoint_encodePoint, base] using hm⟩

theorem clear_independent (which : Fin 2) (a b : Point 9)
    (h : LinearIndependent Field ![a, b, base which]) :
    LinearIndependent Field ![clearLinear which a, clearLinear which b] := by
  exact shifted_pair_independent a b (base which) h (a (baseIndex which)) (b (baseIndex which))

theorem distinct_of_independent (a b : Point 9) (h : LinearIndependent Field ![a, b]) : a ≠ b := by
  intro he
  have hi := h.injective (show (![a, b] : Fin 2 → Point 9) 0 = ![a, b] 1 from he)
  exact (by decide : (0 : Fin 2) ≠ 1) hi

theorem clear_domain_A (a b : Point 9) (h : LinearIndependent Field ![a, b, base 0]) :
    Domain 0 (clearLinear 0 a) (clearLinear 0 b) := by
  have hi := clear_independent 0 a b h
  refine ⟨hi.ne_zero 0, hi.ne_zero 1, distinct_of_independent _ _ hi,
    clear_coordinate 0 a, clear_coordinate 0 b, ?_, ?_, Or.inl rfl⟩
  · exact (hyperplane_mem _).2 (clear_coordinate 0 a)
  · exact (hyperplane_mem _).2 (clear_coordinate 0 b)

theorem clear_domain_B (a b : Point 9) (E : Submodule Field (Point 9))
    (h : LinearIndependent Field ![a, b, base 1])
    (ha : a ∈ E) (hb : b ∈ E) (ht : base 1 ∈ E)
    (hH : E ≤ space 2) (hU : Disjoint E (space 0)) :
    Domain 1 (clearLinear 1 a) (clearLinear 1 b) := by
  have hi := clear_independent 1 a b h
  have haE : clearLinear 1 a ∈ E := E.add_mem ha (E.smul_mem _ ht)
  have hbE : clearLinear 1 b ∈ E := E.add_mem hb (E.smul_mem _ ht)
  have hab : clearLinear 1 a ≠ clearLinear 1 b := distinct_of_independent _ _ hi
  have haU : clearLinear 1 a ∉ space 0 := by
    intro hu
    exact hi.ne_zero 0 ((Submodule.disjoint_def.1 hU) _ haE hu)
  have hbU : clearLinear 1 b ∉ space 0 := by
    intro hu
    exact hi.ne_zero 1 ((Submodule.disjoint_def.1 hU) _ hbE hu)
  have habU : clearLinear 1 a + clearLinear 1 b ∉ space 0 := by
    intro hu
    have hz := (Submodule.disjoint_def.1 hU) _ (E.add_mem haE hbE) hu
    have he := congrArg (fun x => x + clearLinear 1 b) hz
    rw [add_assoc, point_add_self, add_zero, zero_add] at he
    exact hab he
  exact ⟨hi.ne_zero 0, hi.ne_zero 1, hab, clear_coordinate 1 a, clear_coordinate 1 b,
    hH haE, hH hbE, Or.inr ⟨haU, hbU, habU⟩⟩

end Lemmata.RM59.FlagNormalizing
