module

public import Lemmata.SteinerSixSpectrum.Statement
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Sigma

public section

namespace Lemmata.SteinerSixSpectrum

/-- The image of an eligible pair under an embedding. -/
def imagePairs {X Y : Type*} (f : X ↪ Y) (R : X → X → Prop) (x y : Y) : Prop :=
  ∃ a b, f a = x ∧ f b = y ∧ R a b

namespace PairDesign

/-- Transfer a design to an embedded copy of its points. -/
def embed {X Y : Type*} {R : X → X → Prop} (d : PairDesign X R) (f : X ↪ Y) :
    PairDesign Y (imagePairs f R) where
  blocks := { B | ∃ A ∈ d.blocks, A.map f = B }
  six := by
    rintro _ ⟨A, hA, rfl⟩
    rw [Finset.card_map, d.six A hA]
  eligible_of_mem := by
    rintro _ ⟨A, hA, rfl⟩ x hx y hy hne
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact ⟨a, b, rfl, rfl, d.eligible_of_mem A hA a ha b hb (fun e => hne (congrArg f e))⟩
  cover := by
    rintro x y hne ⟨a, b, rfl, rfl, hab⟩
    obtain ⟨A, ⟨hA, ha, hb⟩, unique⟩ := d.cover a b (fun e => hne (congrArg f e)) hab
    refine ⟨A.map f, ⟨⟨A, hA, rfl⟩, Finset.mem_map.mpr ⟨a, ha, rfl⟩,
      Finset.mem_map.mpr ⟨b, hb, rfl⟩⟩, ?_⟩
    rintro _ ⟨⟨C, hC, rfl⟩, hx, hy⟩
    obtain ⟨a', ha', hea⟩ := Finset.mem_map.mp hx
    obtain ⟨b', hb', heb⟩ := Finset.mem_map.mp hy
    have hc : C = A := unique C ⟨hC, f.injective hea ▸ ha', f.injective heb ▸ hb'⟩
    rw [hc]

/-- Transfer a design between extensionally equal eligibility relations. -/
def congr {X : Type*} {R S : X → X → Prop} (d : PairDesign X R)
    (eqv : ∀ x y, R x y ↔ S x y) : PairDesign X S where
  blocks := d.blocks
  six := d.six
  eligible_of_mem B hB x hx y hy hne := (eqv x y).mp (d.eligible_of_mem B hB x hx y hy hne)
  cover x y hne h := d.cover x y hne ((eqv x y).mpr h)

/-- Relabel all the points of a design. -/
def relabel {X Y : Type*} {R : X → X → Prop} (d : PairDesign X R) (e : X ≃ Y) :
    PairDesign Y (fun x y => R (e.symm x) (e.symm y)) :=
  (d.embed e.toEmbedding).congr (by
    intro x y
    constructor
    · rintro ⟨a, b, rfl, rfl, h⟩
      simpa using h
    · intro h
      exact ⟨e.symm x, e.symm y, e.apply_symm_apply x, e.apply_symm_apply y, h⟩)

theorem map_mem_relabel {X Y : Type*} {R : X → X → Prop}
    (d : PairDesign X R) (e : X ≃ Y) {B : Finset X} (hB : B ∈ d.blocks) :
    B.map e.toEmbedding ∈ (d.relabel e).blocks :=
  ⟨B, hB, rfl⟩

/-- Combine designs whose eligible relations partition the pairs to be covered. -/
def assemble {X I : Type*} {R : I → X → X → Prop} {S : X → X → Prop}
    (d : ∀ i, PairDesign X (R i))
    (sound : ∀ i x y, R i x y → S x y)
    (owner : ∀ x y, x ≠ y → S x y → ∃! i, R i x y) : PairDesign X S where
  blocks := { B | ∃ i, B ∈ (d i).blocks }
  six := by
    rintro B ⟨i, hB⟩
    exact (d i).six B hB
  eligible_of_mem := by
    rintro B ⟨i, hB⟩ x hx y hy hne
    exact sound i x y ((d i).eligible_of_mem B hB x hx y hy hne)
  cover := by
    intro x y hne hs
    obtain ⟨i, hi, samePiece⟩ := owner x y hne hs
    obtain ⟨B, ⟨hB, hx, hy⟩, sameBlock⟩ := (d i).cover x y hne hi
    refine ⟨B, ⟨⟨i, hB⟩, hx, hy⟩, ?_⟩
    rintro C ⟨⟨j, hC⟩, hcx, hcy⟩
    have e := samePiece j ((d j).eligible_of_mem C hC x hcx y hcy hne)
    subst j
    exact sameBlock C ⟨hC, hcx, hcy⟩

end PairDesign

/-- An array in which specifying two symbols in distinct columns determines a row. -/
@[expose] def IsTransversal {I T A : Type*} (row : A → I → T) : Prop :=
  ∀ i j, i ≠ j → ∀ x y, ∃! a, row a i = x ∧ row a j = y

private def weightedRow {I T A : Type*} (W : I → T → Type*)
    (row : A → I → T) (a : A) :
    (Σ i, W i (row a i)) ↪ (Σ i, Σ x, W i x) where
  toFun x := ⟨x.1, row a x.1, x.2⟩
  inj' := by
    rintro ⟨i, u⟩ ⟨j, v⟩ h
    have h' : i = j := congrArg Sigma.fst h
    subst j
    have hin : (⟨row a i, u⟩ : Σ x, W i x) = ⟨row a i, v⟩ :=
      eq_of_heq (Sigma.mk.inj h).2
    exact congrArg (Sigma.mk i) (eq_of_heq (Sigma.mk.inj hin).2)

/-- Replace each cell of the transversal array by a set of the prescribed size and
use the local design of each row to cover all pairs in different columns. -/
def weight {I T A : Type*} {row : A → I → T} (transversal : IsTransversal row)
    (W : I → T → Type*)
    (localDesign : ∀ a, PairDesign (Σ i, W i (row a i)) (fun u v => u.1 ≠ v.1)) :
    PairDesign (Σ i, Σ x, W i x) (fun u v => u.1 ≠ v.1) := by
  have eqv (a : A) (u v : Σ i, Σ x, W i x) :
      imagePairs (weightedRow W row a) (fun x y => x.1 ≠ y.1) u v ↔
        u.1 ≠ v.1 ∧ row a u.1 = u.2.1 ∧ row a v.1 = v.2.1 := by
    constructor
    · rintro ⟨x, y, rfl, rfl, h⟩
      exact ⟨h, rfl, rfl⟩
    · obtain ⟨i, x, u⟩ := u
      obtain ⟨j, y, v⟩ := v
      rintro ⟨hne, hx, hy⟩
      change row a i = x at hx
      change row a j = y at hy
      subst x
      subst y
      exact ⟨⟨i, u⟩, ⟨j, v⟩, rfl, rfl, hne⟩
  refine PairDesign.assemble
    (fun a => ((localDesign a).embed (weightedRow W row a)).congr (eqv a))
    (fun _ _ _ h => h.1) ?_
  intro u v _ h
  obtain ⟨a, ha, unique⟩ := transversal u.1 v.1 h u.2.1 v.2.1
  exact ⟨a, ⟨h, ha⟩, fun b hb => unique b hb.2⟩

@[expose] def outsideHole {H G : Type*} : H ⊕ G → H ⊕ G → Prop
  | .inl _, .inl _ => False
  | _, _ => True

private def groupMap {H I : Type*} (G : I → Type*) (i : I) :
    (H ⊕ G i) ↪ (H ⊕ (Σ i, G i)) where
  toFun := Sum.map id (Sigma.mk i)
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp_all [Sum.map]

private def outerMap {H I : Type*} (G : I → Type*) : (Σ i, G i) ↪ (H ⊕ (Σ i, G i)) :=
  ⟨Sum.inr, Sum.inr_injective⟩

private def sharedMap {H I : Type*} (G : I → Type*) : H ↪ (H ⊕ (Σ i, G i)) :=
  ⟨Sum.inl, Sum.inl_injective⟩

private def partitionPairs {H I : Type*} (G : I → Type*) :
    Option (Option I) → H ⊕ (Σ i, G i) → H ⊕ (Σ i, G i) → Prop
  | none => imagePairs (outerMap G) (fun x y => x.1 ≠ y.1)
  | some none => imagePairs (sharedMap G) (fun _ _ => True)
  | some (some i) => imagePairs (groupMap G i) outsideHole

private theorem partition_owner {H I : Type*} {G : I → Type*}
    (x y : H ⊕ (Σ i, G i)) : ∃! part, partitionPairs G part x y := by
  classical
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      refine ⟨some none, ⟨x, y, rfl, rfl, trivial⟩, ?_⟩
      rintro (_ | (_ | i)) ⟨a, b, ha, hb, rel⟩
      · cases ha
      · rfl
      · cases a <;> cases b <;> cases ha <;> cases hb
        exact False.elim rel
    | inr y =>
      obtain ⟨i, y⟩ := y
      refine ⟨some (some i), ⟨.inl x, .inr y, rfl, rfl, trivial⟩, ?_⟩
      rintro (_ | (_ | j)) ⟨a, b, ha, hb, _⟩
      · cases ha
      · cases hb
      · cases b with
        | inl => cases hb
        | inr =>
          have e : j = i := congrArg Sigma.fst (Sum.inr.inj hb)
          simp [e]
  | inr x =>
    obtain ⟨i, x⟩ := x
    cases y with
    | inl y =>
      refine ⟨some (some i), ⟨.inr x, .inl y, rfl, rfl, trivial⟩, ?_⟩
      rintro (_ | (_ | j)) ⟨a, b, ha, hb, _⟩
      · cases hb
      · cases ha
      · cases a with
        | inl => cases ha
        | inr =>
          have e : j = i := congrArg Sigma.fst (Sum.inr.inj ha)
          simp [e]
    | inr y =>
      obtain ⟨j, y⟩ := y
      by_cases h : i = j
      · subst j
        refine ⟨some (some i), ⟨.inr x, .inr y, rfl, rfl, trivial⟩, ?_⟩
        rintro (_ | (_ | k)) ⟨a, b, ha, hb, rel⟩
        · have ea : a = ⟨i, x⟩ := Sum.inr.inj ha
          have eb : b = ⟨i, y⟩ := Sum.inr.inj hb
          subst a
          subst b
          exact False.elim (rel rfl)
        · cases ha
        · cases a with
          | inl => cases ha
          | inr =>
            have e : k = i := congrArg Sigma.fst (Sum.inr.inj ha)
            simp [e]
      · refine ⟨none, ⟨⟨i, x⟩, ⟨j, y⟩, rfl, rfl, h⟩, ?_⟩
        rintro (_ | (_ | k)) ⟨a, b, ha, hb, _⟩
        · rfl
        · cases ha
        · cases a with
          | inl => cases ha
          | inr =>
            cases b with
            | inl => cases hb
            | inr =>
              have ea : k = i := congrArg Sigma.fst (Sum.inr.inj ha)
              have eb : k = j := congrArg Sigma.fst (Sum.inr.inj hb)
              exact False.elim (h (ea.symm.trans eb))

/-- Fill the groups of a group-divisible design using the same set of shared points. -/
def fillGroups {H I : Type*} {G : I → Type*}
    (outer : PairDesign (Σ i, G i) (fun x y => x.1 ≠ y.1))
    (shared : SteinerSystem H) (inner : ∀ i, PairDesign (H ⊕ G i) outsideHole) :
    SteinerSystem (H ⊕ (Σ i, G i)) := by
  let pieces : ∀ part, PairDesign (H ⊕ (Σ i, G i)) (partitionPairs G part)
    | none => outer.embed (outerMap G)
    | some none => shared.embed (sharedMap G)
    | some (some i) => (inner i).embed (groupMap G i)
  exact PairDesign.assemble pieces (fun _ _ _ _ => trivial)
    (fun x y _ _ => partition_owner x y)

end Lemmata.SteinerSixSpectrum
