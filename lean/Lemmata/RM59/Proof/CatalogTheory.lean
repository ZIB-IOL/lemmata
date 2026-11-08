module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.SetTheory.Cardinal.Finite
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Lemmata.RM59

open scoped BigOperators

theorem finite_family_covering_of_mass {I X : Type*} [Fintype I] [Finite X]
    (z : X) (A : I → Set X) (q : I → ℕ)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hzero : ∀ i, z ∉ A i) (hlower : ∀ i, q i ≤ Nat.card (A i))
    (hmass : Nat.card X ≤ 1 + ∑ i, q i) :
    ∀ x : X, x = z ∨ ∃ i, x ∈ A i := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  let Y := Unit ⊕ Σ i, A i
  let f : Y → X := fun y => match y with
    | .inl _ => z
    | .inr a => a.2
  have hf : Function.Injective f := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => cases a; cases b; rfl
      | inr b =>
        change z = (b.2 : X) at hab
        exact False.elim (hzero b.1 (hab.symm ▸ b.2.property))
    | inr a =>
      cases b with
      | inl b =>
        change (a.2 : X) = z at hab
        exact False.elim (hzero a.1 (hab ▸ a.2.property))
      | inr b =>
        rcases a with ⟨i, a⟩
        rcases b with ⟨j, b⟩
        change (a : X) = (b : X) at hab
        have hij : i = j := by
          by_contra hne
          exact (Set.disjoint_left.mp (hdisjoint i j hne))
            a.property (hab.symm ▸ b.property)
        subst j
        have hab' : a = b := Subtype.ext hab
        subst b
        rfl
  have hcard : Fintype.card X ≤ Fintype.card Y := by
    calc
      Fintype.card X ≤ 1 + ∑ i, q i := by
        simpa only [Nat.card_eq_fintype_card] using hmass
      _ ≤ 1 + ∑ i, Nat.card (A i) :=
        Nat.add_le_add_left (Finset.sum_le_sum fun i _ => hlower i) 1
      _ = Fintype.card Y := by simp [Y, Nat.card_eq_fintype_card]
  have hsurj : Function.Surjective f := by
    by_contra h
    have hlt := Fintype.card_lt_of_injective_not_surjective f hf h
    omega
  intro x
  obtain ⟨y, hy⟩ := hsurj x
  cases y with
  | inl y =>
    left
    exact hy.symm
  | inr y =>
    right
    exact ⟨y.1, hy ▸ y.2.property⟩

theorem orbit_card_lower_of_stabilizer_upper {G X : Type*} [Group G]
    [Fintype G] [Finite X] [MulAction G X] (x : X) (U q : ℕ)
    (hU : 0 < U) (hproduct : q * U = Fintype.card G)
    (hstab : Nat.card (MulAction.stabilizer G x) ≤ U) :
    q ≤ Nat.card (MulAction.orbit G x) := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  have hos : Nat.card (MulAction.orbit G x) *
      Nat.card (MulAction.stabilizer G x) = Fintype.card G := by
    simpa only [Nat.card_eq_fintype_card] using
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x
  apply Nat.le_of_mul_le_mul_right _ hU
  calc
    q * U = Fintype.card G := hproduct
    _ = Nat.card (MulAction.orbit G x) * Nat.card (MulAction.stabilizer G x) := hos.symm
    _ ≤ Nat.card (MulAction.orbit G x) * U := Nat.mul_le_mul_left _ hstab

theorem catalog_covering_of_orbit_mass {G X I : Type*} [Group G]
    [Fintype G] [Finite X] [Fintype I] [MulAction G X]
    (z : X) (rep : I → X) (U q : I → ℕ)
    (hseparate : ∀ i j, i ≠ j → rep i ∉ MulAction.orbit G (rep j))
    (hzero : ∀ i, z ∉ MulAction.orbit G (rep i))
    (hU : ∀ i, 0 < U i)
    (hproduct : ∀ i, q i * U i = Fintype.card G)
    (hstab : ∀ i, Nat.card (MulAction.stabilizer G (rep i)) ≤ U i)
    (hmass : Nat.card X ≤ 1 + ∑ i, q i) :
    ∀ x : X, x = z ∨ ∃ i, x ∈ MulAction.orbit G (rep i) := by
  apply finite_family_covering_of_mass z (fun i => MulAction.orbit G (rep i)) q
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    apply hseparate i j hij
    exact MulAction.mem_orbit_trans (MulAction.mem_orbit_symm.mp hxi) hxj
  · exact hzero
  · intro i
    exact orbit_card_lower_of_stabilizer_upper (rep i) (U i) (q i)
      (hU i) (hproduct i) (hstab i)
  · exact hmass

theorem catalog_covering_of_orbit_mass_fixed {G X I : Type*} [Group G]
    [Fintype G] [Finite X] [Fintype I] [MulAction G X]
    (z : X) (rep : I → X) (U q : I → ℕ)
    (hfixed : ∀ g : G, g • z = z) (hnonzero : ∀ i, rep i ≠ z)
    (hseparate : ∀ i j, i ≠ j → rep i ∉ MulAction.orbit G (rep j))
    (hU : ∀ i, 0 < U i)
    (hproduct : ∀ i, q i * U i = Fintype.card G)
    (hstab : ∀ i, Nat.card (MulAction.stabilizer G (rep i)) ≤ U i)
    (hmass : Nat.card X ≤ 1 + ∑ i, q i) :
    ∀ x : X, x = z ∨ ∃ i, x ∈ MulAction.orbit G (rep i) := by
  apply catalog_covering_of_orbit_mass z rep U q hseparate _ hU hproduct hstab hmass
  intro i hi
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.mem_orbit_symm.mp hi)
  exact hnonzero i (hg.symm.trans (hfixed g))

theorem orbit_card_le_of_subset {G X : Type*} [Group G]
    [Fintype G] [Finite X] [MulAction G X] (x : X) (C : Finset X)
    (hcover : MulAction.orbit G x ⊆ (C : Set X)) :
    Nat.card (MulAction.orbit G x) ≤ C.card := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  let f : MulAction.orbit G x → C := fun y => ⟨y, hcover y.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun y : C => (y : X)) hab
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    Fintype.card_le_of_injective f hf

theorem orbit_stabilizer_step_upper {G X : Type*} [Group G]
    [Fintype G] [Finite X] [MulAction G X] (x : X) (C : Finset X)
    (hcover : MulAction.orbit G x ⊆ (C : Set X)) :
    Fintype.card G ≤ C.card * Nat.card (MulAction.stabilizer G x) := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  have hos : Nat.card (MulAction.orbit G x) *
      Nat.card (MulAction.stabilizer G x) = Fintype.card G := by
    simpa only [Nat.card_eq_fintype_card] using
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x
  rw [← hos]
  exact Nat.mul_le_mul_right _ (orbit_card_le_of_subset x C hcover)

theorem card_chain_upper (h c : ℕ → ℕ) (n : ℕ)
    (hstep : ∀ j, j < n → h j ≤ c j * h (j + 1)) (hend : h n = 1) :
    h 0 ≤ ∏ j ∈ Finset.range n, c j := by
  have hprefix : ∀ k, k ≤ n → h 0 ≤ (∏ j ∈ Finset.range k, c j) * h k := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      calc
        h 0 ≤ (∏ j ∈ Finset.range k, c j) * h k := ih (by omega)
        _ ≤ (∏ j ∈ Finset.range k, c j) * (c k * h (k + 1)) :=
          Nat.mul_le_mul_left _ (hstep k hkn)
        _ = (∏ j ∈ Finset.range (k + 1), c j) * h (k + 1) := by
          rw [Finset.prod_range_succ, Nat.mul_assoc]
  simpa [hend] using hprefix n le_rfl

theorem orbit_separation_of_invariant {G X I Y : Type*} [Group G] [MulAction G X]
    (rep : I → X) (inv : X → Y) (hinv : ∀ (g : G) x, inv (g • x) = inv x)
    (hdistinct : Function.Injective fun i => inv (rep i)) :
    ∀ i j, i ≠ j → rep i ∉ MulAction.orbit G (rep j) := by
  intro i j hij hmem
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hmem
  apply hij
  apply hdistinct
  change inv (rep i) = inv (rep j)
  rw [← hg]
  exact hinv g (rep j)

def prefixStabilizer {G X : Type*} [Group G] [MulAction G X]
    (b : ℕ → X) : ℕ → Subgroup G
  | 0 => ⊤
  | n + 1 => prefixStabilizer b n ⊓ MulAction.stabilizer G (b n)

theorem mem_prefixStabilizer {G X : Type*} [Group G] [MulAction G X]
    (b : ℕ → X) (n : ℕ) (g : G) :
    g ∈ prefixStabilizer b n ↔ ∀ j, j < n → g • b j = b j := by
  induction n with
  | zero => simp [prefixStabilizer]
  | succ n ih =>
    change g ∈ prefixStabilizer b n ⊓ MulAction.stabilizer G (b n) ↔ _
    rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨hprev, hlast⟩ j hj
      by_cases h : j < n
      · exact ih.mp hprev j h
      · have : j = n := by omega
        subst j
        exact hlast
    · intro h
      exact ⟨ih.mpr (fun j hj => h j (by omega)), h n (by omega)⟩

theorem prefix_stabilizer_chain_upper {G X : Type*} [Group G]
    [Fintype G] [Finite X] [MulAction G X]
    (b : ℕ → X) (C : ℕ → Finset X) (n : ℕ)
    (hcover : ∀ j, j < n → MulAction.orbit (prefixStabilizer (G := G) b j) (b j) ⊆
      (C j : Set X))
    (hbase : ∀ g : G, (∀ j, j < n → g • b j = b j) → g = 1) :
    Nat.card G ≤ ∏ j ∈ Finset.range n, (C j).card := by
  classical
  have hstep : ∀ j, j < n → Nat.card (prefixStabilizer (G := G) b j) ≤
      (C j).card * Nat.card (prefixStabilizer (G := G) b (j + 1)) := by
    intro j hj
    have hle : prefixStabilizer (G := G) b (j + 1) ≤ prefixStabilizer b j :=
      inf_le_left
    have heq : (prefixStabilizer (G := G) b (j + 1)).subgroupOf (prefixStabilizer b j) =
        MulAction.stabilizer (prefixStabilizer (G := G) b j) (b j) := by
      change (prefixStabilizer (G := G) b j ⊓ MulAction.stabilizer G (b j)).subgroupOf
        (prefixStabilizer b j) = _
      rw [Subgroup.inf_subgroupOf_left, MulAction.stabilizer_subgroupOf]
    have hcardstab : Nat.card (MulAction.stabilizer (prefixStabilizer (G := G) b j) (b j)) =
        Nat.card (prefixStabilizer (G := G) b (j + 1)) := by
      rw [← heq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    have hs := orbit_stabilizer_step_upper (G := prefixStabilizer (G := G) b j)
      (b j) (C j) (hcover j hj)
    rw [hcardstab] at hs
    simpa only [Nat.card_eq_fintype_card] using hs
  have hlast : prefixStabilizer (G := G) b n = ⊥ := by
    apply le_antisymm _ bot_le
    intro g hg
    exact Subgroup.mem_bot.mpr (hbase g ((mem_prefixStabilizer b n g).mp hg))
  have hc := card_chain_upper (fun j => Nat.card (prefixStabilizer (G := G) b j))
    (fun j => (C j).card) n hstep (by rw [hlast, Subgroup.card_bot])
  simpa only [prefixStabilizer, Subgroup.card_top] using hc

end Lemmata.RM59
