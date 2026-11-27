module

public import Lemmata.EnergyShellCrossings.EnergyShellCrossing

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lemmata.EnergyShellCrossings.BalancedCrossing

open Lemmata.FockCircuits

noncomputable section

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

theorem commutative_assembly (a b c d : Matrix K J ℤ) (x y : J → ℤ) :
    orderedAssembly a b c d (fun j (_ : Unit) => x j) (fun j (_ : Unit) => y j) =
      ∑ r, ((∑ j, a r j * x j) * (∑ j, b r j * y j) +
        (∑ j, c r j * y j) * (∑ j, d r j * x j)) := by
  rw [orderedAssembly_expansion]
  simp only [Fintype.sum_unique, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro j hj
    ring

/-- Contract an integral two-cut crossing against four independently chosen vectors. -/
theorem contract [DecidableEq I] [DecidableEq J]
    (a b c d : K → I → J → ℤ)
    (h : ∀ i k j l,
      (∑ r, a r i j * b r k l) + (∑ r, c r i l * d r k j) =
        if i = k then (if j = l then 1 else 0) else 0)
    (u v : I → ℤ) (x y : J → ℤ) :
    (∑ r, (Hurwitz.bilinear (a r) u x * Hurwitz.bilinear (b r) v y +
      Hurwitz.bilinear (c r) u y * Hurwitz.bilinear (d r) v x)) =
      (∑ i, u i * v i) * (∑ j, x j * y j) := by
  have hh := directAssembly_eq_crossing a b c d (fun i j k l => h i k j l) u v
    (fun j (_ : Unit) => x j) (fun j (_ : Unit) => y j)
  rw [commutative_assembly] at hh
  have hbil (f : K → I → J → ℤ) (r : K) (z : I → ℤ) (w : J → ℤ) :
      (∑ j, coefficientRows f z r j * w j) = Hurwitz.bilinear (f r) z w := by
    simpa only [Hurwitz.bilinear, coefficientRows, smul_eq_mul, Finset.sum_mul] using
      (Finset.sum_comm :
        (∑ j, ∑ i, f r i j * z i * w j) = ∑ i, ∑ j, f r i j * z i * w j)
  simp_rw [hbil] at hh
  rw [hh]
  simp only [batchedCrossing, Fintype.sum_unique, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

variable {S T A C D U V W : Type*}
  [Fintype S] [Fintype T] [Fintype C] [Fintype D]
  [Fintype U] [Fintype V] [Fintype W] [DecidableEq A]

def combinedMask (p : Decomposition S A C U) (q : Decomposition T A D V)
    (c : (C × D) × Bool) : S ⊕ T → Bool :=
  Sum.elim (p.mask c.1.1) (fun t => if c.2 then !(q.mask c.1.2 t) else q.mask c.1.2 t)

def combinedLeft (p : Decomposition S A C U) (q : Decomposition T A D V)
    (a c : W → U → V → ℤ) (z : (C × D) × Bool) (r : W) (x : S ⊕ T → A) : ℤ :=
  if z.2 then
    Hurwitz.bilinear (c r) (fun i => p.left z.1.1 i (x ∘ Sum.inl))
      (fun j => q.right z.1.2 j (x ∘ Sum.inr))
  else
    Hurwitz.bilinear (a r) (fun i => p.left z.1.1 i (x ∘ Sum.inl))
      (fun j => q.left z.1.2 j (x ∘ Sum.inr))

def combinedRight (p : Decomposition S A C U) (q : Decomposition T A D V)
    (b d : W → U → V → ℤ) (z : (C × D) × Bool) (r : W) (x : S ⊕ T → A) : ℤ :=
  if z.2 then
    Hurwitz.bilinear (d r) (fun i => p.right z.1.1 i (x ∘ Sum.inl))
      (fun j => q.left z.1.2 j (x ∘ Sum.inr))
  else
    Hurwitz.bilinear (b r) (fun i => p.right z.1.1 i (x ∘ Sum.inl))
      (fun j => q.right z.1.2 j (x ∘ Sum.inr))

theorem select_combined_left (p : Decomposition S A C U) (q : Decomposition T A D V)
    (z : (C × D) × Bool) (x y : S ⊕ T → A) :
    select (combinedMask p q z) x y ∘ Sum.inl =
      select (p.mask z.1.1) (x ∘ Sum.inl) (y ∘ Sum.inl) := by
  rfl

theorem select_combined_right_false (p : Decomposition S A C U) (q : Decomposition T A D V)
    (s : C) (t : D) (x y : S ⊕ T → A) :
    select (combinedMask p q ((s, t), false)) x y ∘ Sum.inr =
      select (q.mask t) (x ∘ Sum.inr) (y ∘ Sum.inr) := by
  funext i
  simp [select, combinedMask]

theorem select_combined_right_true (p : Decomposition S A C U) (q : Decomposition T A D V)
    (s : C) (t : D) (x y : S ⊕ T → A) :
    select (combinedMask p q ((s, t), true)) x y ∘ Sum.inr =
      select (q.mask t) (y ∘ Sum.inr) (x ∘ Sum.inr) := by
  funext i
  cases hm : q.mask t i <;> simp [select, combinedMask, hm]

/-- Compose two grouped decompositions. The new cut has rank index W, not
U × V × W; the child rank indices are contracted inside the side factors. -/
def combine [DecidableEq U] [DecidableEq V]
    (p : Decomposition S A C U) (q : Decomposition T A D V)
    (a b c d : W → U → V → ℤ)
    (h : ∀ i k j l,
      (∑ r, a r i j * b r k l) + (∑ r, c r i l * d r k j) =
        if i = k then (if j = l then 1 else 0) else 0) :
    Decomposition (S ⊕ T) A ((C × D) × Bool) W where
  mask := combinedMask p q
  left := combinedLeft p q a c
  right := combinedRight p q b d
  identity x y := by
    have hinner (s : C) (t : D) :
        (∑ z : Bool, ∑ r : W,
          combinedLeft p q a c ((s,t),z) r (select (combinedMask p q ((s,t),z)) x y) *
            combinedRight p q b d ((s,t),z) r (select (combinedMask p q ((s,t),z)) y x)) =
          (∑ i, p.left s i (select (p.mask s) (x ∘ Sum.inl) (y ∘ Sum.inl)) *
            p.right s i (select (p.mask s) (y ∘ Sum.inl) (x ∘ Sum.inl))) *
          (∑ j, q.left t j (select (q.mask t) (x ∘ Sum.inr) (y ∘ Sum.inr)) *
            q.right t j (select (q.mask t) (y ∘ Sum.inr) (x ∘ Sum.inr))) := by
      simp only [Fintype.sum_bool, combinedLeft, combinedRight, Bool.false_eq_true,
        ite_false, ite_true, select_combined_left, select_combined_right_true,
        select_combined_right_false]
      rw [add_comm, ← Finset.sum_add_distrib]
      exact contract a b c d h
        (fun i => p.left s i (select (p.mask s) (x ∘ Sum.inl) (y ∘ Sum.inl)))
        (fun i => p.right s i (select (p.mask s) (y ∘ Sum.inl) (x ∘ Sum.inl)))
        (fun j => q.left t j (select (q.mask t) (x ∘ Sum.inr) (y ∘ Sum.inr)))
        (fun j => q.right t j (select (q.mask t) (y ∘ Sum.inr) (x ∘ Sum.inr)))
    simp only [Fintype.sum_prod_type]
    simp_rw [hinner]
    rw [← Finset.sum_mul_sum, p.identity, q.identity]
    exact (Fintype.prod_sum_type
      (fun z : S ⊕ T => if x z = y z then (1 : ℤ) else 0)).symm

/-- One identity wire needs one layout and one rank coordinate per label. -/
def single (A : Type*) [Fintype A] [DecidableEq A] : Decomposition Unit A Unit A where
  mask _ _ := true
  left _ k x := if x () = k then 1 else 0
  right _ k x := if x () = k then 1 else 0
  identity x y := by
    simp [select]

/-- A binary merge doubles the number of layout pairs. -/
theorem layout_card : Fintype.card ((C × D) × Bool) = 2 * Fintype.card C * Fintype.card D := by
  simp only [Fintype.card_prod, Fintype.card_bool]
  ring

/-- Fixing one endpoint in each child prevents duplicate transversal cuts. -/
theorem combinedMask_injective (p : Decomposition S A C U) (q : Decomposition T A D V)
    (hp : Function.Injective p.mask) (hq : Function.Injective q.mask)
    (t₀ : T) (ht₀ : ∀ t, q.mask t t₀ = true) :
    Function.Injective (combinedMask p q) := by
  rintro ⟨⟨s, t⟩, b⟩ ⟨⟨s', t'⟩, b'⟩ h
  have hs : s = s' := hp (funext fun i => congrFun h (Sum.inl i))
  have hb : b = b' := by
    have ht := congrFun h (Sum.inr t₀)
    cases b <;> cases b' <;> simp_all [combinedMask]
  subst s'
  subst b'
  have ht : t = t' := hq (by
    funext i
    have hi := congrFun h (Sum.inr i)
    cases b <;> simpa [combinedMask] using hi)
  subst t'
  rfl

theorem leaves_card (r : ℕ) : Fintype.card (Leaves r) = 2 ^ r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change Fintype.card (Leaves r ⊕ Leaves r) = 2 ^ (r + 1)
    rw [Fintype.card_sum, ih, pow_succ]
    omega

theorem layouts_card (r : ℕ) : Fintype.card (Layouts r) = 2 ^ (2 ^ r - 1) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change Fintype.card ((Layouts r × Layouts r) × Bool) = 2 ^ (2 ^ (r + 1) - 1)
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_bool, ih,
      ← pow_add, ← pow_succ]
    congr 1
    have hp : 0 < 2 ^ r := pow_pos (by decide) r
    rw [pow_succ]
    omega

/-- Exact finite balanced fusion, including distinctness of its transversal cuts. -/
theorem balanced_decomposition (n : ℕ) (h : ℕ → ℕ)
    (hpos : ∀ r, 0 < h r)
    (hcapacity : ∀ r, rankSequence n h r ≤ partitionDimension (2 * h r)) (r : ℕ) :
    ∃ p : Decomposition (Leaves r) (Fin n) (Layouts r) (Fin (rankSequence n h r)),
      Function.Injective p.mask ∧ ∀ c, p.mask c (firstLeaf r) = true := by
  induction r with
  | zero =>
    refine ⟨single (Fin n), ?_, ?_⟩
    · intro a b _
      exact @Subsingleton.elim Unit inferInstance a b
    · intro c
      rfl
  | succ r ih =>
    obtain ⟨p, hp, hroot⟩ := ih
    have hex := EnergyShell.integral_shell_crossing
      (h r) (h r) (rankSequence n h r) (rankSequence n h r)
      (hpos r) (hcapacity r) (hcapacity r)
    rw [← two_mul (h r)] at hex
    obtain ⟨a, b, c, d, habcd⟩ := hex
    refine ⟨combine p p a b c d habcd, ?_, ?_⟩
    · exact combinedMask_injective p p hp hp (firstLeaf r) hroot
    · intro z
      exact hroot z.1.1

end

end Lemmata.EnergyShellCrossings.BalancedCrossing
