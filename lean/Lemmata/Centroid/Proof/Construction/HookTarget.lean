module

public import Lemmata.Centroid.Proof.Construction.Monomial
public import Lemmata.Centroid.Def.Bounds

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Construction.Hook

noncomputable section

variable {F : Type*} [Field F]

abbrev Core (n : ℕ) (_ : Fin 3) := Option (Fin n)

abbrev Dual (n t : ℕ) : Fin 3 → Type :=
  ![(Option (Fin n) × Fin n) ⊕ Fin t, (Fin n × Option (Fin n)) ⊕ Fin t,
    (Fin n × Option (Fin n)) ⊕ Fin t]

instance dualFintype (n t : ℕ) (i : Fin 3) : Fintype (Dual n t i) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
  all_goals dsimp [Dual]; infer_instance

def assignment (n : ℕ) (a b c : Option (Fin n)) : ∀ i, Core n i :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun j => Fin.elim0 j)))

@[simp] theorem assignment_zero (n : ℕ) (a b c : Option (Fin n)) : assignment n a b c 0 = a := rfl
@[simp] theorem assignment_one (n : ℕ) (a b c : Option (Fin n)) : assignment n a b c 1 = b := rfl
@[simp] theorem assignment_two (n : ℕ) (a b c : Option (Fin n)) : assignment n a b c 2 = c := rfl

def pairPoint (n t : ℕ) (ht : t ≤ n) (i : Fin 3) : Dual n t i → ∀ j, Core n j := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
  · exact Sum.elim (fun p => assignment n none p.1 (some p.2))
      (fun j => assignment n none (some (j.castLE ht)) none)
  · exact Sum.elim (fun p => assignment n (some p.1) none p.2)
      (fun j => assignment n none none (some (j.castLE ht)))
  · exact Sum.elim (fun p => assignment n (some p.1) p.2 none)
      (fun j => assignment n none (some (j.castLE ht)) none)

def basePairs (n t : ℕ) (ht : t ≤ n) : Realization.PairFamily F (Core n) (Dual n t) :=
  fun i l => Realization.basisVector (fun j : {j // j ≠ i} => pairPoint n t ht i l j.val)

def pairs (n t : ℕ) (ht : t ≤ n) : Realization.PairFamily F (Core n) (Dual n t) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)))
  · exact basePairs n t ht 0
  · exact Sum.elim (fun p => basePairs n t ht 1 (Sum.inl p))
      (fun k => basePairs n t ht 1 (Sum.inr k) -
        Realization.basisVector (fun _ : {j : Fin 3 // j ≠ 1} => (none : Option (Fin n))))
  · exact basePairs n t ht 2

@[simp] theorem pairPoint_zero_old (n t : ℕ) (ht : t ≤ n) (p : Option (Fin n) × Fin n) :
    pairPoint n t ht 0 (Sum.inl p) = assignment n none p.1 (some p.2) := rfl
@[simp] theorem pairPoint_zero_new (n t : ℕ) (ht : t ≤ n) (j : Fin t) :
    pairPoint n t ht 0 (Sum.inr j) = assignment n none (some (j.castLE ht)) none := rfl
@[simp] theorem pairPoint_one_old (n t : ℕ) (ht : t ≤ n) (p : Fin n × Option (Fin n)) :
    pairPoint n t ht 1 (Sum.inl p) = assignment n (some p.1) none p.2 := rfl
@[simp] theorem pairPoint_one_new (n t : ℕ) (ht : t ≤ n) (j : Fin t) :
    pairPoint n t ht 1 (Sum.inr j) = assignment n none none (some (j.castLE ht)) := rfl
@[simp] theorem pairPoint_two_old (n t : ℕ) (ht : t ≤ n) (p : Fin n × Option (Fin n)) :
    pairPoint n t ht 2 (Sum.inl p) = assignment n (some p.1) p.2 none := rfl
@[simp] theorem pairPoint_two_new (n t : ℕ) (ht : t ≤ n) (j : Fin t) :
    pairPoint n t ht 2 (Sum.inr j) = assignment n none (some (j.castLE ht)) none := rfl

def tensor (n t : ℕ) (ht : t ≤ n) :
    Tensor F (Fin 3) (Realization.Coordinates (Core n) (Dual n t)) :=
  Realization.tensor (pairs n t ht) 0

abbrev Cell (n t : ℕ) := (Fin n × ((Option (Fin n) × Fin n) ⊕ Fin t)) ⊕ (Fin t × Fin t)

def cell (n t : ℕ) (ht : t ≤ n) : Cell n t → ∀ i, Core n i
  | Sum.inl (a, Sum.inl (b, c)) => assignment n (some a) b (some c)
  | Sum.inl (a, Sum.inr j) => assignment n (some a) (some (j.castLE ht)) none
  | Sum.inr (j, k) => assignment n none (some (j.castLE ht)) (some (k.castLE ht))

theorem cell_injective (n t : ℕ) (ht : t ≤ n) : Function.Injective (cell n t ht) := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  rcases x with ⟨a, ⟨b, c⟩ | j⟩ | ⟨j, k⟩ <;>
    rcases y with ⟨d, ⟨e, f⟩ | l⟩ | ⟨l, m⟩
  all_goals simp only [cell, assignment_zero, assignment_one, assignment_two,
    Option.some.injEq, Option.some_ne_none] at h0 h1 h2
  all_goals first | contradiction | skip
  · exact congrArg Sum.inl (Prod.ext h0 (congrArg Sum.inl (Prod.ext h1 h2)))
  · exact congrArg Sum.inl (Prod.ext h0 (congrArg Sum.inr (Fin.ext (congrArg (fun x : Fin n => x.val) h1))))
  · exact congrArg Sum.inr (Prod.ext (Fin.ext (congrArg (fun x : Fin n => x.val) h1))
      (Fin.ext (congrArg (fun x : Fin n => x.val) h2)))

theorem pairs_contain_old_cell (n t : ℕ) (ht : t ≤ n)
    (x : Fin n × ((Option (Fin n) × Fin n) ⊕ Fin t)) (i : Fin 3) :
    ∃ l, pairs (F := F) n t ht i l = Realization.basisVector
      (fun j : {j // j ≠ i} => cell n t ht (Sum.inl x) j.val) := by
  rcases x with ⟨a, ⟨b, c⟩ | j⟩ <;> fin_cases i
  · refine ⟨Sum.inl (b, c), ?_⟩
    apply congrArg (fun p => Realization.basisVector (F := F) p)
    funext ⟨i, hi⟩
    fin_cases i <;> first | exact False.elim (hi rfl) | rfl
  · refine ⟨Sum.inl (a, some c), ?_⟩
    apply congrArg (fun p => Realization.basisVector (F := F) p)
    funext ⟨i, hi⟩
    fin_cases i <;> first | exact False.elim (hi rfl) | rfl
  · refine ⟨Sum.inl (a, b), ?_⟩
    apply congrArg (fun p => Realization.basisVector (F := F) p)
    funext ⟨i, hi⟩
    fin_cases i <;> first | exact False.elim (hi rfl) | rfl
  · refine ⟨Sum.inr j, ?_⟩
    apply congrArg (fun p => Realization.basisVector (F := F) p)
    funext ⟨i, hi⟩
    fin_cases i <;> first | exact False.elim (hi rfl) | rfl
  · refine ⟨Sum.inl (a, none), ?_⟩
    apply congrArg (fun p => Realization.basisVector (F := F) p)
    funext ⟨i, hi⟩
    fin_cases i <;> first | exact False.elim (hi rfl) | rfl
  · refine ⟨Sum.inl (a, some (j.castLE ht)), ?_⟩
    apply congrArg (fun p => Realization.basisVector (F := F) p)
    funext ⟨i, hi⟩
    fin_cases i <;> first | exact False.elim (hi rfl) | rfl

def cellTensor (n t : ℕ) (ht : t ≤ n) : Cell n t → Tensor F (Fin 3) (Core n)
  | Sum.inl x => Realization.basisVector (cell n t ht (Sum.inl x))
  | Sum.inr (j, k) => Realization.basisVector (cell n t ht (Sum.inr (j, k))) -
      Realization.basisVector (assignment n none (some (j.castLE ht)) none)

private theorem basis_coordinate_product {I : Type*} {U : I → Type*}
    (a x : ∀ i, U i) (i : I) :
    Realization.basisVector (F := F) a x = Realization.basisVector (a i) (x i) *
      Realization.basisVector (fun j : {j // j ≠ i} => a j.val)
        (fun j : {j // j ≠ i} => x j.val) := by
  have heq : x = a ↔ x i = a i ∧
      (fun j : {j // j ≠ i} => x j.val) = (fun j : {j // j ≠ i} => a j.val) := by
    constructor
    · intro h; subst x; exact ⟨rfl, rfl⟩
    · rintro ⟨hi, hr⟩
      funext j
      by_cases hji : j = i
      · subst j; exact hi
      · exact congrFun hr ⟨j, hji⟩
  by_cases hi : x i = a i <;>
    by_cases hr : (fun j : {j // j ≠ i} => x j.val) = (fun j : {j // j ≠ i} => a j.val) <;>
    simp [Realization.basisVector, heq, hi, hr]

private theorem reconstruction_single {I : Type*} [Fintype I] {U L : I → Type*}
    [∀ i, Fintype (L i)] (P : Realization.PairFamily F U L) (i : I) (l : L i) (u : U i → F) :
    Realization.reconstruction P i (fun a k => u a * Realization.basisVector l k) =
      fun x => u (x i) * P i l (fun j => x j.val) := by
  ext x
  simp [Realization.reconstruction, Realization.basisVector, mul_ite]

private theorem reconstruction_coordinate {I : Type*} [Fintype I] {U L : I → Type*}
    [∀ i, Fintype (L i)] (P : Realization.PairFamily F U L) (a : ∀ i, U i) (i : I) (l : L i)
    (hl : P i l = Realization.basisVector (fun j : {j // j ≠ i} => a j.val)) :
    Realization.reconstruction P i (fun u k => Realization.basisVector (a i) u *
      Realization.basisVector l k) = Realization.basisVector a := by
  rw [reconstruction_single, hl]
  ext x
  exact (basis_coordinate_product a x i).symm

theorem cellTensor_mem (n t : ℕ) (ht : t ≤ n) (x : Cell n t) :
    cellTensor (F := F) n t ht x ∈ Realization.compatibleSpace (pairs n t ht) := by
  rcases x with x | ⟨j, k⟩
  · exact Realization.coordinate_mem_compatibleSpace _ _ (pairs_contain_old_cell n t ht x)
  · let a := cell n t ht (Sum.inr (j, k))
    let b := assignment n none (some (j.castLE ht)) none
    have hpair (i : Fin 3) (l : Dual n t i)
        (h : ∀ r : {r : Fin 3 // r ≠ i}, pairPoint n t ht i l r.val = a r.val) :
        basePairs (F := F) n t ht i l = Realization.basisVector (fun r : {r // r ≠ i} => a r.val) := by
      exact congrArg (fun p => Realization.basisVector (F := F) p) (funext h)
    apply (Submodule.mem_iInf _).mpr
    intro i
    fin_cases i
    · let l : Dual n t 0 := Sum.inl (some (j.castLE ht), k.castLE ht)
      let m : Dual n t 0 := Sum.inr j
      refine ⟨(fun u v => Realization.basisVector none u * Realization.basisVector l v) -
        (fun u v => Realization.basisVector none u * Realization.basisVector m v), ?_⟩
      rw [map_sub]
      have hl : pairs (F := F) n t ht 0 l =
          Realization.basisVector (fun r : {r : Fin 3 // r ≠ 0} => a r.val) := by
        apply hpair
        rintro ⟨r, hr⟩; fin_cases r <;> first | contradiction | rfl
      have hm : pairs (F := F) n t ht 0 m =
          Realization.basisVector (fun r : {r : Fin 3 // r ≠ 0} => b r.val) := by
        apply congrArg (fun p => Realization.basisVector (F := F) p)
        funext ⟨r, hr⟩; fin_cases r <;> first | contradiction | rfl
      erw [reconstruction_coordinate _ a 0 l hl, reconstruction_coordinate _ b 0 m hm]
      rfl
    · let l : Dual n t 1 := Sum.inr k
      refine ⟨fun u v => Realization.basisVector (some (j.castLE ht)) u * Realization.basisVector l v, ?_⟩
      rw [reconstruction_single]
      have hl : basePairs (F := F) n t ht 1 l =
          Realization.basisVector (fun r : {r : Fin 3 // r ≠ 1} => a r.val) := by
        apply hpair
        rintro ⟨r, hr⟩; fin_cases r <;> first | contradiction | rfl
      have hm : (fun _ : {r : Fin 3 // r ≠ 1} => (none : Option (Fin n))) =
          (fun r : {r : Fin 3 // r ≠ 1} => b r.val) := by
        funext ⟨r, hr⟩; fin_cases r <;> first | contradiction | rfl
      ext y
      dsimp only [cellTensor, Pi.sub_apply]
      change Realization.basisVector (F := F) (some (j.castLE ht)) (y 1) *
        (basePairs n t ht 1 l (fun r => y r.val) -
          Realization.basisVector (fun _ : {r : Fin 3 // r ≠ 1} => (none : Option (Fin n))) (fun r => y r.val)) =
        Realization.basisVector a y - Realization.basisVector b y
      erw [hl, hm, mul_sub, ← basis_coordinate_product a y 1, ← basis_coordinate_product b y 1]
    · let l : Dual n t 2 := Sum.inr j
      refine ⟨fun u v => (Realization.basisVector (some (k.castLE ht)) u - Realization.basisVector none u) *
        Realization.basisVector l v, ?_⟩
      rw [reconstruction_single]
      have hl : pairs (F := F) n t ht 2 l =
          Realization.basisVector (fun r : {r : Fin 3 // r ≠ 2} => a r.val) := by
        apply hpair
        rintro ⟨r, hr⟩; fin_cases r <;> first | contradiction | rfl
      have hm : (fun r : {r : Fin 3 // r ≠ 2} => a r.val) =
          (fun r : {r : Fin 3 // r ≠ 2} => b r.val) := by
        funext ⟨r, hr⟩; fin_cases r <;> first | contradiction | rfl
      ext y
      dsimp only [cellTensor, Pi.sub_apply]
      change (Realization.basisVector (some (k.castLE ht)) (y 2) - Realization.basisVector none (y 2)) *
        pairs n t ht 2 l (fun r => y r.val) = Realization.basisVector a y - Realization.basisVector b y
      erw [hl, sub_mul, ← basis_coordinate_product a y 2, hm, ← basis_coordinate_product b y 2]

theorem cellTensor_pivot (n t : ℕ) (ht : t ≤ n) (x y : Cell n t) :
    cellTensor (F := F) n t ht x (cell n t ht y) = if y = x then 1 else 0 := by
  have hneq (j : Fin t) : cell n t ht y ≠ assignment n none (some (j.castLE ht)) none := by
    intro h
    rcases y with ⟨a, ⟨b, c⟩ | k⟩ | ⟨k, l⟩
    · have hh := congrFun h 0; simp [cell] at hh
    · have hh := congrFun h 0; simp [cell] at hh
    · have hh := congrFun h 2; simp [cell] at hh
  rcases x with x | ⟨j, k⟩ <;>
    simp [cellTensor, Realization.basisVector, (cell_injective n t ht).eq_iff, hneq]

theorem cellTensor_independent (n t : ℕ) (ht : t ≤ n) :
    LinearIndependent F (cellTensor (F := F) n t ht) := by
  let r : Tensor F (Fin 3) (Core n) →ₗ[F] (Cell n t → F) :=
    LinearMap.pi (fun x => LinearMap.proj (cell n t ht x))
  have hrows : LinearIndependent F (fun x => r (cellTensor n t ht x)) := by
    convert Pi.linearIndependent_single_one (Cell n t) F using 1
    ext x y
    simpa [r, Pi.single_apply, eq_comm] using cellTensor_pivot (F := F) n t ht x y
  exact LinearIndependent.of_comp r hrows

theorem centroid_lower_bound (n t : ℕ) (ht : t ≤ n) :
    1 + (n * (n * (n + 1) + t) + t ^ 2) ≤
      Module.finrank F (Tensor.centroid (tensor (F := F) n t ht)) := by
  have hli := cellTensor_independent (F := F) n t ht
  have hspan : Submodule.span F (Set.range (cellTensor (F := F) n t ht)) ≤
      Realization.compatibleSpace (pairs n t ht) :=
    Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact cellTensor_mem n t ht x)
  have hd : Fintype.card (Cell n t) ≤ Module.finrank F (Realization.compatibleSpace (pairs (F := F) n t ht)) := by
    rw [← finrank_span_eq_card hli]
    exact Submodule.finrank_mono hspan
  have hc : Fintype.card (Cell n t) = n * (n * (n + 1) + t) + t ^ 2 := by
    simp only [Cell, Fintype.card_sum, Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
    ring
  rw [hc] at hd
  exact (Nat.add_le_add_left hd 1).trans (Realization.centroid_lower_bound (pairs n t ht) 0)

theorem coordinate_card (n t : ℕ) (i : Fin 3) :
    Fintype.card (Realization.Coordinates (Core n) (Dual n t) i) = n * (n + 1) + t + (n + 1) := by
  fin_cases i <;>
    simp only [Realization.Coordinates, Core, Dual, Fintype.card_eq_nat_card] <;> simp <;> ring

end

end Lemmata.Centroid.Construction.Hook
