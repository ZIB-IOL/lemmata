module

public import Lemmata.FrankWolfePS.Lower.Prelude
@[expose] public section

/-! Fixed-size hidden subsets and first-hit decision trees.
A negative membership answer is free. Every positive answer uses a call.
This enlarged model includes a sorted scan for every numerical LMO. -/
namespace Lemmata.FrankWolfePS
open Finset
open scoped BigOperators
variable {ι O : Type*} [DecidableEq ι]

inductive Tree (ι O : Type*) : ℕ → Type _
  | leaf {t} (x : O) : Tree ι O t
  | pass {t} (s : Tree ι O t) : Tree ι O (t + 1)
  | probe {t} (i : ι) (miss : Tree ι O (t + 1)) (hit : Tree ι O t) : Tree ι O (t + 1)

def Tree.run {t} (s : Tree ι O t) (I : Finset ι) : O :=
  match s with
  | .leaf x => x
  | .pass s' => s'.run I
  | .probe i miss hit => if i ∈ I then hit.run I else miss.run I

inductive Orders (ι O : Type*) : ℕ → Type _
  | ret {t} (x : O) : Orders ι O t
  | ask {t} (order : List ι) (next : Option ι → Orders ι O t) : Orders ι O (t + 1)

def first (I : Finset ι) : List ι → Option ι
  | [] => none
  | i :: l => if i ∈ I then some i else first I l

def Orders.run {t} (s : Orders ι O t) (I : Finset ι) : O :=
  match s with
  | .ret x => x
  | .ask l next => (next (first I l)).run I

def scan {t} (next : Option ι → Tree ι O t) : List ι → Tree ι O (t + 1)
  | [] => .pass (next none)
  | i :: l => .probe i (scan next l) (next (some i))

theorem run_scan {t} (next : Option ι → Tree ι O t) (I : Finset ι) (l : List ι) :
    (scan next l).run I = (next (first I l)).run I := by
  induction l with
  | nil => rfl
  | cons i l ih => by_cases hi : i ∈ I <;> simp [scan, first, Tree.run, hi, ih]

def Orders.compile {t} (s : Orders ι O t) : Tree ι O t :=
  match s with
  | .ret x => .leaf x
  | .ask l next => scan (fun j => (next j).compile) l

theorem Orders.run_compile {t} (s : Orders ι O t) (I : Finset ι) :
    s.compile.run I = s.run I := by
  induction s with
  | ret => rfl
  | ask l next ih => simp [compile, run_scan, Orders.run, ih]

/-- Number of completions and number of completions containing a specified unresolved label. -/
def W (n h : ℕ) : ℝ := n.choose h
def V (n h : ℕ) : ℝ := (n - 1).choose (h - 1)

theorem marginal_identity {n h : ℕ} (hn : 0 < n) (hh : 0 < h) :
    (n : ℝ) * V n h = W n h * h := by
  cases n with
  | zero => omega
  | succ n =>
    cases h with
    | zero => omega
    | succ h =>
      simp only [V, W, Nat.succ_sub_one]
      exact_mod_cast Nat.add_one_mul_choose_eq n h

theorem sum_split {β : Type*} [AddCommMonoid β] (U : Finset ι) {i : ι} (hi : i ∈ U) (h : ℕ)
    (f : Finset ι → β) :
    ∑ S ∈ U.powersetCard (h + 1), f S =
      (∑ S ∈ (U.erase i).powersetCard (h + 1), f S) +
      ∑ S ∈ (U.erase i).powersetCard h, f (insert i S) := by
  classical
  have hn {m : ℕ} {S : Finset ι} (hS : S ∈ (U.erase i).powersetCard m) : i ∉ S :=
    fun hiS => (notMem_erase i U) ((mem_powersetCard.mp hS).1 hiS)
  conv_lhs => rw [← insert_erase hi, powersetCard_succ_insert (notMem_erase i U)]
  rw [sum_union, sum_image]
  · intro a ha b hb hab
    have e := congrArg (fun s : Finset ι => s.erase i) hab
    simpa [erase_insert (hn ha), erase_insert (hn hb)] using e
  · apply disjoint_left.mpr
    intro S hS hSi
    obtain ⟨A, _, rfl⟩ := mem_image.mp hSi
    exact hn hS (mem_insert_self ..)

/-- Exact unnormalized posterior marginal under the uniform completion prior. -/
theorem inclusion_sum (U : Finset ι) (i : ι) {h : ℕ} (hh : 0 < h) :
    (∑ S ∈ U.powersetCard h, if i ∈ S then (1 : ℝ) else 0) =
      if i ∈ U then V U.card h else 0 := by
  by_cases hi : i ∈ U
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hh.ne'
    rw [sum_split U hi j]
    have hn {S : Finset ι} (hS : S ∈ (U.erase i).powersetCard (j + 1)) : i ∉ S :=
      fun his => (notMem_erase i U) ((mem_powersetCard.mp hS).1 his)
    have zeroPart : (∑ S ∈ (U.erase i).powersetCard (j + 1), if i ∈ S then (1 : ℝ) else 0) = 0 :=
      sum_eq_zero (fun S hs => ite_eq_right (hn hs))
    rw [zeroPart]; simp [hi, V, card_erase_of_mem hi]
  · have hn {S : Finset ι} (hS : S ∈ U.powersetCard h) : i ∉ S :=
      fun his => hi ((mem_powersetCard.mp hS).1 his)
    simpa [hi] using (sum_eq_zero (s := U.powersetCard h)
      (f := fun S => if i ∈ S then (1 : ℝ) else 0) (fun S hs => ite_eq_right (hn hs)))

/-- A single unknown-label query splits the potential by Pascal's identity.
The statement is valid with arbitrary adaptive continuations and early termination. -/
theorem adaptive_sum {k t : ℕ} (s : Tree ι O t)
    (loss : O → Finset ι → ℝ)
    (terminal : ∀ (x : O) (P U : Finset ι) (h : ℕ), Disjoint P U →
      P.card ≤ k → P.card + h = 8 * k →
      ∑ S ∈ U.powersetCard h, loss x (P ∪ S) ≤ W U.card h / 2 + 2 * V U.card h)
    (P U : Finset ι) (h : ℕ) (hPU : Disjoint P U)
    (calls : P.card + t ≤ k) (size : P.card + h = 8 * k) :
    (∑ S ∈ U.powersetCard h, loss (s.run (P ∪ S)) (P ∪ S)) ≤
      W U.card h / 2 + 2 * V U.card h := by
  induction s generalizing P U h with
  | leaf x => exact terminal x P U h hPU (by omega) size
  | pass s ih => exact ih P U h hPU (by omega) size
  | @probe t i miss hit ihm ihy =>
    by_cases ip : i ∈ P
    · simpa [Tree.run, ip] using ihy P U h hPU (by omega) size
    by_cases iu : i ∈ U
    · by_cases avail : h ≤ U.card
      · have ih2 : 2 ≤ h := by omega
        obtain ⟨j, hj⟩ : ∃ j, h = j + 2 := ⟨h - 2, by omega⟩
        subst h
        let A := U.erase i
        have hn : U.card = A.card + 1 := by
          dsimp [A]; rw [card_erase_of_mem iu]; have := card_pos.mpr ⟨i, iu⟩; omega
        have hA : Disjoint P A := hPU.mono_right (erase_subset _ _)
        have hPA : Disjoint (insert i P) A := by
          simpa [A, disjoint_insert_left] using hA
        have hm := ihm P A (j + 2) hA calls size
        have hy := ihy (insert i P) A (j + 1) hPA
          (by rw [card_insert_of_notMem ip]; omega) (by rw [card_insert_of_notMem ip]; omega)
        rw [sum_split U iu (j + 1)]
        have eqm : (∑ S ∈ A.powersetCard (j + 2),
              loss ((Tree.probe i miss hit).run (P ∪ S)) (P ∪ S)) =
            ∑ S ∈ A.powersetCard (j + 2), loss (miss.run (P ∪ S)) (P ∪ S) := by
          apply sum_congr rfl
          intro S hs
          have hiS : i ∉ S := fun hi => (notMem_erase i U) ((mem_powersetCard.mp hs).1 hi)
          simp [Tree.run, ip, hiS]
        have eqy (S : Finset ι) : P ∪ insert i S = insert i P ∪ S := by ext a; simp
        change _ + _ ≤ _
        rw [show U.erase i = A from rfl, eqm]
        simp only [eqy, Tree.run, mem_union, mem_insert_self, true_or, ite_true]
        have wPas : W U.card (j + 2) = W A.card (j + 2) + W A.card (j + 1) := by
          rw [hn]; unfold W
          exact_mod_cast (Nat.choose_succ_succ A.card (j + 1)).trans (Nat.add_comm ..)
        have npos : 0 < A.card := by omega
        have vPas : V U.card (j + 2) = V A.card (j + 2) + V A.card (j + 1) := by
          obtain ⟨n, hna⟩ := Nat.exists_eq_succ_of_ne_zero npos.ne'
          rw [hn, hna]; simp [V, Nat.choose_succ_succ, add_comm]
        rw [wPas, vPas]
        linarith
      · have e : U.powersetCard h = ∅ := powersetCard_eq_empty.mpr (by omega)
        simp [e, W, V]; positivity
    · have heq : (∑ S ∈ U.powersetCard h, loss ((Tree.probe i miss hit).run (P ∪ S)) (P ∪ S)) =
            ∑ S ∈ U.powersetCard h, loss (miss.run (P ∪ S)) (P ∪ S) := by
        apply sum_congr rfl
        intro S hs
        have hiS : i ∉ S := fun hi => iu ((mem_powersetCard.mp hs).1 hi)
        simp [Tree.run, ip, hiS]
      rw [heq]
      exact ihm P U h hPU calls size

end Lemmata.FrankWolfePS
