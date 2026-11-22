module

public import Lemmata.PlanarSteinerXC.Objects
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Data.Set.Finite.Lemmas

/-!
# From correlation polytopes to minimum vertex covers (Lemma 3)

A CNF formula is presented by its literal occurrences; `next` lists the occurrences of each
variable in a cyclic order. Its *cover graph* has three vertices per occurrence `o`: a true
port `(o,0)`, a false port `(o,1)` and a literal vertex `(o,2)`. The ports of each variable form
the cycle `T₁ F₁ T₂ F₂ …`; the literal vertices of a clause form a clique; every literal vertex
is joined to the port of its occurrence that is chosen when the literal is false.

Maximum independent sets correspond to satisfying assignments together with a choice of a true
literal in every clause; complements give the minimum vertex covers. For the formula
`z_e = x_u x_v` (one variable per vertex and per edge of a graph `L`) reading one true port per
variable maps the minimum-cover face onto the correlation polytope of `L`.
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

open SimpleGraph

/-- A CNF formula given by its literal occurrences: every occurrence has a variable, a clause
and a sign, and `next` runs cyclically through the occurrences of each variable. -/
structure CNF (Occ Var Clause : Type*) where
  /-- The variable of an occurrence. -/
  var : Occ → Var
  /-- The clause of an occurrence. -/
  clause : Occ → Clause
  /-- The sign of an occurrence (`true` for a positive literal). -/
  pos : Occ → Bool
  /-- The cyclic order of the occurrences of each variable. -/
  next : Equiv.Perm Occ
  var_next : ∀ o, var (next o) = var o
  cyclic : ∀ o o', var o = var o' → ∃ k : ℕ, (next ^ k) o = o'

namespace CNF

variable {Occ Var Clause : Type*} (φ : CNF Occ Var Clause)

/-- The port that is selected when the literal of `o` is false: the false port `1` of a positive
literal and the true port `0` of a negative literal. -/
def falsePort (o : Occ) : Fin 3 := if φ.pos o then 1 else 0

/-- The (directed) adjacency relation of the cover graph. -/
def rel : Occ × Fin 3 → Occ × Fin 3 → Prop := fun a b =>
  (a.1 = b.1 ∧ a.2 = 0 ∧ b.2 = 1) ∨
  (b.1 = φ.next a.1 ∧ a.2 = 1 ∧ b.2 = 0) ∨
  (a.1 ≠ b.1 ∧ φ.clause a.1 = φ.clause b.1 ∧ a.2 = 2 ∧ b.2 = 2) ∨
  (a.1 = b.1 ∧ a.2 = 2 ∧ b.2 = φ.falsePort a.1)

/-- The cover graph of the formula. -/
def coverGraph : SimpleGraph (Occ × Fin 3) :=
  SimpleGraph.fromRel φ.rel

/-- The literal of `o` is satisfied by the assignment `a`. -/
def Sat (a : Var → Bool) (o : Occ) : Prop :=
  a (φ.var o) = φ.pos o

/-- An assignment together with a satisfied occurrence in every clause. -/
def IsWitness (a : Var → Bool) (ch : Clause → Occ) : Prop :=
  ∀ c, φ.clause (ch c) = c ∧ φ.Sat a (ch c)

/-- The independent set of a witness: the true ports of true variables, the false ports of false
variables, and the chosen literal vertex of every clause. -/
def indep (a : Var → Bool) (ch : Clause → Occ) : Set (Occ × Fin 3) :=
  {w | (w.2 = 0 ∧ a (φ.var w.1) = true) ∨ (w.2 = 1 ∧ a (φ.var w.1) = false) ∨
    (w.2 = 2 ∧ ch (φ.clause w.1) = w.1)}

theorem falsePort_ne_two (o : Occ) : φ.falsePort o ≠ 2 := by
  unfold falsePort; split_ifs <;> decide

theorem adj_pair (o : Occ) : φ.coverGraph.Adj (o, 0) (o, 1) := by
  rw [coverGraph, fromRel_adj]
  exact ⟨by simp, Or.inl (Or.inl ⟨rfl, rfl, rfl⟩)⟩

theorem adj_cycle (o : Occ) : φ.coverGraph.Adj (o, 1) (φ.next o, 0) := by
  rw [coverGraph, fromRel_adj]
  refine ⟨by simp, Or.inl (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))⟩

theorem adj_clique {o o' : Occ} (h : o ≠ o') (hc : φ.clause o = φ.clause o') :
    φ.coverGraph.Adj (o, 2) (o', 2) := by
  rw [coverGraph, fromRel_adj]
  exact ⟨by simpa using h, Or.inl (Or.inr (Or.inr (Or.inl ⟨h, hc, rfl, rfl⟩)))⟩

theorem adj_port (o : Occ) : φ.coverGraph.Adj (o, 2) (o, φ.falsePort o) := by
  rw [coverGraph, fromRel_adj]
  refine ⟨?_, Or.inl (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))⟩
  intro h
  exact φ.falsePort_ne_two o (congrArg Prod.snd h).symm

variable [Fintype Occ] [Fintype Clause]

/-- The map collapsing the two ports of an occurrence and the literal vertices of a clause. -/
def collapse : Occ × Fin 3 → Occ ⊕ Clause :=
  fun w => if w.2 = 2 then .inr (φ.clause w.1) else .inl w.1

omit [Fintype Occ] [Fintype Clause] in
theorem collapse_injOn {I : Set (Occ × Fin 3)} (hI : φ.coverGraph.IsIndepSet I) :
    Set.InjOn φ.collapse I := by
  rintro ⟨o, i⟩ hw ⟨o', i'⟩ hw' heq
  by_contra hne
  have hadj : ¬ φ.coverGraph.Adj (o, i) (o', i') := hI hw hw' hne
  unfold collapse at heq
  by_cases hi : i = 2 <;> by_cases hi' : i' = 2 <;> simp only [hi, hi', ite_true, ite_false,
    Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at heq
  · subst hi hi'
    have ho : o ≠ o' := fun h => hne (by rw [h])
    exact hadj (φ.adj_clique ho heq)
  · subst heq
    have : i ≠ i' := fun h => hne (by rw [h])
    fin_cases i <;> fin_cases i' <;> simp_all
    · exact hadj (φ.adj_pair o)
    · exact hadj (φ.adj_pair o).symm

/-- Independent sets have at most `|Occ| + |Clause|` vertices. -/
theorem ncard_le_of_isIndepSet {I : Set (Occ × Fin 3)} (hI : φ.coverGraph.IsIndepSet I) :
    I.ncard ≤ Fintype.card Occ + Fintype.card Clause := by
  have h := Set.ncard_le_ncard_of_injOn φ.collapse (fun _ _ => Set.mem_univ _)
    (φ.collapse_injOn hI) (Set.toFinite _)
  rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_sum] at h

omit [Fintype Occ] [Fintype Clause] in
theorem indep_isIndepSet {a : Var → Bool} {ch : Clause → Occ} (hw : φ.IsWitness a ch) :
    φ.coverGraph.IsIndepSet (φ.indep a ch) := by
  rintro ⟨o, i⟩ hw1 ⟨o', i'⟩ hw2 hne hadj
  rw [coverGraph, fromRel_adj] at hadj
  obtain ⟨-, hr⟩ := hadj
  simp only [indep, Set.mem_ofPred_eq] at hw1 hw2
  have key : ∀ (o o' : Occ) (i i' : Fin 3),
      (i = 0 ∧ a (φ.var o) = true ∨ i = 1 ∧ a (φ.var o) = false ∨ i = 2 ∧ ch (φ.clause o) = o) →
      (i' = 0 ∧ a (φ.var o') = true ∨ i' = 1 ∧ a (φ.var o') = false ∨
        i' = 2 ∧ ch (φ.clause o') = o') →
      φ.rel (o, i) (o', i') → False := by
    intro o o' i i' h1 h2 hr
    simp only [rel] at hr
    rcases hr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨hne, hc, rfl, rfl⟩ | ⟨rfl, rfl, hp⟩
    · simp_all
    · rw [φ.var_next] at h2; simp_all
    · simp only [Fin.reduceEq, false_and, false_or, true_and] at h1 h2
      exact hne (h1.symm.trans (hc ▸ h2))
    · simp only [Fin.reduceEq, false_and, false_or, true_and] at h1
      have hsat := (hw (φ.clause o)).2
      rw [h1] at hsat
      unfold Sat at hsat
      unfold falsePort at hp
      cases hpos : φ.pos o <;> simp_all
  rcases hr with hr | hr
  · exact key o o' i i' hw1 hw2 hr
  · exact key o' o i' i hw2 hw1 hr

/-- The vertices of `indep a ch`, listed injectively. -/
def indepList (a : Var → Bool) (ch : Clause → Occ) : Occ ⊕ Clause → Occ × Fin 3
  | .inl o => (o, if a (φ.var o) then 0 else 1)
  | .inr c => (ch c, 2)

omit [Fintype Occ] [Fintype Clause] in
theorem indep_eq_range {a : Var → Bool} {ch : Clause → Occ} (hw : φ.IsWitness a ch) :
    φ.indep a ch = Set.range (φ.indepList a ch) := by
  ext ⟨o, i⟩
  simp only [indep, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ⟨.inl o, by simp [indepList, h]⟩
    · exact ⟨.inl o, by simp [indepList, h]⟩
    · exact ⟨.inr (φ.clause o), by simp [indepList, h]⟩
  · rintro ⟨y | c, hy⟩
    · simp only [indepList, Prod.mk.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      cases h : a (φ.var y) <;> simp [h]
    · simp only [indepList, Prod.mk.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      right; right
      exact ⟨rfl, by rw [(hw c).1]⟩

omit [Fintype Occ] [Fintype Clause] in
theorem indepList_injective {a : Var → Bool} {ch : Clause → Occ} (hw : φ.IsWitness a ch) :
    Function.Injective (φ.indepList a ch) := by
  rintro (o | c) (o' | c') h <;> simp only [indepList, Prod.mk.injEq] at h
  · rw [h.1]
  · exfalso; split_ifs at h <;> simp_all
  · exfalso; split_ifs at h <;> simp_all
  · have := congrArg φ.clause h.1
    rw [(hw c).1, (hw c').1] at this
    rw [this]

theorem ncard_indep {a : Var → Bool} {ch : Clause → Occ} (hw : φ.IsWitness a ch) :
    (φ.indep a ch).ncard = Fintype.card Occ + Fintype.card Clause := by
  rw [φ.indep_eq_range hw, Set.ncard_range_of_injective (φ.indepList_injective hw),
    Nat.card_eq_fintype_card, Fintype.card_sum]

/-- Every maximum-size independent set comes from a witness. -/
theorem exists_witness_of_ncard [DecidableEq Occ] {I : Set (Occ × Fin 3)}
    (hI : φ.coverGraph.IsIndepSet I)
    (hcard : I.ncard = Fintype.card Occ + Fintype.card Clause) :
    ∃ a ch, φ.IsWitness a ch ∧ I = φ.indep a ch := by
  classical
  -- the collapse map is a bijection from `I` onto `Occ ⊕ Clause`
  have hsurj : ∀ y : Occ ⊕ Clause, ∃ w ∈ I, φ.collapse w = y := by
    have himg : φ.collapse '' I = Set.univ := by
      apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
      rw [(φ.collapse_injOn hI).ncard_image, hcard, Set.ncard_univ,
        Nat.card_eq_fintype_card, Fintype.card_sum]
    intro y
    have : y ∈ φ.collapse '' I := himg ▸ Set.mem_univ y
    obtain ⟨w, hw, hwy⟩ := this
    exact ⟨w, hw, hwy⟩
  have hport : ∀ o, (o, 0) ∈ I ∨ (o, 1) ∈ I := by
    intro o
    obtain ⟨⟨o', i⟩, hw, hwy⟩ := hsurj (.inl o)
    unfold collapse at hwy
    split_ifs at hwy with hi
    simp only [Sum.inl.injEq] at hwy
    subst hwy
    fin_cases i
    · exact Or.inl hw
    · exact Or.inr hw
    · exact absurd rfl hi
  have hnot01 : ∀ o, ¬ ((o, 0) ∈ I ∧ (o, 1) ∈ I) := fun o ⟨h0, h1⟩ =>
    hI h0 h1 (by simp) (φ.adj_pair o)
  have hlit : ∀ c, ∃ o, φ.clause o = c ∧ (o, 2) ∈ I := by
    intro c
    obtain ⟨⟨o', i⟩, hw, hwy⟩ := hsurj (.inr c)
    unfold collapse at hwy
    split_ifs at hwy with hi
    · simp only [Sum.inr.injEq] at hwy
      obtain rfl : i = 2 := hi
      exact ⟨o', hwy, hw⟩
  -- propagation of false ports along the cyclic order
  have hprop : ∀ o, (o, 1) ∈ I → (φ.next o, 1) ∈ I := by
    intro o h1
    rcases hport (φ.next o) with h0 | h1'
    · exact absurd (φ.adj_cycle o) (hI h1 h0 (by simp))
    · exact h1'
  have hpropk : ∀ (k : ℕ) o, (o, 1) ∈ I → ((φ.next ^ k) o, 1) ∈ I := by
    intro k
    induction k with
    | zero => intro o h; simpa using h
    | succ k ih =>
      intro o h
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hprop _ (ih o h)
  let a : Var → Bool := fun x => decide (∃ o, φ.var o = x ∧ (o, 0) ∈ I)
  have ha : ∀ o, (o, 0) ∈ I ↔ a (φ.var o) = true := by
    intro o
    simp only [a, decide_eq_true_eq]
    refine ⟨fun h => ⟨o, rfl, h⟩, ?_⟩
    rintro ⟨o', hvar, h0'⟩
    by_contra h0
    have h1 : (o, 1) ∈ I := (hport o).resolve_left h0
    obtain ⟨k, hk⟩ := φ.cyclic o o' hvar.symm
    have := hpropk k o h1
    rw [hk] at this
    exact hnot01 o' ⟨h0', this⟩
  let ch : Clause → Occ := fun c => Classical.choose (hlit c)
  have hch : ∀ c, φ.clause (ch c) = c ∧ (ch c, 2) ∈ I := fun c => Classical.choose_spec (hlit c)
  have hlit_unique : ∀ o o', (o, 2) ∈ I → (o', 2) ∈ I → φ.clause o = φ.clause o' → o = o' := by
    intro o o' h h' hc
    by_contra hne
    exact hI h h' (by simpa using hne) (φ.adj_clique hne hc)
  refine ⟨a, ch, ?_, ?_⟩
  · intro c
    refine ⟨(hch c).1, ?_⟩
    have h2 := (hch c).2
    have hnp : (ch c, φ.falsePort (ch c)) ∉ I := fun h =>
      hI h2 h (fun heq => φ.falsePort_ne_two _ (congrArg Prod.snd heq).symm) (φ.adj_port _)
    unfold Sat
    unfold falsePort at hnp
    cases hpos : φ.pos (ch c)
    · simp only [hpos, Bool.false_eq_true, ite_false] at hnp
      rw [ha] at hnp
      simpa using hnp
    · simp only [hpos, ite_true] at hnp
      have : (ch c, 0) ∈ I := (hport _).resolve_right hnp
      exact (ha _).mp this
  · ext ⟨o, i⟩
    simp only [indep, Set.mem_ofPred_eq]
    fin_cases i
    · simp only [Fin.zero_eta, true_and, Fin.reduceEq, false_and, false_or, or_false]
      exact ha o
    · simp only [Fin.mk_one, Fin.reduceEq, false_and, true_and, false_or, or_false]
      constructor
      · intro h1
        by_contra h
        have : a (φ.var o) = true := by simpa using h
        exact hnot01 o ⟨(ha o).mpr this, h1⟩
      · intro h
        have : (o, 0) ∉ I := fun h0 => by rw [ha] at h0; simp_all
        exact (hport o).resolve_left this
    · simp only [Fin.reduceFinMk, Fin.reduceEq, false_and, true_and, false_or]
      constructor
      · intro h2
        exact (hlit_unique _ _ (hch _).2 h2 (hch _).1).trans rfl
      · intro h
        rw [← h]; exact (hch _).2

variable [Finite Var]

omit [Finite Var] in
/-- The minimum vertex covers of the cover graph are the complements of the independent sets of
witnesses, provided a witness exists. -/
theorem isMinCover_iff [DecidableEq Occ] (hex : ∃ a ch, φ.IsWitness a ch)
    (S : Set (Occ × Fin 3)) :
    IsMinCover φ.coverGraph S ↔ ∃ a ch, φ.IsWitness a ch ∧ S = (φ.indep a ch)ᶜ := by
  have htot : ∀ T : Set (Occ × Fin 3), T.ncard + Tᶜ.ncard = 3 * Fintype.card Occ := by
    intro T
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin,
      mul_comm]
  constructor
  · rintro ⟨hS, hmin⟩
    obtain ⟨a₀, ch₀, hw₀⟩ := hex
    have hcov₀ : φ.coverGraph.IsVertexCover (φ.indep a₀ ch₀)ᶜ := by
      rw [← isIndepSet_compl_iff_isVertexCover, compl_compl]
      exact φ.indep_isIndepSet hw₀
    have h1 := hmin _ hcov₀
    have hindep : φ.coverGraph.IsIndepSet Sᶜ := by
      rwa [isIndepSet_compl_iff_isVertexCover]
    have h2 := φ.ncard_le_of_isIndepSet hindep
    have h3 := htot S
    have h4 := htot (φ.indep a₀ ch₀)ᶜ
    rw [compl_compl, φ.ncard_indep hw₀] at h4
    obtain ⟨a, ch, hw, hI⟩ := φ.exists_witness_of_ncard hindep (by lia)
    exact ⟨a, ch, hw, by rw [← hI, compl_compl]⟩
  · rintro ⟨a, ch, hw, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← isIndepSet_compl_iff_isVertexCover, compl_compl]
      exact φ.indep_isIndepSet hw
    · intro S' hS'
      have hindep : φ.coverGraph.IsIndepSet S'ᶜ := by
        rwa [isIndepSet_compl_iff_isVertexCover]
      have h2 := φ.ncard_le_of_isIndepSet hindep
      have h3 := htot S'
      have h4 := htot (φ.indep a ch)ᶜ
      rw [compl_compl, φ.ncard_indep hw] at h4
      lia

end CNF

/-! ### The product formula `z_e = x_u x_v` -/

section Product

variable {V E : Type*} (src tgt : E → V)

/-- The variable of an occurrence `(e,k)` of the product formula of the oriented edge `e = uv`:
occurrences `k = 0,1,2` form the clause `A = (¬x_u ∨ ¬x_v ∨ z)`, `k = 3,4` the clause
`B = (x_u ∨ ¬z)` and `k = 5,6` the clause `C = (x_v ∨ ¬z)`. -/
def prodVar (o : E × Fin 7) : V ⊕ E :=
  match o.2 with
  | 0 => .inl (src o.1)
  | 1 => .inl (tgt o.1)
  | 2 => .inr o.1
  | 3 => .inl (src o.1)
  | 4 => .inr o.1
  | 5 => .inl (tgt o.1)
  | 6 => .inr o.1

/-- The clause of an occurrence: `0 = A`, `1 = B`, `2 = C`. -/
def prodClause (o : E × Fin 7) : E × Fin 3 :=
  (o.1, match o.2 with
    | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 1 | 4 => 1 | 5 => 2 | 6 => 2)

/-- The sign of an occurrence. -/
def prodPos (o : E × Fin 7) : Bool :=
  match o.2 with
  | 0 => false | 1 => false | 2 => true | 3 => true | 4 => false | 5 => true | 6 => false

/-- The product formula of an oriented graph with a cyclic order `next` of the occurrences of
each variable. -/
def productCNF (next : Equiv.Perm (E × Fin 7))
    (var_next : ∀ o, prodVar src tgt (next o) = prodVar src tgt o)
    (cyclic : ∀ o o', prodVar src tgt o = prodVar src tgt o' → ∃ k : ℕ, (next ^ k) o = o') :
    CNF (E × Fin 7) (V ⊕ E) (E × Fin 3) where
  var := prodVar src tgt
  clause := prodClause
  pos := prodPos
  next := next
  var_next := var_next
  cyclic := cyclic

/-- The correlation polytope indexed by vertices and oriented edges. -/
noncomputable def corVecOr (X : Set V) : V ⊕ E → ℝ :=
  fun i => by
    classical
    exact match i with
      | .inl v => if v ∈ X then 1 else 0
      | .inr e => if src e ∈ X ∧ tgt e ∈ X then 1 else 0

noncomputable def COROr : Set (V ⊕ E → ℝ) :=
  convexHull ℝ (Set.range (corVecOr src tgt))

/-- The assignment induced by a vertex set. -/
noncomputable def prodAssign (X : Set V) : V ⊕ E → Bool := fun i => by
  classical
  exact match i with
    | .inl v => decide (v ∈ X)
    | .inr e => decide (src e ∈ X ∧ tgt e ∈ X)

/-- A satisfied occurrence in every clause, for the assignment induced by `X`. -/
noncomputable def prodChoice (X : Set V) : E × Fin 3 → E × Fin 7 := fun c => by
  classical
  exact match c.2 with
    | 0 => if src c.1 ∈ X ∧ tgt c.1 ∈ X then (c.1, 2) else if src c.1 ∈ X then (c.1, 1)
        else (c.1, 0)
    | 1 => if src c.1 ∈ X then (c.1, 3) else (c.1, 4)
    | 2 => if tgt c.1 ∈ X then (c.1, 5) else (c.1, 6)

variable {src tgt}

variable (next : Equiv.Perm (E × Fin 7))
  (var_next : ∀ o, prodVar src tgt (next o) = prodVar src tgt o)
  (cyclic : ∀ o o', prodVar src tgt o = prodVar src tgt o' → ∃ k : ℕ, (next ^ k) o = o')

theorem prodWitness (X : Set V) :
    (productCNF src tgt next var_next cyclic).IsWitness (prodAssign src tgt X)
      (prodChoice src tgt X) := by
  classical
  rintro ⟨e, c⟩
  fin_cases c <;>
    simp only [productCNF, prodChoice, prodClause, CNF.Sat, prodVar, prodPos, prodAssign,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;>
    split_ifs <;> simp_all

/-- In a witness of the product formula, `z_e = x_u x_v`. -/
theorem prodWitness_edge {a : V ⊕ E → Bool} {ch : E × Fin 3 → E × Fin 7}
    (hw : (productCNF src tgt next var_next cyclic).IsWitness a ch) (e : E) :
    a (.inr e) = (a (.inl (src e)) && a (.inl (tgt e))) := by
  have hA : a (.inl (src e)) = false ∨ a (.inl (tgt e)) = false ∨ a (.inr e) = true := by
    obtain ⟨h1, h2⟩ := hw (e, 0)
    revert h1 h2
    generalize ch (e, 0) = o
    obtain ⟨e', k⟩ := o
    intro h1 h2
    simp only [productCNF, prodClause, Prod.mk.injEq] at h1
    obtain ⟨rfl, hk⟩ := h1
    simp only [productCNF, CNF.Sat] at h2
    fin_cases k <;> simp only [prodVar, prodPos] at h2 hk ⊢ <;> simp_all
  have hB : a (.inl (src e)) = true ∨ a (.inr e) = false := by
    obtain ⟨h1, h2⟩ := hw (e, 1)
    revert h1 h2
    generalize ch (e, 1) = o
    obtain ⟨e', k⟩ := o
    intro h1 h2
    simp only [productCNF, prodClause, Prod.mk.injEq] at h1
    obtain ⟨rfl, hk⟩ := h1
    simp only [productCNF, CNF.Sat] at h2
    fin_cases k <;> simp only [prodVar, prodPos] at h2 hk ⊢ <;> simp_all
  have hC : a (.inl (tgt e)) = true ∨ a (.inr e) = false := by
    obtain ⟨h1, h2⟩ := hw (e, 2)
    revert h1 h2
    generalize ch (e, 2) = o
    obtain ⟨e', k⟩ := o
    intro h1 h2
    simp only [productCNF, prodClause, Prod.mk.injEq] at h1
    obtain ⟨rfl, hk⟩ := h1
    simp only [productCNF, CNF.Sat] at h2
    fin_cases k <;> simp only [prodVar, prodPos] at h2 hk ⊢ <;> simp_all
  revert hA hB hC
  cases a (.inl (src e)) <;> cases a (.inl (tgt e)) <;> cases a (.inr e) <;> simp

end Product

/-! ### Minimum covers as a face of the vertex cover polytope -/

section MinCover

variable {W : Type*} [Fintype W] (J : SimpleGraph W)

theorem exists_isMinCover : ∃ S, IsMinCover J S := by
  obtain ⟨S, hS, hmin⟩ := Set.exists_min_image {S : Set W | J.IsVertexCover S} Set.ncard
    (Set.toFinite _) ⟨Set.univ, isVertexCover_univ⟩
  exact ⟨S, hS, fun S' hS' => hmin S' hS'⟩

/-- The convex hull of the minimum covers is the face `x(V) = τ` of the vertex cover polytope. -/
theorem minCoverFace_eq_inter {S₀ : Set W} (h₀ : IsMinCover J S₀) :
    minCoverFace J = VC J ∩ {x | sumOver Finset.univ x = (S₀.ncard : ℝ)} := by
  unfold minCoverFace VC
  rw [convexHull_inter_hyperplane_of_ge]
  · congr 1
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_inter_iff, sumOver_apply]
    constructor
    · rintro ⟨S, hS, rfl⟩
      refine ⟨⟨S, hS.1, rfl⟩, ?_⟩
      rw [sum_vertexVec]
      exact_mod_cast le_antisymm (hS.2 _ h₀.1) (h₀.2 _ hS.1)
    · rintro ⟨⟨S, hS, rfl⟩, hsum⟩
      rw [sum_vertexVec] at hsum
      have hc : S.ncard = S₀.ncard := by exact_mod_cast hsum
      exact ⟨S, ⟨hS, fun S' hS' => hc ▸ h₀.2 S' hS'⟩, rfl⟩
  · rintro x ⟨S, hS, rfl⟩
    rw [sumOver_apply, sum_vertexVec]
    exact_mod_cast h₀.2 S hS

theorem xc_minCoverFace_le_VC : xc (minCoverFace J) ≤ xc (VC J) := by
  obtain ⟨S₀, h₀⟩ := exists_isMinCover J
  rw [minCoverFace_eq_inter J h₀]
  exact xc_inter_hyperplane_le _ _ _

end MinCover

/-! ### Reading the ports: the correlation polytope is an image of the minimum-cover face -/

section Projection

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {src tgt : E → V} (next : Equiv.Perm (E × Fin 7))
  (var_next : ∀ o, prodVar src tgt (next o) = prodVar src tgt o)
  (cyclic : ∀ o o', prodVar src tgt o = prodVar src tgt o' → ∃ k : ℕ, (next ^ k) o = o')
  (occV : V → E × Fin 7) (hoccV : ∀ v, prodVar src tgt (occV v) = .inl v)

/-- The positions that are read: one true port per variable. -/
def readPos (occV : V → E × Fin 7) : V ⊕ E → (E × Fin 7) × Fin 3
  | .inl v => (occV v, 0)
  | .inr e => ((e, 2), 0)

/-- Reading `1 - y` at one true port per variable. -/
noncomputable def readPorts (occV : V → E × Fin 7) :
    ((E × Fin 7) × Fin 3 → ℝ) →ᵃ[ℝ] (V ⊕ E → ℝ) :=
  AffineMap.const ℝ _ 1 - (LinearMap.funLeft ℝ ℝ (readPos occV)).toAffineMap

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] in
theorem readPorts_apply (y : (E × Fin 7) × Fin 3 → ℝ) (i : V ⊕ E) :
    readPorts occV y i = 1 - y (readPos occV i) := by
  simp [readPorts, LinearMap.funLeft_apply]

include hoccV in
theorem readPorts_vertexVec_indep {a : V ⊕ E → Bool} {ch : E × Fin 3 → E × Fin 7}
    (hw : (productCNF src tgt next var_next cyclic).IsWitness a ch) :
    readPorts occV (vertexVec ((productCNF src tgt next var_next cyclic).indep a ch)ᶜ) =
      corVecOr src tgt {v | a (.inl v) = true} := by
  classical
  funext i
  rw [readPorts_apply, vertexVec_apply]
  rcases i with v | e
  · simp only [readPos, Set.mem_compl_iff, CNF.indep, Set.mem_ofPred_eq, productCNF, hoccV,
      corVecOr, Fin.reduceEq, false_and, or_false, true_and]
    by_cases h : a (.inl v) = true <;> simp [h]
  · have hedge := prodWitness_edge next var_next cyclic hw e
    simp only [readPos, Set.mem_compl_iff, CNF.indep, Set.mem_ofPred_eq, productCNF, prodVar,
      corVecOr, Fin.reduceEq, false_and, or_false, true_and, hedge]
    by_cases h1 : a (.inl (src e)) = true <;> by_cases h2 : a (.inl (tgt e)) = true <;>
      simp [h1, h2]

include hoccV in
/-- **Lemma 3 (projection).** Reading one true port per variable maps the minimum-cover face of
the cover graph of the product formula onto the correlation polytope. -/
theorem readPorts_image_minCoverFace :
    readPorts occV '' minCoverFace (productCNF src tgt next var_next cyclic).coverGraph =
      COROr src tgt := by
  classical
  set φ := productCNF src tgt next var_next cyclic with hφ
  have hex : ∃ a ch, φ.IsWitness a ch := ⟨_, _, prodWitness next var_next cyclic ∅⟩
  unfold minCoverFace COROr
  rw [image_convexHull_eq, Set.image_image]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨S, hS, rfl⟩
    obtain ⟨a, ch, hw, rfl⟩ := (φ.isMinCover_iff hex S).mp hS
    exact ⟨_, (readPorts_vertexVec_indep next var_next cyclic occV hoccV hw).symm⟩
  · rintro ⟨X, rfl⟩
    have hw := prodWitness next var_next cyclic X
    refine ⟨_, (φ.isMinCover_iff hex _).mpr ⟨_, _, hw, rfl⟩, ?_⟩
    rw [readPorts_vertexVec_indep next var_next cyclic occV hoccV hw]
    congr 1
    ext v
    simp [prodAssign]

include hoccV in
theorem xc_COROr_le :
    xc (COROr src tgt) ≤ xc (minCoverFace (productCNF src tgt next var_next cyclic).coverGraph) :=
  xc_le_of_image_eq _ (readPorts_image_minCoverFace next var_next cyclic occV hoccV)

/-- Reindexing oriented edges by the edges of `L`. -/
noncomputable def reindexCOR (L : SimpleGraph V) (eqv : E ≃ L.edgeSet) :
    (V ⊕ E → ℝ) →ₗ[ℝ] (V ⊕ L.edgeSet → ℝ) :=
  LinearMap.funLeft ℝ ℝ (Sum.map id eqv.symm)

theorem COR_eq_image (L : SimpleGraph V) (eqv : E ≃ L.edgeSet)
    (heqv : ∀ e, (eqv e : Sym2 V) = s(src e, tgt e)) :
    reindexCOR L eqv '' COROr src tgt = COR L := by
  classical
  unfold COROr COR
  rw [← LinearMap.coe_toAffineMap, image_convexHull_eq, ← Set.range_comp]
  have hfun : ⇑(reindexCOR L eqv).toAffineMap ∘ corVecOr src tgt = corVec L := by
    funext X i
    simp only [Function.comp_apply, LinearMap.coe_toAffineMap, reindexCOR,
      LinearMap.funLeft_apply]
    rcases i with v | e'
    · simp [corVecOr, corVec]
    · obtain ⟨e, rfl⟩ := eqv.surjective e'
      simp only [Sum.map_inr, Equiv.symm_apply_apply, corVecOr, corVec, heqv, Sym2.mem_iff]
      congr 1
      apply propext
      constructor
      · rintro ⟨h1, h2⟩ v (rfl | rfl) <;> assumption
      · intro h; exact ⟨h _ (Or.inl rfl), h _ (Or.inr rfl)⟩
  rw [hfun]

include hoccV in
/-- **Lemma 3.** For every graph `L` with an orientation of its edges, every cyclic order of the
literal occurrences, and every vertex incident with an edge, the correlation polytope of `L` is
an affine image of the minimum-cover face of the cover graph of the product formula. -/
theorem xc_COR_le_minCoverFace (L : SimpleGraph V) (eqv : E ≃ L.edgeSet)
    (heqv : ∀ e, (eqv e : Sym2 V) = s(src e, tgt e)) :
    xc (COR L) ≤ xc (minCoverFace (productCNF src tgt next var_next cyclic).coverGraph) := by
  rw [← COR_eq_image L eqv heqv, ← LinearMap.coe_toAffineMap]
  exact (xc_image_le _ _).trans (xc_COROr_le next var_next cyclic occV hoccV)

end Projection

end Lemmata.PlanarSteinerXC
