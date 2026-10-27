module

public import Lemmata.CocubicCovering.Compute.CoreSearch
public meta import Lemmata.CocubicCovering.Compute.CoreSearch
public import Lemmata.CocubicCovering.Certificate.CoreCertificateSound
public meta import Lemmata.CocubicCovering.Certificate.CoreCertificateSound
public import Lemmata.CocubicCovering.Proof.Search
public meta import Lemmata.CocubicCovering.Proof.Search
public import Lemmata.CocubicCovering.Proof.Encoding
public meta import Lemmata.CocubicCovering.Proof.Encoding

@[expose] public section

namespace Lemmata.CocubicCovering.Compute.CoreSearch

open Lemmata.CocubicCovering
open CoveringAffine CoveringBits CoveringWitness CoveringPackedWitness CoveringBranching

structure Model where
  roots : Nat → Root
  allowed : Nat → Vector 127 → Prop
  kernel : Vector 127 → Submodule Field (Vector 12)
  kernel_ambient : ∀ root v, allowed root v → kernel v ≤
    familySpan (decoded (n := 12) (roots root).radical.get)
  kernel_dimension : ∀ root v, allowed root v → (roots root).required ≤ Module.finrank Field (kernel v)
  point : ∀ root v, allowed root v → v (Fin.last 126) = 1
  sourceRows : State → List Nat
  sourceRows_sound : ∀ state row, row ∈ sourceRows state → ∀ v, allowed state.root v →
    familySpan (decoded (n := 12) state.core.get) ≤ kernel v → evalRow row v = 0

def Feasible (model : Model) (state : State) : Prop :=
  CoveringSearch.Feasible (model.allowed state.root) model.kernel (decoded state.core.get)

structure Closed (model : Model) (state : State) : Type where
  valid : ¬Feasible model state

structure Equation (model : Model) (state : State) where
  bits : Nat
  valid : ∀ v, model.allowed state.root v →
    familySpan (decoded (n := 12) state.core.get) ≤ model.kernel v → evalRow bits v = 0

def Equation.xor {model : Model} {state : State} (a b : Equation model state) : Equation model state :=
  ⟨a.bits ^^^ b.bits, by intro v hv hc; rw [evalRow_xor, a.valid v hv hc, b.valid v hv hc]; rfl⟩

def Equation.close {model : Model} {state : State} (row : Equation model state) : Option (Closed model state) :=
  if h : row.bits = 2 ^ 126 then
    some ⟨by
      rintro ⟨v, hv, hc⟩
      have hz := row.valid v hv hc
      rw [h] at hz
      have hp : evalRow (2 ^ 126) v = 1 :=
        (CoveringEncoding.evalRow_two_pow (Fin.last 126) v).trans (model.point state.root v hv)
      exact one_ne_zero (hp.symm.trans hz)⟩
  else none

abbrev Basis (model : Model) (state : State) := Array (Option (Equation model state))

def insert {model : Model} {state : State} : Nat → Basis model state → Equation model state →
    Basis model state × Option (Closed model state)
  | 0, basis, _ => (basis, none)
  | fuel + 1, basis, row =>
      if row.bits == 0 then (basis, none)
      else
        match row.close with
        | some closed => (basis, some closed)
        | none =>
            let pivot := (row.bits % 2 ^ 126).log2
            match basis[pivot]?.getD none with
            | none => (basis.set! pivot (some row), none)
            | some previous => insert fuel basis (row.xor previous)

def linearClose (model : Model) (state : State) : Option (Closed model state) := Id.run do
  let mut basis := Array.replicate 126 none
  for row in (model.sourceRows state).attach do
    let equation : Equation model state := ⟨row.val, model.sourceRows_sound state row.val row.property⟩
    let (next, closed) := insert 127 basis equation
    if closed.isSome then return closed
    basis := next
  return none

def branchCheck (root : Root) (state : State) (data : Branch) : Bool :=
  (Certificate.CoreCertificate.listCheckSpan data.fresh root.radical data.inRadical &&
    Certificate.PureDual.listCheckCombinedDual 12 state.core data.fresh data.dual) &&
      decide (root.radical.length < data.fresh.length + root.required)

theorem branch_sound (model : Model) (state : State) (data : Branch)
    (accepted : branchCheck (model.roots state.root) state data = true)
    (closed : ∀ child ∈ children state data, ¬Feasible model child) :
    ¬Feasible model state := by
  obtain ⟨hfirst, hnumeric⟩ := Bool.and_eq_true_iff.mp accepted
  obtain ⟨hin, hdual⟩ := Bool.and_eq_true_iff.mp hfirst
  have hin' := Certificate.CoreCertificate.listCheckSpan_eq data.fresh (model.roots state.root).radical data.inRadical
  rw [hin'] at hin
  have hdual' := Certificate.PureDual.listCheckCombinedDual_eq 12 state.core data.fresh data.dual
  rw [hdual'] at hdual
  have hcombined := listCheckCombinedDual_sound 12 state.core data.fresh data.dual hdual
  rintro ⟨v, hv, hc⟩
  have hambient : Module.finrank Field
      (familySpan (decoded (n := 12) (model.roots state.root).radical.get)) <
      data.fresh.length + (model.roots state.root).required := by
    have upper := finrank_range_le_card (R := Field)
      (decoded (n := 12) (model.roots state.root).radical.get)
    change Module.finrank Field _ ≤ _ at upper
    simp only [Fintype.card_fin] at upper
    exact lt_of_le_of_lt upper (of_decide_eq_true hnumeric)
  obtain ⟨b, hb, hnew, _, _⟩ := exists_kernel_branch
    (decoded (n := 12) data.fresh.get)
    (familySpan (decoded (n := 12) (model.roots state.root).radical.get))
    (model.kernel v) (familySpan (decoded (n := 12) state.core.get))
    (listCheckSpan_sound 12 _ _ _ hin) (model.kernel_ambient state.root v hv) hc
    hcombined.1 hcombined.2 (model.kernel_dimension state.root v hv) hambient
  obtain ⟨mask, hbound, hdecode⟩ := exists_bounded_mask b
  have hpositive : 0 < mask := by
    by_contra hzero
    have hz : mask = 0 := by omega
    have hbzero : b = 0 := by simpa only [hz, decodeMask_zero] using hdecode.symm
    exact (mem_branches b).mp hb hbzero
  have hmask : mask - 1 < 2 ^ data.fresh.length - 1 := by omega
  have hchild : State.mk state.root (state.core ++ [combine data.fresh mask]) ∈ children state data := by
    apply List.mem_map.mpr
    refine ⟨mask - 1, List.mem_range.mpr hmask, ?_⟩
    rw [Nat.sub_add_cancel (by omega : 1 ≤ mask)]
  apply closed _ hchild
  refine ⟨v, hv, Submodule.span_le.mpr ?_⟩
  rintro _ ⟨i, rfl⟩
  change (decodeMask ((state.core ++ [combine data.fresh mask]).get i) : Vector 12) ∈ model.kernel v
  have hi : (state.core ++ [combine data.fresh mask]).get i ∈ state.core ++ [combine data.fresh mask] :=
    List.get_mem _ _
  rcases List.mem_append.mp hi with hi | hi
  · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hi
    rw [← hj]
    exact hc (Submodule.subset_span ⟨j, rfl⟩)
  · have he := List.mem_singleton.mp hi
    rw [he]
    have hcombine : (decodeMask (combine data.fresh mask) : Vector 12) =
        CoveringBranching.combine (decoded data.fresh.get) b := by
      rw [combine, Certificate.CoreCertificate.composeRow_eq,
        CoveringPackedAction.decodeMask_composeRow_familyLinear, hdecode]
      rfl
    rw [hcombine]
    exact hnew

structure CacheEntry (model : Model) where
  state : State
  closed : Closed model state

abbrev Cache (model : Model) := Std.HashMap State (CacheEntry model)

def cached {model : Model} (cache : Cache model) (state : State) : Option (Closed model state) := do
  let entry ← cache[state]?
  if h : entry.state = state then return h ▸ entry.closed else none

def remember {model : Model} (cache : Cache model) (state : State) (closed : Closed model state) : Cache model :=
  cache.insert state ⟨state, closed⟩

structure Normalized (model : Model) (state : State) where
  state' : State
  valid : Feasible model state → Feasible model state'

def normalize (model : Model) (state : State) : Option (Normalized model state) := do
  let core := canonical state.core
  let coordinates ← coefficients core state.core
  if h : Certificate.CoreCertificate.listCheckSpan core state.core coordinates = true then
    have hs : familySpan (decoded (n := 12) core.get) ≤
        familySpan (decoded (n := 12) state.core.get) := by
      rw [Certificate.CoreCertificate.listCheckSpan_eq] at h
      exact listCheckSpan_sound 12 _ _ _ h
    return ⟨⟨state.root, core⟩, by
      rintro ⟨v, hv, hc⟩
      exact ⟨v, hv, hs.trans hc⟩⟩
  else none

structure AllClosed (model : Model) (states : List State) : Type where
  valid : ∀ state ∈ states, ¬Feasible model state

def collect {model : Model}
    (visit : Cache model → (state : State) → Cache model × Option (Closed model state)) :
    (states : List State) → Cache model → Cache model × Option (AllClosed model states)
  | [], cache => (cache, some ⟨by intro _ h; cases h⟩)
  | state :: states, cache =>
      let (cache, first) := visit cache state
      match first with
      | none => (cache, none)
      | some first =>
          let (cache, rest) := collect visit states cache
          match rest with
          | none => (cache, none)
          | some rest =>
              (cache, some ⟨by
                intro next hnext
                rcases List.mem_cons.mp hnext with rfl | hnext
                · exact first.valid
                · exact rest.valid next hnext⟩)

def branchClose (model : Model)
    (visit : Cache model → (state : State) → Cache model × Option (Closed model state))
    (cache : Cache model) (state : State) : Cache model × Option (Closed model state) :=
  match branch (model.roots state.root) state with
  | none => (cache, none)
  | some data =>
      if accepted : branchCheck (model.roots state.root) state data = true then
        let (cache, childrenClosed) := collect visit (children state data) cache
        match childrenClosed with
        | none => (cache, none)
        | some childrenClosed =>
            let closed : Closed model state := ⟨branch_sound model state data accepted childrenClosed.valid⟩
            (remember cache state closed, some closed)
      else (cache, none)

def closeNormalized (model : Model) (terminal : (state : State) → Option (Closed model state))
    (visit : Cache model → (state : State) → Cache model × Option (Closed model state))
    (cache : Cache model) (state : State) : Cache model × Option (Closed model state) :=
  match cached cache state with
  | some closed => (cache, some closed)
  | none =>
      match linearClose model state with
      | some closed => (remember cache state closed, some closed)
      | none =>
          match terminal state with
          | some closed => (remember cache state closed, some closed)
          | none => branchClose model visit cache state

def searchWith (model : Model) (terminal : (state : State) → Option (Closed model state))
    (normalizer : (state : State) → Option (Normalized model state)) :
    Nat → Cache model → (state : State) → Cache model × Option (Closed model state)
  | 0, cache, _ => (cache, none)
  | fuel + 1, cache, state =>
      match cached cache state with
      | some closed => (cache, some closed)
      | none =>
          match linearClose model state with
          | some closed => (remember cache state closed, some closed)
          | none =>
              match terminal state with
              | some closed => (remember cache state closed, some closed)
              | none =>
                  match normalizer state with
                  | none => (cache, none)
                  | some normalized =>
                      let visit := searchWith model terminal normalizer fuel
                      let (cache, normalizedClosed) :=
                        if normalized.state' = state then branchClose model visit cache normalized.state'
                        else closeNormalized model terminal visit cache normalized.state'
                      match normalizedClosed with
                      | none => (cache, none)
                      | some normalizedClosed =>
                          let closed : Closed model state := ⟨fun possible => normalizedClosed.valid (normalized.valid possible)⟩
                          (remember cache state closed, some closed)

def search (model : Model) (terminal : (state : State) → Option (Closed model state)) :=
  searchWith model terminal (normalize model)

def refutesWith (model : Model) (terminal : (state : State) → Option (Closed model state))
    (normalizer : (state : State) → Option (Normalized model state))
    (fuel : Nat) (state : State) : Bool :=
  ((searchWith model terminal normalizer fuel ∅ state).2).isSome

theorem refutesWith_sound (model : Model) (terminal : (state : State) → Option (Closed model state))
    (normalizer : (state : State) → Option (Normalized model state))
    (fuel : Nat) (state : State) (checked : refutesWith model terminal normalizer fuel state = true) :
    ¬Feasible model state := by
  unfold refutesWith at checked
  cases h : (searchWith model terminal normalizer fuel ∅ state).2 with
  | none => simp [h] at checked
  | some closed => exact closed.valid

def refutes (model : Model) (terminal : (state : State) → Option (Closed model state))
    (fuel : Nat) (state : State) : Bool :=
  ((search model terminal fuel ∅ state).2).isSome

theorem refutes_sound (model : Model) (terminal : (state : State) → Option (Closed model state))
    (fuel : Nat) (state : State) (checked : refutes model terminal fuel state = true) :
    ¬Feasible model state := by
  unfold refutes at checked
  cases h : (search model terminal fuel ∅ state).2 with
  | none => simp [h] at checked
  | some closed => exact closed.valid

end Lemmata.CocubicCovering.Compute.CoreSearch
