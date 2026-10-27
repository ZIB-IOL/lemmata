module

public import Lemmata.CocubicCovering.Compute.CoreSearchSound
public meta import Lemmata.CocubicCovering.Compute.CoreSearchSound

@[expose] public section

namespace Lemmata.CocubicCovering.Compute.CoreIncremental

open CoreSearch

def solveUsing (basis : Array (Nat × Nat)) (target : Nat) : Option Nat :=
  let result := reducePair (target.log2 + 1) basis (target, 0)
  if result.1 == 0 then some result.2 else none

def coefficients (source target : List Nat) : Option (List Nat) :=
  let basis := elimination target
  source.mapM (solveUsing basis)

def fresh (radical core : List Nat) (count : Nat) : List Nat × List Nat := Id.run do
  let mut basis := Array.replicate 12 0
  for vector in core do
    let row := reduceVector 12 basis vector
    if row != 0 then basis := basis.set! row.log2 row
  let mut vectors := []
  let mut inclusion := []
  for (vector, i) in radical.zipIdx do
    if vectors.length == count then break
    let row := reduceVector 12 basis vector
    if row != 0 then
      basis := basis.set! row.log2 row
      vectors := vectors ++ [vector]
      inclusion := inclusion ++ [2 ^ i]
  return (vectors, inclusion)

def branch (root : Root) (state : State) : Option Branch := do
  let count := root.radical.length + 1 - root.required
  let (vectors, inclusion) := fresh root.radical state.core count
  if vectors.length != count then return ← none
  let combined := state.core ++ vectors
  let targets := (List.range combined.length).map (2 ^ ·)
  let dualRows ← coefficients targets (transpose 12 combined)
  return ⟨vectors, inclusion, dualRows⟩

open CoreSearch
open Lemmata.CocubicCovering
open CoveringAffine CoveringBits CoveringWitness CoveringPackedWitness CoveringBranching

structure RowsFrom (model : Model) where
  size : State → Nat
  rows : State → Nat → List Nat
  valid : ∀ state skip row, row ∈ rows state skip → row ∈ model.sourceRows state

def extend (state : State) (mask : Nat) : State :=
  ⟨state.root, state.core ++ [mask]⟩

theorem span_extend (state : State) (mask : Nat) :
    familySpan (decoded (n := 12) state.core.get) ≤
      familySpan (decoded (n := 12) (extend state mask).core.get) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change (decodeMask (state.core.get i) : Vector 12) ∈ _
  have hi : state.core.get i ∈ (extend state mask).core := by
    apply List.mem_append.mpr
    exact Or.inl (List.get_mem _ _)
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hi
  rw [← hj]
  exact Submodule.subset_span ⟨j, rfl⟩

def extendEquation {model : Model} {state : State} (mask : Nat)
    (equation : Equation model state) : Equation model (extend state mask) :=
  ⟨equation.bits, by
    intro v hv hc
    exact equation.valid v hv ((span_extend state mask).trans hc)⟩

def extendBasis {model : Model} {state : State} (mask : Nat)
    (basis : Basis model state) : Basis model (extend state mask) :=
  basis.map (Option.map (extendEquation mask))

def emptyBasis (model : Model) (state : State) : Basis model state :=
  Array.replicate 126 none

def linearFrom (model : Model) (source : RowsFrom model) (state : State)
    (basis : Basis model state) (skip : Nat) :
    Basis model state × Option (Closed model state) := Id.run do
  let mut basis := basis
  for row in (source.rows state skip).attach do
    let equation : Equation model state :=
      ⟨row.val, model.sourceRows_sound state row.val
        (source.valid state skip row.val row.property)⟩
    let (next, closed) := insert 127 basis equation
    if closed.isSome then return (next, closed)
    basis := next
  return (basis, none)

structure ExtensionsClosed (model : Model) (state : State) (masks : List Nat) : Type where
  valid : ∀ mask ∈ masks, ¬Feasible model (extend state mask)

def masks (data : Branch) : List Nat :=
  (List.range (2 ^ data.fresh.length - 1)).map fun i => combine data.fresh (i + 1)

structure MemoCache (model : Model) (Alias : Type) where
  closed : CoreSearch.Cache model
  aliases : Alias

def cached {model : Model} {Alias : Type} (cache : MemoCache model Alias) (state : State) :
    Option (Closed model state) :=
  CoreSearch.cached cache.closed state

def remember {model : Model} {Alias : Type} (cache : MemoCache model Alias)
    (state : State) (closed : Closed model state) : MemoCache model Alias :=
  let previous := cache.closed
  let aliases := cache.aliases
  let next := CoreSearch.remember previous state closed
  ⟨next, aliases⟩

def collectExtensions {model : Model} {Alias : Type} (source : RowsFrom model) (state : State)
    (basis : Basis model state)
    (visit : MemoCache model Alias → (child : State) → Basis model child → Nat →
      MemoCache model Alias × Option (Closed model child)) :
    (masks : List Nat) → MemoCache model Alias →
      MemoCache model Alias × Option (ExtensionsClosed model state masks)
  | [], cache => (cache, some ⟨by intro _ h; cases h⟩)
  | mask :: masks, cache =>
      let (cache, first) := visit cache (extend state mask)
        (extendBasis mask basis) (source.size state)
      match first with
      | none => (cache, none)
      | some first =>
          let (cache, rest) := collectExtensions source state basis visit masks cache
          match rest with
          | none => (cache, none)
          | some rest =>
              (cache, some ⟨by
                intro next hnext
                rcases List.mem_cons.mp hnext with rfl | hnext
                · exact first.valid
                · exact rest.valid next hnext⟩)

def branchClose (model : Model) {Alias : Type} (source : RowsFrom model)
    (brancher : Root → State → Option Branch)
    (visit : MemoCache model Alias → (child : State) → Basis model child → Nat →
      MemoCache model Alias × Option (Closed model child))
    (cache : MemoCache model Alias) (state : State) (basis : Basis model state) :
    MemoCache model Alias × Option (Closed model state) :=
  match brancher (model.roots state.root) state with
  | none => (cache, none)
  | some data =>
      if accepted : branchCheck (model.roots state.root) state data = true then
        let (cache, childrenClosed) := collectExtensions source state basis visit (masks data) cache
        match childrenClosed with
        | none => (cache, none)
        | some childrenClosed =>
            let closed : Closed model state := ⟨by
              apply branch_sound model state data accepted
              intro child hchild
              obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hchild
              apply childrenClosed.valid (combine data.fresh (i + 1))
              exact List.mem_map.mpr ⟨i, hi, rfl⟩⟩
            (remember cache state closed, some closed)
      else (cache, none)

def closeNormalized (model : Model) {Alias : Type} (source : RowsFrom model)
    (brancher : Root → State → Option Branch)
    (terminal : (state : State) → Option (Closed model state))
    (visit : MemoCache model Alias → (child : State) → Basis model child → Nat →
      MemoCache model Alias × Option (Closed model child))
    (cache : MemoCache model Alias) (state : State) : MemoCache model Alias × Option (Closed model state) :=
  match cached cache state with
  | some closed => (cache, some closed)
  | none =>
      let (basis, closed) := linearFrom model source state (emptyBasis model state) 0
      match closed with
      | some closed => (remember cache state closed, some closed)
      | none =>
          match terminal state with
          | some closed => (remember cache state closed, some closed)
          | none => branchClose model source brancher visit cache state basis

def searchWith (model : Model) {Alias : Type} (source : RowsFrom model)
    (brancher : Root → State → Option Branch)
    (terminal : (state : State) → Option (Closed model state))
    (normalizer : Alias → (state : State) → Alias × Option (Normalized model state)) :
    Nat → MemoCache model Alias → (state : State) → Basis model state → Nat →
      MemoCache model Alias × Option (Closed model state)
  | 0, cache, _, _, _ => (cache, none)
  | fuel + 1, cache, state, initial, skip =>
      match cached cache state with
      | some closed => (cache, some closed)
      | none =>
          let (basis, closed) := linearFrom model source state initial skip
          match closed with
          | some closed => (remember cache state closed, some closed)
          | none =>
              match terminal state with
              | some closed => (remember cache state closed, some closed)
              | none =>
                  let closedCache := cache.closed
                  let previousAliases := cache.aliases
                  let (aliases, normalized) := normalizer previousAliases state
                  let cache : MemoCache model Alias := ⟨closedCache, aliases⟩
                  match normalized with
                  | none => (cache, none)
                  | some normalized =>
                      let visit := searchWith model source brancher terminal normalizer fuel
                      let (cache, normalizedClosed) :=
                        if h : normalized.state' = state then
                          let basis' : Basis model normalized.state' := h.symm ▸ basis
                          branchClose model source brancher visit cache normalized.state' basis'
                        else closeNormalized model source brancher terminal visit cache normalized.state'
                      match normalizedClosed with
                      | none => (cache, none)
                      | some normalizedClosed =>
                          let closed : Closed model state :=
                            ⟨fun possible => normalizedClosed.valid (normalized.valid possible)⟩
                          (remember cache state closed, some closed)

def refutesWith (model : Model) {Alias : Type} (source : RowsFrom model)
    (brancher : Root → State → Option Branch)
    (terminal : (state : State) → Option (Closed model state))
    (normalizer : Alias → (state : State) → Alias × Option (Normalized model state))
    (aliases : Alias) (fuel : Nat) (state : State) : Bool :=
  ((searchWith model source brancher terminal normalizer fuel ⟨∅, aliases⟩ state
    (emptyBasis model state) 0).2).isSome

theorem refutesWith_sound (model : Model) {Alias : Type} (source : RowsFrom model)
    (brancher : Root → State → Option Branch)
    (terminal : (state : State) → Option (Closed model state))
    (normalizer : Alias → (state : State) → Alias × Option (Normalized model state))
    (aliases : Alias) (fuel : Nat) (state : State)
    (checked : refutesWith model source brancher terminal normalizer aliases fuel state = true) :
    ¬Feasible model state := by
  unfold refutesWith at checked
  cases h : (searchWith model source brancher terminal normalizer fuel ⟨∅, aliases⟩ state
      (emptyBasis model state) 0).2 with
  | none => simp [h] at checked
  | some closed => exact closed.valid

end Lemmata.CocubicCovering.Compute.CoreIncremental
