module

public import Lemmata.SymmetricBellCrossPolytope.Main
public import Mathlib.Analysis.Convex.Exposed

/-! # A projected Bell edge whose lift is not a facet

In the existing three-party, four-setting full-correlation space, the first
negacyclic coefficient is the sum of four disjoint two-setting Mermin forms.
Its maximizers therefore lie in a strictly larger proper exposed face.
The two scaled projected coordinates are the signed convolution coefficients
`(d₀,d₁-d₃)`. -/

@[expose] public section
noncomputable section

open Set Lemmata.SymmetricBellCrossPolytope
open scoped BigOperators
namespace Lemmata.BellFollowup.Facets

abbrev V := Tensor 3 4
abbrev P := localPolytope 3 4

/-- Evaluation of a full correlation tensor at the indicated settings. -/
def entry (i j k : Fin 4) : V →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 3 → Fin 4 => ℝ) ![i,j,k]

@[simp] theorem entry_apply (i j k : Fin 4) (v : V) :
    entry i j k v = v ![i,j,k] := rfl

/-- The four-term, two-setting Mermin form. -/
def mermin (i i' j j' k k' : Fin 4) : V →L[ℝ] ℝ :=
  entry i j k - entry i j' k' - entry i' j k' - entry i' j' k

def block000 := mermin 0 2 0 2 0 2
def block011 := mermin 2 0 3 1 3 1
def block101 := mermin 3 1 2 0 3 1
def block110 := mermin 3 1 3 1 2 0

/-- Coefficient of X⁰ in ABC modulo X⁴+1, extended linearly to tensors. -/
def d0 : V →L[ℝ] ℝ := block000 + block011 + block101 + block110

private lemma mermin_numbers (A A' B B' C C' : ℝ)
    (a : A = 1 ∨ A = -1) (a' : A' = 1 ∨ A' = -1)
    (b : B = 1 ∨ B = -1) (b' : B' = 1 ∨ B' = -1)
    (c : C = 1 ∨ C = -1) (c' : C' = 1 ∨ C' = -1) :
    A*B*C - A*B'*C' - A'*B*C' - A'*B'*C ≤ 2 := by
  rcases a with rfl | rfl <;> rcases a' with rfl | rfl <;>
    rcases b with rfl | rfl <;> rcases b' with rfl | rfl <;>
    rcases c with rfl | rfl <;> rcases c' with rfl | rfl <;> norm_num

private lemma mermin_le_atom (i i' j j' k k' : Fin 4) (v : V)
    (hv : v ∈ strategySet 3 4) : mermin i i' j j' k k' v ≤ 2 := by
  obtain ⟨a, ha, h⟩ := hv
  have coord (x y z : Fin 4) : v ![x,y,z] = a 0 x * a 1 y * a 2 z := by
    rw [h]
    simp [Fin.prod_univ_succ, mul_assoc]
  simpa only [mermin, sub_apply, entry_apply, coord] using
    mermin_numbers _ _ _ _ _ _ (ha 0 i) (ha 0 i') (ha 1 j) (ha 1 j') (ha 2 k) (ha 2 k')

/-- Every Mermin block is bounded by two on the full real local polytope. -/
theorem mermin_le (i i' j j' k k' : Fin 4) (v : V) (hv : v ∈ P) :
    mermin i i' j j' k k' v ≤ 2 := by
  let L := mermin i i' j j' k k'
  have incl : strategySet 3 4 ⊆ {w | L w ≤ 2} :=
    fun w hw => mermin_le_atom i i' j j' k k' w hw
  have hc : Convex ℝ {w | L w ≤ 2} := by
    intro x hx y hy a b ha hb hab
    change L (a • x + b • y) ≤ 2
    change L x ≤ 2 at hx
    change L y ≤ 2 at hy
    simp only [map_add, map_smul, smul_eq_mul]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hx), mul_nonneg hb (sub_nonneg.mpr hy)]
  exact convexHull_min incl hc hv

theorem block_bounds {v : V} (h : v ∈ P) :
    block000 v ≤ 2 ∧ block011 v ≤ 2 ∧ block101 v ≤ 2 ∧ block110 v ≤ 2 :=
  ⟨mermin_le _ _ _ _ _ _ _ h, mermin_le _ _ _ _ _ _ _ h,
    mermin_le _ _ _ _ _ _ _ h, mermin_le _ _ _ _ _ _ _ h⟩

theorem d0_le {v : V} (h : v ∈ P) : d0 v ≤ 8 := by
  obtain ⟨a,b,c,d⟩ := block_bounds h
  simp only [d0, add_apply]
  linarith

theorem all_blocks_tight {v : V} (h : v ∈ P) (h0 : d0 v = 8) :
    block000 v = 2 ∧ block011 v = 2 ∧ block101 v = 2 ∧ block110 v = 2 := by
  obtain ⟨a,b,c,d⟩ := block_bounds h
  simp only [d0, add_apply] at h0
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

def signValue (b : Bool) : ℝ := if b then 1 else -1

/-- An actual full deterministic tensor in the existing model. -/
def atom (a b c : Fin 4 → Bool) : V :=
  WithLp.toLp 2 (fun x : Fin 3 → Fin 4 => signValue (a (x 0)) * signValue (b (x 1)) * signValue (c (x 2)))

theorem atom_mem (a b c : Fin 4 → Bool) : atom a b c ∈ P := by
  apply subset_convexHull ℝ (strategySet 3 4)
  refine ⟨![fun i => signValue (a i), fun i => signValue (b i), fun i => signValue (c i)], ?_, ?_⟩
  · intro n i
    have hs (t : Bool) : signValue t = 1 ∨ signValue t = -1 := by cases t <;> simp [signValue]
    fin_cases n <;> simpa using hs _
  · intro x
    simp [atom, Fin.prod_univ_succ, mul_assoc]

def positive := atom ![true,true,true,true] ![true,true,true,true] ![false,false,false,true]
def intermediate := atom ![true,true,true,true] ![true,true,true,true] ![false,true,false,true]
def outside := atom ![true,true,true,true] ![true,true,true,true] ![true,true,true,true]

private theorem witness_scores : d0 positive = 8 ∧ block000 intermediate = 2 ∧
    d0 intermediate = 0 ∧ block000 outside = -2 := by
  norm_num [positive, intermediate, outside, d0, block000, block011, block101, block110,
    mermin, atom, signValue]

/-- The full-polytope contact set of the lifted inequality. -/
def liftedEdge : Set V := {v ∈ P | d0 v = 8}

/-- A second exposed face that strictly contains the lift. -/
def intermediateFace : Set V := {v ∈ P | block000 v = 2}

private theorem exposed_contact (L : V →L[ℝ] ℝ) (b : ℝ) (bound : ∀ v ∈ P, L v ≤ b)
    (w : V) (hw : w ∈ P) (eq : L w = b) : IsExposed ℝ P {v ∈ P | L v = b} := by
  intro _
  refine ⟨L, ?_⟩
  ext v
  constructor
  · rintro ⟨h, hv⟩
    exact ⟨h, fun y hy => (bound y hy).trans_eq hv.symm⟩
  · rintro ⟨h, hv⟩
    have low := hv w hw
    rw [eq] at low
    exact ⟨h, le_antisymm (bound v h) low⟩

/-- The lifted edge is an exposed face strictly inside another proper exposed
face. Thus it is not a facet of the full local polytope. -/
theorem full_exposed_face_chain : IsExposed ℝ P liftedEdge ∧
    IsExposed ℝ P intermediateFace ∧ liftedEdge ⊂ intermediateFace ∧ intermediateFace ⊂ P := by
  obtain ⟨hp, hi, hz, ho⟩ := witness_scores
  refine ⟨exposed_contact d0 8 (fun _ => d0_le) positive (atom_mem _ _ _) hp,
    exposed_contact block000 2 (fun _ h => (block_bounds h).1) intermediate (atom_mem _ _ _) hi,
    lt_of_le_of_ne (fun _ h => ⟨h.1, (all_blocks_tight h.1 h.2).1⟩) ?_,
    lt_of_le_of_ne (fun _ h => h.1) ?_⟩
  · intro e
    have h : intermediate ∈ intermediateFace := ⟨atom_mem _ _ _, hi⟩
    rw [← e] at h
    have he : d0 intermediate = 8 := h.2
    linarith
  · intro e
    have h : outside ∈ P := atom_mem _ _ _
    rw [← e] at h
    have he : block000 outside = 2 := h.2
    linarith

end Lemmata.BellFollowup.Facets
