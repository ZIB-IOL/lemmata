module

public import Lemmata.Centroid.Proof.Linear.FinsuppLeading
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Dimension.Finite

@[expose] public section

open scoped BigOperators Finset Matrix

noncomputable section

namespace Lemmata.Centroid.Linear

/-- A family with at most one point in each pairwise intersection loses at most one point per pair. -/
theorem sum_card_le_card_biUnion_add_choose {I X : Type*} [DecidableEq I] [DecidableEq X]
    (s : Finset I) (f : I → Finset X)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → #(f i ∩ f j) ≤ 1) :
    ∑ i ∈ s, #(f i) ≤ #(s.biUnion f) + (s.card).choose 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → #(f i ∩ f j) ≤ 1 := by
      intro i hi j hj hij
      exact h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hcross : #(f a ∩ s.biUnion f) ≤ s.card := by
      have heq : f a ∩ s.biUnion f = s.biUnion (fun i => f a ∩ f i) := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_biUnion]
        tauto
      rw [heq]
      calc
        _ ≤ ∑ i ∈ s, #(f a ∩ f i) := Finset.card_biUnion_le
        _ ≤ ∑ _i ∈ s, 1 := Finset.sum_le_sum fun i hi =>
          h a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi) (by
            intro heq
            exact ha (heq.symm ▸ hi))
        _ = s.card := by simp
    have hc := Finset.card_union_add_card_inter (f a) (s.biUnion f)
    have hn : (s.card + 1).choose 2 = s.card + (s.card).choose 2 := by
      simpa using Nat.choose_succ_succ s.card 1
    rw [Finset.sum_insert ha, Finset.biUnion_insert, Finset.card_insert_of_notMem ha, hn]
    have hh := ih hs
    omega

section MonomialShadows

variable {B σ : Type*} [DecidableEq B] [DecidableEq σ] [Fintype σ]

def variableShift (i : σ) (a : B × (σ →₀ ℕ)) : B × (σ →₀ ℕ) :=
  (a.1, a.2 + Finsupp.single i 1)

def monomialShadow (a : B × (σ →₀ ℕ)) : Finset (B × (σ →₀ ℕ)) :=
  Finset.univ.image fun i => variableShift i a

omit [DecidableEq B] [Fintype σ] in
theorem variableShift_variable_injective (a : B × (σ →₀ ℕ)) :
    Function.Injective (fun i => variableShift i a) := by
  intro i j h
  have he := add_left_cancel (congrArg Prod.snd h)
  by_contra hij
  have hval := congrFun (congrArg DFunLike.coe he) i
  simp [Ne.symm hij] at hval

theorem card_monomialShadow (a : B × (σ →₀ ℕ)) :
    (monomialShadow a).card = Fintype.card σ := by
  rw [monomialShadow, Finset.card_image_of_injective _ (variableShift_variable_injective a),
    Finset.card_univ]

theorem monomialShadow_inter_card_le_one {a b : B × (σ →₀ ℕ)} (hab : a ≠ b) :
    #(monomialShadow a ∩ monomialShadow b) ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  rw [Finset.mem_inter] at hp hq
  obtain ⟨i, _, hip⟩ := Finset.mem_image.mp hp.1
  obtain ⟨j, _, hjp⟩ := Finset.mem_image.mp hp.2
  obtain ⟨k, _, hkq⟩ := Finset.mem_image.mp hq.1
  obtain ⟨l, _, hlq⟩ := Finset.mem_image.mp hq.2
  have h₁ := hip.trans hjp.symm
  have h₂ := hkq.trans hlq.symm
  by_cases hik : i = k
  · exact hip.symm.trans (hik ▸ hkq)
  · have hji : j = i := by
      by_contra hji
      have hv₁ := congrArg (fun t => t.2 i) h₁
      have hv₂ := congrArg (fun t => t.2 i) h₂
      simp [variableShift, Finsupp.single_apply, hji, Ne.symm hik] at hv₁ hv₂
      omega
    have hfirst : a.1 = b.1 := by
      change (variableShift i a).1 = (variableShift j b).1
      exact congrArg Prod.fst h₁
    have hsecond : a.2 = b.2 := by
      have hh : a.2 + Finsupp.single i 1 = b.2 + Finsupp.single j 1 := congrArg Prod.snd h₁
      rw [hji] at hh
      exact add_right_cancel hh
    exact (hab (Prod.ext hfirst hsecond)).elim

theorem variable_shadow_card_bound (s : Finset (B × (σ →₀ ℕ))) :
    Fintype.card σ * s.card ≤ #(s.biUnion monomialShadow) + (s.card).choose 2 := by
  have h := sum_card_le_card_biUnion_add_choose s monomialShadow
    (fun _ _ _ _ hab => monomialShadow_inter_card_le_one hab)
  simpa [card_monomialShadow, Nat.mul_comm] using h

end MonomialShadows

section PolynomialExpansion

variable {B σ : Type*} [LinearOrder B] [DecidableEq σ] [Fintype σ]

@[instance_reducible] def polynomialIndexOrder (m : MonomialOrder σ) : LinearOrder (B × (σ →₀ ℕ)) :=
  LinearOrder.lift' (fun a : B × (σ →₀ ℕ) => (toLex (a.1, m.toSyn a.2) : B ×ₗ m.syn))
    (by
      intro a b h
      exact Prod.ext (congrArg (fun t => (ofLex t).1) h)
        (m.toSyn.injective (congrArg (fun t => (ofLex t).2) h)))

omit [DecidableEq σ] [Fintype σ] in
theorem variableShift_strictMono (m : MonomialOrder σ) (i : σ) :
    @StrictMono (B × (σ →₀ ℕ)) (B × (σ →₀ ℕ))
      (polynomialIndexOrder (B := B) m).toPartialOrder.toPreorder
      (polynomialIndexOrder (B := B) m).toPartialOrder.toPreorder (variableShift i) := by
  intro a b hab
  change (toLex (a.1, m.toSyn a.2) : B ×ₗ m.syn) < toLex (b.1, m.toSyn b.2) at hab
  change (toLex (a.1, m.toSyn (a.2 + Finsupp.single i 1)) : B ×ₗ m.syn) <
    toLex (b.1, m.toSyn (b.2 + Finsupp.single i 1))
  rw [Prod.Lex.lt_iff] at hab ⊢
  simp only [map_add] at hab ⊢
  rcases hab with h | ⟨h₁, h₂⟩
  · exact Or.inl h
  · exact Or.inr ⟨h₁, add_lt_add_left h₂ _⟩

variable {F : Type*} [Field F]

/-- Vector-valued polynomials in the coordinates of a basis indexed by `B`. -/
abbrev ModulePolynomial (F B σ : Type*) [Zero F] := (B × (σ →₀ ℕ)) →₀ F

def variableMultiplication (i : σ) : ModulePolynomial F B σ →ₗ[F] ModulePolynomial F B σ :=
  Finsupp.lmapDomain F F (variableShift i)

def variableExpansionMap (L : Submodule F (ModulePolynomial F B σ)) :
    (σ → L) →ₗ[F] ModulePolynomial F B σ :=
  ∑ i, (variableMultiplication i).comp (L.subtype.comp (LinearMap.proj i))

def variableExpansion (L : Submodule F (ModulePolynomial F B σ)) :
    Submodule F (ModulePolynomial F B σ) := LinearMap.range (variableExpansionMap L)

instance finiteDimensional_variableExpansion (L : Submodule F (ModulePolynomial F B σ))
    [FiniteDimensional F L] : FiniteDimensional F (variableExpansion L) := by
  unfold variableExpansion
  infer_instance

omit [LinearOrder B] in
theorem variableMultiplication_mem_expansion (L : Submodule F (ModulePolynomial F B σ))
    (i : σ) {v : ModulePolynomial F B σ} (hv : v ∈ L) :
    variableMultiplication i v ∈ variableExpansion L := by
  classical
  refine ⟨Pi.single i ⟨v, hv⟩, ?_⟩
  simp only [variableExpansionMap, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

omit [LinearOrder B] in
theorem shiftedSubspace_le_expansion (L : Submodule F (ModulePolynomial F B σ)) (i : σ) :
    L.map (variableMultiplication i) ≤ variableExpansion L := by
  rintro _ ⟨v, hv, rfl⟩
  exact variableMultiplication_mem_expansion L i hv

/-- Multiplication by the formal variables expands an `h`-dimensional polynomial space. -/
theorem variable_expansion_bound (m : MonomialOrder σ)
    (L : Submodule F (ModulePolynomial F B σ)) [FiniteDimensional F L]
    (h : ℕ) (hh : h ≤ Module.finrank F L) :
    Fintype.card σ * h ≤ Module.finrank F (variableExpansion L) + h.choose 2 := by
  classical
  let : LinearOrder (B × (σ →₀ ℕ)) := polynomialIndexOrder (B := B) m
  have hd : h ≤ (finsuppLeadingTerms L).card := by rwa [card_finsuppLeadingTerms]
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hd
  have hshadow : s.biUnion monomialShadow ⊆ finsuppLeadingTerms (variableExpansion L) := by
    intro b hb
    obtain ⟨a, ha, hb⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
    apply (mem_finsuppLeadingTerms _ _).mpr
    have hlead := (mem_finsuppLeadingTerms L a).mp (hs ha)
    exact (hlead.mapDomain (variableShift_strictMono (B := B) m i)).mono (shiftedSubspace_le_expansion L i)
  have hcount := variable_shadow_card_bound s
  have hrank : (s.biUnion monomialShadow).card ≤ Module.finrank F (variableExpansion L) :=
    (Finset.card_le_card hshadow).trans_eq (card_finsuppLeadingTerms _)
  rw [hcard] at hcount
  omega

theorem variable_expansion_bound_fin {n : ℕ}
    (L : Submodule F (ModulePolynomial F B (Fin n))) [FiniteDimensional F L]
    (h : ℕ) (hh : h ≤ Module.finrank F L) :
    n * h ≤ Module.finrank F (variableExpansion L) + h.choose 2 := by
  simpa using variable_expansion_bound (MonomialOrder.lex : MonomialOrder (Fin n)) L h hh

end PolynomialExpansion

theorem matrix_kernel_of_card_lt {R ι κ : Type*} [CommRing R] [Nontrivial R]
    [Fintype ι] [Fintype κ] (A : Matrix κ ι R) (h : Fintype.card κ < Fintype.card ι) :
    ∃ v : ι → R, v ≠ 0 ∧ A *ᵥ v = 0 := by
  classical
  have hn : ¬ LinearIndependent R (fun i j => A j i) := by
    intro hi
    have hc := hi.fintype_card_le_finrank
    rw [Module.finrank_pi] at hc
    omega
  obtain ⟨v, hv, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hn
  refine ⟨v, fun hz => hi (congrFun hz i), ?_⟩
  funext j
  have he := congrFun hv j
  simpa only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply, mul_comm] using he

end Lemmata.Centroid.Linear
