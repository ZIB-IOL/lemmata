module

public import Lemmata.PlanarSteinerXC.Objects
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Cut–cycle duality for flag systems

A *flag system* consists of flags with three fixed-point-free involutions `τ₀, τ₁, τ₂` and maps to
"vertices", "edges" and "faces" such that `τᵢ` changes exactly the `i`-th component. The *flag
graph* `Γ` joins every flag to its three images; it is cubic. The vertices, edges and faces are
the vertices of the barycentric subdivision `Q`, the flags are its triangles, and the edges of `Γ`
are dual to the edges of `Q`.

If `Γ` is connected and Euler's formula `|Q₀| - |Q₁| + |Q₂| = 2` holds (in the form
`2 (|Q₀| + |Q₁| + |Q₂|) = |Φ| + 4`), then every even edge set of `Γ` is the cut of a
`2`-colouring of `Q` (`even_eq_cut`). This is the only place where planarity is used.
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

open SimpleGraph

/-- A flag system. -/
structure FlagSystem (Φ Q0 Q1 Q2 : Type*) where
  vtx : Φ → Q0
  edg : Φ → Q1
  fac : Φ → Q2
  τ0 : Φ → Φ
  τ1 : Φ → Φ
  τ2 : Φ → Φ
  τ0_inv : ∀ φ, τ0 (τ0 φ) = φ
  τ1_inv : ∀ φ, τ1 (τ1 φ) = φ
  τ2_inv : ∀ φ, τ2 (τ2 φ) = φ
  vtx_τ0 : ∀ φ, vtx (τ0 φ) ≠ vtx φ
  edg_τ0 : ∀ φ, edg (τ0 φ) = edg φ
  fac_τ0 : ∀ φ, fac (τ0 φ) = fac φ
  vtx_τ1 : ∀ φ, vtx (τ1 φ) = vtx φ
  edg_τ1 : ∀ φ, edg (τ1 φ) ≠ edg φ
  fac_τ1 : ∀ φ, fac (τ1 φ) = fac φ
  vtx_τ2 : ∀ φ, vtx (τ2 φ) = vtx φ
  edg_τ2 : ∀ φ, edg (τ2 φ) = edg φ
  fac_τ2 : ∀ φ, fac (τ2 φ) ≠ fac φ
  vtx_surj : Function.Surjective vtx
  edg_surj : Function.Surjective edg
  fac_surj : Function.Surjective fac

namespace FlagSystem

variable {Φ Q0 Q1 Q2 : Type*} (F : FlagSystem Φ Q0 Q1 Q2)

/-- The flag graph. -/
def graph : SimpleGraph Φ :=
  SimpleGraph.fromRel fun φ ψ => ψ = F.τ0 φ ∨ ψ = F.τ1 φ ∨ ψ = F.τ2 φ

theorem τ0_ne (φ : Φ) : F.τ0 φ ≠ φ := fun h => F.vtx_τ0 φ (by rw [h])
theorem τ1_ne (φ : Φ) : F.τ1 φ ≠ φ := fun h => F.edg_τ1 φ (by rw [h])
theorem τ2_ne (φ : Φ) : F.τ2 φ ≠ φ := fun h => F.fac_τ2 φ (by rw [h])
theorem τ0_ne_τ1 (φ : Φ) : F.τ0 φ ≠ F.τ1 φ := fun h => F.vtx_τ0 φ (by rw [h, F.vtx_τ1])
theorem τ0_ne_τ2 (φ : Φ) : F.τ0 φ ≠ F.τ2 φ := fun h => F.vtx_τ0 φ (by rw [h, F.vtx_τ2])
theorem τ1_ne_τ2 (φ : Φ) : F.τ1 φ ≠ F.τ2 φ := fun h => F.edg_τ1 φ (by rw [h, F.edg_τ2])

theorem graph_adj {φ ψ : Φ} : F.graph.Adj φ ψ ↔ ψ = F.τ0 φ ∨ ψ = F.τ1 φ ∨ ψ = F.τ2 φ := by
  rw [graph, fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · rcases h with h | h | h
      · left; rw [h, F.τ0_inv]
      · right; left; rw [h, F.τ1_inv]
      · right; right; rw [h, F.τ2_inv]
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl
    rcases h with h | h | h
    · exact F.τ0_ne φ h.symm
    · exact F.τ1_ne φ h.symm
    · exact F.τ2_ne φ h.symm

theorem adj_τ0 (φ : Φ) : F.graph.Adj φ (F.τ0 φ) := F.graph_adj.mpr (Or.inl rfl)
theorem adj_τ1 (φ : Φ) : F.graph.Adj φ (F.τ1 φ) := F.graph_adj.mpr (Or.inr (Or.inl rfl))
theorem adj_τ2 (φ : Φ) : F.graph.Adj φ (F.τ2 φ) := F.graph_adj.mpr (Or.inr (Or.inr rfl))

variable [DecidableEq Q0] [DecidableEq Q1] [DecidableEq Q2]

/-- The three elements of `Q` of a flag (the corners of its triangle). -/
def elts (φ : Φ) : Finset (Q0 ⊕ Q1 ⊕ Q2) :=
  {.inl (F.vtx φ), .inr (.inl (F.edg φ)), .inr (.inr (F.fac φ))}

/-- The elements shared by the two ends of a pair of flags. -/
def shared : Sym2 Φ → Finset (Q0 ⊕ Q1 ⊕ Q2) :=
  Sym2.lift ⟨fun φ ψ => F.elts φ ∩ F.elts ψ, fun _ _ => Finset.inter_comm _ _⟩

theorem shared_mk (φ ψ : Φ) : F.shared s(φ, ψ) = F.elts φ ∩ F.elts ψ := rfl

theorem shared_τ0 (φ : Φ) :
    F.shared s(φ, F.τ0 φ) = {.inr (.inl (F.edg φ)), .inr (.inr (F.fac φ))} := by
  rw [shared_mk]; ext q
  simp only [elts, F.edg_τ0, F.fac_τ0, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  have := F.vtx_τ0 φ
  constructor
  · rintro ⟨h1 | h1 | h1, h2 | h2 | h2⟩ <;> subst h1 <;> simp_all
  · rintro (rfl | rfl) <;> simp

theorem shared_τ1 (φ : Φ) :
    F.shared s(φ, F.τ1 φ) = {.inl (F.vtx φ), .inr (.inr (F.fac φ))} := by
  rw [shared_mk]; ext q
  simp only [elts, F.vtx_τ1, F.fac_τ1, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  have := F.edg_τ1 φ
  constructor
  · rintro ⟨h1 | h1 | h1, h2 | h2 | h2⟩ <;> subst h1 <;> simp_all
  · rintro (rfl | rfl) <;> simp

theorem shared_τ2 (φ : Φ) :
    F.shared s(φ, F.τ2 φ) = {.inl (F.vtx φ), .inr (.inl (F.edg φ))} := by
  rw [shared_mk]; ext q
  simp only [elts, F.vtx_τ2, F.edg_τ2, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  have := F.fac_τ2 φ
  constructor
  · rintro ⟨h1 | h1 | h1, h2 | h2 | h2⟩ <;> subst h1 <;> simp_all
  · rintro (rfl | rfl) <;> simp

/-- The value of a colouring of `Q` on a pair of flags: the sum over the shared elements. -/
def cutVal (x : (Q0 ⊕ Q1 ⊕ Q2) → ZMod 2) (ε : Sym2 Φ) : ZMod 2 := ∑ q ∈ F.shared ε, x q

theorem cutVal_τ0 (x : (Q0 ⊕ Q1 ⊕ Q2) → ZMod 2) (φ : Φ) :
    F.cutVal x s(φ, F.τ0 φ) = x (.inr (.inl (F.edg φ))) + x (.inr (.inr (F.fac φ))) := by
  rw [cutVal, shared_τ0, Finset.sum_pair (by simp)]

theorem cutVal_τ1 (x : (Q0 ⊕ Q1 ⊕ Q2) → ZMod 2) (φ : Φ) :
    F.cutVal x s(φ, F.τ1 φ) = x (.inl (F.vtx φ)) + x (.inr (.inr (F.fac φ))) := by
  rw [cutVal, shared_τ1, Finset.sum_pair (by simp)]

theorem cutVal_τ2 (x : (Q0 ⊕ Q1 ⊕ Q2) → ZMod 2) (φ : Φ) :
    F.cutVal x s(φ, F.τ2 φ) = x (.inl (F.vtx φ)) + x (.inr (.inl (F.edg φ))) := by
  rw [cutVal, shared_τ2, Finset.sum_pair (by simp)]

/-- Every edge of the flag graph is of one of the three types at either end. -/
theorem edge_cases {φ ψ : Φ} (h : F.graph.Adj φ ψ) :
    ψ = F.τ0 φ ∨ ψ = F.τ1 φ ∨ ψ = F.τ2 φ := F.graph_adj.mp h

section Fintype

variable [Fintype Φ] [DecidableEq Φ]

noncomputable instance instDecRelGraph : DecidableRel F.graph.Adj := Classical.decRel _

/-- The edges of `Γ` at a flag. -/
noncomputable def inc (φ : Φ) : Finset F.graph.edgeSet :=
  Finset.univ.filter fun ε => φ ∈ (ε : Sym2 Φ)

/-- The three involutions, indexed by `Fin 3`. -/
def tau (i : Fin 3) (φ : Φ) : Φ :=
  match i with
  | 0 => F.τ0 φ
  | 1 => F.τ1 φ
  | 2 => F.τ2 φ

theorem adj_tau (φ : Φ) (i : Fin 3) : F.graph.Adj φ (F.tau i φ) := by
  fin_cases i
  · exact F.adj_τ0 φ
  · exact F.adj_τ1 φ
  · exact F.adj_τ2 φ

theorem tau_index_injective (φ : Φ) : Function.Injective (fun i => F.tau i φ) := by
  intro i j h
  have h01 := F.τ0_ne_τ1 φ
  have h02 := F.τ0_ne_τ2 φ
  have h12 := F.τ1_ne_τ2 φ
  fin_cases i <;> fin_cases j <;> simp only [tau] at h <;> first | rfl | simp_all [eq_comm]

/-- The three edges at a flag. -/
def edgeAt (φ : Φ) (i : Fin 3) : F.graph.edgeSet := ⟨s(φ, F.tau i φ), F.adj_tau φ i⟩

theorem edgeAt_injective (φ : Φ) : Function.Injective (F.edgeAt φ) := by
  intro i j h
  have h' : s(φ, F.tau i φ) = s(φ, F.tau j φ) := congrArg Subtype.val h
  exact F.tau_index_injective φ (Sym2.congr_right.mp h')

theorem inc_eq (φ : Φ) : F.inc φ = Finset.univ.image (F.edgeAt φ) := by
  ext ⟨ε, hε⟩
  simp only [inc, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hφ
    obtain ⟨ψ, rfl⟩ := Sym2.mem_iff_exists.mp hφ
    have hadj : F.graph.Adj φ ψ := F.graph.mem_edgeSet.mp hε
    rcases F.edge_cases hadj with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨i, hi⟩
    have : (F.edgeAt φ i : Sym2 Φ) = ε := congrArg Subtype.val hi
    rw [← this]
    exact Sym2.mem_mk_left _ _

/-- Sums over the edges at a flag. -/
theorem sum_inc {M : Type*} [AddCommMonoid M] (φ : Φ) (g : F.graph.edgeSet → M) :
    ∑ ε ∈ F.inc φ, g ε =
      g (F.edgeAt φ 0) + g (F.edgeAt φ 1) + g (F.edgeAt φ 2) := by
  rw [F.inc_eq, Finset.sum_image (fun i _ j _ h => F.edgeAt_injective φ h), Fin.sum_univ_three]

theorem card_inc (φ : Φ) : (F.inc φ).card = 3 := by
  rw [F.inc_eq, Finset.card_image_of_injective _ (F.edgeAt_injective φ), Finset.card_univ,
    Fintype.card_fin]

/-- `2 |E(Γ)| = 3 |Φ|`. -/
theorem two_mul_card_edges : 2 * Fintype.card F.graph.edgeSet = 3 * Fintype.card Φ := by
  classical
  have h := F.graph.sum_degrees_eq_twice_card_edges
  have hdeg : ∀ φ, F.graph.degree φ = 3 := by
    intro φ
    rw [← card_incidenceFinset_eq_degree, ← F.card_inc φ]
    rw [← Finset.card_map (Function.Embedding.subtype _)]
    congr 1
    ext ε
    simp only [mem_incidenceFinset, inc, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
      true_and, Function.Embedding.subtype_apply]
    constructor
    · intro hε
      exact ⟨⟨ε, hε.1⟩, hε.2, rfl⟩
    · rintro ⟨⟨e, he⟩, hφ, rfl⟩
      exact ⟨he, hφ⟩
  simp only [hdeg, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  rw [edgeFinset_card] at h
  lia

/-! ### The linear maps -/

/-- An edge set of `Γ` is even if every flag has an even number of its edges. -/
def IsEven (z : F.graph.edgeSet → ZMod 2) : Prop := ∀ φ, ∑ ε ∈ F.inc φ, z ε = 0

/-- The cut of a colouring of `Q`. -/
def cut (x : (Q0 ⊕ Q1 ⊕ Q2) → ZMod 2) : F.graph.edgeSet → ZMod 2 := fun ε => F.cutVal x ε

theorem cut_edgeAt (x : (Q0 ⊕ Q1 ⊕ Q2) → ZMod 2) (φ : Φ) :
    F.cut x (F.edgeAt φ 0) = x (.inr (.inl (F.edg φ))) + x (.inr (.inr (F.fac φ))) ∧
    F.cut x (F.edgeAt φ 1) = x (.inl (F.vtx φ)) + x (.inr (.inr (F.fac φ))) ∧
    F.cut x (F.edgeAt φ 2) = x (.inl (F.vtx φ)) + x (.inr (.inl (F.edg φ))) :=
  ⟨F.cutVal_τ0 x φ, F.cutVal_τ1 x φ, F.cutVal_τ2 x φ⟩

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

/-- Cuts are even. -/
theorem cut_isEven (x : (Q0 ⊕ Q1 ⊕ Q2) → ZMod 2) : F.IsEven (F.cut x) := by
  intro φ
  rw [F.sum_inc]
  obtain ⟨h0, h1, h2⟩ := F.cut_edgeAt x φ
  rw [h0, h1, h2]
  have h2' : (2 : ZMod 2) = 0 := by decide
  calc _ = 2 * (x (.inl (F.vtx φ)) + x (.inr (.inl (F.edg φ))) + x (.inr (.inr (F.fac φ)))) := by
        ring
    _ = 0 := by rw [h2', zero_mul]

end Fintype

/-! ### Linear algebra over `ZMod 2` -/

section Linear

open Matrix

variable [Fintype Φ] [DecidableEq Φ]

/-- A function constant along the edges of a connected graph is constant. -/
theorem const_of_connected {α : Type*} {G : SimpleGraph Φ} (hG : G.Connected) (f : Φ → α)
    (h : ∀ a b, G.Adj a b → f a = f b) (a b : Φ) : f a = f b := by
  obtain ⟨p⟩ := hG.preconnected a b
  induction p with
  | nil => rfl
  | cons hab _ ih => exact (h _ _ hab).trans ih

theorem zmod2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  rw [eq_neg_of_add_eq_zero_left h, ZMod.neg_eq_self_mod_two]

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

theorem zmod2_eq_of_ne_of_ne {a b c : ZMod 2} (h1 : a ≠ b) (h2 : c ≠ b) : a = c := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    rcases zmod2_cases c with rfl | rfl <;> simp_all

theorem zmod2_add_eq_one_of_ne {a b : ZMod 2} (h : a ≠ b) : a + b = 1 := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> simp_all

theorem zmod2_add_eq_zero_iff {a b : ZMod 2} : a + b = 0 ↔ a = b :=
  ⟨zmod2_eq_of_add_eq_zero, fun h => h ▸ zmod2_add_self a⟩

/-- Colourings with zero cut are constant (the barycentric subdivision is connected). -/
theorem cut_eq_zero_iff (hconn : F.graph.Connected) (x : Q0 ⊕ Q1 ⊕ Q2 → ZMod 2) :
    F.cut x = 0 ↔ ∃ c, x = fun _ => c := by
  constructor
  · intro h
    have h3 : ∀ φ, x (.inl (F.vtx φ)) = x (.inr (.inl (F.edg φ))) ∧
        x (.inl (F.vtx φ)) = x (.inr (.inr (F.fac φ))) := by
      intro φ
      obtain ⟨h0, h1, h2⟩ := F.cut_edgeAt x φ
      have e1 := congrFun h (F.edgeAt φ 1)
      have e2 := congrFun h (F.edgeAt φ 2)
      rw [h1] at e1; rw [h2] at e2
      exact ⟨zmod2_eq_of_add_eq_zero e2, zmod2_eq_of_add_eq_zero e1⟩
    let c : Φ → ZMod 2 := fun φ => x (.inl (F.vtx φ))
    have hc : ∀ a b, F.graph.Adj a b → c a = c b := by
      intro a b hab
      rcases F.edge_cases hab with rfl | rfl | rfl
      · show x (.inl (F.vtx a)) = x (.inl (F.vtx (F.τ0 a)))
        rw [(h3 a).1, (h3 (F.τ0 a)).1, F.edg_τ0]
      · show x (.inl (F.vtx a)) = x (.inl (F.vtx (F.τ1 a)))
        rw [F.vtx_τ1]
      · show x (.inl (F.vtx a)) = x (.inl (F.vtx (F.τ2 a)))
        rw [F.vtx_τ2]
    obtain ⟨φ₀⟩ := hconn.nonempty
    refine ⟨c φ₀, funext fun q => ?_⟩
    rcases q with a | b | b
    · obtain ⟨φ, rfl⟩ := F.vtx_surj a
      exact const_of_connected hconn c hc φ φ₀
    · obtain ⟨φ, rfl⟩ := F.edg_surj b
      rw [← (h3 φ).1]
      exact const_of_connected hconn c hc φ φ₀
    · obtain ⟨φ, rfl⟩ := F.fac_surj b
      rw [← (h3 φ).2]
      exact const_of_connected hconn c hc φ φ₀
  · rintro ⟨c, rfl⟩
    funext ⟨ε, hε⟩
    induction ε using Sym2.ind with
    | h a b =>
      have hadj : F.graph.Adj a b := F.graph.mem_edgeSet.mp hε
      show F.cutVal (fun _ => c) s(a, b) = 0
      rcases F.edge_cases hadj with rfl | rfl | rfl
      · rw [F.cutVal_τ0]; exact zmod2_add_self c
      · rw [F.cutVal_τ1]; exact zmod2_add_self c
      · rw [F.cutVal_τ2]; exact zmod2_add_self c

variable [Fintype Q0] [Fintype Q1] [Fintype Q2]

/-- The cut map as a matrix. -/
noncomputable def cutMat : Matrix F.graph.edgeSet (Q0 ⊕ Q1 ⊕ Q2) (ZMod 2) :=
  fun ε q => if q ∈ F.shared ε then 1 else 0

/-- The edge–flag incidence matrix. -/
noncomputable def incMat : Matrix F.graph.edgeSet Φ (ZMod 2) :=
  fun ε φ => if φ ∈ (ε : Sym2 Φ) then 1 else 0

theorem cutMat_mulVec (x : Q0 ⊕ Q1 ⊕ Q2 → ZMod 2) : F.cutMat.mulVec x = F.cut x := by
  funext ε
  simp only [Matrix.mulVec, dotProduct, cutMat, ite_mul, one_mul, zero_mul, cut, cutVal]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem incMat_transpose_mulVec (z : F.graph.edgeSet → ZMod 2) :
    F.incMatᵀ.mulVec z = fun φ => ∑ ε ∈ F.inc φ, z ε := by
  funext φ
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, incMat, ite_mul, one_mul,
    zero_mul, inc]
  rw [Finset.sum_filter]

theorem incMat_mulVec (y : Φ → ZMod 2) (a b : Φ) (hab : F.graph.Adj a b) :
    F.incMat.mulVec y ⟨s(a, b), hab⟩ = y a + y b := by
  simp only [Matrix.mulVec, dotProduct, incMat, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  have : Finset.univ.filter (fun φ => φ ∈ (s(a, b) : Sym2 Φ)) = {a, b} := by
    ext φ; simp [Sym2.mem_iff]
  rw [this, Finset.sum_pair hab.ne]

theorem finrank_ker_cut (hconn : F.graph.Connected) :
    Module.finrank (ZMod 2) (LinearMap.ker F.cutMat.mulVecLin) = 1 := by
  have hker : LinearMap.ker F.cutMat.mulVecLin =
      Submodule.span (ZMod 2) {fun _ => (1 : ZMod 2)} := by
    ext x
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, cutMat_mulVec, F.cut_eq_zero_iff hconn,
      Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩; exact ⟨c, by funext q; simp only [Pi.smul_apply, smul_eq_mul, mul_one]⟩
    · rintro ⟨c, rfl⟩; exact ⟨c, by funext q; simp only [Pi.smul_apply, smul_eq_mul, mul_one]⟩
  rw [hker]
  apply finrank_span_singleton
  obtain ⟨φ⟩ := hconn.nonempty
  intro h
  exact one_ne_zero (congrFun h (.inl (F.vtx φ)))

theorem finrank_ker_inc (hconn : F.graph.Connected) :
    Module.finrank (ZMod 2) (LinearMap.ker F.incMat.mulVecLin) = 1 := by
  have hker : LinearMap.ker F.incMat.mulVecLin =
      Submodule.span (ZMod 2) {fun _ => (1 : ZMod 2)} := by
    ext y
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Submodule.mem_span_singleton]
    constructor
    · intro h
      obtain ⟨φ₀⟩ := hconn.nonempty
      refine ⟨y φ₀, funext fun φ => ?_⟩
      have hc : ∀ a b, F.graph.Adj a b → y a = y b := by
        intro a b hab
        have := congrFun h ⟨s(a, b), hab⟩
        rw [F.incMat_mulVec y a b hab] at this
        exact zmod2_eq_of_add_eq_zero this
      simp only [Pi.smul_apply, smul_eq_mul, mul_one]
      exact const_of_connected hconn y hc φ₀ φ
    · rintro ⟨c, rfl⟩
      funext ⟨ε, hε⟩
      induction ε using Sym2.ind with
      | h a b =>
        rw [F.incMat_mulVec _ a b hε]
        exact zmod2_add_self _
  rw [hker]
  apply finrank_span_singleton
  obtain ⟨φ⟩ := hconn.nonempty
  intro h
  exact one_ne_zero (congrFun h φ)

/-- **Cut–cycle duality.** If the flag graph is connected and Euler's formula holds, every even
edge set of the flag graph is the cut of a colouring of the barycentric subdivision. -/
theorem even_eq_cut (hconn : F.graph.Connected)
    (heuler : 2 * (Fintype.card Q0 + Fintype.card Q1 + Fintype.card Q2) = Fintype.card Φ + 4)
    (z : F.graph.edgeSet → ZMod 2) (hz : F.IsEven z) : ∃ x, z = F.cut x := by
  classical
  set δ := F.cutMat.mulVecLin
  set dT := F.incMatᵀ.mulVecLin
  have hle : LinearMap.range δ ≤ LinearMap.ker dT := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, cutMat_mulVec,
      incMat_transpose_mulVec]
    funext φ
    exact F.cut_isEven x φ
  have hδ := LinearMap.finrank_range_add_finrank_ker δ
  rw [F.finrank_ker_cut hconn, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
    Fintype.card_sum] at hδ
  have hdT := LinearMap.finrank_range_add_finrank_ker dT
  rw [Module.finrank_fintype_fun_eq_card] at hdT
  have hd := LinearMap.finrank_range_add_finrank_ker F.incMat.mulVecLin
  rw [F.finrank_ker_inc hconn, Module.finrank_fintype_fun_eq_card] at hd
  have hrank : Module.finrank (ZMod 2) (LinearMap.range dT) =
      Module.finrank (ZMod 2) (LinearMap.range F.incMat.mulVecLin) := by
    have := Matrix.rank_transpose F.incMat
    simpa only [Matrix.rank] using this
  have hE := F.two_mul_card_edges
  have heq : LinearMap.range δ = LinearMap.ker dT := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    lia
  have hzker : z ∈ LinearMap.ker dT := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, incMat_transpose_mulVec]
    funext φ
    exact hz φ
  rw [← heq] at hzker
  obtain ⟨x, hx⟩ := hzker
  refine ⟨x, ?_⟩
  rw [← hx, Matrix.mulVecLin_apply, cutMat_mulVec]

end Linear

/-! ### Minimal cuts and connected colour classes -/

section MinimalCuts

variable [Fintype Φ] [DecidableEq Φ] [Fintype Q0] [Fintype Q1] [Fintype Q2]

/-- Two elements of `Q` lie on a common flag. -/
def QAdj (a b : Q0 ⊕ Q1 ⊕ Q2) : Prop := ∃ φ, a ∈ F.elts φ ∧ b ∈ F.elts φ

/-- The colour classes of `x` are connected: elements of the same colour are joined by a chain of
elements of that colour, consecutive ones lying on a common flag. -/
def MonoConnected (x : Q0 ⊕ Q1 ⊕ Q2 → ZMod 2) : Prop :=
  ∀ a b, x a = x b → Relation.ReflTransGen (fun p q => F.QAdj p q ∧ x p = x q) a b

theorem cut_add (x y : Q0 ⊕ Q1 ⊕ Q2 → ZMod 2) : F.cut (x + y) = F.cut x + F.cut y := by
  funext ε
  simp [cut, cutVal, Finset.sum_add_distrib]

/-- Every edge of the flag graph is dual to a pair of elements on a common flag. -/
theorem edge_shared (ε : F.graph.edgeSet) :
    ∃ φ p q, F.shared ε = {p, q} ∧ p ≠ q ∧ p ∈ F.elts φ ∧ q ∈ F.elts φ := by
  obtain ⟨ε, hε⟩ := ε
  induction ε using Sym2.ind with
  | h a b =>
    have hadj : F.graph.Adj a b := F.graph.mem_edgeSet.mp hε
    rcases F.edge_cases hadj with rfl | rfl | rfl
    · exact ⟨a, _, _, F.shared_τ0 a, by simp, by simp [elts], by simp [elts]⟩
    · exact ⟨a, _, _, F.shared_τ1 a, by simp, by simp [elts], by simp [elts]⟩
    · exact ⟨a, _, _, F.shared_τ2 a, by simp, by simp [elts], by simp [elts]⟩

theorem cut_affine (x : Q0 ⊕ Q1 ⊕ Q2 → ZMod 2) (c d : ZMod 2) :
    F.cut (fun r => c + d * x r) = fun ε => d * F.cut x ε := by
  funext ε
  obtain ⟨φ, p, q, hsh, hpq, -, -⟩ := F.edge_shared ε
  simp only [cut, cutVal, hsh, Finset.sum_pair hpq]
  have := zmod2_add_self c
  linear_combination this

/-- The edges of a flag between two of its corners. -/
theorem exists_edge_between {φ : Φ} {p q : Q0 ⊕ Q1 ⊕ Q2} (hp : p ∈ F.elts φ) (hq : q ∈ F.elts φ)
    (hpq : p ≠ q) : ∃ ε : F.graph.edgeSet, F.shared ε = {p, q} := by
  simp only [elts, Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  · exact absurd rfl hpq
  · exact ⟨F.edgeAt φ 2, F.shared_τ2 φ⟩
  · exact ⟨F.edgeAt φ 1, F.shared_τ1 φ⟩
  · exact ⟨F.edgeAt φ 2, (F.shared_τ2 φ).trans (Finset.pair_comm _ _)⟩
  · exact absurd rfl hpq
  · exact ⟨F.edgeAt φ 0, F.shared_τ0 φ⟩
  · exact ⟨F.edgeAt φ 1, (F.shared_τ1 φ).trans (Finset.pair_comm _ _)⟩
  · exact ⟨F.edgeAt φ 0, (F.shared_τ0 φ).trans (Finset.pair_comm _ _)⟩
  · exact absurd rfl hpq

/-- **Minimal cuts.** If both colour classes of `x` are connected, every even edge set inside the
cut of `x` is empty or the whole cut. -/
theorem even_sub_cut (hconn : F.graph.Connected)
    (heuler : 2 * (Fintype.card Q0 + Fintype.card Q1 + Fintype.card Q2) = Fintype.card Φ + 4)
    (x : Q0 ⊕ Q1 ⊕ Q2 → ZMod 2) (hx : F.MonoConnected x) (z : F.graph.edgeSet → ZMod 2)
    (hz : F.IsEven z) (hsub : ∀ ε, F.cut x ε = 0 → z ε = 0) : z = 0 ∨ z = F.cut x := by
  obtain ⟨y, rfl⟩ := F.even_eq_cut hconn heuler z hz
  -- `y` is constant along monochromatic steps
  have hstep : ∀ p q, F.QAdj p q → x p = x q → y p = y q := by
    rintro p q ⟨φ, hp, hq⟩ hxpq
    by_cases hpq : p = q
    · rw [hpq]
    obtain ⟨ε, hε⟩ := F.exists_edge_between hp hq hpq
    have h1 : F.cut x ε = 0 := by
      simp only [cut, cutVal, hε, Finset.sum_pair hpq, hxpq]; exact zmod2_add_self _
    have h2 := hsub ε h1
    simp only [cut, cutVal, hε, Finset.sum_pair hpq] at h2
    exact zmod2_eq_of_add_eq_zero h2
  have hcol : ∀ a b, x a = x b → y a = y b := by
    intro a b hab
    have h := hx a b hab
    clear hab
    induction h with
    | refl => rfl
    | tail _ hst ih => exact ih.trans (hstep _ _ hst.1 hst.2)
  by_cases hboth : ∃ p q, x p ≠ x q
  · obtain ⟨p, q, hpq⟩ := hboth
    have hy : y = fun r => y p + (y p + y q) * (x r + x p) := by
      funext r
      by_cases hr : x r = x p
      · rw [hr, zmod2_add_self, mul_zero, add_zero]; exact hcol r p hr
      · have hrq : x r = x q := zmod2_eq_of_ne_of_ne hr hpq.symm
        have hxr : x r + x p = 1 := zmod2_add_eq_one_of_ne hr
        rw [hxr, mul_one, ← add_assoc, zmod2_add_self, zero_add]
        exact hcol r q hrq
    have hcut : F.cut y = fun ε => (y p + y q) * F.cut x ε := by
      calc F.cut y = F.cut (fun r => (y p + (y p + y q) * x p) + (y p + y q) * x r) := by
            congr 1; funext r; rw [congrFun hy r]; ring
        _ = _ := F.cut_affine x _ _
    generalize hd : y p + y q = d at hcut
    rcases zmod2_cases d with rfl | rfl
    · left; rw [hcut]; funext ε; simp
    · right; rw [hcut]; funext ε; simp
  · push_neg at hboth
    left
    obtain ⟨p⟩ : Nonempty (Q0 ⊕ Q1 ⊕ Q2) := by
      obtain ⟨φ⟩ := hconn.nonempty
      exact ⟨.inl (F.vtx φ)⟩
    have hy : y = fun _ => y p := funext fun r => hcol r p (hboth r p)
    rw [hy]
    exact (F.cut_eq_zero_iff hconn _).mpr ⟨_, rfl⟩

/-- **Connected colour classes.** If the cut of `x` is nonzero and contains no nonempty proper even
edge set, then both colour classes of `x` are connected. -/
theorem monoConnected_of_minimal (hconn : F.graph.Connected) (x : Q0 ⊕ Q1 ⊕ Q2 → ZMod 2)
    (hne : F.cut x ≠ 0)
    (hmin : ∀ z, F.IsEven z → (∀ ε, F.cut x ε = 0 → z ε = 0) → z = 0 ∨ z = F.cut x) :
    F.MonoConnected x := by
  classical
  intro a b hab
  let R := fun p q => F.QAdj p q ∧ x p = x q
  let X1 : Set (Q0 ⊕ Q1 ⊕ Q2) := {q | Relation.ReflTransGen R a q}
  let y : Q0 ⊕ Q1 ⊕ Q2 → ZMod 2 := fun q => if q ∈ X1 then 1 else 0
  have hya : y a = 1 := by simp [y, X1, Relation.ReflTransGen.refl]
  have hcolX1 : ∀ q ∈ X1, x q = x a := by
    intro q hq
    induction hq with
    | refl => rfl
    | tail _ hst ih => exact hst.2.symm.trans ih
  have hsub : ∀ ε, F.cut x ε = 0 → F.cut y ε = 0 := by
    intro ε hε
    obtain ⟨φ, p, q, hsh, hpq, hp, hq⟩ := F.edge_shared ε
    simp only [cut, cutVal, hsh, Finset.sum_pair hpq] at hε ⊢
    have hxpq := zmod2_eq_of_add_eq_zero hε
    have hiff : p ∈ X1 ↔ q ∈ X1 := by
      constructor
      · intro h; exact Relation.ReflTransGen.tail h ⟨⟨φ, hp, hq⟩, hxpq⟩
      · intro h; exact Relation.ReflTransGen.tail h ⟨⟨φ, hq, hp⟩, hxpq.symm⟩
    simp only [y]
    by_cases h : p ∈ X1
    · rw [if_pos h, if_pos (hiff.mp h)]; exact zmod2_add_self 1
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]; simp
  rcases hmin (F.cut y) (F.cut_isEven y) hsub with h0 | h1
  · exfalso
    obtain ⟨c, hc⟩ := (F.cut_eq_zero_iff hconn y).mp h0
    have hc1 : c = 1 := by rw [← hya, hc]
    apply hne
    rw [F.cut_eq_zero_iff hconn]
    refine ⟨x a, funext fun q => ?_⟩
    have : q ∈ X1 := by
      by_contra hq
      have := congrFun hc q
      simp only [y, if_neg hq, hc1] at this
      exact zero_ne_one this
    exact hcolX1 q this
  · have h2 : F.cut (y + x) = 0 := by
      rw [F.cut_add, h1]; funext ε; exact zmod2_add_self _
    obtain ⟨c, hc⟩ := (F.cut_eq_zero_iff hconn _).mp h2
    have ha' := congrFun hc a
    have hb' := congrFun hc b
    simp only [Pi.add_apply] at ha' hb'
    have hyb : y b = 1 := by
      rw [hya, hab] at ha'
      have : y b + x b = 1 + x b := hb'.trans ha'.symm
      exact add_right_cancel this
    by_contra hb
    have : y b = 0 := if_neg hb
    rw [this] at hyb
    exact zero_ne_one hyb

end MinimalCuts

end FlagSystem

end Lemmata.PlanarSteinerXC
