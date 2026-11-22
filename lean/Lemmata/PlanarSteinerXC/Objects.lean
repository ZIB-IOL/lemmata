module

public import Lemmata.PlanarSteinerXC.Polyhedral
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Data.Set.Card

/-!
# The polytopes and polyhedra

Edge sets of a graph `G` are represented by spanning subgraphs `K ≤ G`; the coordinates of all
edge polytopes are the edges of `G`.

* `Pmin G T`: convex hull of inclusion-minimal edge sets connecting `T` (minimal Steiner trees).
* `Pconn G T`: convex hull of edge sets whose support graph is connected and contains `T`.
* `Pup G T`: convex hull of edge sets with all of `T` in one component.
* `Dom G T = Pmin G T + ℝ^E_{≥ 0}`: the Steiner tree dominant.
* `HP G s t`: convex hull of Hamiltonian `s`-`t` paths.
* `VC J`, `minCoverFace J`: vertex cover polytope and the convex hull of minimum vertex covers.
* `COR L`: correlation polytope of a graph `L`, in the coordinates `V(L) ⊔ E(L)`.
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

open SimpleGraph

variable {V : Type*}

/-- `K` connects `T`: all vertices of `T` lie in one connected component of `K`. -/
def Connects (K : SimpleGraph V) (T : Set V) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, K.Reachable a b

/-- `K` is an inclusion-minimal edge set of `G` connecting `T` (a minimal Steiner tree). -/
def IsMinConnector (G : SimpleGraph V) (T : Set V) (K : SimpleGraph V) : Prop :=
  K ≤ G ∧ Connects K T ∧ ∀ K' ≤ K, Connects K' T → K' = K

/-- The support graph of `K` (edges of `K` and their endpoints) is connected and contains `T`. -/
def IsConnectedSupport (G : SimpleGraph V) (T : Set V) (K : SimpleGraph V) : Prop :=
  K ≤ G ∧ T ⊆ K.support ∧ ∀ u ∈ K.support, ∀ v ∈ K.support, K.Reachable u v

/-- The incidence vector of the edge set of `K`, in the edge coordinates of `G`. -/
noncomputable def edgeVec (G K : SimpleGraph V) : G.edgeSet → ℝ :=
  fun e => by classical exact if (e : Sym2 V) ∈ K.edgeSet then 1 else 0

/-- Convex hull of the inclusion-minimal edge sets connecting `T`. -/
noncomputable def Pmin (G : SimpleGraph V) (T : Set V) : Set (G.edgeSet → ℝ) :=
  convexHull ℝ (edgeVec G '' {K | IsMinConnector G T K})

/-- Convex hull of the edge sets with connected support graph containing `T`. -/
noncomputable def Pconn (G : SimpleGraph V) (T : Set V) : Set (G.edgeSet → ℝ) :=
  convexHull ℝ (edgeVec G '' {K | IsConnectedSupport G T K})

/-- Convex hull of the edge sets having all of `T` in one component. -/
noncomputable def Pup (G : SimpleGraph V) (T : Set V) : Set (G.edgeSet → ℝ) :=
  convexHull ℝ (edgeVec G '' {K | K ≤ G ∧ Connects K T})

/-- The Steiner tree dominant `Pmin G T + ℝ^E_{≥ 0}`. -/
def Dom (G : SimpleGraph V) (T : Set V) : Set (G.edgeSet → ℝ) :=
  {x | ∃ p ∈ Pmin G T, ∃ r : G.edgeSet → ℝ, 0 ≤ r ∧ x = p + r}

/-- The Hamiltonian `s`-`t` path polytope. -/
noncomputable def HP [DecidableEq V] (G : SimpleGraph V) (s t : V) : Set (G.edgeSet → ℝ) :=
  convexHull ℝ
    (edgeVec G '' {K | ∃ p : G.Walk s t, p.IsHamiltonian ∧ K = p.toSubgraph.spanningCoe})

/-- The indicator vector of a vertex set. -/
noncomputable def vertexVec (S : Set V) : V → ℝ :=
  fun v => by classical exact if v ∈ S then 1 else 0

/-- The vertex cover polytope. -/
noncomputable def VC (J : SimpleGraph V) : Set (V → ℝ) :=
  convexHull ℝ (vertexVec '' {S | J.IsVertexCover S})

/-- The minimum vertex covers. -/
def IsMinCover (J : SimpleGraph V) (S : Set V) : Prop :=
  J.IsVertexCover S ∧ ∀ S', J.IsVertexCover S' → S.ncard ≤ S'.ncard

/-- The minimum-cardinality face of the vertex cover polytope (convex hull of minimum covers). -/
noncomputable def minCoverFace (J : SimpleGraph V) : Set (V → ℝ) :=
  convexHull ℝ (vertexVec '' {S | IsMinCover J S})

/-- The correlation vector `(x_v, x_u x_v)` of the indicator vector of `X ⊆ V(L)`. -/
noncomputable def corVec (L : SimpleGraph V) (X : Set V) : V ⊕ L.edgeSet → ℝ :=
  fun i => by
    classical
    exact match i with
      | .inl v => if v ∈ X then 1 else 0
      | .inr e => if ∀ v ∈ (e : Sym2 V), v ∈ X then 1 else 0

/-- The correlation polytope of a graph `L` (one coordinate per vertex and per edge). -/
noncomputable def COR (L : SimpleGraph V) : Set (V ⊕ L.edgeSet → ℝ) :=
  convexHull ℝ (Set.range (corVec L))

/-- The `h × h` grid graph. -/
def grid (h : ℕ) : SimpleGraph (Fin h × Fin h) :=
  (pathGraph h) □ (pathGraph h)

/-! ### Basic facts -/

theorem edgeVec_apply (G K : SimpleGraph V) (e : G.edgeSet) [Decidable ((e : Sym2 V) ∈ K.edgeSet)] :
    edgeVec G K e = if (e : Sym2 V) ∈ K.edgeSet then 1 else 0 := by
  unfold edgeVec; congr

theorem edgeVec_eq_one_iff (G K : SimpleGraph V) (e : G.edgeSet) :
    edgeVec G K e = 1 ↔ (e : Sym2 V) ∈ K.edgeSet := by
  classical
  rw [edgeVec_apply]; split_ifs with h <;> simp [h]

theorem edgeVec_eq_zero_iff (G K : SimpleGraph V) (e : G.edgeSet) :
    edgeVec G K e = 0 ↔ (e : Sym2 V) ∉ K.edgeSet := by
  classical
  rw [edgeVec_apply]; split_ifs with h <;> simp [h]

theorem edgeVec_nonneg (G K : SimpleGraph V) (e : G.edgeSet) : 0 ≤ edgeVec G K e := by
  classical
  rw [edgeVec_apply]; split_ifs <;> norm_num

theorem edgeVec_le_one (G K : SimpleGraph V) (e : G.edgeSet) : edgeVec G K e ≤ 1 := by
  classical
  rw [edgeVec_apply]; split_ifs <;> norm_num

/-- Subgraphs of `G` are determined by their incidence vectors. -/
theorem edgeVec_injOn (G : SimpleGraph V) {K K' : SimpleGraph V} (hK : K ≤ G) (hK' : K' ≤ G)
    (h : edgeVec G K = edgeVec G K') : K = K' := by
  rw [← edgeSet_inj]
  ext e
  constructor
  · intro he
    have heG : e ∈ G.edgeSet := edgeSet_mono hK he
    have := congrFun h ⟨e, heG⟩
    rwa [(edgeVec_eq_one_iff G K _).mpr he, eq_comm, edgeVec_eq_one_iff] at this
  · intro he
    have heG : e ∈ G.edgeSet := edgeSet_mono hK' he
    have := congrFun h ⟨e, heG⟩
    rwa [(edgeVec_eq_one_iff G K' _).mpr he, edgeVec_eq_one_iff] at this

theorem vertexVec_apply (S : Set V) (v : V) [Decidable (v ∈ S)] :
    vertexVec S v = if v ∈ S then 1 else 0 := by
  unfold vertexVec; congr

/-- The coordinate sum of an incidence vector is the number of edges. -/
theorem sum_edgeVec [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : SimpleGraph V) (hK : K ≤ G) :
    ∑ e : G.edgeSet, edgeVec G K e = (Nat.card K.edgeSet : ℝ) := by
  classical
  simp_rw [edgeVec_apply]
  rw [Finset.sum_boole]
  congr 1
  rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  exact Fintype.card_congr
    (Equiv.subtypeSubtypeEquivSubtype (fun {e} (he : e ∈ K.edgeSet) => edgeSet_mono hK he))

/-- The coordinate sum of an indicator vector is the cardinality. -/
theorem sum_vertexVec [Fintype V] (S : Set V) :
    ∑ v : V, vertexVec S v = (S.ncard : ℝ) := by
  classical
  simp_rw [vertexVec_apply]
  rw [Finset.sum_boole, Set.ncard_eq_toFinset_card']
  congr 2
  ext v; simp

end Lemmata.PlanarSteinerXC
