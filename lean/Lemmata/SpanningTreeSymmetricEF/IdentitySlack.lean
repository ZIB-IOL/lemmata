module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Lemmata.SpanningTreeSymmetricEF.PSDRank

@[expose] public section


/-!
# Actual spanning-tree coordinate slacks

For any actual spanning tree of the complete graph, its missing edges index
an identity submatrix of coordinate incidences on actual spanning trees.
The final two endpoints here assume concrete PSD trace factors. The companion
PrimalPSDBound.lean uses these actual trees in a direct geometric proof;
NonnegativeOuter.lean supplies the full-coordinate outer-relaxation endpoint.
That route requires no construction of dual trace factors.
-/

namespace Lemmata.SpanningTreeSymmetricEF.IdentitySlack

open SimpleGraph Classical

variable {V : Type*}

/-- Missing edges of `T₀` among the loopless edges of the complete graph. -/
def Nonedge (T₀ : SimpleGraph V) :=
  {e : Sym2 V // e ∈ (⊤ : SimpleGraph V).edgeSet ∧ e ∉ T₀.edgeSet}

/-- A single loopless edge is acyclic, on the full vertex set. -/
theorem isAcyclic_singleton (e : Sym2 V)
    (he : e ∈ (⊤ : SimpleGraph V).edgeSet) :
    (fromEdgeSet {e}).IsAcyclic := by
  induction e using Sym2.ind with
  | _ u v =>
    have huv : u ≠ v := by simpa using he
    have h := (isAcyclic_bot : (⊥ : SimpleGraph V).IsAcyclic).sup_edge_of_not_reachable
      (u := u) (v := v) (by simpa only [reachable_bot] using huv)
    simpa only [bot_sup_eq, edge] using h

/-- Extend the chosen missing edge inside `T₀ ∪ {e}` to an actual spanning tree.
No cycle deletion or abstract identity hypothesis is required. -/
theorem exists_tree_for_nonedge (T₀ : SimpleGraph V) (hT₀ : T₀.IsTree)
    (e : Nonedge T₀) :
    ∃ T : SimpleGraph V, T.IsTree ∧
      ∀ f : Nonedge T₀, f.val ∈ T.edgeSet ↔ f = e := by
  have hconn : (T₀ ⊔ fromEdgeSet {e.val}).Connected :=
    hT₀.connected.mono le_sup_left
  obtain ⟨T, hlow, hupp, htree⟩ :=
    hconn.exists_isTree_le_of_le_of_isAcyclic le_sup_right
      (isAcyclic_singleton e.val e.property.1)
  refine ⟨T, htree, fun f => ⟨?_, ?_⟩⟩
  · intro hf
    have hmem := edgeSet_mono hupp hf
    rw [edgeSet_sup, edgeSet_fromEdgeSet] at hmem
    rcases hmem with hmem | hmem
    · exact False.elim (f.property.2 hmem)
    · exact Subtype.ext (Set.mem_singleton_iff.mp hmem.1)
  · rintro rfl
    apply edgeSet_mono hlow
    rw [edgeSet_fromEdgeSet]
    exact ⟨Set.mem_singleton _, by simpa only [edgeSet_top, Set.mem_compl_iff] using f.property.1⟩

/-- Coordinate slack of the valid inequality `x_e ≥ 0` at a graph incidence vector. -/
noncomputable def coordinateSlack (e : Sym2 V) (T : SimpleGraph V) : ℝ :=
  if e ∈ T.edgeSet then 1 else 0

/-- Every chosen coordinate inequality is tight at the original tree. -/
theorem coordinateSlack_base (T₀ : SimpleGraph V) (e : Nonedge T₀) :
    coordinateSlack e.val T₀ = 0 := by
  simp [coordinateSlack, e.property.2]

/-- Graph incidence coordinates satisfy the nonnegative coordinate inequalities. -/
theorem coordinateSlack_nonneg (e : Sym2 V) (T : SimpleGraph V) :
    0 ≤ coordinateSlack e T := by
  unfold coordinateSlack
  split <;> norm_num

/-- An actual identity submatrix, with rows indexed by missing edges and columns
by actual spanning trees on the same vertex set. -/
theorem exists_identity_slack (T₀ : SimpleGraph V) (hT₀ : T₀.IsTree) :
    ∃ T : Nonedge T₀ → SimpleGraph V,
      (∀ j, (T j).IsTree) ∧
      ∀ i j, coordinateSlack i.val (T j) = if i = j then 1 else 0 := by
  classical
  choose T hT hmem using exists_tree_for_nonedge T₀ hT₀
  exact ⟨T, hT, fun i j => by simp only [coordinateSlack, hmem]⟩

noncomputable instance [Fintype V] (T₀ : SimpleGraph V) : Fintype (Nonedge T₀) :=
  by
    classical
    unfold Nonedge
    infer_instance

/-- The number of missing edges of an actual spanning tree is exactly
`choose (|V| - 1) 2`, including the one- and two-vertex boundary cases. -/
theorem card_nonedge [Fintype V] (T₀ : SimpleGraph V) (hT₀ : T₀.IsTree) :
    Fintype.card (Nonedge T₀) = (Fintype.card V - 1).choose 2 := by
  classical
  have hcard : Fintype.card (Nonedge T₀) =
      ((⊤ : SimpleGraph V).edgeFinset \ T₀.edgeFinset).card :=
    Fintype.card_of_subtype _ (fun e => by simp)
  rw [hcard, Finset.card_sdiff_of_subset (edgeFinset_mono le_top),
    card_edgeFinset_top_eq_card_choose_two]
  have ht := hT₀.card_edgeFinset
  have hn : Fintype.card V = T₀.edgeFinset.card + 1 := ht.symm
  rw [hn, Nat.add_sub_cancel, Nat.choose_succ_succ' _ 1, Nat.choose_one_right]
  simp

/-- Concrete PSD factors for coordinate incidences of all actual spanning trees
must have order at least `choose (|V| - 1) 2`. The factorization itself is an
explicit input, not a claimed consequence of a geometric lift. -/
theorem order_bound_of_coordinate_factorization [Fintype V]
    {κ : Type*} [Fintype κ]
    (T₀ : SimpleGraph V) (hT₀ : T₀.IsTree)
    (A : Nonedge T₀ → Matrix κ κ ℝ)
    (B : {T : SimpleGraph V // T.IsTree} → Matrix κ κ ℝ)
    (hA : ∀ e, (A e).PosSemidef)
    (hB : ∀ T, (B T).PosSemidef)
    (htrace : ∀ e T, (A e * B T).trace = coordinateSlack e.val T.val) :
    (Fintype.card V - 1).choose 2 ≤ Fintype.card κ := by
  classical
  obtain ⟨T, hT, hid⟩ := exists_identity_slack T₀ hT₀
  rw [← card_nonedge T₀ hT₀]
  exact PSDRank.card_le_of_identity_factorization A (fun j => B ⟨T j, hT j⟩)
    hA (fun j => hB ⟨T j, hT j⟩) (fun i j => (htrace i ⟨T j, hT j⟩).trans (hid i j))

/-- The same bound for products of real PSD cones, with size measured by the
sum of the block orders. Again concrete coordinate trace factors are inputs. -/
theorem sum_order_bound_of_coordinate_factorization [Fintype V]
    {β : Type*} [Fintype β] {κ : β → Type*} [∀ b, Fintype (κ b)]
    (T₀ : SimpleGraph V) (hT₀ : T₀.IsTree)
    (A : Nonedge T₀ → ∀ b, Matrix (κ b) (κ b) ℝ)
    (B : {T : SimpleGraph V // T.IsTree} → ∀ b, Matrix (κ b) (κ b) ℝ)
    (hA : ∀ e b, (A e b).PosSemidef)
    (hB : ∀ T b, (B T b).PosSemidef)
    (htrace : ∀ e T, (∑ b, (A e b * B T b).trace) = coordinateSlack e.val T.val) :
    (Fintype.card V - 1).choose 2 ≤ ∑ b, Fintype.card (κ b) := by
  classical
  obtain ⟨T, hT, hid⟩ := exists_identity_slack T₀ hT₀
  rw [← card_nonedge T₀ hT₀]
  exact PSDRank.card_le_sum_of_identity_block_factorization A (fun j => B ⟨T j, hT j⟩)
    hA (fun j => hB ⟨T j, hT j⟩) (fun i j => (htrace i ⟨T j, hT j⟩).trans (hid i j))

end Lemmata.SpanningTreeSymmetricEF.IdentitySlack
