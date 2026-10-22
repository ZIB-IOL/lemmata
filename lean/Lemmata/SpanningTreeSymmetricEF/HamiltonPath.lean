module

public import Lemmata.SpanningTreeSymmetricEF.PathOrbit
public import Lemmata.SpanningTreeSymmetricEF.GraphSubsetBounds

@[expose] public section

set_option backward.isDefEq.respectTransparency false


/-! Actual labeled Hamilton paths and their signed triangle certificate.
Labelings send vertex labels to positions; vertex relabeling is inverse
precomposition. Repeated trees in the permutation-indexed family are allowed. -/
namespace Lemmata.SpanningTreeSymmetricEF.HamiltonPath
open scoped BigOperators
open SimpleGraph PathCertificate PathLabeling ApproximationUpper GraphSubsetBounds Approximation
noncomputable section

/-- The actual graph on labels, pulled back from consecutive positions. -/
def graph {N : ℕ} (π : Equiv.Perm (Fin N)) : SimpleGraph (Fin N) :=
  (SimpleGraph.pathGraph N).comap π

/-- Consecutive positions determine an unordered edge on labels. -/
def pathEdge {n : ℕ} (π : Equiv.Perm (Fin (n + 1))) (t : Fin n) : Sym2 (Fin (n + 1)) :=
  s(π.symm t.castSucc, π.symm t.succ)

theorem pathEdge_injective {n : ℕ} (π : Equiv.Perm (Fin (n + 1))) :
    Function.Injective (pathEdge π) := by
  intro t u h
  rcases Sym2.eq_iff.mp h with h | h
  · have hh := π.symm.injective h.1
    exact Fin.ext (show t.val = u.val from congrArg (fun x : Fin (n + 1) => x.val) hh)
  · have h₁ := congrArg Fin.val (π.symm.injective h.1)
    have h₂ := congrArg Fin.val (π.symm.injective h.2)
    simp only [Fin.val_castSucc, Fin.val_succ] at h₁ h₂
    omega

/-- An explicit exhaustive edge enumeration, including the singleton path. -/
theorem edgeFinset_eq {n : ℕ} (π : Equiv.Perm (Fin (n + 1))) :
    letI := Classical.decRel (graph π).Adj
    (graph π).edgeFinset = Finset.univ.image (pathEdge π) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ a b =>
    simp only [mem_edgeFinset, mem_edgeSet, graph, comap_adj, pathGraph_adj,
      Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro h
      rcases h with h | h
      · let t : Fin n := ⟨(π a).val, by have := (π b).isLt; omega⟩
        refine ⟨t, ?_⟩
        have ha : t.castSucc = π a := by apply Fin.ext; rfl
        have hb : t.succ = π b := by apply Fin.ext; exact h
        simp [pathEdge, ha, hb]
      · let t : Fin n := ⟨(π b).val, by have := (π a).isLt; omega⟩
        refine ⟨t, ?_⟩
        have hb : t.castSucc = π b := by apply Fin.ext; rfl
        have ha : t.succ = π a := by apply Fin.ext; exact h
        simp [pathEdge, ha, hb, Sym2.eq_swap]
    · rintro ⟨t, ht⟩
      rcases Sym2.eq_iff.mp ht with ht | ht
      · left
        have ha := congrArg π ht.1
        have hb := congrArg π ht.2
        simp only [Equiv.apply_symm_apply] at ha hb
        rw [← ha, ← hb]
        rfl
      · right
        have ha := congrArg π ht.1
        have hb := congrArg π ht.2
        simp only [Equiv.apply_symm_apply] at ha hb
        rw [← ha, ← hb]
        rfl

theorem graph_isTree_succ {n : ℕ} (π : Equiv.Perm (Fin (n + 1))) :
    (graph π).IsTree := by
  classical
  apply isTree_iff_connected_and_card.mpr
  constructor
  · exact (SimpleGraph.Iso.comap π (pathGraph (n + 1))).connected_iff.mpr
      (pathGraph_connected n)
  · rw [Nat.card_eq_fintype_card, ← edgeFinset_card, edgeFinset_eq,
      Finset.card_image_of_injective _ (pathEdge_injective π)]
    simp

/-- Every nonempty labeled path is a genuine spanning tree. -/
theorem graph_isTree {N : ℕ} (hN : 1 ≤ N) (π : Equiv.Perm (Fin N)) :
    (graph π).IsTree := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  exact graph_isTree_succ π

/-- Actual graph equivariance for the inverse-precomposition action. -/
theorem graph_equivariant {N : ℕ} (π g : Equiv.Perm (Fin N)) :
    graph (π * g⁻¹) = (graph π).map g := by
  change graph (π * g⁻¹) = (graph π).map g.toEmbedding
  rw [← SimpleGraph.comap_symm (graph π) g]
  rfl

/-- The distinguished three-element vertex set. -/
def distinguished {N : ℕ} (s : Fin 3 ↪ Fin N) : Finset (Fin N) :=
  Finset.univ.image s

@[simp] theorem mem_distinguished {N : ℕ} (s : Fin 3 ↪ Fin N) (a : Fin N) :
    a ∈ distinguished s ↔ a = s 0 ∨ a = s 1 ∨ a = s 2 := by
  simp [distinguished, Fin.exists_fin_succ, eq_comm]

@[simp] theorem card_distinguished {N : ℕ} (s : Fin 3 ↪ Fin N) :
    (distinguished s).card = 3 := by
  simp [distinguished, Finset.card_image_of_injective _ s.injective]

/-- The usual triangle objective on the actual graph equals the count of
consecutive occupied positions, pointwise for every full labeling. -/
theorem triangle_objective_eq {n : ℕ} (s : Fin 3 ↪ Fin (n + 1))
    (π : Equiv.Perm (Fin (n + 1))) :
    objective (subsetCost (distinguished s)) (graphIncidence (graph π)) =
      ∑ t : Fin n, if t.castSucc ∈ ({π (s 0), π (s 1), π (s 2)} : Finset _) ∧
        t.succ ∈ ({π (s 0), π (s 1), π (s 2)} : Finset _) then (1 : ℝ) else 0 := by
  classical
  rw [objective_graphIncidence, edgeFinset_eq,
    Finset.sum_image (fun _ _ _ _ h => pathEdge_injective π h)]
  apply Finset.sum_congr rfl
  intro t _
  simp [subsetCost, pathEdge, mem_distinguished, Equiv.symm_apply_eq]

/-- The triangle objective of each actual labeled tree is at most two. -/
theorem triangle_objective_le_two {n : ℕ} (s : Fin 3 ↪ Fin (n + 1))
    (π : Equiv.Perm (Fin (n + 1))) :
    objective (subsetCost (distinguished s)) (graphIncidence (graph π)) ≤ 2 := by
  have h := tree_subset_objective (graph_isTree_succ π) (distinguished s)
    (show (distinguished s).Nonempty from ⟨s 0, by simp⟩)
  simpa using h.trans_eq (by norm_num : ((distinguished s).card : ℝ) - 1 = 2)

/-- Exact finite weighted objective of the actual labeled trees. No assumed
triangle moment or tree membership interface occurs in the hypotheses. -/
theorem weighted_triangle_objective {n : ℕ} (hn : 6 ≤ n + 1)
    (s : Fin 3 ↪ Fin (n + 1)) :
    (∑ π : Equiv.Perm (Fin (n + 1)), weight (cycleGraph (n + 1)) s π *
      objective (subsetCost (distinguished s)) (graphIncidence (graph π))) =
      3 * n / (n + 1) := by
  classical
  simp_rw [triangle_objective_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h (t : Fin n) :
      (∑ π : Equiv.Perm (Fin (n + 1)), weight (cycleGraph (n + 1)) s π *
        (if t.castSucc ∈ ({π (s 0), π (s 1), π (s 2)} : Finset _) ∧
          t.succ ∈ ({π (s 0), π (s 1), π (s 2)} : Finset _) then (1 : ℝ) else 0)) =
        eventMass (cycleGraph (n + 1)) (fun A => t.castSucc ∈ A ∧ t.succ ∈ A) := by
    simpa [mass, mul_ite] using mass_occupied (cycleGraph (n + 1)) s
      (fun A => t.castSucc ∈ A ∧ t.succ ∈ A)
  simp_rw [h]
  exact path_edge_moment n hn

/-- Labels and parity classify the permutation orbits. This finite key is
also used to partition preimages of tree orbits, without choosing tree fibers. -/
def orbitKey {N : ℕ} (W : Finset (Fin N)) (π : Equiv.Perm (Fin N)) :
    (↥W → Fin N) × ℤˣ := (fun w => π w, Equiv.Perm.sign π)

theorem orbitKey_eq_iff {N : ℕ} (W : Finset (Fin N))
    (π ρ : Equiv.Perm (Fin N)) :
    orbitKey W ρ = orbitKey W π ↔ PathOrbit.alternatingOrbit W π ρ := by
  rw [PathOrbit.alternatingOrbit_iff]
  simp only [orbitKey, Prod.mk.injEq, funext_iff]
  constructor
  · rintro ⟨h, hs⟩
    exact ⟨fun w hw => h ⟨w,hw⟩, hs⟩
  · rintro ⟨h, hs⟩
    exact ⟨fun w => h w w.property, hs⟩

/-- A union of actual permutation orbits has nonnegative signed mass. The
proof partitions a finite sum by restrictions and parity, so does not require
individual nonnegative weights. -/
theorem invariant_mass_nonneg {N : ℕ} (hN : 7 ≤ N)
    (s : Fin 3 ↪ Fin N) (W : Finset (Fin N)) (hW : W.card ≤ 2)
    (P : Equiv.Perm (Fin N) → Prop) [DecidablePred P]
    (hP : ∀ π ρ, PathOrbit.alternatingOrbit W π ρ → (P π ↔ P ρ)) :
    0 ≤ mass (cycleGraph N) s P := by
  classical
  let K := (↥W → Fin N) × ℤˣ
  have hfiber (k : K) : 0 ≤ ∑ ρ : Equiv.Perm (Fin N),
      if orbitKey W ρ = k then (if P ρ then weight (cycleGraph N) s ρ else 0) else 0 := by
    by_cases hk : ∃ π, orbitKey W π = k
    · obtain ⟨π, rfl⟩ := hk
      have he (ρ : Equiv.Perm (Fin N)) :
          (if orbitKey W ρ = orbitKey W π then
            (if P ρ then weight (cycleGraph N) s ρ else 0) else 0) =
          if P π then (if PathOrbit.alternatingOrbit W π ρ then weight (cycleGraph N) s ρ else 0)
            else 0 := by
        by_cases ho : PathOrbit.alternatingOrbit W π ρ
        · have hp := hP π ρ ho
          simp only [orbitKey_eq_iff, ho, if_true]
          by_cases hh : P π <;> simp_all
        · simp [orbitKey_eq_iff, ho]
      simp_rw [he]
      by_cases hp : P π
      · simp only [hp, if_true]
        exact PathOrbit.alternatingOrbit_nonneg (cycleGraph N) s
          (cycle_degree N (by omega)) (by simpa) W hW π
      · simp [hp]
    · have hh (ρ) : orbitKey W ρ ≠ k := fun h => hk ⟨ρ,h⟩
      simp [hh]
  have hsum : mass (cycleGraph N) s P = ∑ k : K, ∑ ρ : Equiv.Perm (Fin N),
      if orbitKey W ρ = k then (if P ρ then weight (cycleGraph N) s ρ else 0) else 0 := by
    rw [Finset.sum_comm]
    simp [mass, K]
  rw [hsum]
  exact Finset.sum_nonneg (fun k _ => hfiber k)

/-- Orbit relation on actual graphs under the alternating point stabilizer. -/
def graphOrbit {N : ℕ} (W : Finset (Fin N)) (T U : SimpleGraph (Fin N)) : Prop :=
  ∃ g : Equiv.Perm (Fin N), Equiv.Perm.sign g = 1 ∧
    (∀ w ∈ W, g w = w) ∧ U = T.comap (g⁻¹ : Equiv.Perm (Fin N))

/-- The relation really uses the standard vertex relabeling of graphs. -/
theorem graphOrbit_iff_map {N : ℕ} (W : Finset (Fin N)) (T U : SimpleGraph (Fin N)) :
    graphOrbit W T U ↔ ∃ g : Equiv.Perm (Fin N), Equiv.Perm.sign g = 1 ∧
      (∀ w ∈ W, g w = w) ∧ U = T.map g := by
  unfold graphOrbit
  apply exists_congr
  intro g
  have h : T.comap (g⁻¹ : Equiv.Perm (Fin N)) = T.map g :=
    SimpleGraph.comap_symm T g
  rw [h]

theorem graphOrbit_refl {N : ℕ} (W : Finset (Fin N)) (T : SimpleGraph (Fin N)) :
    graphOrbit W T T := by
  exact ⟨1, by simp, by simp, by simp⟩

theorem graphOrbit_symm {N : ℕ} (W : Finset (Fin N)) {T U : SimpleGraph (Fin N)}
    (h : graphOrbit W T U) : graphOrbit W U T := by
  obtain ⟨g, hg, hW, rfl⟩ := h
  refine ⟨g⁻¹, by simp [hg], ?_, ?_⟩
  · intro w hw
    apply g.injective
    simpa using (hW w hw).symm
  · ext a b
    simp

theorem graphOrbit_trans {N : ℕ} (W : Finset (Fin N)) {T U Z : SimpleGraph (Fin N)}
    (h : graphOrbit W T U) (h' : graphOrbit W U Z) : graphOrbit W T Z := by
  obtain ⟨g, hg, hgW, rfl⟩ := h
  obtain ⟨k, hk, hkW, rfl⟩ := h'
  refine ⟨k * g, by simp [hg, hk], ?_, ?_⟩
  · intro w hw
    simp [Equiv.Perm.mul_apply, hgW w hw, hkW w hw]
  · rfl

/-- Actual equivariant transfer of each labeling orbit into its graph orbit. -/
theorem labelOrbit_graphOrbit {N : ℕ} (W : Finset (Fin N))
    (π ρ : Equiv.Perm (Fin N)) (h : PathOrbit.alternatingOrbit W π ρ) :
    graphOrbit W (graph π) (graph ρ) := by
  obtain ⟨g, hg, hW, rfl⟩ := (PathOrbit.alternatingOrbit_iff_inverse_relabel W π ρ).mp h
  exact ⟨g, hg, hW, rfl⟩

/-- The full preimage of every actual graph orbit has nonnegative signed
mass. This includes graph fibers identifying different path orientations. -/
theorem graphOrbit_preimage_nonneg {N : ℕ} (hN : 7 ≤ N)
    (s : Fin 3 ↪ Fin N) (W : Finset (Fin N)) (hW : W.card ≤ 2)
    (T : SimpleGraph (Fin N)) :
    letI : DecidablePred (fun π : Equiv.Perm (Fin N) => graphOrbit W T (graph π)) :=
      fun _ => Classical.propDecidable _
    0 ≤ mass (cycleGraph N) s (fun π => graphOrbit W T (graph π)) := by
  classical
  have hP (π ρ : Equiv.Perm (Fin N)) (h : PathOrbit.alternatingOrbit W π ρ) :
      graphOrbit W T (graph π) ↔ graphOrbit W T (graph ρ) := by
    have hh := labelOrbit_graphOrbit W π ρ h
    exact ⟨fun hp => graphOrbit_trans W hp hh,
      fun hp => graphOrbit_trans W hp (graphOrbit_symm W hh)⟩
  exact invariant_mass_nonneg hN s W hW (fun π => graphOrbit W T (graph π)) hP

end
end Lemmata.SpanningTreeSymmetricEF.HamiltonPath
