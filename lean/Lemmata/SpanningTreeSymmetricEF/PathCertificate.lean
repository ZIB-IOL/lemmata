module

/-
Actual finite cycle-incidence counting for the Hamilton-path certificate.
The sample points are ordered placements of the three distinguished labels.
Repeated placements have weight zero. Thus an unordered triple occurs six
 times, each with one sixth of its manuscript weight. No orbit or extension
membership claim is made here.
-/
public import Lemmata.SpanningTreeSymmetricEF.Approximation
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

@[expose] public section


namespace Lemmata.SpanningTreeSymmetricEF.PathCertificate

open scoped BigOperators
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Real indicator of an actual graph edge. -/
def edge (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) : ℝ :=
  if G.Adj i j then 1 else 0

omit [Fintype V] [DecidableEq V] in
@[simp] theorem edge_self (G : SimpleGraph V) [DecidableRel G.Adj] (i : V) :
    edge G i i = 0 := by simp [edge]

omit [Fintype V] [DecidableEq V] in
theorem edge_symm (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) :
    edge G i j = edge G j i := by simp only [edge, G.adj_comm]

omit [DecidableEq V] in
theorem sum_edge (G : SimpleGraph V) [DecidableRel G.Adj] (i : V) :
    ∑ j, edge G i j = (G.degree i : ℝ) := by
  simp [edge, SimpleGraph.degree, SimpleGraph.neighborFinset_def]

/-- Number of the three possible edges present on three specified vertices.
Its use below is restricted to distinct vertices. -/
def incidence (G : SimpleGraph V) [DecidableRel G.Adj] (i j k : V) : ℝ :=
  edge G i j + edge G i k + edge G j k

/-- The available third vertices form a genuine finite set. -/
def thirds (i j : V) : Finset V := (Finset.univ.erase i).erase j

@[simp] theorem mem_thirds (i j k : V) : k ∈ thirds i j ↔ k ≠ j ∧ k ≠ i := by
  simp [thirds]

theorem card_thirds (i j : V) (hij : i ≠ j) :
    (thirds i j).card = Fintype.card V - 2 := by
  simp [thirds, Finset.card_erase_of_mem, Ne.symm hij, Nat.sub_sub]

theorem sum_thirds (f : V → ℝ) (i j : V) (hij : i ≠ j) :
    ∑ k ∈ thirds i j, f k = (∑ k, f k) - f i - f j := by
  have hi : i ∈ (Finset.univ : Finset V) := Finset.mem_univ i
  have hj : j ∈ (Finset.univ.erase i : Finset V) := by simp [Ne.symm hij]
  have h₁ := Finset.sum_erase_add (Finset.univ : Finset V) f hi
  have h₂ := Finset.sum_erase_add (Finset.univ.erase i) f hj
  unfold thirds
  linarith

/-- Double-incidence count with a fixed pair, for any actual 2-regular graph.
For a cycle this is n for an edge and 4 for a nonedge; no counting formula
is a hypothesis. -/
theorem pair_incidence_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdegree : ∀ i, G.degree i = 2) (hn : 2 ≤ Fintype.card V)
    (i j : V) (hij : i ≠ j) :
    ∑ k ∈ thirds i j, incidence G i j k =
      ((Fintype.card V : ℝ) - 4) * edge G i j + 4 := by
  have hc : ((thirds i j).card : ℝ) = (Fintype.card V : ℝ) - 2 := by
    rw [card_thirds i j hij, Nat.cast_sub hn]
    norm_num
  simp only [incidence, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [hc, sum_thirds _ i j hij, sum_thirds _ i j hij,
    sum_edge, sum_edge, hdegree, hdegree, edge_self, edge_self, edge_symm G j i]
  norm_num
  ring

/-- Fixed-position incidence count. The factor two removes the two orders of
 the remaining positions. -/
theorem one_incidence_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdegree : ∀ i, G.degree i = 2) (hn : 2 ≤ Fintype.card V) (i : V) :
    (1 / 2 : ℝ) * (∑ j ∈ Finset.univ.erase i,
      ∑ k ∈ thirds i j, incidence G i j k) = 3 * (Fintype.card V - 2) := by
  have he : (∑ j ∈ Finset.univ.erase i, edge G i j) = 2 := by
    have h := Finset.sum_erase_add (Finset.univ : Finset V) (edge G i)
      (Finset.mem_univ i)
    rw [edge_self, add_zero, sum_edge, hdegree] at h
    exact_mod_cast h
  have hc : ((Finset.univ.erase i : Finset V).card : ℝ) = Fintype.card V - 1 := by
    simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card V)]
    norm_num
  have heq : (∑ j ∈ Finset.univ.erase i, ∑ k ∈ thirds i j, incidence G i j k) =
      ∑ j ∈ Finset.univ.erase i, (((Fintype.card V : ℝ) - 4) * edge G i j + 4) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact pair_incidence_count G hdegree hn i j (Ne.symm (Finset.mem_erase.mp hj).1)
  rw [heq, Finset.sum_add_distrib, ← Finset.mul_sum, he]
  simp only [Finset.sum_const, nsmul_eq_mul, hc]
  ring

/-- Total incidence count, counting each unordered triple six times before
 dividing by six. -/
theorem total_incidence_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdegree : ∀ i, G.degree i = 2) (hn : 2 ≤ Fintype.card V) :
    (1 / 6 : ℝ) * (∑ i, ∑ j ∈ Finset.univ.erase i,
      ∑ k ∈ thirds i j, incidence G i j k) =
        Fintype.card V * (Fintype.card V - 2) := by
  have hlocal (i : V) : (∑ j ∈ Finset.univ.erase i,
      ∑ k ∈ thirds i j, incidence G i j k) = 6 * (Fintype.card V - 2) := by
    linarith [one_incidence_count G hdegree hn i]
  simp_rw [hlocal]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem cycle_degree (n : ℕ) (hn : 3 ≤ n) (i : Fin n) :
    (SimpleGraph.cycleGraph n).degree i = 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  exact SimpleGraph.cycleGraph_degree_three_le

/-- Actual cycle specialization, using mathlib's proved cycle degrees. -/
theorem cycle_pair_incidence_count (n : ℕ) (hn : 3 ≤ n)
    (i j : Fin n) (hij : i ≠ j) :
    ∑ k ∈ thirds i j, incidence (SimpleGraph.cycleGraph n) i j k =
      ((n : ℝ) - 4) * edge (SimpleGraph.cycleGraph n) i j + 4 := by
  simpa using pair_incidence_count (SimpleGraph.cycleGraph n) (cycle_degree n hn)
    (by simpa using (show 2 ≤ n by omega)) i j hij

/-- Signed mass of an ordered placement of the three distinguished labels.
This is exactly `w_{ {i,j,k} } / 6` on distinct placements, and zero otherwise. -/
def orderedWeight (G : SimpleGraph V) [DecidableRel G.Adj] (i j k : V) : ℝ :=
  if i ≠ j ∧ i ≠ k ∧ j ≠ k then
    (3 / ((Fintype.card V : ℝ) * (Fintype.card V - 4)) / 6) *
      (incidence G i j k - 4 / (Fintype.card V - 2))
  else 0

theorem orderedWeight_swap_first (G : SimpleGraph V) [DecidableRel G.Adj]
    (i j k : V) : orderedWeight G i j k = orderedWeight G j i k := by
  simp only [orderedWeight, incidence, edge_symm G j i]
  by_cases hij : i = j <;> by_cases hik : i = k <;> by_cases hjk : j = k <;>
    simp_all [Ne.symm, add_comm, add_left_comm, add_assoc]

theorem orderedWeight_swap_last (G : SimpleGraph V) [DecidableRel G.Adj]
    (i j k : V) : orderedWeight G i j k = orderedWeight G i k j := by
  simp only [orderedWeight, incidence, edge_symm G k j]
  by_cases hij : i = j <;> by_cases hik : i = k <;> by_cases hjk : j = k <;>
    simp_all [Ne.symm, add_comm, add_assoc]

/-- Actual two-distinguished-label marginal, derived by summing over third
placements. No marginal identity is assumed. -/
theorem orderedWeight_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdegree : ∀ i, G.degree i = 2) (hn : 6 ≤ Fintype.card V) (i j : V) :
    ∑ k, orderedWeight G i j k = edge G i j / (2 * Fintype.card V) := by
  by_cases hij : i = j
  · subst j
    simp [orderedWeight]
  have hN : (6 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have h0 : (Fintype.card V : ℝ) ≠ 0 := by linarith
  have h2 : (Fintype.card V : ℝ) - 2 ≠ 0 := by linarith
  have h4 : (Fintype.card V : ℝ) - 4 ≠ 0 := by linarith
  have hc : ((thirds i j).card : ℝ) = (Fintype.card V : ℝ) - 2 := by
    rw [card_thirds i j hij, Nat.cast_sub (by omega : 2 ≤ Fintype.card V)]
    norm_num
  have heq : (∑ k, orderedWeight G i j k) =
      ∑ k ∈ thirds i j,
        (3 / ((Fintype.card V : ℝ) * (Fintype.card V - 4)) / 6) *
          (incidence G i j k - 4 / (Fintype.card V - 2)) := by
    calc
      _ = ∑ k ∈ thirds i j, orderedWeight G i j k := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro k _ hk
        simp only [mem_thirds, not_and_or, not_not] at hk
        rcases hk with rfl | rfl <;> simp [orderedWeight]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        have hm : k ≠ j ∧ k ≠ i := (mem_thirds i j k).mp hk
        simp [orderedWeight, hij, Ne.symm hm.1, Ne.symm hm.2]
  rw [heq, ← Finset.mul_sum, Finset.sum_sub_distrib,
    pair_incidence_count G hdegree (by omega) i j hij]
  simp only [Finset.sum_const, nsmul_eq_mul, hc]
  field_simp
  ring

/-- An individual distinguished label has uniform position marginal. -/
theorem orderedWeight_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdegree : ∀ i, G.degree i = 2) (hn : 6 ≤ Fintype.card V) (i : V) :
    ∑ j, ∑ k, orderedWeight G i j k = 1 / Fintype.card V := by
  simp_rw [orderedWeight_pair G hdegree hn, ← Finset.sum_div, sum_edge, hdegree]
  norm_num
  ring

/-- Normalization of the actual finite signed mass, not just of a formula. -/
theorem orderedWeight_total (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdegree : ∀ i, G.degree i = 2) (hn : 6 ≤ Fintype.card V) :
    ∑ i, ∑ j, ∑ k, orderedWeight G i j k = 1 := by
  simp_rw [orderedWeight_one G hdegree hn]
  have h0 : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast (show Fintype.card V ≠ 0 by omega)
  simp [h0]

/-- Mass of an event on the actual occupied-position set, pushed forward from
ordered placements. In particular this is a finite signed measure on triples. -/
def eventMass (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V → Prop)
    [DecidablePred P] : ℝ :=
  ∑ a, ∑ b, ∑ c, if P {a, b, c} then orderedWeight G a b c else 0

/-- The whole finite signed measure has mass one. -/
theorem eventMass_total (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdegree : ∀ i, G.degree i = 2) (hn : 6 ≤ Fintype.card V) :
    eventMass G (fun _ => True) = 1 := by
  simpa [eventMass] using orderedWeight_total G hdegree hn

private theorem one_event_split (G : SimpleGraph V) [DecidableRel G.Adj]
    (i a b c : V) :
    (if i ∈ ({a,b,c} : Finset V) then orderedWeight G a b c else 0) =
      (if a = i then orderedWeight G a b c else 0) +
      (if b = i then orderedWeight G a b c else 0) +
      (if c = i then orderedWeight G a b c else 0) := by
  by_cases ha : a = i <;> by_cases hb : b = i <;> by_cases hc : c = i <;>
    simp_all [orderedWeight, eq_comm]

/-- The occupied-position marginal is 3/n for the constructed measure. -/
theorem eventMass_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdegree : ∀ i, G.degree i = 2) (hn : 6 ≤ Fintype.card V) (i : V) :
    eventMass G (fun A => i ∈ A) = 3 / Fintype.card V := by
  simp only [eventMass, one_event_split, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h₁ := orderedWeight_one G hdegree hn i
  have h₂ : (∑ a, ∑ c, orderedWeight G a i c) = 1 / Fintype.card V := by
    simpa only [orderedWeight_swap_first G _ i] using h₁
  have h₃ : (∑ a, ∑ b, orderedWeight G a b i) = 1 / Fintype.card V := by
    simpa only [orderedWeight_swap_last G _ _ i] using h₂
  rw [h₁, h₂, h₃]
  ring

private theorem two_event_split (G : SimpleGraph V) [DecidableRel G.Adj]
    (i j a b c : V) (hij : i ≠ j) :
    (if i ∈ ({a,b,c} : Finset V) ∧ j ∈ ({a,b,c} : Finset V)
      then orderedWeight G a b c else 0) =
      (if a = i ∧ b = j then orderedWeight G a b c else 0) +
      (if a = i ∧ c = j then orderedWeight G a b c else 0) +
      (if b = i ∧ a = j then orderedWeight G a b c else 0) +
      (if b = i ∧ c = j then orderedWeight G a b c else 0) +
      (if c = i ∧ a = j then orderedWeight G a b c else 0) +
      (if c = i ∧ b = j then orderedWeight G a b c else 0) := by
  by_cases hai : a = i <;> by_cases hbi : b = i <;> by_cases hci : c = i <;>
    by_cases haj : a = j <;> by_cases hbj : b = j <;> by_cases hcj : c = j <;>
    simp_all [orderedWeight, eq_comm]

/-- Two-position marginal of the actual pushforward measure. -/
theorem eventMass_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdegree : ∀ i, G.degree i = 2) (hn : 6 ≤ Fintype.card V)
    (i j : V) (hij : i ≠ j) :
    eventMass G (fun A => i ∈ A ∧ j ∈ A) =
      3 * edge G i j / Fintype.card V := by
  simp only [eventMass, two_event_split G i j _ _ _ hij, Finset.sum_add_distrib]
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h₁ := orderedWeight_pair G hdegree hn i j
  have h₂ : (∑ b, orderedWeight G i b j) = edge G i j / (2 * Fintype.card V) := by
    simpa only [orderedWeight_swap_last G i _ j] using h₁
  have h₃ := orderedWeight_pair G hdegree hn j i
  have h₄ : (∑ a, orderedWeight G a i j) = edge G i j / (2 * Fintype.card V) := by
    simpa only [orderedWeight_swap_first G _ i] using h₂
  have h₅ : (∑ b, orderedWeight G j b i) = edge G j i / (2 * Fintype.card V) := by
    simpa only [orderedWeight_swap_last G j _ i] using h₃
  have h₆ : (∑ a, orderedWeight G a j i) = edge G j i / (2 * Fintype.card V) := by
    simpa only [orderedWeight_swap_first G _ j] using h₅
  rw [h₁, h₂, h₃, h₄, h₅, h₆, edge_symm G j i]
  ring

/-- Inclusion-exclusion is proved for the finite event sums themselves. -/
theorem eventMass_and_not (G : SimpleGraph V) [DecidableRel G.Adj]
    (i j : V) :
    eventMass G (fun A => i ∈ A ∧ j ∉ A) =
      eventMass G (fun A => i ∈ A) - eventMass G (fun A => i ∈ A ∧ j ∈ A) := by
  simp only [eventMass, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  by_cases hi : i ∈ ({a,b,c} : Finset V) <;>
    by_cases hj : j ∈ ({a,b,c} : Finset V) <;> simp [hi, hj]

theorem eventMass_neither (G : SimpleGraph V) [DecidableRel G.Adj]
    (i j : V) :
    eventMass G (fun A => i ∉ A ∧ j ∉ A) =
      eventMass G (fun _ => True) - eventMass G (fun A => i ∈ A) -
        eventMass G (fun A => j ∈ A) + eventMass G (fun A => i ∈ A ∧ j ∈ A) := by
  simp only [eventMass, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  by_cases hi : i ∈ ({a,b,c} : Finset V) <;>
    by_cases hj : j ∈ ({a,b,c} : Finset V) <;> simp [hi, hj]

/-- All three two-position color events have nonnegative actual signed mass.
The mixed event with the positions reversed follows by exchanging i and j.
These are occupation events, not yet fibers of full vertex permutations. -/
theorem two_position_events_nonnegative (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdegree : ∀ i, G.degree i = 2) (hn : 6 ≤ Fintype.card V)
    (i j : V) (hij : i ≠ j) :
    0 ≤ eventMass G (fun A => i ∈ A ∧ j ∈ A) ∧
    0 ≤ eventMass G (fun A => i ∈ A ∧ j ∉ A) ∧
    0 ≤ eventMass G (fun A => i ∉ A ∧ j ∉ A) := by
  rw [eventMass_and_not, eventMass_neither, eventMass_total G hdegree hn,
    eventMass_one G hdegree hn, eventMass_one G hdegree hn,
    eventMass_pair G hdegree hn i j hij]
  have hN : (6 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hpos : (0 : ℝ) < Fintype.card V := by linarith
  have hsmall : 6 / (Fintype.card V : ℝ) ≤ 1 := (div_le_one hpos).mpr hN
  have hsplit : (6 : ℝ) / Fintype.card V =
      3 / Fintype.card V + 3 / Fintype.card V := by ring
  by_cases he : G.Adj i j
  · simp only [edge, if_pos he, mul_one]
    refine ⟨by positivity, by simp, ?_⟩
    linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 3) hpos.le]
  · simp only [edge, if_neg he, mul_zero, zero_div, sub_zero, add_zero]
    refine ⟨le_rfl, by positivity, ?_⟩
    linarith

/-- Unconditional cycle certificate at the occupied-position level. The only
hypothesis is the manuscript's n ≥ 6. Full permutation-labeling fibers and
alternating tree-orbit pushforward are not asserted by this endpoint. -/
theorem cycle_certificate (n : ℕ) (hn : 6 ≤ n) :
    eventMass (SimpleGraph.cycleGraph n) (fun _ => True) = 1 ∧
    (∀ i : Fin n, eventMass (SimpleGraph.cycleGraph n) (fun A => i ∈ A) = 3 / n) ∧
    (∀ i j : Fin n, i ≠ j →
      eventMass (SimpleGraph.cycleGraph n) (fun A => i ∈ A ∧ j ∈ A) =
        if (SimpleGraph.cycleGraph n).Adj i j then (3 : ℝ) / n else 0) ∧
    (∀ i j : Fin n, i ≠ j →
      0 ≤ eventMass (SimpleGraph.cycleGraph n) (fun A => i ∈ A ∧ j ∈ A) ∧
      0 ≤ eventMass (SimpleGraph.cycleGraph n) (fun A => i ∈ A ∧ j ∉ A) ∧
      0 ≤ eventMass (SimpleGraph.cycleGraph n) (fun A => i ∉ A ∧ j ∉ A)) := by
  have hd := cycle_degree n (by omega)
  have hc : 6 ≤ Fintype.card (Fin n) := by simpa
  refine ⟨eventMass_total _ hd hc, ?_, ?_, ?_⟩
  · intro i
    simpa using eventMass_one _ hd hc i
  · intro i j hij
    rw [eventMass_pair _ hd hc i j hij]
    by_cases he : (SimpleGraph.cycleGraph n).Adj i j <;> simp [edge, he]
  · intro i j hij
    exact two_position_events_nonnegative _ hd hc i j hij

/-- The sum of the actual occupied-pair moments over the n edges of the
Hamilton path on n+1 positions. The closing cycle edge is omitted. This is
already the required triangle count at the position level, before tree
pushforward or assigning the remaining labels. -/
theorem path_edge_moment (n : ℕ) (hn : 6 ≤ n + 1) :
    (∑ t : Fin n, eventMass (SimpleGraph.cycleGraph (n + 1))
      (fun A => t.castSucc ∈ A ∧ t.succ ∈ A)) = 3 * n / (n + 1) := by
  have hpair (t : Fin n) : eventMass (SimpleGraph.cycleGraph (n + 1))
      (fun A => t.castSucc ∈ A ∧ t.succ ∈ A) = 3 / (n + 1) := by
    have hadj : (SimpleGraph.cycleGraph (n + 1)).Adj t.castSucc t.succ := by
      apply SimpleGraph.pathGraph_le_cycleGraph
      simp [SimpleGraph.pathGraph_adj]
    have hne : t.castSucc ≠ t.succ := by
      intro heq
      have := congrArg Fin.val heq
      simp only [Fin.val_castSucc, Fin.val_succ] at this
      omega
    simpa [hadj] using (cycle_certificate (n + 1) hn).2.2.1 t.castSucc t.succ hne
  simp_rw [hpair]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end
end Lemmata.SpanningTreeSymmetricEF.PathCertificate
